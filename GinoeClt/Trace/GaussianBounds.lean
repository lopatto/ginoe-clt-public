/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.Energy
public import GinoeClt.Trace.GaussianPath

/-! # Absolute Gaussian bounds on the actual cycle integrands -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Paper.Trace

theorem pathEnergy_cons_succ {n : ℕ} (z : ℂ) (u : Fin (n + 1) → ℂ) :
    pathEnergy (Fin.cons z u) = ‖u 0 - z‖ ^ 2 +
      pathEnergy (Fin.cons (u 0) (Fin.tail u)) := by
  simp only [pathEnergy, Fin.sum_univ_succ]
  simp [Fin.tail]

theorem pathGaussian_eq_exp {a : ℝ} (n : ℕ) (z : ℂ) (u : Fin n → ℂ) :
    pathGaussian a n z u = Real.exp (-a * pathEnergy (Fin.cons z u)) := by
  induction n generalizing z with
  | zero => simp [pathGaussian, pathEnergy]
  | succ n ih =>
    rw [pathGaussian, ih, pathEnergy_cons_succ, mul_add, Real.exp_add]

theorem continuous_cycleEnergy (k : ℕ) : Continuous (cycleEnergy (k := k)) := by
  change Continuous (fun z : Fin k → ℂ => ∑ i : Fin k, ‖z i - z (finRotate k i)‖ ^ 2)
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).sub (continuous_apply (finRotate k i))).norm.pow 2

theorem continuous_cons (n : ℕ) (z : ℂ) :
    Continuous (fun u : Fin n → ℂ => (Fin.cons z u : Fin (n + 1) → ℂ)) :=
  continuous_pi fun i => Fin.cases continuous_const (fun j => continuous_apply j) i

theorem cycleGaussian_le_pathGaussian {a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (z : ℂ) (u : Fin n → ℂ) :
    Real.exp (-a * cycleEnergy (Fin.cons z u)) ≤ pathGaussian a n z u := by
  rw [pathGaussian_eq_exp]
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (pathEnergy_le_cycleEnergy _) (neg_nonpos.mpr ha))

theorem integrable_cycleGaussian {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) :
    Integrable (fun u : Fin n → ℂ => Real.exp (-a * cycleEnergy (Fin.cons z u))) := by
  have hc : Continuous (fun u : Fin n → ℂ =>
      Real.exp (-a * cycleEnergy (Fin.cons z u))) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_cycleEnergy (n + 1)).comp (continuous_cons n z)))
  apply (integrable_integral_pathGaussian ha n z).1.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact cycleGaussian_le_pathGaussian ha.le n z u

theorem setIntegral_cycleGaussian_le {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ)
    (E : Set (Fin n → ℂ)) :
    (∫ u in E, Real.exp (-a * cycleEnergy (Fin.cons z u))) ≤ (Real.pi / a) ^ n := by
  calc
    (∫ u in E, Real.exp (-a * cycleEnergy (Fin.cons z u))) ≤
        ∫ u in E, pathGaussian a n z u := by
      exact integral_mono_ae (integrable_cycleGaussian ha n z).integrableOn
        (integrable_integral_pathGaussian ha n z).1.integrableOn
        (Filter.Eventually.of_forall fun u => cycleGaussian_le_pathGaussian ha.le n z u)
    _ ≤ ∫ u : Fin n → ℂ, pathGaussian a n z u :=
      setIntegral_le_integral (integrable_integral_pathGaussian ha n z).1
        (Filter.Eventually.of_forall fun u => pathGaussian_nonneg a n z u)
    _ = _ := (integrable_integral_pathGaussian ha n z).2

theorem integrable_anchored_cycleGaussian {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    Integrable (fun p : ℂ × (Fin n → ℂ) =>
      Real.exp (-a * cycleEnergy (Fin.cons p.1 p.2)))
      ((volume.restrict A).prod volume) := by
  let F : (ℂ × (Fin n → ℂ)) → ℝ := fun p =>
    Real.exp (-a * cycleEnergy (Fin.cons p.1 p.2))
  have hc : Continuous F := by
    have hcons : Continuous (fun p : ℂ × (Fin n → ℂ) =>
        (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ)) :=
      continuous_pi fun i => Fin.cases continuous_fst
        (fun j => (continuous_apply j).comp continuous_snd) i
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_cycleEnergy (n + 1)).comp hcons))
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun z => integrable_cycleGaussian ha n z
  · have hm : AEStronglyMeasurable (fun z : ℂ => ∫ u : Fin n → ℂ, ‖F (z, u)‖)
        (volume.restrict A) := hc.aestronglyMeasurable.norm.integral_prod_right'
    apply (integrableOn_const (C := (Real.pi / a) ^ n) hA).mono' hm
    filter_upwards with z
    rw [Real.norm_of_nonneg (integral_nonneg fun u => norm_nonneg _)]
    have he : (fun u : Fin n → ℂ => ‖F (z, u)‖) =
        (fun u => Real.exp (-a * cycleEnergy (Fin.cons z u))) := by
      funext u
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    rw [he]
    exact (integral_mono_ae (integrable_cycleGaussian ha n z)
      (integrable_integral_pathGaussian ha n z).1
      (Filter.Eventually.of_forall fun u => cycleGaussian_le_pathGaussian ha.le n z u)).trans_eq
        (integrable_integral_pathGaussian ha n z).2

theorem anchored_cycleGaussian_bound {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    (∫ z in A, ∫ u : Fin n → ℂ, Real.exp (-a * cycleEnergy (Fin.cons z u))) ≤
      volume.real A * (Real.pi / a) ^ n := by
  have hi := integrable_anchored_cycleGaussian ha n A hA
  calc
    (∫ z in A, ∫ u : Fin n → ℂ, Real.exp (-a * cycleEnergy (Fin.cons z u))) ≤
        ∫ _z in A, (Real.pi / a) ^ n := by
      apply integral_mono_ae hi.integral_prod_left (integrableOn_const hA)
      filter_upwards with z
      exact (integral_mono_ae (integrable_cycleGaussian ha n z)
        (integrable_integral_pathGaussian ha n z).1
        (Filter.Eventually.of_forall fun u => cycleGaussian_le_pathGaussian ha.le n z u)).trans_eq
          (integrable_integral_pathGaussian ha n z).2
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

theorem cycleGaussian_integral_split {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    IntegrableOn (fun x : Fin (n + 1) → ℂ => Real.exp (-a * cycleEnergy x))
      (Set.univ.pi fun _ : Fin (n + 1) => A) ∧
    (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A), Real.exp (-a * cycleEnergy x)) =
      ∫ z in A, ∫ u in Set.univ.pi (fun _ : Fin n => A),
        Real.exp (-a * cycleEnergy (Fin.cons z u)) := by
  let E := Set.univ.pi (fun _ : Fin n => A)
  let B := Set.univ.pi (fun _ : Fin (n + 1) => A)
  let F : (ℂ × (Fin n → ℂ)) → ℝ := fun p =>
    Real.exp (-a * cycleEnergy (Fin.cons p.1 p.2))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  have hm : MeasurePreserving e.symm ((volume.restrict A).prod (volume.restrict E))
      (volume.restrict B) := by
    change MeasurePreserving e.symm
      (((volume : Measure ℂ).restrict A).prod
        ((Measure.pi (fun _ : Fin n => (volume : Measure ℂ))).restrict
          (Set.univ.pi (fun _ : Fin n => A))))
      ((Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℂ))).restrict
        (Set.univ.pi (fun _ : Fin (n + 1) => A)))
    rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
    exact (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (volume : Measure ℂ).restrict A) 0).symm
  have heq : (fun x => Real.exp (-a * cycleEnergy x)) ∘ e.symm = F := by
    funext p
    simp [e, F, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.zero_succAbove]
  have hFi : Integrable F ((volume.restrict A).prod (volume.restrict E)) :=
    (integrable_anchored_cycleGaussian ha n A hA).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hvec : Integrable (fun x : Fin (n + 1) → ℂ => Real.exp (-a * cycleEnergy x))
      (volume.restrict B) := by
    apply (hm.integrable_comp_emb e.symm.measurableEmbedding).mp
    rw [heq]
    exact hFi
  refine ⟨hvec, ?_⟩
  calc
    (∫ x in B, Real.exp (-a * cycleEnergy x)) =
        ∫ p, F p ∂((volume.restrict A).prod (volume.restrict E)) := by
      rw [← hm.integral_comp' (fun x => Real.exp (-a * cycleEnergy x))]
      change (∫ p, ((fun x => Real.exp (-a * cycleEnergy x)) ∘ e.symm) p
        ∂((volume.restrict A).prod (volume.restrict E))) = _
      rw [heq]
    _ = _ := integral_prod F hFi

theorem cycleGaussian_bound {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A), Real.exp (-a * cycleEnergy x)) ≤
      volume.real A * (Real.pi / a) ^ n := by
  rw [(cycleGaussian_integral_split ha n A hA).2]
  have hi := ((integrable_anchored_cycleGaussian ha n A hA).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := Set.univ.pi
      (fun _ : Fin n => A))))).integral_prod_left
  calc
    (∫ z in A, ∫ u in Set.univ.pi (fun _ : Fin n => A),
        Real.exp (-a * cycleEnergy (Fin.cons z u))) ≤
        ∫ _z in A, (Real.pi / a) ^ n := by
      apply integral_mono_ae hi (integrableOn_const hA)
      exact Filter.Eventually.of_forall fun z => setIntegral_cycleGaussian_le ha n z _
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

end Paper.Trace
