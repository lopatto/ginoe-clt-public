/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.CrossingGaussian

/-! # Integrating the free leaves of a Gaussian path with one crossing -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Paper.Trace

def pathWeight (a : ℝ) {n : ℕ} (x : Fin (n + 1) → ℂ) : ℝ :=
  Real.exp (-a * pathEnergy x)

def pathCrossingDomain (A : Set ℂ) (n : ℕ) (j : Fin (n + 1)) :
    Set (Fin (n + 2) → ℂ) := {x | x j.castSucc ∈ A ∧ x j.succ ∈ Aᶜ}

theorem pathWeight_cons (a : ℝ) (n : ℕ) (z : ℂ) (u : Fin n → ℂ) :
    pathWeight a (Fin.cons z u) = pathGaussian a n z u :=
  (pathGaussian_eq_exp (a := a) n z u).symm

theorem pathWeight_cons_succ (a : ℝ) {n : ℕ} (z : ℂ) (u : Fin (n + 1) → ℂ) :
    pathWeight a (Fin.cons z u) =
      Real.exp (-a * ‖u 0 - z‖ ^ 2) * pathWeight a u := by
  rw [pathWeight_cons, pathGaussian]
  congr 1
  rw [pathGaussian_eq_exp, Fin.cons_self_tail]
  rfl

theorem measurableSet_pathCrossingDomain {A : Set ℂ} (hA : MeasurableSet A)
    (n : ℕ) (j : Fin (n + 1)) : MeasurableSet (pathCrossingDomain A n j) :=
  (hA.preimage (measurable_pi_apply j.castSucc)).inter
    (hA.compl.preimage (measurable_pi_apply j.succ))

theorem firstExit_subset_pathCrossingDomain (A : Set ℂ) (n : ℕ) (j : Fin (n + 1)) :
    firstExitDomain A (n + 1) j ⊆ pathCrossingDomain A n j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · intro x hx
    exact ⟨hx.1, hx.2.2⟩
  · intro x hx
    refine ⟨?_, hx.2.2⟩
    change x i.castSucc.succ ∈ A
    exact hx.2.1 i.castSucc (by change (i : ℕ) < (i : ℕ) + 1; omega)

private theorem split_head_restrict (n : ℕ) (B : Set ℂ) (S : Set (Fin n → ℂ)) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
      ((volume.restrict B).prod (volume.restrict S))
      (volume.restrict {x : Fin (n + 1) → ℂ | x 0 ∈ B ∧ Fin.tail x ∈ S}) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  have hm : MeasurePreserving e.symm (volume : Measure (ℂ × (Fin n → ℂ))) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
  have hb : e.symm ⁻¹' {x : Fin (n + 1) → ℂ | x 0 ∈ B ∧ Fin.tail x ∈ S} = B ×ˢ S := by
    ext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.zero_succAbove]
  have h := hm.restrict_preimage_emb e.symm.measurableEmbedding
    {x : Fin (n + 1) → ℂ | x 0 ∈ B ∧ Fin.tail x ∈ S}
  rw [hb, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  exact h

theorem pathGaussian_restrict_first {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) (B : Set ℂ) :
    IntegrableOn (pathGaussian a (n + 1) z) {u | u 0 ∈ B} ∧
    (∫ u : Fin (n + 1) → ℂ in {u | u 0 ∈ B}, pathGaussian a (n + 1) z u) =
      (Real.pi / a) ^ n * (∫ w in B, Real.exp (-a * ‖w - z‖ ^ 2)) := by
  let D : Set (Fin (n + 1) → ℂ) := {u | u 0 ∈ B}
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  let F : (ℂ × (Fin n → ℂ)) → ℝ := fun p =>
    Real.exp (-a * ‖p.1 - z‖ ^ 2) * pathGaussian a n p.1 p.2
  have hr : MeasurePreserving e.symm ((volume.restrict B).prod volume) (volume.restrict D) := by
    simpa only [Measure.restrict_univ, Set.mem_univ, and_true] using
      split_head_restrict n B (Set.univ : Set (Fin n → ℂ))
  have he : (pathGaussian a (n + 1) z) ∘ e.symm = F := by
    funext p
    simp [e, F, pathGaussian, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.zero_succAbove]
  have hi : IntegrableOn (pathGaussian a (n + 1) z) D :=
    (integrable_integral_pathGaussian ha (n + 1) z).1.integrableOn
  have hFi : Integrable F ((volume.restrict B).prod volume) := by
    have h := (hr.integrable_comp_emb e.symm.measurableEmbedding).mpr hi
    rwa [he] at h
  refine ⟨hi, ?_⟩
  calc
    (∫ u in D, pathGaussian a (n + 1) z u) = ∫ p, F p ∂((volume.restrict B).prod volume) := by
      rw [← hr.integral_comp' (pathGaussian a (n + 1) z)]
      change (∫ p, ((pathGaussian a (n + 1) z) ∘ e.symm) p ∂((volume.restrict B).prod volume)) = _
      rw [he]
    _ = ∫ w in B, ∫ u : Fin n → ℂ, F (w, u) := integral_prod F hFi
    _ = ∫ w in B, Real.exp (-a * ‖w - z‖ ^ 2) * (Real.pi / a) ^ n := by
      apply integral_congr_ae
      filter_upwards with w
      dsimp only [F]
      rw [integral_const_mul, (integrable_integral_pathGaussian ha n w).2]
    _ = _ := by rw [integral_mul_const]; ring

theorem path_crossing_zero {a : ℝ} (ha : 0 < a) (n : ℕ) (A : Set ℂ)
    (hA : volume A ≠ ⊤) :
    IntegrableOn (pathWeight a) (pathCrossingDomain A n 0) ∧
      (∫ x in pathCrossingDomain A n 0, pathWeight a x) =
        (Real.pi / a) ^ n * gaussianCrossing a A := by
  let S : Set (Fin (n + 1) → ℂ) := {u | u 0 ∈ Aᶜ}
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℂ) 0
  let F : (ℂ × (Fin (n + 1) → ℂ)) → ℝ := fun p => pathGaussian a (n + 1) p.1 p.2
  have hr : MeasurePreserving e.symm ((volume.restrict A).prod (volume.restrict S))
      (volume.restrict (pathCrossingDomain A n 0)) := by
    simpa only [e, S, pathCrossingDomain, Set.mem_ofPred_eq, Fin.tail, Fin.castSucc_zero] using
      split_head_restrict (n + 1) A S
  have he : (pathWeight a) ∘ e.symm = F := by
    funext p
    simp [e, F, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.zero_succAbove, pathWeight_cons]
  have hnorm (z : ℂ) : (∫ u in S, ‖F (z, u)‖) =
      (Real.pi / a) ^ n * (∫ w in Aᶜ, Real.exp (-a * ‖w - z‖ ^ 2)) := by
    calc
      (∫ u in S, ‖F (z, u)‖) = ∫ u in S, F (z, u) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u =>
          Real.norm_of_nonneg (pathGaussian_nonneg a (n + 1) z u)
      _ = _ := (pathGaussian_restrict_first ha n z Aᶜ).2
  have hFi : Integrable F ((volume.restrict A).prod (volume.restrict S)) := by
    apply (integrable_prod_iff (continuous_pathGaussian a (n + 1)).aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun z => (pathGaussian_restrict_first ha n z Aᶜ).1
    · change Integrable (fun z : ℂ => ∫ u in S, ‖F (z, u)‖) (volume.restrict A)
      simp only [hnorm]
      exact (integrable_gaussianCrossing ha A hA).integral_prod_left.const_mul ((Real.pi / a) ^ n)
  have hi : IntegrableOn (pathWeight a) (pathCrossingDomain A n 0) := by
    apply (hr.integrable_comp_emb e.symm.measurableEmbedding).mp
    rw [he]
    exact hFi
  refine ⟨hi, ?_⟩
  calc
    (∫ x in pathCrossingDomain A n 0, pathWeight a x) =
        ∫ p, F p ∂((volume.restrict A).prod (volume.restrict S)) := by
      rw [← hr.integral_comp' (pathWeight a)]
      change (∫ p, ((pathWeight a) ∘ e.symm) p ∂((volume.restrict A).prod (volume.restrict S))) = _
      rw [he]
    _ = ∫ z in A, ∫ u in S, F (z, u) := integral_prod F hFi
    _ = ∫ z in A, (Real.pi / a) ^ n * (∫ w in Aᶜ, Real.exp (-a * ‖w - z‖ ^ 2)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => (pathGaussian_restrict_first ha n z Aᶜ).2
    _ = _ := by rw [integral_const_mul]; rfl

theorem continuous_pathWeight (a : ℝ) (n : ℕ) : Continuous (pathWeight a (n := n)) := by
  have he : Continuous (pathEnergy (n := n)) := by
    change Continuous (fun x : Fin (n + 1) → ℂ => ∑ i : Fin n, ‖x i.succ - x i.castSucc‖ ^ 2)
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i.succ).sub (continuous_apply i.castSucc)).norm.pow 2
  unfold pathWeight
  exact Real.continuous_exp.comp (continuous_const.mul he)

private theorem path_crossing_step {a : ℝ} (ha : 0 < a) (n : ℕ) (A : Set ℂ)
    (j : Fin (n + 1))
    (htail : IntegrableOn (pathWeight a) (pathCrossingDomain A n j) ∧
      (∫ v in pathCrossingDomain A n j, pathWeight a v) =
        (Real.pi / a) ^ n * gaussianCrossing a A) :
    IntegrableOn (pathWeight a) (pathCrossingDomain A (n + 1) j.succ) ∧
      (∫ x in pathCrossingDomain A (n + 1) j.succ, pathWeight a x) =
        (Real.pi / a) ^ (n + 1) * gaussianCrossing a A := by
  let D := pathCrossingDomain A n j
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 3) => ℂ) 0
  let F : (ℂ × (Fin (n + 2) → ℂ)) → ℝ := fun p =>
    Real.exp (-a * ‖p.2 0 - p.1‖ ^ 2) * pathWeight a p.2
  have hD : {x : Fin (n + 3) → ℂ | x 0 ∈ (Set.univ : Set ℂ) ∧ Fin.tail x ∈ D} =
      pathCrossingDomain A (n + 1) j.succ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, D, pathCrossingDomain]
    rfl
  have hr : MeasurePreserving e.symm (volume.prod (volume.restrict D))
      (volume.restrict (pathCrossingDomain A (n + 1) j.succ)) := by
    have h := split_head_restrict (n + 2) (Set.univ : Set ℂ) D
    rw [Measure.restrict_univ, hD] at h
    exact h
  have he : (pathWeight a) ∘ e.symm = F := by
    funext p
    simp [e, F, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.zero_succAbove, pathWeight_cons_succ]
  have hc : Continuous F := by
    have hg : Continuous (fun p : ℂ × (Fin (n + 2) → ℂ) =>
        Real.exp (-a * ‖p.2 0 - p.1‖ ^ 2)) := by fun_prop
    exact hg.mul ((continuous_pathWeight a (n + 1)).comp continuous_snd)
  have hinner (v : Fin (n + 2) → ℂ) : (∫ w : ℂ, F (w, v)) =
      (Real.pi / a) * pathWeight a v := by
    dsimp only [F]
    rw [integral_mul_const]
    have hg : (∫ w : ℂ, Real.exp (-a * ‖v 0 - w‖ ^ 2)) = Real.pi / a := by
      simpa only [norm_sub_rev] using integral_gaussian_sub ha (v 0)
    rw [hg]
  have hnorm (v : Fin (n + 2) → ℂ) : (∫ w : ℂ, ‖F (w, v)‖) =
      (Real.pi / a) * pathWeight a v := by
    calc
      (∫ w : ℂ, ‖F (w, v)‖) = ∫ w : ℂ, F (w, v) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => Real.norm_of_nonneg
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = _ := hinner v
  have hFi : Integrable F (volume.prod (volume.restrict D)) := by
    apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
    constructor
    · exact Filter.Eventually.of_forall fun v => by
        simpa only [F, norm_sub_rev] using
          (integrable_gaussian_sub ha (v 0)).mul_const (pathWeight a v)
    · change Integrable (fun v => ∫ w : ℂ, ‖F (w, v)‖) (volume.restrict D)
      simp only [hnorm]
      exact htail.1.const_mul (Real.pi / a)
  have hi : IntegrableOn (pathWeight a) (pathCrossingDomain A (n + 1) j.succ) := by
    apply (hr.integrable_comp_emb e.symm.measurableEmbedding).mp
    rw [he]
    exact hFi
  refine ⟨hi, ?_⟩
  calc
    (∫ x in pathCrossingDomain A (n + 1) j.succ, pathWeight a x) =
        ∫ p, F p ∂(volume.prod (volume.restrict D)) := by
      rw [← hr.integral_comp' (pathWeight a)]
      change (∫ p, ((pathWeight a) ∘ e.symm) p ∂(volume.prod (volume.restrict D))) = _
      rw [he]
    _ = ∫ v in D, ∫ w : ℂ, F (w, v) := integral_prod_symm F hFi
    _ = (Real.pi / a) * ∫ v in D, pathWeight a v := by
      simp_rw [hinner]
      rw [integral_const_mul]
    _ = _ := by rw [htail.2, pow_succ]; ring

theorem path_crossing_integral {a : ℝ} (ha : 0 < a) (n : ℕ) (A : Set ℂ)
    (hA : volume A ≠ ⊤) (j : Fin (n + 1)) :
    IntegrableOn (pathWeight a) (pathCrossingDomain A n j) ∧
      (∫ x in pathCrossingDomain A n j, pathWeight a x) =
        (Real.pi / a) ^ n * gaussianCrossing a A := by
  induction n with
  | zero =>
    have hj : j = 0 := by
      apply Fin.ext
      have h := j.isLt
      omega
    subst j
    exact path_crossing_zero ha 0 A hA
  | succ n ih =>
    exact Fin.cases (path_crossing_zero ha (n + 1) A hA)
      (fun i => path_crossing_step ha n A i (ih i)) j

theorem norm_firstExit_cycleIntegral_le {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) (j : Fin (n + 1)) :
    ‖∫ x in firstExitDomain A (n + 1) j, Complex.exp (cycleExponent a x)‖ ≤
      (2 * Real.pi / a) ^ n * gaussianCrossing (a / 2) A := by
  have hh : 0 < a / 2 := by linarith
  have hp := (path_crossing_integral hh n A hA j).1
  have hpe := hp.mono_set (firstExit_subset_pathCrossingDomain A n j)
  have hf := (anchored_cycle_integral ha (n + 1) A hA).1.mono_set
    (firstExitDomain_subset_anchor A (n + 1) j)
  have hpoint (x : Fin (n + 2) → ℂ) :
      ‖Complex.exp (cycleExponent a x)‖ ≤ pathWeight (a / 2) x := by
    rw [norm_exp_cycleExponent, pathWeight]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
      (pathEnergy_le_cycleEnergy x) (by linarith : -(a / 2) ≤ 0))
  calc
    ‖∫ x in firstExitDomain A (n + 1) j, Complex.exp (cycleExponent a x)‖ ≤
        ∫ x in firstExitDomain A (n + 1) j, ‖Complex.exp (cycleExponent a x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in firstExitDomain A (n + 1) j, pathWeight (a / 2) x :=
      integral_mono_ae hf.norm hpe (Filter.Eventually.of_forall hpoint)
    _ ≤ ∫ x in pathCrossingDomain A n j, pathWeight (a / 2) x :=
      setIntegral_mono_set hp (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
        (Filter.Eventually.of_forall fun x hx => firstExit_subset_pathCrossingDomain A n j hx)
    _ = (Real.pi / (a / 2)) ^ n * gaussianCrossing (a / 2) A :=
      (path_crossing_integral hh n A hA j).2
    _ = _ := by
      rw [show Real.pi / (a / 2) = 2 * Real.pi / a by field_simp]

end Paper.Trace
