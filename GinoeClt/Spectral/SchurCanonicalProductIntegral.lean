/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurSpectralIntegral
public import Mathlib.Data.List.OfFn
public import Mathlib.MeasureTheory.Constructions.Pi
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Paper.Spectral

abbrev schurCanonicalWord (k l : ℕ) : List Bool := List.replicate k false ++ List.replicate l true

/-- ORIGINAL representative order: all real coordinates, then all upper complex
coordinates. The cast identifies the actual word length with k+l, without reordering. -/
def schurCanonicalHeads (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    Fin (schurCanonicalWord k l).length → ℂ :=
  fun i => Fin.append (fun j => (x j : ℂ)) z (Fin.cast (by simp [schurCanonicalWord]) i)

def schurComplexHeads (l : ℕ) (z : Fin l → ℂ) : Fin (List.replicate l true).length → ℂ :=
  fun i => z (Fin.cast (by simp) i)

theorem ofFn_schurCanonicalHeads (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    List.ofFn (schurCanonicalHeads k l x z) = (List.ofFn x).map Complex.ofReal ++ List.ofFn z := by
  have hc := (List.ofFn_congr
    (by simp [schurCanonicalWord] : k+l = (schurCanonicalWord k l).length)
      (Fin.append (fun j => (x j : ℂ)) z)).symm
  calc
    _ = List.ofFn (Fin.append (fun j => (x j : ℂ)) z) := hc
    _ = List.ofFn (fun j => (x j : ℂ)) ++ List.ofFn z := List.ofFn_fin_append _ _
    _ = _ := congrArg (fun v => v ++ List.ofFn z) (List.ofFn_comp' x Complex.ofReal)

theorem ofFn_schurComplexHeads (l : ℕ) (z : Fin l → ℂ) :
    List.ofFn (schurComplexHeads l z) = List.ofFn z :=
  (List.ofFn_congr (by simp : l = (List.replicate l true).length) z).symm

theorem schurCanonicalHeads_cons (k l : ℕ) (a : ℝ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    schurCanonicalHeads (k+1) l (Fin.cons a x) z =
      Fin.cons (a : ℂ) (schurCanonicalHeads k l x z) := by
  apply List.ofFn_injective
  simp only [ofFn_schurCanonicalHeads,List.ofFn_cons,List.map_cons,List.cons_append]

theorem schurComplexHeads_cons (l : ℕ) (a : ℂ) (z : Fin l → ℂ) :
    schurComplexHeads (l+1) (Fin.cons a z) = Fin.cons a (schurComplexHeads l z) := by
  apply List.ofFn_injective
  simp only [ofFn_schurComplexHeads,List.ofFn_cons]

theorem schurCanonicalHeads_zero (l : ℕ) (x : Fin 0 → ℝ) (z : Fin l → ℂ) :
    schurCanonicalHeads 0 l x z = schurComplexHeads l z := by
  apply List.ofFn_injective
  simp only [ofFn_schurCanonicalHeads,List.ofFn_zero,List.map_nil,List.nil_append,ofFn_schurComplexHeads]

theorem continuous_schurCanonicalHeads (k l : ℕ) :
    Continuous (fun p : (Fin k → ℝ) × (Fin l → ℂ) => schurCanonicalHeads k l p.1 p.2) := by
  apply continuous_pi
  intro i
  change Continuous (fun p : (Fin k → ℝ) × (Fin l → ℂ) =>
    Fin.append (fun j => (p.1 j : ℂ)) p.2 (Fin.cast (by simp [schurCanonicalWord]) i))
  refine Fin.addCases ?_ ?_ (Fin.cast (by simp [schurCanonicalWord]) i)
  · intro j
    simpa only [Fin.append_left] using!
      Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_fst)
  · intro j
    simpa only [Fin.append_right] using! (continuous_apply j).comp continuous_snd

theorem measurable_schurComplexHeads (l : ℕ) : Measurable (schurComplexHeads l) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_pi_apply (Fin.cast (by simp) i)

/-- Ordinary product measure's exact first-coordinate Tonelli formula. -/
theorem lintegral_pi_finCons {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (n : ℕ)
    (G : (Fin (n+1) → α) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x, G x ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫⁻ a, ∫⁻ v, G (Fin.cons a v) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) 0
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) (0 : Fin (n+1))
  have hm : Measurable (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n+1) → α)) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using measurable_fst
    · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp measurable_snd
  have he (x : Fin (n+1) → α) : Fin.cons (e x).1 (e x).2 = x := by
    change Fin.cons (x 0) (fun j => x (Fin.succAbove 0 j)) = x
    simpa only [Fin.succAbove_zero,Fin.tail_def] using Fin.cons_self_tail x
  calc
    _ = ∫⁻ x, G (Fin.cons (e x).1 (e x).2) ∂Measure.pi (fun _ : Fin (n+1) => μ) := by
      simp only [he]
    _ = ∫⁻ p : α × (Fin n → α), G (Fin.cons p.1 p.2) ∂μ.prod (Measure.pi (fun _ : Fin n => μ)) :=
      hp.lintegral_comp (hG.comp hm)
    _ = _ := lintegral_prod _ (hG.comp hm).aemeasurable

/-- Finite pointwise density weights, with no restriction on the remaining
nonnegative function's size or integrability. -/
theorem lintegral_pi_weight_finCons {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (n : ℕ) (q : α → ℝ≥0∞) (hq : Measurable q)
    (hqfin : ∀ a, q a ≠ ∞) (G : (Fin (n+1) → α) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x, (∏ i, q (x i)) * G x ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫⁻ a, q a * (∫⁻ v, (∏ i, q (v i)) * G (Fin.cons a v)
        ∂Measure.pi (fun _ : Fin n => μ)) ∂μ := by
  have hp : Measurable (fun x : Fin (n+1) → α => ∏ i, q (x i)) := by fun_prop
  refine (lintegral_pi_finCons μ n (fun x => (∏ i, q (x i)) * G x) (hp.mul hG)).trans ?_
  simp_rw [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_assoc]
  apply lintegral_congr_ae
  filter_upwards with a
  exact lintegral_const_mul' (q a) _ (hqfin a)

/-- The all-pair suffix is ordinary product AREA on the upper half plane. -/
theorem schurSpectralIntegral_replicate_true (l : ℕ)
    (F : (Fin (List.replicate l true).length → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    schurSpectralIntegral (List.replicate l true) F =
      ∫⁻ z : Fin l → ℂ, (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
        F (schurComplexHeads l z)
        ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {z | 0 < z.im}) := by
  induction l with
  | zero =>
    rw [Measure.pi_of_empty _ (Fin.elim0 : Fin 0 → ℂ),lintegral_dirac]
    simp only [List.replicate_zero,schurSpectralIntegral,Finset.univ_eq_empty,Finset.prod_empty,one_mul]
    congr 1
  | succ l ih =>
    let μ : Measure ℂ := volume.restrict {z : ℂ | 0 < z.im}
    let q : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight z)
    have hq : Measurable q := Paper.SkewOrthogonal.continuous_complexWeight.measurable.ennreal_ofReal
    have hG : Measurable (fun z : Fin (l+1) → ℂ => F (schurComplexHeads (l+1) z)) :=
      hF.comp (measurable_schurComplexHeads _)
    have hp := lintegral_pi_weight_finCons μ l q hq (fun _ => ENNReal.ofReal_ne_top) _ hG
    change (∫⁻ a, q a * schurSpectralIntegral (List.replicate l true)
      (fun v => F (Fin.cons a v)) ∂μ) = _
    calc
      _ = ∫⁻ a, q a * (∫⁻ z : Fin l → ℂ, (∏ i, q (z i)) *
          F (Fin.cons a (schurComplexHeads l z)) ∂Measure.pi (fun _ : Fin l => μ)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with a
        rw [ih (fun v => F (Fin.cons a v))
          (hF.comp (measurable_finCons _ measurable_const _ measurable_id))]
      _ = _ := by simpa only [schurComplexHeads_cons] using! hp.symm

/-- Literal canonical-sector transport. Real heads use ordinary REAL product
volume; pair heads use ordinary COMPLEX upper-area product measure. Original
representative order/casts are explicit, and real ordering can stay inside F. -/
theorem schurSpectralIntegral_canonical_product (k l : ℕ)
    (F : (Fin (schurCanonicalWord k l).length → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    schurSpectralIntegral (schurCanonicalWord k l) F =
      ∫⁻ x : Fin k → ℝ, (∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/2))) *
        (∫⁻ z : Fin l → ℂ, (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
          F (schurCanonicalHeads k l x z)
          ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {z | 0 < z.im})) := by
  induction k with
  | zero =>
    rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.dirac Fin.elim0 from Measure.volume_pi_eq_dirac _,
      lintegral_dirac]
    simp only [Finset.univ_eq_empty,Finset.prod_empty,one_mul]
    simpa only [schurCanonicalHeads_zero,schurCanonicalWord,List.replicate_zero,List.nil_append]
      using! schurSpectralIntegral_replicate_true l F hF
  | succ k ih =>
    let μ : Measure ℂ := volume.restrict {z : ℂ | 0 < z.im}
    let q : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (Real.exp (-a^2/2))
    have hq : Measurable q := by fun_prop
    let G : (Fin (k+1) → ℝ) → ℝ≥0∞ := fun x =>
      ∫⁻ z : Fin l → ℂ, (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
        F (schurCanonicalHeads (k+1) l x z) ∂Measure.pi (fun _ : Fin l => μ)
    have hW : Measurable (fun z : ℂ => ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight z)) :=
      Paper.SkewOrthogonal.continuous_complexWeight.measurable.ennreal_ofReal
    have hJ : Measurable (fun p : (Fin (k+1) → ℝ) × (Fin l → ℂ) =>
        (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (p.2 i))) *
          F (schurCanonicalHeads (k+1) l p.1 p.2)) :=
      (show Measurable (fun p : (Fin (k+1) → ℝ) × (Fin l → ℂ) =>
        ∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (p.2 i))) from
        Finset.measurable_prod Finset.univ (fun i _ =>
          hW.comp ((measurable_pi_apply i).comp measurable_snd))).mul
          (hF.comp (continuous_schurCanonicalHeads _ _).measurable)
    have hG : Measurable G := hJ.lintegral_prod_right'
    have hp := lintegral_pi_weight_finCons volume k q hq (fun _ => ENNReal.ofReal_ne_top) G hG
    change (∫⁻ a : ℝ, q a * schurSpectralIntegral (schurCanonicalWord k l)
      (fun v => F (Fin.cons (a : ℂ) v))) = _
    calc
      _ = ∫⁻ a : ℝ, q a * (∫⁻ x : Fin k → ℝ,
          (∏ i, q (x i)) * (∫⁻ z : Fin l → ℂ,
            (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
              F (Fin.cons (a : ℂ) (schurCanonicalHeads k l x z))
              ∂Measure.pi (fun _ : Fin l => μ))) := by
        apply lintegral_congr_ae
        filter_upwards with a
        rw [ih (fun v => F (Fin.cons (a : ℂ) v))
          (hF.comp (measurable_finCons _ measurable_const _ measurable_id))]
      _ = _ := by simpa only [G,schurCanonicalHeads_cons] using! hp.symm

end Paper.Spectral
