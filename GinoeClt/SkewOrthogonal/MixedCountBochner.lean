/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.MixedRealAlternation
public import GinoeClt.Spectral.CountMixedPartition
@[expose] public section
noncomputable section
open MeasureTheory Set Classical
open scoped BigOperators ComplexConjugate NNReal ENNReal
namespace Paper.SkewOrthogonal
open Paper.Spectral

theorem ofReal_norm_countFactor (B : Set ℂ) (t : ℝ≥0) (z : ℂ) :
    ENNReal.ofReal ‖(if z ∈ B then 1+(t : ℂ) else 1)‖ =
      if z ∈ B then 1+(t : ℝ≥0∞) else 1 := by
  by_cases hz : z ∈ B
  · simp only [hz,ite_true]
    have he : (1+(t : ℂ) : ℂ) = ((1+(t : ℝ) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [he]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
      ENNReal.ofReal_add (by positivity) t.coe_nonneg]
    simp
  · simp [hz]

/-- Exact pointwise norm identity, retaining every root and the single pair count factor. -/
theorem ofReal_norm_weightedMixedVandermonde (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) :
    ENNReal.ofReal ‖weightedMixedVandermonde B t k l z x‖ =
      (∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/2))) *
        ((∏ j, ENNReal.ofReal (complexWeight (z j))) *
          (ENNReal.ofReal (schurHeadVandermondeNorm (schurCanonicalWord k l)
            (schurCanonicalHeads k l x z)) * schurHeadCountProduct B t z)) := by
  rw [weightedMixedVandermonde,norm_mul,ENNReal.ofReal_mul (norm_nonneg _),
    mixedDeterminantWeight,norm_mul,ENNReal.ofReal_mul (norm_nonneg _)]
  rw [norm_prod,ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _),
    norm_prod,ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _)]
  have hR (i : Fin k) :
      ENNReal.ofReal ‖(Real.exp (-(x i)^2/2) : ℂ)‖ =
        ENNReal.ofReal (Real.exp (-(x i)^2/2)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hW (j : Fin l) :
      ENNReal.ofReal ‖(complexWeight (z j) : ℂ)‖ = ENNReal.ofReal (complexWeight (z j)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (complexWeight_nonneg _)]
  have hv : ‖(Matrix.vandermonde (mixedRoots k l x z)).det‖ =
      schurHeadVandermondeNorm (schurCanonicalWord k l) (schurCanonicalHeads k l x z) :=
    congrArg norm (mixedRoots_vandermonde k l x z)
  simp_rw [hR,norm_mul,ENNReal.ofReal_mul (norm_nonneg _),hW,ofReal_norm_countFactor]
  rw [hv,Finset.prod_mul_distrib]
  unfold schurHeadCountProduct
  ac_rfl

/-- The actual nonnegative mixed integral is precisely the ordered norm integral. -/
theorem mixedCountIntegral_eq_lintegral_norm (B : Set ℂ) (t : ℝ≥0) (k l : ℕ) :
    mixedCountIntegral B t k l =
      ∫⁻ x in {x : Fin k → ℝ | Monotone x}, ∫⁻ z : Fin l → ℂ,
        ENNReal.ofReal ‖weightedMixedVandermonde B t k l z x‖
        ∂Measure.pi (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}) := by
  unfold mixedCountIntegral
  apply lintegral_congr_ae
  filter_upwards [] with x
  have hc : (∏ i : Fin k, ENNReal.ofReal (Real.exp (-(x i)^2/2))) ≠ ∞ :=
    ENNReal.prod_ne_top (fun _ _ ↦ ENNReal.ofReal_ne_top)
  rw [← lintegral_const_mul' _ _ hc]
  apply lintegral_congr_ae
  filter_upwards [] with z
  exact (ofReal_norm_weightedMixedVandermonde B t k l x z).symm

theorem measurableSet_realOrdered (k : ℕ) :
    MeasurableSet {x : Fin k → ℝ | Monotone x} := by
  simpa only [orderingChamber,Function.comp_def,id_eq] using
    measurableSet_orderingChamber k (id : ℝ → ℝ)
      (measurableSet_le measurable_fst measurable_snd)

/-- Joint L1 remains true after restricting to the actual weak real ordering. -/
theorem integrable_ordered_weightedMixedVandermonde (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) :
    Integrable (fun xz : (Fin k → ℝ) × (Fin l → ℂ) ↦
      weightedMixedVandermonde B t k l xz.2 xz.1)
      (((Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))).restrict
        {x : Fin k → ℝ | Monotone x}).prod
          (Measure.pi (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}))) := by
  have h := integrable_mixedVandermonde B hB t k l
  exact h.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

/-- The mixed sector mass is finite for every Borel count domain. -/
theorem mixedCountIntegral_lt_top (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) : mixedCountIntegral B t k l < ∞ := by
  have h := integrable_ordered_weightedMixedVandermonde B hB t k l
  have hm : AEMeasurable (fun xz : (Fin k → ℝ) × (Fin l → ℂ) ↦
      ENNReal.ofReal ‖weightedMixedVandermonde B t k l xz.2 xz.1‖)
      (((Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))).restrict
        {x : Fin k → ℝ | Monotone x}).prod
          (Measure.pi (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}))) := by
    simpa only [ofReal_norm] using h.aestronglyMeasurable.enorm
  rw [mixedCountIntegral_eq_lintegral_norm]
  exact lt_of_eq_of_lt (lintegral_prod _ hm).symm
    ((hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral)

theorem norm_countFactor_cast (B : Set ℂ) (t : ℝ≥0) (z : ℂ) :
    ((‖(if z ∈ B then 1+(t : ℂ) else 1)‖ : ℝ) : ℂ) =
      if z ∈ B then 1+(t : ℂ) else 1 := by
  by_cases hz : z ∈ B
  · simp only [hz,ite_true]
    have he : (1+(t : ℂ) : ℂ) = ((1+(t : ℝ) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  · simp [hz]

/-- Every literal scalar weight is a nonnegative REAL scalar, expressed without
choosing a branch or discarding an imaginary component. -/
theorem norm_mixedDeterminantWeight_cast (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) :
    ((‖mixedDeterminantWeight B t k l x z‖ : ℝ) : ℂ) =
      mixedDeterminantWeight B t k l x z := by
  unfold mixedDeterminantWeight
  simp only [norm_mul,norm_prod,Complex.ofReal_mul,Complex.ofReal_prod]
  have he (r : ℝ) (hr : 0 ≤ r) : ((‖(r : ℂ)‖ : ℝ) : ℂ) = (r : ℂ) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
  simp_rw [he _ (Real.exp_pos _).le,he _ (complexWeight_nonneg _),norm_countFactor_cast]

/-- The exact FULL determinant phase becomes its norm on the original domain. -/
theorem weightedMixedVandermonde_phase (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) (hx : Monotone x) (hz : ∀ i, 0 < (z i).im) :
    Complex.I^l * weightedMixedVandermonde B t k l z x =
      (‖weightedMixedVandermonde B t k l z x‖ : ℂ) := by
  have hd : Complex.I^l * (Matrix.vandermonde (mixedRoots k l x z)).det =
      (‖(Matrix.vandermonde (mixedRoots k l x z)).det‖ : ℂ) := by
    rw [mixedRoots_vandermonde]
    exact canonical_vandermonde_phase k l x z hx hz
  unfold weightedMixedVandermonde
  calc
    _ = mixedDeterminantWeight B t k l x z *
        (Complex.I^l*(Matrix.vandermonde (mixedRoots k l x z)).det) := by ring
    _ = _ := by
      rw [hd,norm_mul,Complex.ofReal_mul,norm_mixedDeterminantWeight_cast]

/-- The actual finite nonnegative sector mass is the full phased Bochner
determinant integral. This is an equality in ℂ, not an equality of real parts. -/
theorem mixedCountIntegral_toReal_eq_bochner (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) :
    ((mixedCountIntegral B t k l).toReal : ℂ) =
      ((Complex.I^l * ∫ x in {x : Fin k → ℝ | Monotone x},
        ∫ z : Fin l → ℂ, weightedMixedVandermonde B t k l z x
          ∂Measure.pi (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})) : ℂ) := by
  let μ : Measure (Fin k → ℝ) := (Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))).restrict
    {x : Fin k → ℝ | Monotone x}
  let ν : Measure (Fin l → ℂ) := Measure.pi
    (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})
  let D : (Fin k → ℝ) × (Fin l → ℂ) → ℂ :=
    fun p ↦ weightedMixedVandermonde B t k l p.2 p.1
  have h : Integrable D (μ.prod ν) := integrable_ordered_weightedMixedVandermonde B hB t k l
  have hx0 : ∀ᵐ x ∂μ, Monotone x := ae_restrict_mem (measurableSet_realOrdered k)
  have hz0 : ∀ᵐ z ∂ν, ∀ i, 0 < (z i).im := ae_upper_complexPi l
  have hx := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hx0
  have hz := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hz0
  have hphase : (fun p ↦ Complex.I^l * D p) =ᵐ[μ.prod ν] (fun p ↦ (‖D p‖ : ℂ)) := by
    filter_upwards [hx,hz] with p hp hzp
    exact weightedMixedVandermonde_phase B t k l p.1 p.2 hp hzp
  have hp : Complex.I^l * (∫ p, D p ∂μ.prod ν) = Complex.ofReal (∫ p, ‖D p‖ ∂μ.prod ν) := by
    exact (integral_const_mul (Complex.I^l) D).symm.trans
      ((integral_congr_ae hphase).trans (integral_ofReal (𝕜 := ℂ) (f := fun p ↦ ‖D p‖)))
  have hm : (∫⁻ p, ‖D p‖ₑ ∂μ.prod ν) = mixedCountIntegral B t k l := by
    calc
      _ = ∫⁻ x, ∫⁻ z, ‖D (x,z)‖ₑ ∂ν ∂μ := lintegral_prod _ h.aestronglyMeasurable.enorm
      _ = _ := by
        simpa only [D,μ,ν,ofReal_norm,volume_pi] using! (mixedCountIntegral_eq_lintegral_norm B t k l).symm
  have hn : (∫ p, ‖D p‖ ∂μ.prod ν) = (mixedCountIntegral B t k l).toReal :=
    (integral_norm_eq_lintegral_enorm h.aestronglyMeasurable).trans (congrArg ENNReal.toReal hm)
  have hj : ((mixedCountIntegral B t k l).toReal : ℂ) =
      Complex.I^l * (∫ p, D p ∂μ.prod ν) :=
    (congrArg Complex.ofReal hn).symm.trans hp.symm
  simpa only [D,μ,ν,volume_pi] using! hj.trans
    (congrArg (fun c : ℂ ↦ Complex.I^l*c) (integral_prod D h))

end Paper.SkewOrthogonal
