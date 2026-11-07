/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.CountSectorPartition
public import GinoeClt.Spectral.SchurCanonicalSymmetry
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal NNReal Classical BigOperators
namespace Paper.Spectral

/-- The ACTUAL un-ordered complex-coordinate weight at fixed real coordinates.
It contains the full Vandermonde norm and one generating factor per representative. -/
def schurUnorderedComplexWeight (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) : ℝ≥0∞ :=
  (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
    (ENNReal.ofReal (schurHeadVandermondeNorm (schurCanonicalWord k l)
      (schurCanonicalHeads k l x z)) *
        schurHeadCountProduct B t (schurCanonicalHeads k l x z))

theorem measurable_schurUnorderedComplexWeight (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) (x : Fin k → ℝ) :
    Measurable (schurUnorderedComplexWeight B t k l x) := by
  have hc : Measurable (fun z : Fin l → ℂ => schurCanonicalHeads k l x z) :=
    (continuous_schurCanonicalHeads k l).measurable.comp
      (measurable_const.prodMk measurable_id)
  have hW : Measurable (fun z : Fin l → ℂ =>
      ∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) :=
    Finset.measurable_prod Finset.univ (fun i _ =>
      (Paper.SkewOrthogonal.continuous_complexWeight.measurable.comp
        (measurable_pi_apply i)).ennreal_ofReal)
  exact hW.mul (((continuous_schurHeadVandermondeNorm _).measurable.comp hc).ennreal_ofReal.mul
    ((measurable_schurHeadCountProduct B hB t _).comp hc))

theorem schurUnorderedComplexWeight_perm (B : Set ℂ) (t : ℝ≥0)
    (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) (σ : Equiv.Perm (Fin l)) :
    schurUnorderedComplexWeight B t k l x (z ∘ σ) =
      schurUnorderedComplexWeight B t k l x z := by
  unfold schurUnorderedComplexWeight
  rw [complexWeight_product_perm,canonical_headVandermondeNorm_perm,
    canonical_headCountProduct_perm]

theorem schurUnorderedComplexWeight_eq_zero (B : Set ℂ) (t : ℝ≥0)
    {k l : ℕ} (x : Fin k → ℝ) (z : Fin l → ℂ) (hz : ¬ Function.Injective z) :
    schurUnorderedComplexWeight B t k l x z = 0 := by
  unfold schurUnorderedComplexWeight
  rw [canonical_headVandermondeNorm_eq_zero x z hz,ENNReal.ofReal_zero,zero_mul,mul_zero]

/-- Product of ordinary restricted upper-plane areas is carried by points
whose EVERY coordinate is genuinely upper. Includes the empty coordinate family. -/
theorem ae_upper_complexPi (l : ℕ) :
    ∀ᵐ z : Fin l → ℂ ∂Measure.pi
      (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}),
        ∀ i, 0 < (z i).im := by
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ a : ℂ ∂(volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}, 0 < a.im :=
    ae_restrict_mem (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  exact (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}) i).ae h

/-- The specific complex chamber integral is 1/l! of the specific unordered
weight. All generic symmetry/repeat-zero premises have been proved above. -/
theorem lintegral_schurComplexChamber (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) (x : Fin k → ℝ) :
    (∫⁻ z in orderingChamber l schurRootKey, schurUnorderedComplexWeight B t k l x z
      ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})) =
      (l.factorial : ℝ≥0∞)⁻¹ *
        ∫⁻ z, schurUnorderedComplexWeight B t k l x z
          ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}) := by
  have h := lintegral_symmetric_eq_factorial_orderingChamber
    ((volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}) l schurRootKey schurRootKey_injective
    (measurableSet_schurRootKey_le Prod.fst Prod.snd continuous_fst continuous_snd)
    (schurUnorderedComplexWeight B t k l x) (measurable_schurUnorderedComplexWeight B hB t k l x)
    (fun σ z => schurUnorderedComplexWeight_perm B t k l x z σ)
    (fun z hz => schurUnorderedComplexWeight_eq_zero B t x z hz)
  rw [h]
  exact (ENNReal.inv_mul_cancel_left (by exact_mod_cast Nat.factorial_ne_zero l) (by simp)).symm

theorem lintegral_canonical_countTest_inner (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) (x : Fin k → ℝ) :
    (∫⁻ z : Fin l → ℂ,
      (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
        schurHeadCountTest B t (schurCanonicalWord k l) (schurCanonicalHeads k l x z)
      ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})) =
      if Monotone x then
        (l.factorial : ℝ≥0∞)⁻¹ *
          ∫⁻ z, schurUnorderedComplexWeight B t k l x z
            ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})
      else 0 := by
  by_cases hx : Monotone x
  · rw [ite_eq_left hx,← lintegral_schurComplexChamber B hB t k l x,
      ← lintegral_indicator (measurableSet_schurHeadOrdering l)]
    apply lintegral_congr_ae
    filter_upwards [ae_upper_complexPi l] with z hz
    rw [canonical_headCountTest_ordering B t k l x z hz,ite_eq_left hx]
    by_cases ho : z ∈ orderingChamber l schurRootKey
    · rw [Set.indicator_of_mem ho,Set.indicator_of_mem ho]
      rfl
    · rw [Set.indicator_of_notMem ho,Set.indicator_of_notMem ho,mul_zero]
  · rw [ite_eq_right hx]
    have he :
        (fun z : Fin l → ℂ =>
          (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
            schurHeadCountTest B t (schurCanonicalWord k l) (schurCanonicalHeads k l x z)) =ᵐ[
              Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})]
          (fun _ => 0) := by
      filter_upwards [ae_upper_complexPi l] with z hz
      rw [canonical_headCountTest_ordering B t k l x z hz,ite_eq_right hx,mul_zero]
    exact (lintegral_congr_ae he).trans (lintegral_zero)

/-- Exact 1/l! relaxation of ONLY the complex ordering, in ordinary upper area.
Original weak REAL ordering is retained and no finite-integral premise is added. -/
theorem schurSpectralIntegral_canonical_countTest (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) :
    schurSpectralIntegral (schurCanonicalWord k l) (schurHeadCountTest B t (schurCanonicalWord k l)) =
      (l.factorial : ℝ≥0∞)⁻¹ *
        ∫⁻ x in {x : Fin k → ℝ | Monotone x},
          (∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/2))) *
            ∫⁻ z, schurUnorderedComplexWeight B t k l x z
              ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im}) := by
  rw [schurSpectralIntegral_canonical_product _ _ _
    (measurable_schurHeadCountTest B hB t _)]
  have hR : MeasurableSet {x : Fin k → ℝ | Monotone x} := by
    exact measurableSet_orderingChamber k id
      (measurableSet_le measurable_fst measurable_snd)
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.factorial_ne_zero l)),
    ← lintegral_indicator hR]
  apply lintegral_congr
  intro x
  rw [lintegral_canonical_countTest_inner B hB t k l x]
  by_cases hx : Monotone x
  · have hx' : x ∈ {x : Fin k → ℝ | Monotone x} := hx
    rw [Set.indicator_of_mem hx',ite_eq_left hx]
    exact mul_left_comm _ _ _
  · have hx' : x ∉ {x : Fin k → ℝ | Monotone x} := hx
    rw [Set.indicator_of_notMem hx',ite_eq_right hx,mul_zero]

end Paper.Spectral
