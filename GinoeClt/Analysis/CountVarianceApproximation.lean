/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.PseudoVariance

/-! # The O(1) variance approximation with its finite-law dependency explicit

The analytic pseudo-cumulant estimate is unconditional. The count approximations
here take the finite factorial-moment identity as an explicit proof parameter.
It is proved and supplied in SkewOrthogonal.CountPfaffianIdentity, which also
exports the resulting count-variance approximation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Real Topology

namespace Paper.Kernel

theorem realDeterminantalPseudoCumulant_two_error_bigO {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) :
    (fun N : ℕ => realDeterminantalPseudoCumulant A N 2 - gaussianVarianceExpression A N)
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  have hh := (varianceKernelExpression_error_bigO hA).add (diKernelTerm_bigO hA)
  have hc : (fun N : ℕ =>
      ((realDeterminantalPseudoCumulant A N 2 - gaussianVarianceExpression A N : ℝ) : ℂ))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    exact hh.congr_left fun N => by
      rw [Complex.ofReal_sub, realDeterminantalPseudoCumulant_two_eq_kernel hA]
      ring
  apply IsBigO.of_norm_left
  simpa only [Complex.norm_real] using hc.norm_left

end Paper.Kernel

namespace Paper

/-- Analytic raw-count cumulant two is the actual variance of the algebraic
multiplicity count; no correlation identity is needed for this equality. -/
theorem countCumulant_two_eq_variance {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    countCumulant A n 2 =
      variance (fun M : SampleSpace n => (count A n M : ℝ)) (matrixLaw n) := by
  have hb : ∀ᵐ M : SampleSpace n ∂matrixLaw n,
      (count A n M : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℝ) := by
    apply ae_of_all
    intro M
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast count_le A n M⟩
  have hp := memLp_of_bounded hb (h n).aestronglyMeasurable 2
  rw [countCumulant, iteratedDeriv_two_cgf (count_mem_interior_integrableExpSet h n 0),
    variance_eq_sub hp, deriv_cgf_zero (count_mem_interior_integrableExpSet h n 0)]
  simp

/-- Conditional source L31, with the exact physical matrix size N=n+1. -/
theorem countCumulant_two_error_bigO_of_finiteLaw {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    (fun n : ℕ => countCumulant A n 2 - Kernel.gaussianVarianceExpression A (n + 1))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨c, hc, hE⟩ := countCumulant_determinantal_exp_close hA hLaw
  have he : (fun n : ℕ => Real.exp (-c * (n + 1 : ℝ)))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_norm_le
    intro n
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by positivity)
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hD := (hE 2 (by decide)).trans he
  have hP := (Kernel.realDeterminantalPseudoCumulant_two_error_bigO hA).comp_tendsto hshift
  have hout := hD.add hP
  convert! hout using 1
  funext n
  simp only [Function.comp_def]
  ring

/-- The actual count variance has the source Gaussian-kernel approximation
with bounded error, conditional on the explicit finite-ensemble identity. -/
theorem countVariance_error_bigO_of_finiteLaw {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    (fun n : ℕ =>
      variance (fun M : SampleSpace n => (count A n M : ℝ)) (matrixLaw n) -
        Kernel.gaussianVarianceExpression A (n + 1))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  simpa only [countCumulant_two_eq_variance (countMeasurable_of_isOpen A hA.1)] using
    countCumulant_two_error_bigO_of_finiteLaw hA hLaw

end Paper
