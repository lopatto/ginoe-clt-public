/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.VarianceAsymptotic

/-! # The literal analytic variance-kernel expression

This module does not identify this expression with the ensemble count variance.
That identification requires the still-open correlation-law input.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace Paper.Kernel

def varianceKernelExpression (A : Set ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * (∫ z in A, S N (rescale N z) (rescale N z)) -
    (((N : ℝ) ^ 2 * (∫ z in A, ∫ w in A, ‖S N (rescale N z) (rescale N w)‖ ^ 2) : ℝ) : ℂ) -
      diKernelTerm A N

lemma varianceKernelExpression_error_eq {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    varianceKernelExpression A N - (gaussianVarianceExpression A N : ℂ) =
      diagonalKernelError A N - (squaredKernelError A N : ℂ) - diKernelTerm A N := by
  rw [squaredKernelError_eq hA N]
  simp only [varianceKernelExpression, diagonalKernelError, gaussianVarianceExpression]
  push_cast
  ring

/-- The complete O(1) analytic approximation in Lemma 3.1, prior to identifying
the kernel expression with the actual random-matrix count variance. -/
theorem varianceKernelExpression_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    (fun N : ℕ => varianceKernelExpression A N - (gaussianVarianceExpression A N : ℂ)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  have hs : (fun N : ℕ => (squaredKernelError A N : ℂ)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_norm_left
    simpa only [Complex.norm_real] using (squaredKernelError_bigO hA).norm_left
  have hh := ((diagonalKernelError_bigO hA).sub hs).sub (diKernelTerm_bigO hA)
  exact hh.congr_left (fun N => (varianceKernelExpression_error_eq hA N).symm)

/-- The exact source variance constant for the literal analytic kernel
expression. No assertion about count variance is made without the ensemble law. -/
theorem varianceKernelExpression_tendsto {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => varianceKernelExpression A N / (Real.sqrt (N : ℝ) : ℂ)) atTop
      (𝓝 (((Paper.boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  have hzero : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hi : (fun N : ℕ => ((Real.sqrt (N : ℝ))⁻¹ : ℂ)) =O[atTop]
      (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) := by
    apply IsBigO.of_norm_left
    simpa only [← Complex.ofReal_inv, Complex.norm_real] using (isBigO_refl (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop).norm_left
  have he := ((varianceKernelExpression_error_bigO hA).mul hi).trans_tendsto
    (by simpa only [one_mul] using hzero)
  have hg := Complex.continuous_ofReal.continuousAt.tendsto.comp (gaussianVarianceExpression_tendsto hA)
  have hout := he.add hg
  convert! hout using 1
  · ext N
    change varianceKernelExpression A N / (Real.sqrt (N : ℝ) : ℂ) =
      (varianceKernelExpression A N - (gaussianVarianceExpression A N : ℂ)) * (Real.sqrt (N : ℝ) : ℂ)⁻¹ +
        ((gaussianVarianceExpression A N / Real.sqrt (N : ℝ) : ℝ) : ℂ)
    push_cast
    ring
  · simp only [zero_add]

end Paper.Kernel
