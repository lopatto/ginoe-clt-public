/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.AnalyticPartition

/-!
# Gaussian moments in finite partition form

The CGF is the actual quadratic CGF of the centered Gaussian measure. All
derivatives except the variance derivative vanish, so the general analytic
moment formula becomes the prescribed pair-partition polynomial.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace Paper.Cumulants

theorem gaussian_cgf_eq_quadratic (v : ℝ≥0) :
    cgf id (gaussianReal 0 v) = fun t : ℝ => (v : ℝ) / 2 * t ^ 2 := by
  funext t
  rw [cgf_gaussianReal (X := id) (p := gaussianReal 0 v) (μ := 0) (v := v) (by simp)]
  ring

theorem gaussian_cumulant_eq_pair (v : ℝ≥0) (r : ℕ) :
    iteratedDeriv r (cgf id (gaussianReal 0 v)) 0 = pairCumulant v r := by
  rw [gaussian_cgf_eq_quadratic, iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  by_cases hr : r = 2
  · subst r
    norm_num [pairCumulant]
  · simp [pairCumulant, hr]

end Paper.Cumulants

namespace Paper

/-- The centered Gaussian has exactly the reviewed pair-partition moments,
including variance zero and moment order zero. -/
theorem gaussianPartitionMoments : GaussianPartitionMoments := by
  intro v r
  have h := Cumulants.moment_eq_partition_cumulants id (gaussianReal 0 v)
    (by simp) r
  simp only [Cumulants.gaussian_cumulant_eq_pair] at h
  simpa only [Function.id_def] using h

end Paper
