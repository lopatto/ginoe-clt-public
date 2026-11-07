/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.BoundaryLength
public import GinoeClt.AnalyticCumulants
public import GinoeClt.Spectral.Count
public import GinoeClt.Cumulants.GaussianMoments
public import GinoeClt.Probability.MomentCriterion

/-!
# Reduction from cumulant limits to the CLT

The reductions here take actual GinOE cumulant limits as explicit proof parameters.
Those limits are proved and supplied in SkewOrthogonal.CountPfaffianIdentity.
All probability and finite-positive boundary-length prerequisites are proved.
-/

public section
open MeasureTheory
open scoped NNReal ENNReal
namespace Paper

theorem momentCumulantIdentity_of_isOpen (A : Set ℂ) (hA : IsOpen A) :
    MomentCumulantIdentity A := by
  intro n r
  exact Cumulants.moment_eq_partition_cumulants (statistic A n) (matrixLaw n)
    (statistic_mem_interior_integrableExpSet (countMeasurable_of_isOpen A hA) n 0) r

/-- The earlier reduction retaining length and cumulant-limit premises.
Length is supplied by boundaryLengthRegular_of_admissible; the cumulant limits are supplied in
SkewOrthogonal.CountPfaffianIdentity.
This is not an unconditional proof of PrincipalStatement. -/
theorem mainTheorem_of_length_and_cumulantLimits (A : Set ℂ)
    (hA : IsAdmissibleLipschitzDomain A) (hLength : BoundaryLengthRegular A)
    (hCL : ∀ ell : ℝ≥0, (ell : ℝ≥0∞) = boundaryMeasure A → 0 < ell →
      CumulantLimits A ell) : MainConclusion A :=
  mainTheorem A hA hLength (countMeasurable_of_isOpen A hA.1)
    (momentCumulantIdentity_of_isOpen A hA.1) hCL gaussianPartitionMoments
    gaussianMomentCriterion

/-- All probability and boundary-length prerequisites have been proved.
Actual GinOE cumulant limits are an explicit parameter of this reduction. -/
theorem mainTheorem_of_cumulantLimits (A : Set ℂ)
    (hA : IsAdmissibleLipschitzDomain A)
    (hCL : ∀ ell : ℝ≥0, (ell : ℝ≥0∞) = boundaryMeasure A → 0 < ell →
      CumulantLimits A ell) : MainConclusion A :=
  mainTheorem_of_length_and_cumulantLimits A hA
    (boundaryLengthRegular_of_admissible hA) hCL

end Paper
