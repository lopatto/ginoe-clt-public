/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Definitions
import Mathlib.Tactic.Positivity

/-!
# Checked cumulant-to-moment logical reduction

The analytic and geometric prerequisites are explicit proof parameters in this
conditional reduction. They are discharged in downstream modules, culminating
in the unconditional principal theorem in SkewOrthogonal.CountPfaffianIdentity.
-/

public section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace Paper

/-- An unconditional bound for the actual scaled-matrix count. -/
theorem count_le (A : Set ℂ) (n : ℕ) (M : SampleSpace n) :
    count A n M ≤ n + 1 := by
  classical
  calc
    count A n M ≤ (eigenvalues n M).card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    _ ≤ (scaledMatrix n M).charpoly.natDegree :=
      Polynomial.card_roots_map_le_natDegree _
    _ = n + 1 := by simp

/-- Exact centering uses a genuinely integrable raw count. -/
theorem count_integrable {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    Integrable (fun M : SampleSpace n ↦ (count A n M : ℝ)) (matrixLaw n) := by
  apply (integrable_const (n + 1 : ℝ)).mono' (h n).aestronglyMeasurable
  apply ae_of_all
  intro M
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast count_le A n M

theorem varianceOfLength_pos {ell : ℝ≥0} (h : 0 < ell) :
    0 < varianceOfLength ell := by
  unfold varianceOfLength
  apply div_pos h
  positivity

theorem statistic_measurable {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    Measurable (statistic A n) := by
  unfold statistic
  exact ((h n).sub_const _).div_const _

theorem statistic_aemeasurable {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    AEMeasurable (statistic A n) (matrixLaw n) :=
  (statistic_measurable h n).aemeasurable

/-- A finite deterministic bound at each matrix size; no uniform exponential
moment assumption is used. -/
theorem statistic_norm_le (A : Set ℂ) (n : ℕ) (M : SampleSpace n) :
    ‖statistic A n M‖ ≤
      ((n + 1 : ℝ) + ‖meanCount A n‖) / ‖(n + 1 : ℝ) ^ (1 / 4 : ℝ)‖ := by
  have hcount : ‖(count A n M : ℝ)‖ ≤ (n + 1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast count_le A n M
  unfold statistic
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (add_le_add hcount le_rfl)

/-- All absolute moments follow from count measurability and the deterministic
count bound. This routine prerequisite is discharged, not assumed. -/
theorem allMoments_of_measurable {A : Set ℂ} (h : CountMeasurable A) : AllMoments A := by
  intro n r
  let C : ℝ := ((n + 1 : ℝ) + ‖meanCount A n‖) /
    ‖(n + 1 : ℝ) ^ (1 / 4 : ℝ)‖
  apply (integrable_const (C ^ r)).mono'
    ((statistic_measurable h n).pow_const r).aestronglyMeasurable
  apply ae_of_all
  intro M
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (statistic_norm_le A n M) r

/-- Finite sums and products preserve limits; blocks have positive size. -/
theorem momentPolynomial_tendsto {kappa : ℕ → ℕ → ℝ} {limit : ℕ → ℝ}
    (h : ∀ r, 1 ≤ r → Tendsto (fun n ↦ kappa n r) atTop (𝓝 (limit r)))
    (r : ℕ) :
    Tendsto (fun n ↦ momentPolynomial r (kappa n)) atTop
      (𝓝 (momentPolynomial r limit)) := by
  classical
  unfold momentPolynomial
  apply tendsto_finsetSum
  intro P hP
  apply tendsto_finsetProd
  intro B hB
  exact h B.card (Finset.one_le_card.mpr (P.nonempty_of_mem_parts hB))

theorem moments_tendsto {A : Set ℂ} {ell : ℝ≥0}
    (hMC : MomentCumulantIdentity A) (hCL : CumulantLimits A ell)
    (hGM : GaussianPartitionMoments) (r : ℕ) :
    Tendsto (fun n ↦ moment A n r) atTop
      (𝓝 (∫ x : ℝ, x ^ r ∂ProbabilityTheory.gaussianReal 0 (varianceOfLength ell))) := by
  have hId : (fun n ↦ moment A n r) =
      (fun n ↦ momentPolynomial r (cumulant A n)) := by
    funext n
    exact hMC n r
  rw [hId, hGM (varianceOfLength ell) r]
  exact momentPolynomial_tendsto hCL r

/-- A parameterized reduction, not the unconditional manuscript theorem. -/
theorem mainTheorem (A : Set ℂ) (_hA : IsAdmissibleLipschitzDomain A)
    (hLength : BoundaryLengthRegular A)
    (hMeas : CountMeasurable A)
    (hMC : MomentCumulantIdentity A)
    (hCL : ∀ ell : ℝ≥0, (ell : ℝ≥0∞) = boundaryMeasure A → 0 < ell →
      CumulantLimits A ell)
    (hGM : GaussianPartitionMoments)
    (hMM : GaussianMomentCriterion) : MainConclusion A := by
  rcases hLength with ⟨ell, hMeasure, hpos⟩
  refine ⟨ell, hMeasure, hpos, ?_⟩
  apply hMM SampleSpace matrixLaw (statistic A) (varianceOfLength ell)
    (varianceOfLength_pos hpos)
  · exact statistic_aemeasurable hMeas
  · exact allMoments_of_measurable hMeas
  · exact moments_tendsto hMC (hCL ell hMeasure hpos) hGM

end Paper
