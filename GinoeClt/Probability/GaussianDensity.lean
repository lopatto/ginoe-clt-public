/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Probability.MatrixGaussianLaw
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Exact finite-coordinate standard Gaussian density -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Paper.Probability

variable {ι : Type*} [Fintype ι]

def gaussianProductDensity (x : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma gaussianProductDensity_nonneg (x : ι → ℝ) : 0 ≤ gaussianProductDensity x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma integrable_gaussianProductDensity : Integrable (gaussianProductDensity (ι := ι)) := by
  exact Integrable.fintype_prod (fun _ : ι => integrable_gaussianPDFReal 0 1)

/-- Exact Lebesgue density, including dimension zero. -/
theorem gaussian_pi_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (gaussianProductDensity x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal integrable_gaussianProductDensity.restrict
      (Filter.Eventually.of_forall gaussianProductDensity_nonneg)]
  have hm : (volume : Measure (ι → ℝ)).restrict (Set.univ.pi s) =
      Measure.pi (fun i : ι => (volume : Measure ℝ).restrict (s i)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  change ENNReal.ofReal (∫ x, ∏ i, gaussianPDFReal 0 1 (x i)
    ∂(volume.restrict (Set.univ.pi s))) = _
  rw [hm, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0) (s i)).symm

lemma gaussianProductDensity_eq (x : ι → ℝ) :
    gaussianProductDensity x = (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
      Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [gaussianProductDensity, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

end Paper.Probability
