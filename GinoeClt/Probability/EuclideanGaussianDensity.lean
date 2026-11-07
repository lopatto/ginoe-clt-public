/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Probability.GaussianDensity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Exact Gaussian density in Euclidean matrix coordinates -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Paper.Probability

variable {ι : Type*} [Fintype ι]

def euclideanGaussianDensity (x : EuclideanSpace ℝ ι) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-‖x‖ ^ 2 / 2)

lemma gaussianProductDensity_toLp (x : ι → ℝ) :
    gaussianProductDensity x = euclideanGaussianDensity (WithLp.toLp 2 x) := by
  rw [gaussianProductDensity_eq, euclideanGaussianDensity, EuclideanSpace.real_norm_sq_eq]

/-- Standard Gaussian has the exact usual density against ordinary Euclidean volume. -/
theorem stdGaussian_euclidean_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ ι) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (euclideanGaussianDensity x)) := by
  rw [← map_pi_eq_stdGaussian, gaussian_pi_eq_withDensity]
  ext s hs
  have hm : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) := by fun_prop
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs]
  calc
    _ = ∫⁻ x in (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹' s,
        ENNReal.ofReal (euclideanGaussianDensity (WithLp.toLp 2 x)) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall fun x => congrArg ENNReal.ofReal (gaussianProductDensity_toLp x)
    _ = _ := (PiLp.volume_preserving_toLp ι).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
        (fun y : EuclideanSpace ℝ ι => ENNReal.ofReal (euclideanGaussianDensity y)) s

/-- The density of the actual frozen GinOE matrix law in Frobenius coordinates. -/
theorem matrixLaw_matrixVector_eq_withDensity (n : ℕ) :
    (Paper.matrixLaw n).map (Paper.matrixVector n) =
      (volume : Measure (Paper.MatrixCoordinates n)).withDensity
        (fun x => ENNReal.ofReal (euclideanGaussianDensity x)) := by
  rw [Paper.matrixLaw_matrixVector_map, stdGaussian_euclidean_eq_withDensity]

end Paper.Probability
