/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Probability.EuclideanGaussianDensity
public import GinoeClt.Probability.OrthogonalInvariance

/-! # The actual real matrix density against coordinate Lebesgue measure -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Paper

/-- Entrywise Lebesgue measure, explicitly avoiding a new global matrix instance. -/
def matrixVolume (n : ℕ) : Measure (SampleSpace n) :=
  Measure.pi fun _ : Fin (n + 1) =>
    Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ)

lemma matrixVolume_uncurry_map (n : ℕ) :
    (matrixVolume n).map
      (Function.uncurry : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) = volume := by
  change Measure.map Function.uncurry
      (Measure.pi (fun _ : Fin (n + 1) => Measure.pi (fun _ : Fin (n + 1) =>
        (volume : Measure ℝ)))) = Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => volume)
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have he : (Function.uncurry : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext M
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair, Prod.forall]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- Column vectorization followed by toLp2 preserves the ordinary matrix
coordinate volume exactly. No Frobenius norm is imposed on SampleSpace. -/
lemma matrixVector_volumePreserving (n : ℕ) :
    MeasurePreserving (matrixVector n) (matrixVolume n) volume := by
  have hu : MeasurePreserving
      (Function.uncurry : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) (matrixVolume n) volume :=
    ⟨by fun_prop, matrixVolume_uncurry_map n⟩
  have hv : MeasurePreserving (Matrix.vec : SampleSpace n →
      (Fin (n + 1) × Fin (n + 1) → ℝ)) (matrixVolume n) volume := by
    exact (measurePreserving_piCongrLeft
      (fun _ : Fin (n + 1) × Fin (n + 1) => (volume : Measure ℝ))
      (Equiv.prodComm (Fin (n + 1)) (Fin (n + 1)))).comp hu
  exact (PiLp.volume_preserving_toLp (Fin (n + 1) × Fin (n + 1))).comp hv

def matrixGaussianDensity (n : ℕ) (M : SampleSpace n) : ℝ :=
  Probability.euclideanGaussianDensity (matrixVector n M)

/-- Exact original GinOE density, against the original product-coordinate volume. -/
theorem matrixLaw_eq_withDensity (n : ℕ) : matrixLaw n =
    (matrixVolume n).withDensity
      (fun M => ENNReal.ofReal (matrixGaussianDensity n M)) := by
  apply (measurableEmbedding_matrixVector n).map_injective
  rw [Probability.matrixLaw_matrixVector_eq_withDensity]
  ext s hs
  have hm := (measurableEmbedding_matrixVector n).measurable
  rw [Measure.map_apply hm hs, withDensity_apply _ hs, withDensity_apply _ (hm hs)]
  exact ((matrixVector_volumePreserving n).setLIntegral_comp_preimage_emb
    (measurableEmbedding_matrixVector n)
    (fun x : MatrixCoordinates n => ENNReal.ofReal (Probability.euclideanGaussianDensity x)) s).symm

lemma matrixGaussianDensity_eq (n : ℕ) (M : SampleSpace n) :
    matrixGaussianDensity n M = (Real.sqrt (2 * Real.pi))⁻¹ ^ ((n + 1) ^ 2) *
      Real.exp (-(∑ i : Fin (n + 1), ∑ j : Fin (n + 1), M i j ^ 2) / 2) := by
  unfold matrixGaussianDensity Probability.euclideanGaussianDensity
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.card_prod, Fintype.card_fin, matrixVector, Matrix.vec]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 2
  exact (pow_two (n + 1)).symm

end Paper
