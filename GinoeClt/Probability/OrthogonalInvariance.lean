/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Probability.MatrixGaussianLaw
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup

/-! # Orthogonal invariance of the actual real Gaussian matrix law -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Kronecker Matrix

namespace Paper

def matrixActionIsometry (n : ℕ)
    (Q R : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    MatrixCoordinates n ≃ₗᵢ[ℝ] MatrixCoordinates n := by
  let K : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℝ :=
    (R : Matrix _ _ ℝ)ᵀ ⊗ₖ (Q : Matrix _ _ ℝ)
  have hK : K ∈ unitary (Matrix _ _ ℝ) := Matrix.kronecker_mem_unitary
    (Matrix.transpose_mem_unitaryGroup_iff.mpr R.property) Q.property
  exact Unitary.linearIsometryEquiv
    ⟨Matrix.toEuclideanCLM (n := Fin (n + 1) × Fin (n + 1)) (𝕜 := ℝ) K,
      Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin (n + 1) × Fin (n + 1)) (𝕜 := ℝ)) hK⟩

lemma matrixActionIsometry_matrixVector (n : ℕ)
    (Q R : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) (M : SampleSpace n) :
    matrixActionIsometry n Q R (matrixVector n M) =
      matrixVector n ((Q : Matrix _ _ ℝ) * M * (R : Matrix _ _ ℝ)) := by
  change Matrix.toEuclideanCLM (n := Fin (n + 1) × Fin (n + 1)) (𝕜 := ℝ) ((R : Matrix _ _ ℝ)ᵀ ⊗ₖ (Q : Matrix _ _ ℝ))
      (WithLp.toLp 2 (Matrix.vec M)) =
    WithLp.toLp 2 (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (R : Matrix _ _ ℝ)))
  rw [Matrix.toEuclideanCLM_toLp, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose]

def matrixVectorMeasurableEquiv (n : ℕ) : SampleSpace n ≃ᵐ MatrixCoordinates n :=
  ((MeasurableEquiv.curry (Fin (n + 1)) (Fin (n + 1)) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) × Fin (n + 1) => ℝ)
      (Equiv.prodComm (Fin (n + 1)) (Fin (n + 1))))).trans
    (EuclideanSpace.equiv (Fin (n + 1) × Fin (n + 1)) ℝ).symm.toHomeomorph.toMeasurableEquiv

lemma matrixVectorMeasurableEquiv_apply (n : ℕ) (M : SampleSpace n) :
    matrixVectorMeasurableEquiv n M = matrixVector n M := rfl

lemma measurableEmbedding_matrixVector (n : ℕ) : MeasurableEmbedding (matrixVector n) :=
  (matrixVectorMeasurableEquiv n).measurableEmbedding

/-- The actual iid standard real Gaussian matrix law is invariant under
independent orthogonal changes on the left and right. -/
theorem matrixLaw_orthogonal_map (n : ℕ)
    (Q R : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    (matrixLaw n).map (fun M : SampleSpace n =>
      (Q : Matrix _ _ ℝ) * M * (R : Matrix _ _ ℝ)) = matrixLaw n := by
  let f : SampleSpace n → SampleSpace n := fun M =>
    (Q : Matrix _ _ ℝ) * M * (R : Matrix _ _ ℝ)
  let e := matrixActionIsometry n Q R
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hv : Measurable (matrixVector n) := (measurableEmbedding_matrixVector n).measurable
  have he : (matrixVector n) ∘ f = e ∘ matrixVector n := by
    funext M
    exact (matrixActionIsometry_matrixVector n Q R M).symm
  apply (measurableEmbedding_matrixVector n).map_injective
  calc
    ((matrixLaw n).map f).map (matrixVector n) =
        (matrixLaw n).map ((matrixVector n) ∘ f) := Measure.map_map hv hf
    _ = (matrixLaw n).map (e ∘ matrixVector n) :=
      congrArg (fun g : SampleSpace n → MatrixCoordinates n => (matrixLaw n).map g) he
    _ = ((matrixLaw n).map (matrixVector n)).map e :=
      (Measure.map_map e.continuous.measurable hv).symm
    _ = (stdGaussian (MatrixCoordinates n)).map e := by rw [matrixLaw_matrixVector_map]
    _ = stdGaussian (MatrixCoordinates n) := stdGaussian_map e
    _ = (matrixLaw n).map (matrixVector n) := (matrixLaw_matrixVector_map n).symm

end Paper
