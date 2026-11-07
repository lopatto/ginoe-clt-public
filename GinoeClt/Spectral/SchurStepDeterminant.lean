/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurStepCoordinates
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The determinant of an actual recursive Schur differential step -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

def schurDiagonalLinearMap {R ι : Type*} [CommRing R] [Fintype ι]
    (B : Matrix ι ι R) (omega K : (ι × ι → R) →ₗ[R] Matrix ι ι R) :
    (ι × ι → R) →ₗ[R] (ι × ι → R) where
  toFun h := Matrix.vec (K h + omega h * B - B * omega h)
  map_add' x y := by
    simp only [map_add, Matrix.add_mul, Matrix.mul_add, Matrix.vec_add, Matrix.vec_sub]
    abel
  map_smul' r x := by
    simp only [map_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ← smul_sub,
      Matrix.vec_smul, RingHom.id_apply]

variable {R : Type*} [CommRing R]
variable {d m : ℕ}
variable (B : Matrix (Fin d) (Fin d) R) (D : Matrix (Fin m) (Fin m) R)
variable (U : Matrix (Fin d) (Fin m) R)
variable (omega KB : (Fin d × Fin d → R) →ₗ[R] Matrix (Fin d) (Fin d) R)
variable (eta KD : (Fin m × Fin m → R) →ₗ[R] Matrix (Fin m) (Fin m) R)

/-- Coefficients of the actual commutator map, in the same four-block coordinate
order for its domain and codomain. -/
def schurStepCoefficientMatrix :=
  LinearMap.toMatrix' (schurStepLinearMap B D U omega KB eta KD)


@[simp] lemma schurLowerInput_single (j : SchurStepIndex (Fin d) (Fin m)) :
    Matrix.vec (schurLowerInput (R := R) (Pi.single j 1)) =
      match j with
      | .inl q => Pi.single q 1
      | .inr _ => 0 := by
  rcases j with j | j
  · ext p
    change (Pi.single (Sum.inl j) (1 : R) : SchurStepIndex (Fin d) (Fin m) → R)
      (Sum.inl p) = Pi.single (M := fun _ => R) j 1 p
    simp [Pi.single_apply]
  · ext p
    change (Pi.single (Sum.inr j) (1 : R) : SchurStepIndex (Fin d) (Fin m) → R)
      (Sum.inl p) = 0
    simp

@[simp] lemma schurHeadInput_single (j : SchurStepIndex (Fin d) (Fin m)) :
    schurHeadInput (R := R) (Pi.single j 1) =
      match j with
      | .inr (.inl q) => Pi.single q 1
      | _ => 0 := by
  rcases j with j | j | j
  all_goals
    ext p
    simp [schurHeadInput, Pi.single_apply]

@[simp] lemma schurTailInput_single (j : SchurStepIndex (Fin d) (Fin m)) :
    schurTailInput (R := R) (Pi.single j 1) =
      match j with
      | .inr (.inr (.inl q)) => Pi.single q 1
      | _ => 0 := by
  rcases j with j | j | j | j
  all_goals
    ext p
    simp [schurTailInput, Pi.single_apply]

@[simp] lemma schurUpperInput_single (j : SchurStepIndex (Fin d) (Fin m)) :
    Matrix.vec (schurUpperInput (R := R) (Pi.single j 1)) =
      match j with
      | .inr (.inr (.inr q)) => Pi.single q 1
      | _ => 0 := by
  rcases j with j | j | j | j
  · ext p
    change (Pi.single (Sum.inl j) (1 : R) : SchurStepIndex (Fin d) (Fin m) → R)
      (Sum.inr (Sum.inr (Sum.inr p))) = 0
    simp
  · ext p
    change (Pi.single (Sum.inr (Sum.inl j)) (1 : R) : SchurStepIndex (Fin d) (Fin m) → R)
      (Sum.inr (Sum.inr (Sum.inr p))) = 0
    simp
  · ext p
    change (Pi.single (Sum.inr (Sum.inr (Sum.inl j))) (1 : R) : SchurStepIndex (Fin d) (Fin m) → R)
      (Sum.inr (Sum.inr (Sum.inr p))) = 0
    simp
  · ext p
    change (Pi.single (Sum.inr (Sum.inr (Sum.inr j))) (1 : R) : SchurStepIndex (Fin d) (Fin m) → R)
      (Sum.inr (Sum.inr (Sum.inr p))) = Pi.single (M := fun _ => R) j 1 p
    simp [Pi.single_apply]


theorem schurStepCoefficientMatrix_lower :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₁₁ =
      sylvesterMatrix D B := by
  ext i j
  change schurStepMap B D U omega KB eta KD (Pi.single (Sum.inl j) 1) (Sum.inl i) =
    sylvesterMatrix D B i j
  rw [schurStepMap_components]
  change (schurLowerInput (Pi.single (Sum.inl j) (1 : R)) * B -
    D * schurLowerInput (Pi.single (Sum.inl j) (1 : R))) i.2 i.1 = _
  have hs := congrArg (fun v : Fin d × Fin m → R => v i)
    (sylvesterMatrix_mulVec D B
      (schurLowerInput (Pi.single (Sum.inl j) (1 : R))))
  rw [schurLowerInput_single] at hs
  simpa only [Matrix.mulVec_single_one, Matrix.vec, Matrix.col_apply] using hs.symm


@[simp] lemma schurLowerInput_single_inr
    (j : (Fin d × Fin d) ⊕ ((Fin m × Fin m) ⊕ (Fin m × Fin d))) :
    schurLowerInput (R := R) (Pi.single (Sum.inr j) 1) = 0 := by
  apply Matrix.vec_eq_zero_iff.mp
  exact schurLowerInput_single (Sum.inr j)

theorem schurStepCoefficientMatrix_zero₁₂ :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₁₂ = 0 := by
  ext i j
  change schurStepMap B D U omega KB eta KD (Pi.single (Sum.inr j) 1) (Sum.inl i) = 0
  rw [schurStepMap_components]
  simp [schurBlockCoordinates]

theorem schurStepCoefficientMatrix_head :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₂₂.toBlocks₁₁ =
      LinearMap.toMatrix' (schurDiagonalLinearMap B omega KB) := by
  ext i j
  change schurStepMap B D U omega KB eta KD
    (Pi.single (Sum.inr (Sum.inl j)) 1) (Sum.inr (Sum.inl i)) =
      schurDiagonalLinearMap B omega KB (Pi.single j 1) i
  rw [schurStepMap_components]
  simp only [schurBlockCoordinates, schurLowerInput_single_inr, schurHeadInput_single,
    Matrix.mul_zero, sub_zero]
  rfl

theorem schurStepCoefficientMatrix_head_zero₁₂ :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₂₂.toBlocks₁₂ = 0 := by
  ext i j
  change schurStepMap B D U omega KB eta KD
    (Pi.single (Sum.inr (Sum.inr j)) 1) (Sum.inr (Sum.inl i)) = 0
  rw [schurStepMap_components]
  rcases j with j | j <;> simp [schurBlockCoordinates]

theorem schurStepCoefficientMatrix_tail :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₂₂.toBlocks₂₂.toBlocks₁₁ =
      LinearMap.toMatrix' (schurDiagonalLinearMap D eta KD) := by
  ext i j
  change schurStepMap B D U omega KB eta KD
    (Pi.single (Sum.inr (Sum.inr (Sum.inl j))) 1) (Sum.inr (Sum.inr (Sum.inl i))) =
      schurDiagonalLinearMap D eta KD (Pi.single j 1) i
  rw [schurStepMap_components]
  simp only [schurBlockCoordinates, schurLowerInput_single_inr, schurTailInput_single,
    Matrix.zero_mul, add_zero]
  rfl

theorem schurStepCoefficientMatrix_tail_zero₁₂ :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₂₂.toBlocks₂₂.toBlocks₁₂ = 0 := by
  ext i j
  change schurStepMap B D U omega KB eta KD
    (Pi.single (Sum.inr (Sum.inr (Sum.inr j))) 1) (Sum.inr (Sum.inr (Sum.inl i))) = 0
  rw [schurStepMap_components]
  simp [schurBlockCoordinates]

theorem schurStepCoefficientMatrix_upper :
    (schurStepCoefficientMatrix B D U omega KB eta KD).toBlocks₂₂.toBlocks₂₂.toBlocks₂₂ = 1 := by
  ext i j
  change schurStepMap B D U omega KB eta KD
    (Pi.single (Sum.inr (Sum.inr (Sum.inr j))) 1) (Sum.inr (Sum.inr (Sum.inr i))) = _
  rw [schurStepMap_components]
  simp only [schurBlockCoordinates, schurLowerInput_single_inr, schurHeadInput_single,
    schurTailInput_single, map_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.transpose_zero,
    add_zero, sub_zero]
  have hu := congrArg (fun v : Fin m × Fin d → R => v i)
    (schurUpperInput_single (R := R) (Sum.inr (Sum.inr (Sum.inr j))))
  simpa [Matrix.vec, Pi.single_apply, Matrix.one_apply, eq_comm] using hu



private lemma det_eq_diagonal_blocks {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R)
    (h : M.toBlocks₁₂ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  have hm : M = Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ M.toBlocks₂₂ := by
    calc
      M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
        (Matrix.fromBlocks_toBlocks M).symm
      _ = _ := by rw [h]
  exact (congrArg Matrix.det hm).trans (Matrix.det_fromBlocks_zero₁₂ _ _ _)

/-- Determinant of the genuine square commutator step. No spectral separation,
invertibility or nonzero pair gap is assumed in this algebraic identity. -/
theorem det_schurStepLinearMap :
    (schurStepCoefficientMatrix B D U omega KB eta KD).det =
      (sylvesterMatrix D B).det *
        (LinearMap.toMatrix' (schurDiagonalLinearMap B omega KB)).det *
        (LinearMap.toMatrix' (schurDiagonalLinearMap D eta KD)).det := by
  rw [det_eq_diagonal_blocks _ (schurStepCoefficientMatrix_zero₁₂ B D U omega KB eta KD),
    schurStepCoefficientMatrix_lower,
    det_eq_diagonal_blocks _ (schurStepCoefficientMatrix_head_zero₁₂ B D U omega KB eta KD),
    schurStepCoefficientMatrix_head,
    det_eq_diagonal_blocks _ (schurStepCoefficientMatrix_tail_zero₁₂ B D U omega KB eta KD),
    schurStepCoefficientMatrix_tail, schurStepCoefficientMatrix_upper, Matrix.det_one, mul_one]
  ring


end Paper.Spectral
