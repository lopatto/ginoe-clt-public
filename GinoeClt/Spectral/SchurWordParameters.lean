/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurAngularLift
public import GinoeClt.Spectral.RealSchur

/-! Concrete free-parameter assembly for scalar/pair Schur words. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

variable {d m : ℕ}

/-- Head and tail parameters with their actual upper-right entries and zero cross angles. -/
def schurStepFreeCoordinates (h : Fin d × Fin d → ℝ) (t : Fin m × Fin m → ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) : SchurStepIndex (Fin d) (Fin m) → ℝ
  | .inl _ => 0
  | .inr (.inl p) => h p
  | .inr (.inr (.inl p)) => t p
  | .inr (.inr (.inr (j, i))) => U i j

def schurStepFreeCells (h : Fin d × Fin d → ℝ) (t : Fin m × Fin m → ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) : Fin (d + m) × Fin (d + m) → ℝ :=
  (schurCellCoordinateEquiv ℝ d m).symm (schurStepFreeCoordinates h t U)

@[simp] theorem schurStepFreeCells_coordinates (h : Fin d × Fin d → ℝ)
    (t : Fin m × Fin m → ℝ) (U : Matrix (Fin d) (Fin m) ℝ) :
    schurCellCoordinateEquiv ℝ d m (schurStepFreeCells h t U) =
      schurStepFreeCoordinates h t U := (schurCellCoordinateEquiv ℝ d m).apply_symm_apply _

@[simp] theorem schurHeadInput_free (h : Fin d × Fin d → ℝ)
    (t : Fin m × Fin m → ℝ) (U : Matrix (Fin d) (Fin m) ℝ) :
    schurHeadInput (schurStepFreeCoordinates h t U) = h := rfl

@[simp] theorem schurTailInput_free (h : Fin d × Fin d → ℝ)
    (t : Fin m × Fin m → ℝ) (U : Matrix (Fin d) (Fin m) ℝ) :
    schurTailInput (schurStepFreeCoordinates h t U) = t := rfl

theorem schurParameterPhysical_free
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (h : Fin d × Fin d → ℝ) (t : Fin m × Fin m → ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) :
    schurParameterPhysical d m K L (schurStepFreeCells h t U) =
      upperBlockMatrix (K h) U (L t) := by
  rw [schurParameterPhysical_eq, schurStepFreeCells_coordinates]
  rfl

theorem schurOmegaPhysical_free_zero
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (h : Fin d × Fin d → ℝ) (t : Fin m × Fin m → ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) (hh : ω h = 0) (ht : η t = 0) :
    schurOmegaPhysical d m ω η (schurStepFreeCells h t U) = 0 := by
  apply (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).symm.injective
  change (schurOmegaPhysical d m ω η (schurStepFreeCells h t U)).submatrix
    finSumFinEquiv finSumFinEquiv = 0
  rw [schurOmegaPhysical_submatrix, schurStepFreeCells_coordinates]
  change Matrix.fromBlocks (ω h) (-(0 : Matrix (Fin m) (Fin d) ℝ)ᵀ) 0 (η t) = 0
  simp only [hh, ht, Matrix.transpose_zero, neg_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- Actual head input slots a,b,c,0 in column,row coordinates. -/
def pairFreeInput (a b c : ℝ) : Fin 2 × Fin 2 → ℝ := Matrix.vec !![a, c; b, 0]

theorem pairHeadParameter_free (a b c : ℝ) :
    pairHeadParameter (pairFreeInput a b c) = schurBlock a b c := rfl

theorem pairHeadOmega_free (a b c : ℝ) : pairHeadOmega (pairFreeInput a b c) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairHeadOmega_apply, pairFreeInput, pairSkew, flip]

/-- The original source normalization, allowing the degenerate pair boundary. -/
def SchurWordPositive : (w : List Bool) → SchurWordCells w → Prop
  | [], _ => True
  | false :: w, p =>
      SchurWordPositive w (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p))
  | true :: w, p =>
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      0 < h (1, 0) ∧ h (1, 0) ≤ h (0, 1) ∧ SchurWordPositive w (schurTailInput x)

/-- The concrete scalar constructor preserves the source shape and zero angular entries. -/
theorem schurWord_free_scalar (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ)
    (hΩ : schurWordOmega w t = 0) (ht : SchurWordPositive w t) :
    let p := schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U
    schurWordParameter (false :: w) p = upperBlockMatrix (scalarBlock a) U (schurWordParameter w t) ∧
      schurWordOmega (false :: w) p = 0 ∧ SchurWordPositive (false :: w) p := by
  refine ⟨schurParameterPhysical_free scalarHeadParameter (schurWordParameter w) _ t U, ?_, ?_⟩
  · exact schurOmegaPhysical_free_zero 0 (schurWordOmega w) _ t U (by simp) hΩ
  · simpa only [SchurWordPositive, schurStepFreeCells_coordinates, schurTailInput_free] using ht

/-- The concrete pair constructor retains the original weak ordering c≤b. -/
theorem schurWord_free_pair (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ)
    (hΩ : schurWordOmega w t = 0) (ht : SchurWordPositive w t)
    (hc : 0 < c) (hcb : c ≤ b) :
    let p := schurStepFreeCells (pairFreeInput a b c) t U
    schurWordParameter (true :: w) p = upperBlockMatrix (schurBlock a b c) U (schurWordParameter w t) ∧
      schurWordOmega (true :: w) p = 0 ∧ SchurWordPositive (true :: w) p := by
  refine ⟨schurParameterPhysical_free pairHeadParameter (schurWordParameter w) _ t U, ?_, ?_⟩
  · exact schurOmegaPhysical_free_zero pairHeadOmega (schurWordOmega w) _ t U
      (pairHeadOmega_free a b c) hΩ
  · dsimp only [SchurWordPositive]
    rw [schurStepFreeCells_coordinates, schurHeadInput_free, schurTailInput_free]
    change 0 < c ∧ c ≤ b ∧ SchurWordPositive w t
    exact ⟨hc, hcb, ht⟩

/-- Embed an actual orthogonal tail frame into ordinary physical block coordinates. -/
def schurTailOrthogonal (d m : ℕ) (R : Matrix.orthogonalGroup (Fin m) ℝ) :
    Matrix.orthogonalGroup (Fin (d + m)) ℝ := by
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d + m))
  let P : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.fromBlocks 1 0 0 R
  refine ⟨ρ P, ?_⟩
  apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
  have hP : P * Pᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp
    (orthogonal_fromBlocks_identity (ι := Fin d) R)
  change ρ P * ρ Pᵀ = 1
  rw [← map_mul, hP, map_one]

theorem schurTailOrthogonal_conjugation (B : Matrix (Fin d) (Fin d) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (R : Matrix.orthogonalGroup (Fin m) ℝ) :
    (schurTailOrthogonal d m R : Matrix _ _ ℝ)ᵀ * upperBlockMatrix B U D *
      (schurTailOrthogonal d m R : Matrix _ _ ℝ) =
        upperBlockMatrix B (U * (R : Matrix (Fin m) (Fin m) ℝ))
          ((R : Matrix (Fin m) (Fin m) ℝ)ᵀ * D * (R : Matrix (Fin m) (Fin m) ℝ)) := by
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d + m))
  let P : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.fromBlocks 1 0 0 R
  change ρ Pᵀ * ρ (Matrix.fromBlocks B U 0 D) * ρ P =
    ρ (Matrix.fromBlocks B (U * (R : Matrix (Fin m) (Fin m) ℝ)) 0
      ((R : Matrix (Fin m) (Fin m) ℝ)ᵀ * D * (R : Matrix (Fin m) (Fin m) ℝ)))
  rw [← map_mul, ← map_mul]
  exact congrArg ρ (orthogonal_tail_conjugation B U D R)

end Paper.Spectral
