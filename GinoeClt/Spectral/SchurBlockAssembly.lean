/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.RealFirstBlock
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite orthogonal block assembly -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

theorem orthogonal_fromBlocks_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Q : Matrix.orthogonalGroup κ ℝ) :
    Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 0 (Q : Matrix κ κ ℝ) ∈
      Matrix.orthogonalGroup (ι ⊕ κ) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff _ _]
  have hQ := (Matrix.mem_orthogonalGroup_iff κ ℝ).mp Q.property
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero, hQ, Matrix.fromBlocks_one]

theorem orthogonal_tail_conjugation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (B : Matrix ι ι ℝ) (U : Matrix ι κ ℝ)
    (D Q : Matrix κ κ ℝ) :
    (Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 0 Q)ᵀ *
        Matrix.fromBlocks B U 0 D * Matrix.fromBlocks 1 0 0 Q =
      Matrix.fromBlocks B (U * Q) 0 (Qᵀ * D * Q) := by
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero]

/-- Concrete entrywise normalized real Schur shape: bandwidth one below the
diagonal, no consecutive nonzero subdiagonals, and every active pair has the
source-normalized 2×2 signs, equal diagonals, and ordered off-diagonal sizes. -/
def IsNormalizedQuasiTriangular {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, j.val + 1 < i.val → T i j = 0) ∧
    (∀ i j k, j.val + 1 = i.val → i.val + 1 = k.val → T i j * T k i = 0) ∧
      ∀ i j, j.val + 1 = i.val → T i j ≠ 0 →
        T i i = T j j ∧ 0 < T j i ∧ T i j < 0 ∧ -T i j ≤ T j i

def upperBlockMatrix {d m : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
  (Matrix.fromBlocks B U 0 D).reindex finSumFinEquiv finSumFinEquiv

@[simp] theorem upperBlockMatrix_left_left {d m : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (i j : Fin d) :
    upperBlockMatrix B U D (Fin.castAdd m i) (Fin.castAdd m j) = B i j := by
  simp [upperBlockMatrix, Matrix.reindex_apply]

@[simp] theorem upperBlockMatrix_left_right {d m : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (i : Fin d) (j : Fin m) :
    upperBlockMatrix B U D (Fin.castAdd m i) (Fin.natAdd d j) = U i j := by
  simp [upperBlockMatrix, Matrix.reindex_apply]

@[simp] theorem upperBlockMatrix_right_left {d m : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) (j : Fin d) :
    upperBlockMatrix B U D (Fin.natAdd d i) (Fin.castAdd m j) = 0 := by
  simp [upperBlockMatrix, Matrix.reindex_apply]

@[simp] theorem upperBlockMatrix_right_right {d m : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin m) ℝ)
    (D : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    upperBlockMatrix B U D (Fin.natAdd d i) (Fin.natAdd d j) = D i j := by
  simp [upperBlockMatrix, Matrix.reindex_apply]

theorem IsNormalizedQuasiTriangular.upperBlocks {d m : ℕ}
    {B : Matrix (Fin d) (Fin d) ℝ} {D : Matrix (Fin m) (Fin m) ℝ}
    (hB : IsNormalizedQuasiTriangular B) (hD : IsNormalizedQuasiTriangular D)
    (U : Matrix (Fin d) (Fin m) ℝ) :
    IsNormalizedQuasiTriangular (upperBlockMatrix B U D) := by
  obtain ⟨hB0, hB1, hB2⟩ := hB
  obtain ⟨hD0, hD1, hD2⟩ := hD
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro h
        simpa only [upperBlockMatrix_left_left] using hB0 i j h
      · intro h
        have hi := i.isLt
        have hj := j.isLt
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        omega
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro _
        simp only [upperBlockMatrix_right_left]
      · intro h
        simp only [upperBlockMatrix_right_right]
        apply hD0
        simp only [Fin.val_natAdd] at h
        omega
  · intro i j k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · intro hji hik
      simpa only [upperBlockMatrix_left_left] using hB1 i j k hji hik
    · intro _ _
      simp only [upperBlockMatrix_left_left, upperBlockMatrix_right_left, mul_zero]
    · intro hji _
      have hi := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hji
      omega
    · intro hji _
      have hi := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hji
      omega
    · intro _ hik
      have hk := k.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hik
      omega
    · intro _ _
      simp only [upperBlockMatrix_right_left, upperBlockMatrix_right_right, zero_mul]
    · intro _ hik
      have hk := k.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hik
      omega
    · intro hji hik
      simp only [upperBlockMatrix_right_right]
      apply hD1
      · simp only [Fin.val_natAdd] at hji
        omega
      · simp only [Fin.val_natAdd] at hik
        omega
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hji hne
      simp only [upperBlockMatrix_left_left] at hne ⊢
      exact hB2 i j hji hne
    · intro hji _
      have hi := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hji
      omega
    · intro _ hne
      simp only [upperBlockMatrix_right_left, ne_eq, not_true_eq_false] at hne
    · intro hji hne
      simp only [upperBlockMatrix_right_right] at hne ⊢
      apply hD2 _ _ ?_ hne
      simp only [Fin.val_natAdd] at hji
      omega

theorem normalizedQuasiTriangular_empty (T : Matrix (Fin 0) (Fin 0) ℝ) :
    IsNormalizedQuasiTriangular T := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

theorem normalizedQuasiTriangular_singleton (T : Matrix (Fin 1) (Fin 1) ℝ) :
    IsNormalizedQuasiTriangular T := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    have hi := i.isLt
    omega
  · intro i j k hji hik
    have hk := k.isLt
    omega
  · intro i j hji _
    have hi := i.isLt
    omega

theorem normalizedQuasiTriangular_pair (a b c : ℝ) (hc : 0 < c) (hcb : c ≤ b) :
    IsNormalizedQuasiTriangular !![a, b; -c, a] := by
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    have hi := i.isLt
    omega
  · intro i j k hji hik
    have hk := k.isLt
    omega
  · intro i j hji hne
    fin_cases i <;> fin_cases j <;> simp_all

end Paper.Spectral
