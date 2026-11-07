/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.ContinuousWedgeDeterminant
@[expose] public section
noncomputable section
open Equiv
open scoped BigOperators
namespace Paper.SkewOrthogonal

/-- A whole-pair permutation has positive determinant sign. -/
theorem det_pairColumn_permute {m : ℕ}
    (M : Matrix (PairedIndex m) (PairedIndex m) ℂ) (σ : Perm (Fin m)) :
    (M.submatrix id (Pfaffian.basePerm σ σ)).det = M.det := by
  rw [Matrix.det_permute']
  have hs : Perm.sign (Pfaffian.basePerm σ σ) = 1 := by
    rw [Pfaffian.sign_basePerm,Int.units_mul_self]
  rw [hs]
  simp

/-- The continuous adjacent-pair determinant is symmetric in its pair variables. -/
theorem pairedFeatureMatrix_det_perm {X : Type*} {m : ℕ}
    (A : X → PairedIndex m → Fin 2 → ℂ) (x : Fin m → X) (σ : Perm (Fin m)) :
    (pairedFeatureMatrix (fun i ↦ A (x (σ i)))).det =
      (pairedFeatureMatrix (fun i ↦ A (x i))).det := by
  have he : pairedFeatureMatrix (fun i ↦ A (x (σ i))) =
      (pairedFeatureMatrix (fun i ↦ A (x i))).submatrix id (Pfaffian.basePerm σ σ) := by
    ext p q
    rcases q with ⟨i,a⟩
    simp [pairedFeatureMatrix,Matrix.submatrix_apply,Pfaffian.basePerm,Equiv.prodCongrLeft]
  rw [he,det_pairColumn_permute]

/-- Scale the two columns of each pair by arbitrary finite complex scalars.
No nonzero assumption or cancellation is used. -/
theorem pairedFeatureMatrix_det_scale_pairs {m : ℕ}
    (A : Fin m → PairedIndex m → Fin 2 → ℂ) (c d : Fin m → ℂ) :
    (pairedFeatureMatrix (fun i p a ↦ if a = 0 then c i*A i p 0 else d i*A i p 1)).det =
      (∏ i : Fin m, c i*d i) * (pairedFeatureMatrix A).det := by
  have he : pairedFeatureMatrix (fun i p a ↦ if a = 0 then c i*A i p 0 else d i*A i p 1) =
      Matrix.of (fun p q : PairedIndex m ↦ (if q.2 = 0 then c q.1 else d q.1) *
        pairedFeatureMatrix A p q) := by
    ext p q
    rcases q with ⟨i,a⟩
    fin_cases a <;> simp [pairedFeatureMatrix]
  rw [he,Matrix.det_mul_row]
  have hp : (∏ q : PairedIndex m, if q.2 = 0 then c q.1 else d q.1) =
      ∏ i : Fin m, c i*d i := by
    rw [Fintype.prod_prod_type]
    simp [Fin.prod_univ_two]
  rw [hp]

end Paper.SkewOrthogonal
