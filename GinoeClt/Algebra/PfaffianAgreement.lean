/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Algebra.PfaffianCofactor

/-! # Agreement of the full permutation and recursive Pfaffians

The full signed numerator is compared before division by its exact normalizer.
The definition of `Paper.pfaffian` is unchanged.
-/

@[expose] public section
noncomputable section
open Equiv
open scoped BigOperators Matrix

namespace Paper.PfaffianBridge

/-- The fixed first image in paired coordinates is the fixed zero in finite coordinates. -/
def fixedZeroIndexEquiv (k : ℕ) :
    FixedZero k ≃ {σ : Perm (Fin (2 * (k + 1))) // σ 0 = 0} :=
  Equiv.subtypeEquiv (PfaffianMinor.pairColumnEquiv (k + 1)).permCongr (by
    intro σ
    let e := PfaffianMinor.pairColumnEquiv (k + 1)
    have he0 : e (0, 0) = 0 := pairCol_zero_zero k
    have hes0 : e.symm 0 = (0, 0) := e.symm_apply_eq.mpr he0.symm
    change σ (0, 0) = (0, 0) ↔ e (σ (e.symm 0)) = 0
    rw [hes0, ← he0]
    exact e.injective.eq_iff.symm)

/-- Fixing the first paired index leaves an unrestricted finite tail permutation. -/
def fixedZeroTailEquiv (k : ℕ) : FixedZero k ≃ Perm (Fin (2 * k + 1)) :=
  (fixedZeroIndexEquiv k).trans (fixedZeroFinEquiv (2 * k + 1))

theorem term_fixedZeroTail {k : ℕ}
    (A : Matrix (Fin (2 * (k + 1))) (Fin (2 * (k + 1))) ℂ)
    (σ : Perm (Fin (2 * k + 1))) :
    term (A.submatrix (PfaffianMinor.pairColumnEquiv (k + 1))
      (PfaffianMinor.pairColumnEquiv (k + 1)))
        ((fixedZeroTailEquiv k).symm σ).val =
      finTerm A ((firstPermEquiv (2 * k + 1)).symm (0, σ)) := by
  rw [term_eq_finTerm]
  congr 1
  apply (firstPermEquiv (2 * k + 1)).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rw [firstPermEquiv_fst]
    exact ((fixedZeroIndexEquiv k) ((fixedZeroTailEquiv k).symm σ)).property
  · exact (fixedZeroTailEquiv k).apply_symm_apply σ

theorem sum_term_coordinates {k : ℕ}
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ) :
    (∑ σ : Perm (PairedIndex k), term
      (A.submatrix (PfaffianMinor.pairColumnEquiv k)
        (PfaffianMinor.pairColumnEquiv k)) σ) =
      ∑ σ : Perm (Fin (2 * k)), finTerm A σ := by
  simp_rw [term_eq_finTerm]
  exact (PfaffianMinor.pairColumnEquiv k).permCongr.sum_comp (finTerm A)

theorem sum_term_fixedZero_coordinates {k : ℕ}
    (A : Matrix (Fin (2 * (k + 1))) (Fin (2 * (k + 1))) ℂ) :
    (∑ τ : FixedZero k, term
      (A.submatrix (PfaffianMinor.pairColumnEquiv (k + 1))
        (PfaffianMinor.pairColumnEquiv (k + 1))) τ.val) =
      ∑ σ : Perm (Fin (2 * k + 1)),
        finTerm A ((firstPermEquiv (2 * k + 1)).symm (0, σ)) := by
  calc
    _ = ∑ σ : Perm (Fin (2 * k + 1)), term
        (A.submatrix (PfaffianMinor.pairColumnEquiv (k + 1))
          (PfaffianMinor.pairColumnEquiv (k + 1)))
            ((fixedZeroTailEquiv k).symm σ).val :=
      ((fixedZeroTailEquiv k).symm.sum_comp _).symm
    _ = _ := by simp_rw [term_fixedZeroTail]

/-- The two successive first-image decompositions extract precisely one cofactor sum. -/
theorem sum_tail_cofactors {k : ℕ}
    (A : Matrix (Fin (2 * (k + 1))) (Fin (2 * (k + 1))) ℂ) :
    (∑ σ : Perm (Fin (2 * k + 1)),
      finTerm A ((firstPermEquiv (2 * k + 1)).symm (0, σ))) =
      ∑ j : Fin (2 * k + 1), (-1 : ℂ) ^ j.val * A 0 j.succ *
        ∑ σ : Perm (Fin (2 * k)),
          finTerm (A.submatrix (fun i ↦ (j.succAbove i).succ)
            (fun i ↦ (j.succAbove i).succ)) σ := by
  calc
    _ = ∑ d : Fin (2 * k + 1) × Perm (Fin (2 * k)),
        finTerm A ((firstPermEquiv (2 * k + 1)).symm
          (0, (firstPermEquiv (2 * k)).symm d)) :=
      ((firstPermEquiv (2 * k)).symm.sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [finTerm_firstPair, Finset.mul_sum]

/-- The full signed numerator has exactly the expected unnormalized cofactor recurrence. -/
theorem sum_finTerm_cofactor {k : ℕ}
    (A : Matrix (Fin (2 * (k + 1))) (Fin (2 * (k + 1))) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    (∑ σ : Perm (Fin (2 * (k + 1))), finTerm A σ) =
      (2 * (k + 1) : ℂ) *
        ∑ j : Fin (2 * k + 1), (-1 : ℂ) ^ j.val * A 0 j.succ *
          ∑ σ : Perm (Fin (2 * k)),
            finTerm (A.submatrix (fun i ↦ (j.succAbove i).succ)
              (fun i ↦ (j.succAbove i).succ)) σ := by
  have h := sum_term_fixedZero
    (A.submatrix (PfaffianMinor.pairColumnEquiv (k + 1))
      (PfaffianMinor.pairColumnEquiv (k + 1)))
    (fun p q ↦ hA (PfaffianMinor.pairColumnEquiv (k + 1) p)
      (PfaffianMinor.pairColumnEquiv (k + 1) q))
  rw [sum_term_coordinates, sum_term_fixedZero_coordinates, sum_tail_cofactors] at h
  exact h

/-- Induction identifies the entire numerator before any division. -/
theorem sum_finTerm_eq_normalizer_recursivePf (k : ℕ)
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    (∑ σ : Perm (Fin (2 * k)), finTerm A σ) =
      ((2 : ℂ) ^ k * (k.factorial : ℂ)) * PfaffianMinor.recursivePf k A := by
  induction k with
  | zero => simp [finTerm, permutationSign, PfaffianMinor.recursivePf]
  | succ k ih =>
    rw [sum_finTerm_cofactor A hA]
    have hsum :
        (∑ j : Fin (2 * k + 1), (-1 : ℂ) ^ j.val * A 0 j.succ *
          ∑ σ : Perm (Fin (2 * k)),
            finTerm (A.submatrix (fun i ↦ (j.succAbove i).succ)
              (fun i ↦ (j.succAbove i).succ)) σ) =
        ((2 : ℂ) ^ k * (k.factorial : ℂ)) * PfaffianMinor.recursivePf (k + 1) A := by
      rw [PfaffianMinor.recursivePf, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hminor : ∀ i l : Fin (2 * k),
          (A.submatrix (fun i ↦ (j.succAbove i).succ)
            (fun i ↦ (j.succAbove i).succ)) l i =
            -(A.submatrix (fun i ↦ (j.succAbove i).succ)
              (fun i ↦ (j.succAbove i).succ)) i l := by
        intro i l
        exact hA (j.succAbove i).succ (j.succAbove l).succ
      rw [ih (A.submatrix (fun i ↦ (j.succAbove i).succ)
        (fun i ↦ (j.succAbove i).succ)) hminor]
      ring
    rw [hsum, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The paired-index full Pfaffian agrees with recursion after an explicit reindexing. -/
theorem pfaffian_coordinates_eq_recursivePf {k : ℕ}
    (A : Matrix (Fin (2 * k)) (Fin (2 * k)) ℂ)
    (hA : ∀ i j, A j i = -A i j) :
    pfaffian (A.submatrix (PfaffianMinor.pairColumnEquiv k)
      (PfaffianMinor.pairColumnEquiv k)) = PfaffianMinor.recursivePf k A := by
  have hn : (2 : ℂ) ^ k * (k.factorial : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast Nat.factorial_ne_zero k
  unfold pfaffian
  change ((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ *
    (∑ σ : Perm (PairedIndex k), term
      (A.submatrix (PfaffianMinor.pairColumnEquiv k)
        (PfaffianMinor.pairColumnEquiv k)) σ) = _
  rw [sum_term_coordinates, sum_finTerm_eq_normalizer_recursivePf k A hA,
    ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end Paper.PfaffianBridge

namespace Paper

/-- The frozen full normalized permutation sum is the recursive Pfaffian, for every size. -/
theorem pfaffian_eq_recursivePf {k : ℕ}
    (M : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (hM : ∀ p q, M q p = -M p q) :
    pfaffian M = PfaffianMinor.recursivePf k
      (M.submatrix (PfaffianMinor.pairColumnEquiv k).symm
        (PfaffianMinor.pairColumnEquiv k).symm) := by
  let A := M.submatrix (PfaffianMinor.pairColumnEquiv k).symm
    (PfaffianMinor.pairColumnEquiv k).symm
  have hA : ∀ i j, A j i = -A i j := fun i j ↦
    hM ((PfaffianMinor.pairColumnEquiv k).symm i)
      ((PfaffianMinor.pairColumnEquiv k).symm j)
  have h := PfaffianBridge.pfaffian_coordinates_eq_recursivePf A hA
  have hback : A.submatrix (PfaffianMinor.pairColumnEquiv k)
      (PfaffianMinor.pairColumnEquiv k) = M := by
    ext p q
    simp [A, Matrix.submatrix_apply]
  rw [hback] at h
  exact h

/-- Congruence for the frozen full Pfaffian; the change-of-basis matrix may be singular. -/
theorem pfaffian_congruence {k : ℕ}
    (M P : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (hM : ∀ p q, M q p = -M p q) :
    pfaffian (P * M * P.transpose) = P.det * pfaffian M := by
  have ht : M.transpose = -M := by
    ext p q
    exact hM p q
  have hcong : (P * M * P.transpose).transpose = -(P * M * P.transpose) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, ht,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hskew : ∀ p q, (P * M * P.transpose) q p = -(P * M * P.transpose) p q := by
    intro p q
    exact congrArg (fun B ↦ B p q) hcong
  rw [pfaffian_eq_recursivePf _ hskew, pfaffian_eq_recursivePf M hM]
  let e := PfaffianMinor.pairColumnEquiv k
  have hreindex : (P * M * P.transpose).submatrix e.symm e.symm =
      P.submatrix e.symm e.symm * M.submatrix e.symm e.symm *
        (P.submatrix e.symm e.symm).transpose := by
    rw [← Matrix.submatrix_mul_equiv (P * M) P.transpose e.symm e.symm e.symm,
      ← Matrix.submatrix_mul_equiv P M e.symm e.symm e.symm]
    rfl
  change PfaffianMinor.recursivePf k ((P * M * P.transpose).submatrix e.symm e.symm) =
    P.det * PfaffianMinor.recursivePf k (M.submatrix e.symm e.symm)
  rw [hreindex, PfaffianMinor.recursivePf_congruence
    (M.submatrix e.symm e.symm) (P.submatrix e.symm e.symm)
      (fun i j ↦ hM (e.symm i) (e.symm j)), Matrix.det_submatrix_equiv_self]

end Paper
