/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Algebra.Pfaffian
public import GinoeClt.Algebra.PfaffianCongruence
import Mathlib.GroupTheory.Perm.Fin

/-! # Pair symmetries of the literal Pfaffian permutation sum

These finite identities apply to the numerator in `Paper.pfaffian`.
They do not yet identify it with the auxiliary recursive Pfaffian.
-/

@[expose] public section
noncomputable section
open Equiv
open scoped BigOperators Matrix

namespace Paper.PfaffianBridge

/-- The actual summand in the frozen full permutation definition. -/
def term {k : ℕ} (M : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (σ : Perm (PairedIndex k)) : ℂ :=
  permutationSign σ * ∏ i : Fin k, M (σ (i, 0)) (σ (i, 1))

/-- Permuting whole ordered pairs preserves the signed summand. -/
theorem term_basePerm {k : ℕ} (M : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (σ : Perm (PairedIndex k)) (α : Perm (Fin k)) :
    term M (σ * Pfaffian.basePerm α α) = term M σ := by
  have hp : (∏ i : Fin k,
      M ((σ * Pfaffian.basePerm α α) (i, 0))
        ((σ * Pfaffian.basePerm α α) (i, 1))) =
      ∏ i : Fin k, M (σ (i, 0)) (σ (i, 1)) := by
    simpa [Pfaffian.basePerm, Equiv.Perm.mul_apply] using
      (Equiv.prod_comp α (fun i : Fin k ↦ M (σ (i, 0)) (σ (i, 1))))
  unfold term
  rw [Pfaffian.permutationSign_mul, Pfaffian.permutationSign_basePerm,
    Pfaffian.permutationSign_mul_self, mul_one, hp]

lemma orientation_entry {k : ℕ} (M : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (hM : ∀ p q, M q p = -M p q) (σ : Perm (PairedIndex k))
    (ε : Fin k → Fin 2) (i : Fin k) :
    M (σ (Pfaffian.orientationPerm ε (i, 0)))
        (σ (Pfaffian.orientationPerm ε (i, 1))) =
      permutationSign (Pfaffian.sideFlip (ε i)) * M (σ (i, 0)) (σ (i, 1)) := by
  have he : ε i = 0 ∨ ε i = 1 := by
    have hh := (ε i).isLt
    omega
  rcases he with he | he
  · simp [Pfaffian.orientationPerm, Pfaffian.sideFlip, he, permutationSign]
  · simpa [Pfaffian.orientationPerm, Pfaffian.sideFlip, he, permutationSign] using
      hM (σ (i, 0)) (σ (i, 1))

/-- A pair flip changes the permutation sign and the skew entry sign together. -/
theorem term_orientationPerm {k : ℕ}
    (M : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (hM : ∀ p q, M q p = -M p q) (σ : Perm (PairedIndex k))
    (ε : Fin k → Fin 2) :
    term M (σ * Pfaffian.orientationPerm ε) = term M σ := by
  have hp : (∏ i : Fin k,
      M ((σ * Pfaffian.orientationPerm ε) (i, 0))
        ((σ * Pfaffian.orientationPerm ε) (i, 1))) =
      (∏ i : Fin k, permutationSign (Pfaffian.sideFlip (ε i))) *
        ∏ i : Fin k, M (σ (i, 0)) (σ (i, 1)) := by
    simp only [Equiv.Perm.mul_apply]
    simp_rw [orientation_entry M hM σ ε]
    exact Finset.prod_mul_distrib
  have hc : (∏ i : Fin k, permutationSign (Pfaffian.sideFlip (ε i))) *
      (∏ i : Fin k, permutationSign (Pfaffian.sideFlip (ε i))) = 1 := by
    rw [← Pfaffian.permutationSign_orientationPerm,
      Pfaffian.permutationSign_mul_self]
  unfold term
  rw [Pfaffian.permutationSign_mul, Pfaffian.permutationSign_orientationPerm, hp]
  calc
    _ = permutationSign σ *
        ((∏ i : Fin k, permutationSign (Pfaffian.sideFlip (ε i))) *
          ∏ i : Fin k, permutationSign (Pfaffian.sideFlip (ε i))) *
        ∏ i : Fin k, M (σ (i, 0)) (σ (i, 1)) := by ring
    _ = _ := by rw [hc]; ring


/-- A pair-preserving permutation sending the first index to a prescribed index. -/
def moveZero {k : ℕ} (p : PairedIndex (k + 1)) : Perm (PairedIndex (k + 1)) :=
  Pfaffian.pairedPerm (Equiv.swap 0 p.1) (Equiv.swap 0 p.1) (fun _ ↦ p.2)

@[simp] theorem moveZero_apply_zero {k : ℕ} (p : PairedIndex (k + 1)) :
    moveZero p (0, 0) = p := by
  rcases p with ⟨i, a⟩
  simp [moveZero, Pfaffian.pairedPerm, Pfaffian.basePerm,
    Pfaffian.orientationPerm, Equiv.Perm.mul_apply]

theorem term_moveZero {k : ℕ}
    (M : Matrix (PairedIndex (k + 1)) (PairedIndex (k + 1)) ℂ)
    (hM : ∀ p q, M q p = -M p q)
    (σ : Perm (PairedIndex (k + 1))) (p : PairedIndex (k + 1)) :
    term M (σ * moveZero p) = term M σ := by
  rw [moveZero, Pfaffian.pairedPerm, ← mul_assoc,
    term_orientationPerm M hM, term_basePerm]

/-- Permutations whose first image is the first index. -/
abbrev FixedZero (k : ℕ) :=
  {σ : Perm (PairedIndex (k + 1)) // σ (0, 0) = (0, 0)}

/-- Every permutation has a unique pair-preserving normalization fixing zero. -/
def fixedZeroEquiv (k : ℕ) :
    Perm (PairedIndex (k + 1)) ≃ PairedIndex (k + 1) × FixedZero k where
  toFun σ :=
    let p := σ.symm (0, 0)
    (p, ⟨σ * moveZero p, by simp [Equiv.Perm.mul_apply, p]⟩)
  invFun d := d.2.val * (moveZero d.1)⁻¹
  left_inv σ := by
    simp only
    simp [mul_assoc]
  right_inv d := by
    rcases d with ⟨p, τ⟩
    have hτ : τ.val.symm (0, 0) = (0, 0) := by
      apply τ.val.injective
      rw [τ.val.apply_symm_apply, τ.property]
    have hp : (τ.val * (moveZero p)⁻¹).symm (0, 0) = p := by
      change (τ.val * (moveZero p)⁻¹)⁻¹ (0, 0) = p
      rw [mul_inv_rev, inv_inv]
      change moveZero p (τ.val.symm (0, 0)) = p
      rw [hτ, moveZero_apply_zero]
    apply Prod.ext
    · exact hp
    · apply Subtype.ext
      change (τ.val * (moveZero p)⁻¹) *
        moveZero ((τ.val * (moveZero p)⁻¹).symm (0, 0)) = τ.val
      rw [hp]
      simp [mul_assoc]


/-- The literal numerator is exactly 2(k+1) copies of its fixed-zero numerator. -/
theorem sum_term_fixedZero {k : ℕ}
    (M : Matrix (PairedIndex (k + 1)) (PairedIndex (k + 1)) ℂ)
    (hM : ∀ p q, M q p = -M p q) :
    (∑ σ : Perm (PairedIndex (k + 1)), term M σ) =
      (2 * (k + 1) : ℂ) * ∑ τ : FixedZero k, term M τ.val := by
  classical
  have ht (d : PairedIndex (k + 1) × FixedZero k) :
      term M ((fixedZeroEquiv k).symm d) = term M d.2.val := by
    change term M (d.2.val * (moveZero d.1)⁻¹) = term M d.2.val
    have hh := term_moveZero M hM (d.2.val * (moveZero d.1)⁻¹) d.1
    simpa [mul_assoc] using hh.symm
  calc
    (∑ σ : Perm (PairedIndex (k + 1)), term M σ) =
        ∑ d : PairedIndex (k + 1) × FixedZero k,
          term M ((fixedZeroEquiv k).symm d) :=
      ((fixedZeroEquiv k).symm.sum_comp (term M)).symm
    _ = ∑ p : PairedIndex (k + 1), ∑ τ : FixedZero k, term M τ.val := by
      simp_rw [ht]
      rw [Fintype.sum_prod_type]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, PairedIndex,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring

end Paper.PfaffianBridge
