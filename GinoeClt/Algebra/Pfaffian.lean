/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Basic.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Interlaced Pfaffians and determinant blocks

The pair (i, a) represents interlaced position 2*i+a. The Pfaffian below
uses the full permutation sum and the exact factor 2^k*k!.
-/

@[expose] public section
noncomputable section
open Equiv
open scoped BigOperators

namespace Paper

abbrev PairedIndex (k : ℕ) := Fin k × Fin 2

def permutationSign {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Perm ι) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ)

/-- Full normalized permutation sum in the interlaced order. -/
def pfaffian {k : ℕ} (M : Matrix (PairedIndex k) (PairedIndex k) ℂ) : ℂ :=
  ((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ *
    ∑ σ : Perm (PairedIndex k),
      permutationSign σ * ∏ i : Fin k, M (σ (i, 0)) (σ (i, 1))

/-- The off-diagonal block Q in the interlaced ordering. -/
def interlacedMatrix {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (PairedIndex k) (PairedIndex k) ℂ :=
  fun p q ↦ if p.2 = 0 ∧ q.2 = 1 then Q p.1 q.1 else
    if p.2 = 1 ∧ q.2 = 0 then -Q q.1 p.1 else 0

theorem interlacedMatrix_skew {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ) :
    (interlacedMatrix Q).transpose = -interlacedMatrix Q := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [interlacedMatrix, Matrix.transpose_apply]

namespace Pfaffian

def sideFlip (a : Fin 2) : Perm (Fin 2) :=
  if a = 0 then 1 else Equiv.swap 0 1

def orientationPerm {k : ℕ} (ε : Fin k → Fin 2) : Perm (PairedIndex k) :=
  Equiv.prodCongrRight (fun i ↦ sideFlip (ε i))

def basePerm {k : ℕ} (α β : Perm (Fin k)) : Perm (PairedIndex k) :=
  Equiv.prodCongrLeft (fun a : Fin 2 ↦ if a = 0 then α else β)

def pairedPerm {k : ℕ} (α β : Perm (Fin k)) (ε : Fin k → Fin 2) :
    Perm (PairedIndex k) :=
  basePerm α β * orientationPerm ε

theorem sign_basePerm {k : ℕ} (α β : Perm (Fin k)) :
    Perm.sign (basePerm α β) = Perm.sign α * Perm.sign β := by
  rw [basePerm, Perm.sign_prodCongrLeft]
  simp [Fin.prod_univ_two]

theorem sign_orientationPerm {k : ℕ} (ε : Fin k → Fin 2) :
    Perm.sign (orientationPerm ε) = ∏ i, Perm.sign (sideFlip (ε i)) :=
  Perm.sign_prodCongrRight _

theorem interlacedMatrix_paired_entry {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ)
    (α β : Perm (Fin k)) (ε : Fin k → Fin 2) (i : Fin k) :
    interlacedMatrix Q (pairedPerm α β ε (i, 0)) (pairedPerm α β ε (i, 1)) =
      permutationSign (sideFlip (ε i)) * Q (α i) (β i) := by
  have hside : ε i = 0 ∨ ε i = 1 := by
    have := (ε i).isLt
    omega
  rcases hside with he | he <;>
    simp [pairedPerm, basePerm, orientationPerm, sideFlip, he,
      Equiv.Perm.mul_apply, interlacedMatrix, permutationSign]

@[simp] theorem sideFlip_zero (a : Fin 2) : sideFlip a 0 = a := by
  fin_cases a <;> simp [sideFlip]

theorem sideFlip_one_of_ne (a b : Fin 2) (h : a ≠ b) : sideFlip a 1 = b := by
  fin_cases a <;> fin_cases b <;> simp_all [sideFlip]

theorem sideFlip_symm (a : Fin 2) : (sideFlip a).symm = sideFlip a := by
  by_cases h : a = 0
  · simp only [sideFlip, ite_eq_left h]
    rfl
  · simp [sideFlip, h]

theorem sideFlip_involutive (a : Fin 2) : Function.Involutive (sideFlip a) := by
  intro b
  have h := (sideFlip a).symm_apply_apply b
  rwa [sideFlip_symm] at h

theorem orientationPerm_symm {k : ℕ} (ε : Fin k → Fin 2) :
    (orientationPerm ε).symm = orientationPerm ε := by
  rw [orientationPerm, Equiv.prodCongrRight_symm]
  congr 1
  funext i
  exact sideFlip_symm (ε i)

theorem orientationPerm_mul_self {k : ℕ} (ε : Fin k → Fin 2) :
    orientationPerm ε * orientationPerm ε = 1 := by
  ext x : 1
  change orientationPerm ε (orientationPerm ε x) = x
  have h := (orientationPerm ε).symm_apply_apply x
  rwa [orientationPerm_symm] at h

@[simp] theorem pairedPerm_apply_snd {k : ℕ} (α β : Perm (Fin k))
    (ε : Fin k → Fin 2) (i : Fin k) (a : Fin 2) :
    (pairedPerm α β ε (i, a)).2 = sideFlip (ε i) a := rfl

/-- Exactly the permutations whose every pair crosses between the two sides. -/
def Good {k : ℕ} (σ : Perm (PairedIndex k)) : Prop :=
  ∀ i, (σ (i, 0)).2 ≠ (σ (i, 1)).2

theorem good_pairedPerm {k : ℕ} (α β : Perm (Fin k)) (ε : Fin k → Fin 2) :
    Good (pairedPerm α β ε) := by
  intro i h
  rw [pairedPerm_apply_snd, pairedPerm_apply_snd] at h
  exact (by decide : (0 : Fin 2) ≠ 1) ((sideFlip (ε i)).injective h)

theorem sides_of_good {k : ℕ} {σ : Perm (PairedIndex k)} (hσ : Good σ)
    (i : Fin k) (a : Fin 2) :
    (σ (i, a)).2 = sideFlip ((σ (i, 0)).2) a := by
  fin_cases a
  · exact (sideFlip_zero _).symm
  · exact (sideFlip_one_of_ne _ _ (hσ i)).symm

theorem normalized_preservesSide {k : ℕ} {σ : Perm (PairedIndex k)}
    (hσ : Good σ) (x : PairedIndex k) :
    ((σ * orientationPerm (fun i ↦ (σ (i, 0)).2)) x).2 = x.2 := by
  rcases x with ⟨i, a⟩
  change (σ (i, sideFlip ((σ (i, 0)).2) a)).2 = a
  rw [sides_of_good hσ]
  exact sideFlip_involutive _ _

/-- Fiber permutations, following the elementary construction used in
Mathlib's determinant-of-blockDiagonal proof. -/
def fiberPerm {k : ℕ} (D : Perm (PairedIndex k))
    (hD : ∀ x, (D x).2 = x.2) (b : Fin 2) : Perm (Fin k) where
  toFun i := (D (i, b)).1
  invFun i := (D.symm (i, b)).1
  left_inv i := by
    have hp : ((D (i, b)).1, b) = D (i, b) := Prod.ext rfl (hD (i, b)).symm
    change (D.symm ((D (i, b)).1, b)).1 = i
    rw [hp]
    simp
  right_inv i := by
    have hi : (D.symm (i, b)).2 = b := by
      have h := hD (D.symm (i, b))
      simpa using h.symm
    have hp : ((D.symm (i, b)).1, b) = D.symm (i, b) := Prod.ext rfl hi.symm
    change (D ((D.symm (i, b)).1, b)).1 = i
    rw [hp]
    simp

theorem basePerm_fiberPerm {k : ℕ} (D : Perm (PairedIndex k))
    (hD : ∀ x, (D x).2 = x.2) :
    basePerm (fiberPerm D hD 0) (fiberPerm D hD 1) = D := by
  ext ⟨i, a⟩ : 1
  apply Prod.ext
  · fin_cases a <;> rfl
  · exact (hD (i, a)).symm

abbrev PermData (k : ℕ) :=
  Perm (Fin k) × Perm (Fin k) × (Fin k → Fin 2)

theorem pairedPerm_data_injective {k : ℕ} :
    Function.Injective
      (fun d : PermData k ↦ pairedPerm d.1 d.2.1 d.2.2) := by
  rintro ⟨α, β, ε⟩ ⟨α', β', ε'⟩ h
  have he : ε = ε' := by
    funext i
    have hh := congrArg (fun σ : Perm (PairedIndex k) ↦ (σ (i, 0)).2) h
    simpa only [pairedPerm_apply_snd, sideFlip_zero] using hh
  change basePerm α β * orientationPerm ε = basePerm α' β' * orientationPerm ε' at h
  rw [← he] at h
  have hb : basePerm α β = basePerm α' β' := mul_right_cancel h
  have ha : α = α' := by
    ext i : 1
    have hh := congrArg (fun σ : Perm (PairedIndex k) ↦ (σ (i, 0)).1) hb
    simpa [basePerm] using hh
  have hb' : β = β' := by
    ext i : 1
    have hh := congrArg (fun σ : Perm (PairedIndex k) ↦ (σ (i, 1)).1) hb
    simpa [basePerm] using hh
  exact Prod.ext ha (Prod.ext hb' he)

theorem pairedPerm_covers_good {k : ℕ} (σ : Perm (PairedIndex k)) (hσ : Good σ) :
    ∃ d : PermData k, pairedPerm d.1 d.2.1 d.2.2 = σ := by
  let ε : Fin k → Fin 2 := fun i ↦ (σ (i, 0)).2
  let D : Perm (PairedIndex k) := σ * orientationPerm ε
  have hD : ∀ x, (D x).2 = x.2 := normalized_preservesSide hσ
  refine ⟨⟨fiberPerm D hD 0, fiberPerm D hD 1, ε⟩, ?_⟩
  change basePerm (fiberPerm D hD 0) (fiberPerm D hD 1) * orientationPerm ε = σ
  rw [basePerm_fiberPerm]
  change (σ * orientationPerm ε) * orientationPerm ε = σ
  rw [mul_assoc, orientationPerm_mul_self, mul_one]

/-- Every crossing permutation has exactly two label permutations and one
independent choice of pair orientations. -/
def goodPermEquiv (k : ℕ) : PermData k ≃ {σ : Perm (PairedIndex k) // Good σ} :=
  Equiv.ofBijective
    (fun d ↦ ⟨pairedPerm d.1 d.2.1 d.2.2, good_pairedPerm _ _ _⟩)
    ⟨fun _ _ h ↦ pairedPerm_data_injective (congrArg Subtype.val h), by
      rintro ⟨σ, hσ⟩
      obtain ⟨d, hd⟩ := pairedPerm_covers_good σ hσ
      exact ⟨d, Subtype.ext hd⟩⟩

theorem permutationSign_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ τ : Perm ι) :
    permutationSign (σ * τ) = permutationSign σ * permutationSign τ := by
  simp [permutationSign, map_mul]

theorem permutationSign_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Perm ι) : permutationSign σ * permutationSign σ = 1 := by
  have h := congrArg (fun z : ℤ ↦ (z : ℂ)) (Int.units_coe_mul_self (Perm.sign σ))
  simpa only [Int.cast_mul, Int.cast_one, permutationSign] using h

theorem permutationSign_basePerm {k : ℕ} (α β : Perm (Fin k)) :
    permutationSign (basePerm α β) = permutationSign α * permutationSign β := by
  simp [permutationSign, sign_basePerm]

theorem permutationSign_orientationPerm {k : ℕ} (ε : Fin k → Fin 2) :
    permutationSign (orientationPerm ε) = ∏ i, permutationSign (sideFlip (ε i)) := by
  simp [permutationSign, sign_orientationPerm]

theorem signedTerm_pairedPerm {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ)
    (α β : Perm (Fin k)) (ε : Fin k → Fin 2) :
    permutationSign (pairedPerm α β ε) *
      (∏ i : Fin k,
        interlacedMatrix Q (pairedPerm α β ε (i, 0)) (pairedPerm α β ε (i, 1))) =
      permutationSign α * permutationSign β * ∏ i : Fin k, Q (α i) (β i) := by
  have hs : permutationSign (pairedPerm α β ε) =
      (permutationSign α * permutationSign β) * permutationSign (orientationPerm ε) := by
    rw [pairedPerm, permutationSign_mul, permutationSign_basePerm]
  rw [hs]
  simp_rw [interlacedMatrix_paired_entry]
  rw [Finset.prod_mul_distrib, ← permutationSign_orientationPerm]
  calc
    _ = (permutationSign α * permutationSign β) *
        (permutationSign (orientationPerm ε) * permutationSign (orientationPerm ε)) *
        (∏ i : Fin k, Q (α i) (β i)) := by ring
    _ = _ := by rw [permutationSign_mul_self, mul_one]

def signedTerm {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ)
    (σ : Perm (PairedIndex k)) : ℂ :=
  permutationSign σ * ∏ i : Fin k, interlacedMatrix Q (σ (i, 0)) (σ (i, 1))

theorem interlacedMatrix_zero_of_same_side {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ)
    (p q : PairedIndex k) (h : p.2 = q.2) : interlacedMatrix Q p q = 0 := by
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  dsimp only at h
  subst b
  fin_cases a <;> simp [interlacedMatrix]

theorem signedTerm_zero_of_not_good {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ)
    (σ : Perm (PairedIndex k)) (h : ¬ Good σ) : signedTerm Q σ = 0 := by
  classical
  simp only [Good, not_forall, not_not] at h
  obtain ⟨i, hi⟩ := h
  have hp : (∏ j : Fin k, interlacedMatrix Q (σ (j, 0)) (σ (j, 1))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i)
      (interlacedMatrix_zero_of_same_side Q _ _ hi)
  simp only [signedTerm, hp, mul_zero]

theorem sum_signedTerm_eq_data {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ) :
    (∑ σ : Perm (PairedIndex k), signedTerm Q σ) =
      ∑ d : PermData k,
        permutationSign d.1 * permutationSign d.2.1 *
          ∏ i : Fin k, Q (d.1 i) (d.2.1 i) := by
  classical
  have hfilter :
      (∑ σ ∈ Finset.univ.filter Good, signedTerm Q σ) =
        ∑ σ : Perm (PairedIndex k), signedTerm Q σ := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro σ _ hnot
    apply signedTerm_zero_of_not_good Q σ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  have hsub :
      (∑ σ : {σ : Perm (PairedIndex k) // Good σ}, signedTerm Q σ.val) =
        ∑ σ ∈ Finset.univ.filter Good, signedTerm Q σ := by
    simpa only [Finset.subtype_univ] using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := Good) (signedTerm Q))
  calc
    _ = ∑ σ : {σ : Perm (PairedIndex k) // Good σ}, signedTerm Q σ.val :=
      hfilter.symm.trans hsub.symm
    _ = ∑ d : PermData k, signedTerm Q ((goodPermEquiv k d).val) :=
      ((goodPermEquiv k).sum_comp (fun σ ↦ signedTerm Q σ.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      exact signedTerm_pairedPerm Q d.1 d.2.1 d.2.2

@[simp] theorem permutationSign_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Perm ι) : permutationSign σ⁻¹ = permutationSign σ := by
  simp [permutationSign]

theorem sum_signed_labels {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ)
    (β : Perm (Fin k)) :
    (∑ α : Perm (Fin k),
      permutationSign α * permutationSign β * ∏ i : Fin k, Q (α i) (β i)) = Q.det := by
  rw [Matrix.det_apply']
  change _ = ∑ σ : Perm (Fin k), permutationSign σ * ∏ i : Fin k, Q (σ i) i
  apply Fintype.sum_equiv (Equiv.mulRight (β⁻¹)) _ _
  intro α
  change permutationSign α * permutationSign β * (∏ i : Fin k, Q (α i) (β i)) =
    permutationSign (α * β⁻¹) * ∏ i : Fin k, Q ((α * β⁻¹) i) i
  rw [permutationSign_mul, permutationSign_inv]
  congr 1
  simpa [Equiv.Perm.mul_apply] using
    (Equiv.prod_comp β (fun i : Fin k ↦ Q ((α * β⁻¹) i) i))

theorem double_sum_signed_labels {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ) :
    (∑ α : Perm (Fin k), ∑ β : Perm (Fin k),
      permutationSign α * permutationSign β * ∏ i : Fin k, Q (α i) (β i)) =
      (k.factorial : ℂ) * Q.det := by
  rw [Finset.sum_comm]
  simp_rw [sum_signed_labels Q]
  simp [Fintype.card_perm]

theorem sum_signedTerm_eq {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ) :
    (∑ σ : Perm (PairedIndex k), signedTerm Q σ) =
      (2 : ℂ) ^ k * ((k.factorial : ℂ) * Q.det) := by
  rw [sum_signedTerm_eq_data]
  simp only [PermData, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← double_sum_signed_labels Q, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]

end Pfaffian

/-- The exact determinant identity for interlaced zero diagonal blocks. -/
theorem pfaffian_interlacedMatrix_det {k : ℕ} (Q : Matrix (Fin k) (Fin k) ℂ) :
    pfaffian (interlacedMatrix Q) = Q.det := by
  have hn : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  change ((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ *
    (∑ σ : Perm (PairedIndex k), Pfaffian.signedTerm Q σ) = Q.det
  rw [Pfaffian.sum_signedTerm_eq]
  calc
    _ = (((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ *
        ((2 : ℂ) ^ k * (k.factorial : ℂ))) * Q.det := by ring
    _ = Q.det := by rw [inv_mul_cancel₀ (mul_ne_zero h2 hn), one_mul]

/-- The manuscript's zero-block lemma, with arbitrary complex off-diagonal
block and no nondegeneracy assumption. -/
theorem pfaffian_zero_blocks_det {k : ℕ}
    (M : Matrix (PairedIndex k) (PairedIndex k) ℂ)
    (hskew : M.transpose = -M)
    (h00 : ∀ i j, M (i, 0) (j, 0) = 0)
    (h11 : ∀ i j, M (i, 1) (j, 1) = 0) :
    pfaffian M = Matrix.det (fun i j : Fin k ↦ M (i, 0) (j, 1)) := by
  have heq : M = interlacedMatrix (fun i j : Fin k ↦ M (i, 0) (j, 1)) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b
    · simpa [interlacedMatrix] using h00 i j
    · simp [interlacedMatrix]
    · have hs := congrArg (fun D : Matrix (PairedIndex k) (PairedIndex k) ℂ ↦
        D (j, 0) (i, 1)) hskew
      simpa [interlacedMatrix, Matrix.transpose_apply] using hs
    · simpa [interlacedMatrix] using h11 i j
  exact (congrArg pfaffian heq).trans (pfaffian_interlacedMatrix_det _)

namespace Pfaffian

end Pfaffian
end Paper
