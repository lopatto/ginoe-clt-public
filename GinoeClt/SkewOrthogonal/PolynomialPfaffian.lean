/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.AtomicExpansion
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Coeff

/-! # Exact polynomial encoding of the frozen full Pfaffian

The definition is the finite normalized permutation sum. Its evaluation is
proved to be the frozen Paper.pfaffian; no alternate Pfaffian convention is
assumed. Atomic coefficients remain finite algebra, not an ensemble law.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
open Equiv

namespace Paper.SkewOrthogonal

/-- The frozen normalized full-permutation formula, over coefficient polynomials. -/
def pfaffianPolynomial {σ : Type*} {m : ℕ}
    (M : Matrix (PairedIndex m) (PairedIndex m) (MvPolynomial σ ℂ)) : MvPolynomial σ ℂ :=
  MvPolynomial.C (((2 : ℂ) ^ m * (m.factorial : ℂ))⁻¹) *
    ∑ τ : Perm (PairedIndex m), MvPolynomial.C (permutationSign τ) *
      ∏ i : Fin m, M (τ (i,0)) (τ (i,1))

/-- Every evaluation reproduces the actual frozen Pfaffian exactly. -/
theorem eval_pfaffianPolynomial {σ : Type*} {m : ℕ}
    (M : Matrix (PairedIndex m) (PairedIndex m) (MvPolynomial σ ℂ)) (c : σ → ℂ) :
    MvPolynomial.eval c (pfaffianPolynomial M) =
      pfaffian (fun p q ↦ MvPolynomial.eval c (M p q)) := by
  simp [pfaffianPolynomial, pfaffian, map_sum, map_prod]

/-- The actual affine atomic Gram matrix, with one independent variable per atom. -/
def atomicGramPolynomial {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    Matrix (PairedIndex m) (PairedIndex m) (MvPolynomial (Fin r) ℂ) :=
  fun p q ↦ MvPolynomial.C (interlacedMatrix (Matrix.diagonal w) p q) +
    ∑ x : Fin r, MvPolynomial.X x * MvPolynomial.C (A x p 0 * A x q 1 - A x p 1 * A x q 0)

theorem eval_atomicGramPolynomial {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (c : Fin r → ℂ) :
    (fun p q ↦ MvPolynomial.eval c (atomicGramPolynomial w A p q)) = finiteAtomicGram w c A := by
  ext p q
  simp [atomicGramPolynomial, finiteAtomicGram, map_sum]

/-- The normalized source matrix polynomial, defined from its full Pfaffian numerator. -/
def atomicGeneratingPolynomial {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) : MvPolynomial (Fin r) ℂ :=
  MvPolynomial.C ((pfaffian (interlacedMatrix (Matrix.diagonal w)))⁻¹) *
    pfaffianPolynomial (atomicGramPolynomial w A)

theorem eval_atomicGeneratingPolynomial {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (c : Fin r → ℂ) :
    MvPolynomial.eval c (atomicGeneratingPolynomial w A) =
      pfaffian (finiteAtomicGram w c A) / pfaffian (interlacedMatrix (Matrix.diagonal w)) := by
  simp only [atomicGeneratingPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_pfaffianPolynomial, eval_atomicGramPolynomial]
  rw [div_eq_mul_inv, mul_comm]

/-- The genuine atomic matrix generating polynomial is squarefree in its atom variables. -/
theorem atomicGeneratingPolynomial_eq {m r : ℕ} (w : Fin m → ℂ) (hw : ∀ i, w i ≠ 0)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    atomicGeneratingPolynomial w A =
      ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
        MvPolynomial.C (pfaffian (selectedAtomicKernel w A S)) * ∏ x ∈ S, MvPolynomial.X x := by
  let : Infinite ℂ := Infinite.of_injective (fun n : ℕ ↦ (n : ℂ)) Nat.cast_injective
  apply MvPolynomial.funext
  intro c
  rw [eval_atomicGeneratingPolynomial, pfaffian_finiteAtomicGram_ratio w hw]
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro S hS
  ring

/-- The full squarefree multi-index, including zero variables. -/
def fullSquarefreeIndex (r : ℕ) : Fin r →₀ ℕ :=
  Finsupp.indicator Finset.univ (fun _ _ ↦ 1)

theorem fullSquarefreeIndex_eq_indicator_iff {r : ℕ} (S : Finset (Fin r)) :
    fullSquarefreeIndex r = Finsupp.indicator S (fun _ _ ↦ 1) ↔ S = Finset.univ := by
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have hc := congrArg (fun f : Fin r →₀ ℕ ↦ f i) h
    simp [fullSquarefreeIndex, Finsupp.indicator_apply, hi] at hc
  · rintro rfl
    rfl

/-- A subset monomial contributes to the full mixed coefficient exactly once. -/
theorem coeff_fullSquarefree_prod_X {r : ℕ} (S : Finset (Fin r)) :
    (∏ x ∈ S, (MvPolynomial.X x : MvPolynomial (Fin r) ℂ)).coeff (fullSquarefreeIndex r) =
      if S = Finset.univ then 1 else 0 := by
  have h := MvPolynomial.coeff_prod_X_pow (R := ℂ) (fullSquarefreeIndex r) (fun _ ↦ 1) S
  simpa only [pow_one, fullSquarefreeIndex_eq_indicator_iff] using h

/-- The actual full mixed coefficient equals the Pfaffian of the selected full kernel. -/
theorem coeff_atomicGeneratingPolynomial_full {m r : ℕ} (w : Fin m → ℂ)
    (hw : ∀ i, w i ≠ 0) (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    (atomicGeneratingPolynomial w A).coeff (fullSquarefreeIndex r) =
      pfaffian (selectedAtomicKernel w A Finset.univ) := by
  rw [atomicGeneratingPolynomial_eq w hw]
  simp [MvPolynomial.coeff_C_mul, coeff_fullSquarefree_prod_X]

theorem sortedPairEquiv_univ_val (r : ℕ)
    (h : (Finset.univ : Finset (Fin r)).card = r) (i : Fin r) :
    (PfaffianMinor.sortedPairEquiv Finset.univ h i).val = i := by
  rw [PfaffianMinor.sortedPairEquiv_apply]
  apply Fin.ext
  simp [PfaffianMinor.sortedPairVectorOfCard, Fin.sort_univ, List.Vector.get]
  rfl

theorem pfaffian_selectedAtomicKernel_eq_of_card {m r k : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (S : Finset (Fin r)) (h : S.card = k) :
    pfaffian (selectedAtomicKernel w A S) =
      pfaffian (fun p q : PairedIndex k ↦ atomicFeatureKernel w A
        ((PfaffianMinor.sortedPairEquiv S h p.1).val, p.2)
        ((PfaffianMinor.sortedPairEquiv S h q.1).val, q.2)) := by
  subst k
  rfl

/-- Full selection is the literal kernel in its original atom order. -/
theorem pfaffian_selectedAtomicKernel_univ {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    pfaffian (selectedAtomicKernel w A Finset.univ) = pfaffian (atomicFeatureKernel w A) := by
  rw [pfaffian_selectedAtomicKernel_eq_of_card w A Finset.univ (by simp :
    (Finset.univ : Finset (Fin r)).card = r)]
  congr 1
  ext p q
  simp only [sortedPairEquiv_univ_val]

/-- The full mixed coefficient is exactly the actual atom-kernel Pfaffian. -/
theorem coeff_atomicGeneratingPolynomial_kernel {m r : ℕ} (w : Fin m → ℂ)
    (hw : ∀ i, w i ≠ 0) (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    (atomicGeneratingPolynomial w A).coeff (fullSquarefreeIndex r) =
      pfaffian (atomicFeatureKernel w A) := by
  rw [coeff_atomicGeneratingPolynomial_full w hw, pfaffian_selectedAtomicKernel_univ]

end Paper.SkewOrthogonal
