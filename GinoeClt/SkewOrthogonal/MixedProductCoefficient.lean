/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.DiagonalCoefficient

/-! # Actual full mixed coefficients of finite products of linear forms -/
@[expose] public section
noncomputable section
open scoped BigOperators
open Equiv Function

namespace Paper.SkewOrthogonal

/-- The actual exponent multi-index of an assignment of one variable per factor. -/
def assignmentIndex {n k : ℕ} (f : Fin n → Fin k) : Fin k →₀ ℕ :=
  ∑ j : Fin n, Finsupp.single (f j) 1

theorem prod_X_assignment {α : Type*} [DecidableEq α] {k : ℕ}
    (s : Finset α) (f : α → Fin k) :
    (∏ j ∈ s, (MvPolynomial.X (f j) : MvPolynomial (Fin k) ℂ)) =
      MvPolynomial.monomial (∑ j ∈ s, Finsupp.single (f j) 1) 1 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih]
    simp [MvPolynomial.X, MvPolynomial.monomial_mul_monomial]

/-- In equal finite dimensions, the squarefree assignment condition is precisely bijectivity. -/
theorem assignmentIndex_eq_full_iff {k : ℕ} (f : Fin k → Fin k) :
    assignmentIndex f = fullSquarefreeIndex k ↔ Bijective f := by
  classical
  constructor
  · intro h
    have hs : Surjective f := by
      intro i
      by_contra hn
      push Not at hn
      have hn' (j : Fin k) : i ≠ f j := Ne.symm (hn j)
      have hc := congrArg (fun d : Fin k →₀ ℕ ↦ d i) h
      simp [assignmentIndex, fullSquarefreeIndex, Finsupp.indicator_apply, hn'] at hc
    exact Finite.surjective_iff_bijective.mp hs
  · intro hf
    let e : Perm (Fin k) := Equiv.ofBijective f hf
    have he : (∑ j : Fin k, Finsupp.single (e j) (1 : ℕ)) =
        ∑ j : Fin k, Finsupp.single j (1 : ℕ) :=
      Equiv.sum_comp e (fun j : Fin k ↦ (Finsupp.single j (1 : ℕ) : Fin k →₀ ℕ))
    change (∑ j : Fin k, Finsupp.single (e j) 1) = _
    rw [he]
    ext i
    simp [fullSquarefreeIndex, Finsupp.indicator_apply, Finsupp.single_apply]

/-- An exact finite assignment formula, prior to reindexing by permutations. -/
theorem coeff_prod_linearForms_assignments (k : ℕ) (b : Fin k → Fin k → ℂ) :
    (∏ j : Fin k, ∑ i : Fin k,
      MvPolynomial.C (b j i) * MvPolynomial.X i).coeff (fullSquarefreeIndex k) =
      ∑ f : Fin k → Fin k, if Bijective f then ∏ j : Fin k, b j (f j) else 0 := by
  classical
  rw [Fintype.prod_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.coeff_C_mul,
    prod_X_assignment]
  change (∏ j : Fin k, b j (f j)) *
      (MvPolynomial.monomial (assignmentIndex f) (1 : ℂ)).coeff (fullSquarefreeIndex k) = _
  simp [MvPolynomial.coeff_monomial, assignmentIndex_eq_full_iff]

/-- The full mixed coefficient is the actual finite permutation sum, with no admission of a count. -/
theorem coeff_prod_linearForms (k : ℕ) (b : Fin k → Fin k → ℂ) :
    (∏ j : Fin k, ∑ i : Fin k,
      MvPolynomial.C (b j i) * MvPolynomial.X i).coeff (fullSquarefreeIndex k) =
      ∑ σ : Perm (Fin k), ∏ j : Fin k, b j (σ j) := by
  classical
  rw [coeff_prod_linearForms_assignments, ← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun f hf ↦ Equiv.ofBijective f (Finset.mem_filter.mp hf).2)
    (fun σ _ ↦ (σ : Fin k → Fin k)) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    exact Finset.mem_univ _
  · intro σ hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩
  · intro f hf
    rfl
  · intro σ hσ
    apply Equiv.ext
    intro j
    rfl
  · intro f hf
    rfl

end Paper.SkewOrthogonal
