/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.MixedProductCoefficient

/-! # Exact affine-product coefficient selection for the full Pfaffian integral -/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace Paper.SkewOrthogonal

theorem sum_single_total {ι : Type*} [Fintype ι] {k : ℕ} (f : ι → Fin k) :
    (∑ j : ι, Finsupp.single (f j) (1 : ℕ)).sum (fun _ n ↦ n) = Fintype.card ι := by
  classical
  have hs (s : Finset ι) : (∑ j ∈ s, Finsupp.single (f j) (1 : ℕ)).sum (fun _ n ↦ n) = s.card := by
    induction s using Finset.induction with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), ih]
      simp [Finset.card_insert_of_notMem hj, Nat.add_comm]
  simpa only [Finset.card_univ] using hs Finset.univ

/-- A product of n linear forms cannot contribute to full squarefree degree k when n differs. -/
theorem coeff_prod_linearForms_zero_of_card_ne {ι : Type*} [Fintype ι] {k : ℕ}
    (b : ι → Fin k → ℂ) (h : Fintype.card ι ≠ k) :
    (∏ j : ι, ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i).coeff
      (fullSquarefreeIndex k) = 0 := by
  classical
  rw [Fintype.prod_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro f hf
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.coeff_C_mul, prod_X_assignment]
  have hd : (∑ j : ι, Finsupp.single (f j) (1 : ℕ)) ≠ fullSquarefreeIndex k := by
    intro hd
    have hc := congrArg (fun d : Fin k →₀ ℕ ↦ d.sum (fun _ n ↦ n)) hd
    rw [sum_single_total, fullSquarefreeIndex_sum] at hc
    exact h hc
  simp [MvPolynomial.coeff_monomial, hd]

/-- The actual product of affine entries, with the variable part displayed first. -/
def affineProductPolynomial {ι : Type*} [Fintype ι] {k : ℕ}
    (g : ι → ℂ) (b : ι → Fin k → ℂ) : MvPolynomial (Fin k) ℂ :=
  ∏ j : ι, ((∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i) + MvPolynomial.C (g j))

/-- Coefficients choose exactly k variable factors and keep the actual complementary constants. -/
theorem coeff_affineProductPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (g : ι → ℂ) (b : ι → Fin k → ℂ) :
    (affineProductPolynomial g b).coeff (fullSquarefreeIndex k) =
      ∑ T ∈ (Finset.univ : Finset ι).powersetCard k,
        (∏ j ∈ Tᶜ, g j) *
          (∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i).coeff
            (fullSquarefreeIndex k) := by
  have hp : affineProductPolynomial g b =
      ∑ T ∈ (Finset.univ : Finset ι).powerset,
        MvPolynomial.C (∏ j ∈ Tᶜ, g j) *
          ∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i := by
    rw [affineProductPolynomial, Finset.prod_add]
    apply Finset.sum_congr rfl
    intro T hT
    rw [← map_prod]
    simp only [← Finset.compl_eq_univ_sdiff]
    ring
  rw [hp, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases h : T.card = k
  · simp [h]
  · have hz : (∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k) = 0 := by
      rw [← Finset.prod_coe_sort T
        (fun j ↦ ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i)]
      exact coeff_prod_linearForms_zero_of_card_ne (fun j : T ↦ b j.val)
        (by simpa only [Fintype.card_coe] using h)
    simp [h, hz]

end Paper.SkewOrthogonal
