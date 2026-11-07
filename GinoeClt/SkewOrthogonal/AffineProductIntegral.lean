/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.AffineProductCoefficient
public import GinoeClt.SkewOrthogonal.MixedProductIntegral

/-! # Finite-product integration of genuine affine mixed coefficients -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Paper.SkewOrthogonal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Selection of k distinct row factors can be enumerated without changing its product. -/
theorem selected_linear_product_reindex {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (T : Finset ι) (hT : T.card = k) (b : ι → Fin k → ℂ) :
    (∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i) =
      ∏ j : Fin k, ∑ i : Fin k,
        MvPolynomial.C (b ((Fintype.equivFinOfCardEq (α := ↥T) (by simpa using hT)).symm j).val i) *
          MvPolynomial.X i := by
  rw [← Finset.prod_coe_sort T
    (fun j ↦ ∑ i : Fin k, MvPolynomial.C (b j i) * MvPolynomial.X i)]
  exact (Equiv.prod_comp (Fintype.equivFinOfCardEq (α := ↥T) (by simpa using hT)).symm _).symm

/-- Actual L1 of the selected mixed coefficient; no integrability of constant unused variables is required. -/
theorem integrable_coeff_selected_linear {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (T : Finset ι) (hT : T.card = k) (f : ι → X → ℂ)
    (hf : ∀ j, Integrable (f j) μ) :
    Integrable (fun x : Fin k → X ↦
      (∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (f j (x i)) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k)) (Measure.pi (fun _ ↦ μ)) := by
  simp_rw [selected_linear_product_reindex T hT]
  exact integrable_coeff_prod_linearForms μ k _ (fun j ↦ hf _)

/-- Genuine coefficient/integral commutation on the selected factors. -/
theorem integral_coeff_selected_linear {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (T : Finset ι) (hT : T.card = k) (f : ι → X → ℂ)
    (hf : ∀ j, Integrable (f j) μ) :
    (∫ x : Fin k → X,
      (∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (f j (x i)) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k) ∂(Measure.pi (fun _ ↦ μ))) =
      (∏ j ∈ T, ∑ i : Fin k, MvPolynomial.C (∫ u, f j u ∂μ) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k) := by
  simp_rw [selected_linear_product_reindex T hT]
  exact integral_coeff_prod_linearForms_eq_coeff μ k _ (fun j ↦ hf _)

/-- Full mixed coefficients of affine products are genuinely integrable. -/
theorem integrable_coeff_affineProductPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (g : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j, Integrable (f j) μ) :
    Integrable (fun x : Fin k → X ↦
      (affineProductPolynomial g (fun j i ↦ f j (x i))).coeff (fullSquarefreeIndex k))
      (Measure.pi (fun _ ↦ μ)) := by
  simp_rw [coeff_affineProductPolynomial]
  apply integrable_finsetSum
  intro T hT
  exact (integrable_coeff_selected_linear μ T (Finset.mem_powersetCard.mp hT).2 f hf).const_mul _

/-- Every Fubini and finite-sum interchange is discharged from entry L1.
Constants are kept in the complementary factors, rather than integrated against an infinite measure. -/
theorem integral_coeff_affineProductPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (g : ι → ℂ) (f : ι → X → ℂ) (hf : ∀ j, Integrable (f j) μ) :
    (∫ x : Fin k → X,
      (affineProductPolynomial g (fun j i ↦ f j (x i))).coeff (fullSquarefreeIndex k)
        ∂(Measure.pi (fun _ ↦ μ))) =
      (affineProductPolynomial g (fun (j : ι) (_ : Fin k) ↦ ∫ u, f j u ∂μ)).coeff
        (fullSquarefreeIndex k) := by
  simp_rw [coeff_affineProductPolynomial]
  rw [integral_finsetSum _ (fun T hT ↦
    (integrable_coeff_selected_linear μ T (Finset.mem_powersetCard.mp hT).2 f hf).const_mul _)]
  apply Finset.sum_congr rfl
  intro T hT
  rw [integral_const_mul, integral_coeff_selected_linear μ T (Finset.mem_powersetCard.mp hT).2 f hf]

end Paper.SkewOrthogonal
