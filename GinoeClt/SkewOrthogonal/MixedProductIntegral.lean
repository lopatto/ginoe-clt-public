/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.MixedProductCoefficient
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Complex.Basic

/-! # Genuine product-measure integrals of full mixed coefficients

Every separated product is proved integrable before any finite integral sum.
No coefficient/integral interchange is an assumption.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
open Equiv

namespace Paper.SkewOrthogonal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

theorem integrable_perm_product (k : ℕ) (f : Fin k → X → ℂ)
    (hf : ∀ j, Integrable (f j) μ) (σ : Perm (Fin k)) :
    Integrable (fun x : Fin k → X ↦ ∏ j : Fin k, f j (x (σ j))) (Measure.pi (fun _ ↦ μ)) := by
  have hb : Integrable (fun x : Fin k → X ↦ ∏ j : Fin k, f j (x j))
      (Measure.pi (fun _ ↦ μ)) := Integrable.fintype_prod hf
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin k ↦ X) σ.symm
  have hp (x : Fin k → X) (j : Fin k) : e x j = x (σ j) := by
    simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin k ↦ X) σ.symm x (σ j)
  have h := ((measurePreserving_piCongrLeft (fun _ : Fin k ↦ μ) σ.symm).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).mpr hb
  change Integrable (fun x : Fin k → X ↦ ∏ j : Fin k, f j (e x j))
    (Measure.pi (fun _ ↦ μ)) at h
  simpa only [hp] using h

/-- Native totalized product identity. The genuine L1 version above is used
before the finite integral sum in the coefficient theorem below. -/
theorem integral_perm_product (k : ℕ) (f : Fin k → X → ℂ) (σ : Perm (Fin k)) :
    (∫ x : Fin k → X, ∏ j : Fin k, f j (x (σ j)) ∂(Measure.pi (fun _ ↦ μ))) =
      ∏ j : Fin k, ∫ u, f j u ∂μ := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin k ↦ X) σ.symm
  have hp (x : Fin k → X) (j : Fin k) : e x j = x (σ j) := by
    simpa [e] using MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin k ↦ X) σ.symm x (σ j)
  calc
    _ = ∫ x : Fin k → X, ∏ j : Fin k, f j (e x j) ∂(Measure.pi (fun _ ↦ μ)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [hp]
    _ = ∫ x : Fin k → X, ∏ j : Fin k, f j (x j) ∂(Measure.pi (fun _ ↦ μ)) :=
      by
        simpa only [e] using! (measurePreserving_piCongrLeft (fun _ : Fin k ↦ μ) σ.symm).integral_comp'
          (fun x : Fin k → X ↦ ∏ j : Fin k, f j (x j))
    _ = _ := integral_fintype_prod_eq_prod _

/-- The actual full mixed coefficient is genuinely integrable. -/
theorem integrable_coeff_prod_linearForms (k : ℕ) (f : Fin k → X → ℂ)
    (hf : ∀ j, Integrable (f j) μ) :
    Integrable (fun x : Fin k → X ↦
      (∏ j : Fin k, ∑ i : Fin k, MvPolynomial.C (f j (x i)) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k)) (Measure.pi (fun _ ↦ μ)) := by
  simp_rw [coeff_prod_linearForms]
  apply integrable_finsetSum
  intro σ hσ
  exact integrable_perm_product μ k f hf σ

/-- The exact integral coefficient formula and factorial, with all Fubini hypotheses discharged. -/
theorem integral_coeff_prod_linearForms (k : ℕ) (f : Fin k → X → ℂ)
    (hf : ∀ j, Integrable (f j) μ) :
    (∫ x : Fin k → X,
      (∏ j : Fin k, ∑ i : Fin k, MvPolynomial.C (f j (x i)) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k) ∂(Measure.pi (fun _ ↦ μ))) =
      (k.factorial : ℂ) * ∏ j : Fin k, ∫ u, f j u ∂μ := by
  simp_rw [coeff_prod_linearForms]
  rw [integral_finsetSum _ (fun σ _ ↦ integrable_perm_product μ k f hf σ)]
  simp only [integral_perm_product μ k f, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- For these finite products, integration of the full coefficient commutes with
replacing each entry by its actual integral; this is proved, not assumed. -/
theorem integral_coeff_prod_linearForms_eq_coeff (k : ℕ) (f : Fin k → X → ℂ)
    (hf : ∀ j, Integrable (f j) μ) :
    (∫ x : Fin k → X,
      (∏ j : Fin k, ∑ i : Fin k, MvPolynomial.C (f j (x i)) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k) ∂(Measure.pi (fun _ ↦ μ))) =
      (∏ j : Fin k, ∑ i : Fin k, MvPolynomial.C (∫ u, f j u ∂μ) * MvPolynomial.X i).coeff
        (fullSquarefreeIndex k) := by
  rw [integral_coeff_prod_linearForms μ k f hf, coeff_prod_linearForms]
  simp [Fintype.card_perm, nsmul_eq_mul]

end Paper.SkewOrthogonal
