/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.ContinuousRankTwo
@[expose] public section
noncomputable section
open MeasureTheory Equiv
open scoped BigOperators
namespace Paper.SkewOrthogonal

/-- Literal matrix of m adjacent feature pairs, with the original paired row order. -/
def pairedFeatureMatrix {m : ℕ} (A : Fin m → PairedIndex m → Fin 2 → ℂ) :
    Matrix (PairedIndex m) (PairedIndex m) ℂ :=
  fun row col ↦ A col.1 row col.2

/-- Square finite wedge sums have exactly one maximal selected minor. -/
theorem pfaffian_square_wedges {m : ℕ} (A : Fin m → PairedIndex m → Fin 2 → ℂ)
    (c : Fin m → ℂ) :
    pfaffian (fun p q ↦ ∑ i : Fin m,
      c i * (A i p 0 * A i q 1 - A i p 1 * A i q 0)) =
      (∏ i, c i) * (pairedFeatureMatrix A).det := by
  rw [pfaffian_finite_wedges]
  unfold PfaffianMinor.finsetADMSRhs
  have hc : (Finset.univ : Finset (Fin m)).powersetCard m = {Finset.univ} := by
    simpa using (Finset.powersetCard_self (Finset.univ : Finset (Fin m)))
  rw [hc]
  simp only [Finset.sum_singleton]
  congr 1
  let e : Fin m ≃ (Finset.univ : Finset (Fin m)) :=
    { toFun := fun i ↦ ⟨i,Finset.mem_univ i⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [selectedPairDetFinset_eq_of_equiv _ Finset.univ e]
  have he : selectedPairMatrixOfEquiv
      (fun i j a ↦ A i ((PfaffianMinor.pairColumnEquiv m).symm j) a)
        Finset.univ e =
      (pairedFeatureMatrix A).submatrix (PfaffianMinor.pairColumnEquiv m).symm
        (PfaffianMinor.pairColumnEquiv m).symm := by
    ext i j
    rfl
  rw [he,Matrix.det_submatrix_equiv_self]

/-- Pure rank-two matrix polynomials have the literal determinant as full coefficient. -/
theorem coeff_pure_wedges {m : ℕ} (A : Fin m → PairedIndex m → Fin 2 → ℂ) :
    (pfaffianPolynomial (affineMatrixPolynomial (0 : Matrix (PairedIndex m) (PairedIndex m) ℂ)
      (fun i p q ↦ A i p 0 * A i q 1 - A i p 1 * A i q 0))).coeff
        (fullSquarefreeIndex m) = (pairedFeatureMatrix A).det := by
  have he : pfaffianPolynomial
      (affineMatrixPolynomial (0 : Matrix (PairedIndex m) (PairedIndex m) ℂ)
        (fun i p q ↦ A i p 0 * A i q 1 - A i p 1 * A i q 0)) =
      MvPolynomial.C ((pairedFeatureMatrix A).det) * ∏ i : Fin m, MvPolynomial.X i := by
    let : Infinite ℂ := Infinite.of_injective (fun n : ℕ ↦ (n : ℂ)) Nat.cast_injective
    apply MvPolynomial.funext
    intro c
    rw [eval_pfaffianPolynomial]
    simp only [affineMatrixPolynomial,Matrix.zero_apply,
      MvPolynomial.eval_sum,MvPolynomial.eval_mul,MvPolynomial.eval_C,
      MvPolynomial.eval_X,MvPolynomial.eval_prod,map_zero,add_zero]
    simpa only [mul_comm] using! (pfaffian_square_wedges A c)
  rw [he,MvPolynomial.coeff_C_mul]
  have hc := coeff_fullSquarefree_prod_X (Finset.univ : Finset (Fin m))
  simpa using congrArg (fun a : ℂ ↦ (pairedFeatureMatrix A).det*a) hc

theorem coeff_univariatePfaffian_zero_base {m : ℕ}
    (M : Matrix (PairedIndex m) (PairedIndex m) ℂ) :
    (univariatePfaffianPolynomial (univariateAffineMatrix 0 M)).coeff m = pfaffian M := by
  simp only [univariatePfaffianPolynomial,univariateAffineMatrix,Matrix.zero_apply,
    Polynomial.C_0,add_zero,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,← map_prod,← mul_assoc,← Polynomial.C_mul,
    ← Finset.sum_mul,← map_sum,Polynomial.coeff_C_mul_X_pow,ite_eq_left]
  rfl

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integrable_rankTwo_of_pair_products {m : ℕ}
    (A : X → PairedIndex m → Fin 2 → ℂ)
    (hA : ∀ p q, Integrable (fun x ↦ A x p 0 * A x q 1) μ)
    (p q : PairedIndex m) :
    Integrable (fun x ↦ rankTwoEntry A x p q) μ := by
  exact (hA p q).sub ((hA q p).congr (Filter.Eventually.of_forall fun x ↦ mul_comm _ _))

variable [SigmaFinite μ]

/-- Genuine L1 for the literal adjacent-pair determinant, from pair-product L1 only. -/
theorem integrable_pairedFeatureMatrix {m : ℕ}
    (A : X → PairedIndex m → Fin 2 → ℂ)
    (hA : ∀ p q, Integrable (fun x ↦ A x p 0 * A x q 1) μ) :
    Integrable (fun x : Fin m → X ↦ (pairedFeatureMatrix (fun i ↦ A (x i))).det)
      (Measure.pi (fun _ : Fin m ↦ μ)) := by
  have h := integrable_coeff_pfaffian_affine μ m 0 (rankTwoEntry A)
    (integrable_rankTwo_of_pair_products μ A hA)
  have he (x : Fin m → X) : (fun i ↦ rankTwoEntry A (x i)) =
      (fun i p q ↦ A (x i) p 0 * A (x i) q 1 - A (x i) p 1 * A (x i) q 0) := rfl
  simp_rw [he,coeff_pure_wedges] at h
  exact h

/-- Continuous de Bruijn wedge identity with every L1/Fubini premise discharged. -/
theorem integral_pairedFeatureMatrix {m : ℕ}
    (A : X → PairedIndex m → Fin 2 → ℂ)
    (hA : ∀ p q, Integrable (fun x ↦ A x p 0 * A x q 1) μ) :
    (∫ x : Fin m → X, (pairedFeatureMatrix (fun i ↦ A (x i))).det
      ∂Measure.pi (fun _ : Fin m ↦ μ)) =
      (m.factorial : ℂ) * pfaffian (fun p q ↦ ∫ x,
        (A x p 0 * A x q 1 - A x p 1 * A x q 0) ∂μ) := by
  have h := integral_coeff_pfaffian_affine_eq_factorial μ m 0 (rankTwoEntry A)
    (integrable_rankTwo_of_pair_products μ A hA)
  have he (x : Fin m → X) : (fun i ↦ rankTwoEntry A (x i)) =
      (fun i p q ↦ A (x i) p 0 * A (x i) q 1 - A (x i) p 1 * A (x i) q 0) := rfl
  simp_rw [he,coeff_pure_wedges] at h
  exact h.trans (congrArg (fun c : ℂ ↦ (m.factorial : ℂ)*c)
    (coeff_univariatePfaffian_zero_base (Matrix.of (fun p q ↦ ∫ x, rankTwoEntry A x p q ∂μ))))

end Paper.SkewOrthogonal
