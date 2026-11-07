/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.RawOddBorderSpecialization
public import GinoeClt.SkewOrthogonal.PairedPolynomialDegree
public import GinoeClt.SkewOrthogonal.DeBruijnSourceDeterminant
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal Matrix
namespace Paper.SkewOrthogonal

/-- One transparent total-size cast, retaining the ACTUAL interlaced row/column order. -/
def oddFullColumnEquiv (m : ℕ) : PairedIndex (m+1) ≃ Fin (2*m+2) :=
  (PfaffianMinor.pairColumnEquiv (m+1)).trans (finCongr (by omega))

theorem oddFullColumnEquiv_val (m : ℕ) (p : PairedIndex (m+1)) :
    (oddFullColumnEquiv m p).val = 2*p.1.val+p.2.val := by
  simpa [oddFullColumnEquiv] using pairColumnEquiv_val (m+1) p

@[simp] theorem oddFullColumnEquiv_border (m : ℕ) :
    oddFullColumnEquiv m (Fin.last m,1) = Fin.last (2*m+1) := by
  apply Fin.ext
  rw [oddFullColumnEquiv_val]
  simp

@[simp] theorem oddFullColumnEquiv_first_zero (m : ℕ) :
    oddFullColumnEquiv m (0,0) = 0 := by
  apply Fin.ext
  rw [oddFullColumnEquiv_val]
  simp

@[simp] theorem oddFullColumnEquiv_first_one (m : ℕ) :
    oddFullColumnEquiv m (0,1) = 1 := by
  apply Fin.ext
  rw [oddFullColumnEquiv_val]
  simp

/-- The ordinary degree-ordered family q0,...,q(2m), final even polynomial unchanged. -/
def unborderedOddPolynomial (m : ℕ) : Fin (2*m+1) → Polynomial ℂ :=
  Fin.lastCases (evenPolynomial m)
    (fun i : Fin (2*m) => pairedPolynomial m ((PfaffianMinor.pairColumnEquiv m).symm i))

theorem unborderedOddPolynomial_monic (m : ℕ) (i : Fin (2*m+1)) :
    (unborderedOddPolynomial m i).Monic := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [unborderedOddPolynomial,evenPolynomial]
  · simpa [unborderedOddPolynomial] using pairedPolynomial_fin_monic m j

theorem unborderedOddPolynomial_natDegree (m : ℕ) (i : Fin (2*m+1)) :
    (unborderedOddPolynomial m i).natDegree = i.val := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [unborderedOddPolynomial,evenPolynomial]
  · simpa [unborderedOddPolynomial] using pairedPolynomial_fin_natDegree m j

@[simp] theorem rawOddPolynomial_castSucc (m : ℕ) (p : PairedIndex m) :
    rawOddPolynomial m (p.1.castSucc,p.2) = pairedPolynomial m p := by
  simp [rawOddPolynomial,isBorderIndex,extendedPolynomial]

/-- Deleting the final border row yields EXACTLY the degree-ordered actual family. -/
theorem rawOddPolynomial_unbordered (m : ℕ) (i : Fin (2*m+1)) :
    rawOddPolynomial m ((oddFullColumnEquiv m).symm i.castSucc) = unborderedOddPolynomial m i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : oddFullColumnEquiv m (Fin.last m,0) = (Fin.last (2*m)).castSucc := by
      apply Fin.ext
      rw [oddFullColumnEquiv_val]
      simp
    have hs := (oddFullColumnEquiv m).symm_apply_eq.mpr he.symm
    rw [hs,rawOddPolynomial_last_even]
    simp [unborderedOddPolynomial]
  · let p := (PfaffianMinor.pairColumnEquiv m).symm j
    have he : oddFullColumnEquiv m (p.1.castSucc,p.2) = j.castSucc.castSucc := by
      apply Fin.ext
      rw [oddFullColumnEquiv_val]
      have hp := pairColumnEquiv_val m p
      have hj : PfaffianMinor.pairColumnEquiv m p = j :=
        (PfaffianMinor.pairColumnEquiv m).apply_symm_apply j
      rw [hj] at hp
      exact hp.symm
    have hs := (oddFullColumnEquiv m).symm_apply_eq.mpr he.symm
    rw [hs,rawOddPolynomial_castSucc]
    simp only [unborderedOddPolynomial,Fin.lastCases_castSucc,p]

/-- Unbordered actual polynomial evaluation determinant, including m=0/N=1. -/
theorem det_unborderedOddPolynomial_eval (m : ℕ) (v : Fin (2*m+1) → ℂ) :
    (Matrix.of (fun i j : Fin (2*m+1) => (unborderedOddPolynomial m i).eval (v j))).det =
      (Matrix.vandermonde v).det := by
  rw [← Matrix.det_transpose]
  exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
    (unborderedOddPolynomial m) (unborderedOddPolynomial_natDegree m)
    (unborderedOddPolynomial_monic m)).symm

/-- Expansion at the actual last BORDER row and column ONE has sign +1.
Deleting column one leaves column zero first, then the remaining adjacent pairs. -/
theorem det_odd_last_row_delta_one (m : ℕ) (A : Matrix (Fin (2*m+2)) (Fin (2*m+2)) ℂ)
    (hrow : ∀ j, A (Fin.last (2*m+1)) j = if j = 1 then 1 else 0) :
    A.det = (A.submatrix Fin.castSucc (1 : Fin (2*m+2)).succAbove).det := by
  have hsign : (-1 : ℂ)^(2*m+1+1) = 1 := by
    rw [show 2*m+1+1 = 2*(m+1) by omega,pow_mul]
    norm_num
  rw [Matrix.det_succ_row A (Fin.last (2*m+1))]
  simp only [hrow,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,Fin.succAbove_last,Fin.val_last,Fin.val_one]
  rw [hsign,one_mul]

/-- ACTUAL original feature matrix with one real singleton in the FIRST pair position. -/
def oddFirstSourceMatrix (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (x : ℝ)
    (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) : Matrix (Fin (2*m+2)) (Fin (2*m+2)) ℂ :=
  (pairedFeatureMatrix (fun i : Fin (m+1) =>
    deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
      (Fin.cons (α := fun _ => (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x) (fun j => Sum.inl (s j)) i))).submatrix
        (oddFullColumnEquiv m).symm (oddFullColumnEquiv m).symm

theorem oddFirstSourceMatrix_last_row (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (x : ℝ)
    (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) (j : Fin (2*m+2)) :
    oddFirstSourceMatrix B t m x s (Fin.last (2*m+1)) j = if j = 1 then 1 else 0 := by
  have hb : (oddFullColumnEquiv m).symm (Fin.last (2*m+1)) = (Fin.last m,1) :=
    (oddFullColumnEquiv m).symm_apply_eq.mpr (oddFullColumnEquiv_border m).symm
  have hone (i : Fin (m+1)) (a : Fin 2) :
      oddFullColumnEquiv m (i,a) = 1 ↔ i = 0 ∧ a = 1 := by
    rw [← oddFullColumnEquiv_first_one m]
    simpa only [Prod.mk.injEq] using ((oddFullColumnEquiv m).injective.eq_iff (a := (i,a)) (b := (0,1)))
  obtain ⟨⟨i,a⟩,rfl⟩ := (oddFullColumnEquiv m).surjective j
  simp only [oddFirstSourceMatrix,Matrix.submatrix_apply,hb,Equiv.symm_apply_apply,
    pairedFeatureMatrix]
  simp only [hone]
  refine Fin.cases ?_ (fun k => ?_) i
  · fin_cases a <;>
      simp [deBruijnBorderFeature,singleBorderFeature,rawOddPolynomial_border,realGaussianPolynomial]
  · rw [Fin.cons_succ,deBruijnBorderFeature_pair_border_zero B t (rawOddPolynomial m)
      (Fin.last m,1) (rawOddPolynomial_border m)]
    simp

/-- The FIRST-single ACTUAL paired determinant is its literal last-row/column-one
minor. This proves the cofactor orientation without moving ANY column. -/
theorem det_first_single_border_reduction (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (x : ℝ)
    (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) :
    (pairedFeatureMatrix (fun i : Fin (m+1) =>
      deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
        (Fin.cons (α := fun _ => (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x) (fun j => Sum.inl (s j)) i))).det =
      ((oddFirstSourceMatrix B t m x s).submatrix Fin.castSucc (1 : Fin (2*m+2)).succAbove).det := by
  have hr := Matrix.det_submatrix_equiv_self (oddFullColumnEquiv m).symm
    (pairedFeatureMatrix (fun i : Fin (m+1) =>
      deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
        (Fin.cons (α := fun _ => (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x) (fun j => Sum.inl (s j)) i)))
  exact hr.symm.trans (det_odd_last_row_delta_one m (oddFirstSourceMatrix B t m x s)
    (oddFirstSourceMatrix_last_row B t m x s))

/-- The tail pair coordinates retain their original order after the first singleton. -/
theorem oddFullColumnEquiv_tail (m : ℕ) (i : Fin m) (a : Fin 2) :
    oddFullColumnEquiv m (i.succ,a) = (PfaffianMinor.pairColumnEquiv m (i,a)).succ.succ := by
  apply Fin.ext
  rw [oddFullColumnEquiv_val]
  simp only [Fin.val_succ]
  rw [pairColumnEquiv_val]
  change 2*(i.val+1)+a.val = 2*i.val+a.val+1+1
  omega

theorem oddFullColumnEquiv_symm_tail (m : ℕ) (j : Fin (2*m)) :
    (oddFullColumnEquiv m).symm j.succ.succ =
      (((PfaffianMinor.pairColumnEquiv m).symm j).1.succ,
        ((PfaffianMinor.pairColumnEquiv m).symm j).2) := by
  apply (oddFullColumnEquiv m).injective
  rw [Equiv.apply_symm_apply,oddFullColumnEquiv_tail]
  simp only [Prod.eta,Equiv.apply_symm_apply]

/-- The leftover root vector is genuinely UNPAIRED REAL FIRST, then ordinary pairs. -/
def oddFirstRootVector (m : ℕ) (x : ℝ) (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) : Fin (2*m+1) → ℂ :=
  Fin.cons (x : ℂ) (fun j : Fin (2*m) =>
    let p := (PfaffianMinor.pairColumnEquiv m).symm j
    deBruijnPairRoot (s p.1) p.2)

def oddFirstScalarVector (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (x : ℝ)
    (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) : Fin (2*m+1) → ℂ :=
  Fin.cons (Real.exp (-x^2/2) : ℂ) (fun j : Fin (2*m) =>
    let p := (PfaffianMinor.pairColumnEquiv m).symm j
    deBruijnPairScalar B t (s p.1) p.2)

/-- Every actual cofactor entry is its original scalar times polynomial evaluation.
This checks BOTH the zero column and every remaining pair column explicitly. -/
theorem oddFirstSourceMatrix_minor_eq (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (x : ℝ)
    (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) :
    (oddFirstSourceMatrix B t m x s).submatrix Fin.castSucc (1 : Fin (2*m+2)).succAbove =
      Matrix.of (fun i j : Fin (2*m+1) => oddFirstScalarVector B t m x s j *
        (unborderedOddPolynomial m i).eval (oddFirstRootVector m x s j)) := by
  ext i j
  change oddFirstSourceMatrix B t m x s i.castSucc ((1 : Fin (2*m+2)).succAbove j) = _
  have hrow := rawOddPolynomial_unbordered m i
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Fin.one_succAbove_zero]
    have h0 : (oddFullColumnEquiv m).symm (0 : Fin (2*m+2)) = (0,0) :=
      (oddFullColumnEquiv m).symm_apply_eq.mpr (oddFullColumnEquiv_first_zero m).symm
    change deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
      (Fin.cons (α := fun _ => (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x) (fun j => Sum.inl (s j)) (((oddFullColumnEquiv m).symm 0).1))
      ((oddFullColumnEquiv m).symm i.castSucc) (((oddFullColumnEquiv m).symm 0).2) = _
    rw [h0]
    simp only [Fin.cons_zero,deBruijnBorderFeature,singleBorderFeature,↓reduceIte,
      Sum.elim_inr,Matrix.of_apply,realGaussianPolynomial,hrow,oddFirstScalarVector,oddFirstRootVector,Fin.cons_zero]
  · rw [Fin.one_succAbove_succ]
    change deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
      (Fin.cons (α := fun _ => (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x) (fun j => Sum.inl (s j))
        (((oddFullColumnEquiv m).symm k.succ.succ).1))
      ((oddFullColumnEquiv m).symm i.castSucc) (((oddFullColumnEquiv m).symm k.succ.succ).2) = _
    rw [oddFullColumnEquiv_symm_tail]
    simp only [Fin.cons_succ,deBruijnBorderFeature,oddFirstScalarVector,oddFirstRootVector,
      Fin.cons_succ,Sum.elim_inl,Matrix.of_apply]
    rw [deBruijnPairFeature_factorization,hrow]

/-- Full pointwise FIRST-single determinant formula. Ordinary pair scalar factors
are unchanged; all roots/collisions and m=0/N=1 are included. -/
theorem det_first_single_border_vandermonde (B : Set ℂ) (t : ℝ≥0) (m : ℕ) (x : ℝ)
    (s : Fin m → ((ℝ × ℝ) ⊕ ℂ)) :
    (pairedFeatureMatrix (fun i : Fin (m+1) =>
      deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1)
        (Fin.cons (α := fun _ => (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x) (fun j => Sum.inl (s j)) i))).det =
      (Real.exp (-x^2/2) : ℂ) *
        (∏ i : Fin m, deBruijnPairScalar B t (s i) 0 * deBruijnPairScalar B t (s i) 1) *
        (Matrix.vandermonde (oddFirstRootVector m x s)).det := by
  rw [det_first_single_border_reduction,oddFirstSourceMatrix_minor_eq]
  have hd := Matrix.det_mul_row (oddFirstScalarVector B t m x s)
    (Matrix.of (fun i j : Fin (2*m+1) =>
      (unborderedOddPolynomial m i).eval (oddFirstRootVector m x s j)))
  simp only [Matrix.of_apply] at hd
  rw [hd,det_unborderedOddPolynomial_eval]
  have hp : (∏ j : Fin (2*m),
      let p := (PfaffianMinor.pairColumnEquiv m).symm j
      deBruijnPairScalar B t (s p.1) p.2) =
      ∏ i : Fin m, deBruijnPairScalar B t (s i) 0 * deBruijnPairScalar B t (s i) 1 := by
    rw [← Equiv.prod_comp (PfaffianMinor.pairColumnEquiv m)
      (fun j : Fin (2*m) => let p := (PfaffianMinor.pairColumnEquiv m).symm j
        deBruijnPairScalar B t (s p.1) p.2)]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.prod_prod_type]
    simp [Fin.prod_univ_two]
  simp only [oddFirstScalarVector,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  rw [hp]

end Paper.SkewOrthogonal
