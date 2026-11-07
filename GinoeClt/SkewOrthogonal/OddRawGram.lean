/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.GramNormalization
public import GinoeClt.Algebra.PfaffianAgreement

/-! # The determinant-one bridge from the unmodified odd bordered Gram matrix -/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace Paper.SkewOrthogonal

/-- Split off the last actual interlaced pair, without changing the order inside a pair. -/
def splitLastPair (m : ℕ) : PairedIndex (m + 1) ≃ PairedIndex m ⊕ Fin 2 where
  toFun p := Fin.lastCases (Sum.inr p.2) (fun i : Fin m ↦ Sum.inl (i, p.2)) p.1
  invFun p := match p with
    | Sum.inl p => (p.1.castSucc, p.2)
    | Sum.inr a => (Fin.last m, a)
  left_inv p := by
    rcases p with ⟨i, a⟩
    induction i using Fin.lastCases <;> simp
  right_inv p := by
    rcases p with ⟨i, a⟩ | a <;> simp

@[simp] theorem splitLastPair_symm_inl (m : ℕ) (p : PairedIndex m) :
    (splitLastPair m).symm (Sum.inl p) = (p.1.castSucc, p.2) := rfl
@[simp] theorem splitLastPair_symm_inr (m : ℕ) (a : Fin 2) :
    (splitLastPair m).symm (Sum.inr a) = (Fin.last m, a) := rfl

/-- Extend an actual paired polynomial family by its final polynomial. -/
def extendedPolynomial (m : ℕ) (F : PairedIndex m → Polynomial ℂ) (L : Polynomial ℂ)
    (p : PairedIndex (m + 1)) : Polynomial ℂ :=
  Fin.lastCases L (fun j : Fin m ↦ F (j, p.2)) p.1

/-- The bordered Gram construction uses actual skew integrals and Gaussian moments. -/
def borderedGram (m : ℕ) (F : PairedIndex m → Polynomial ℂ) (L : Polynomial ℂ) :
    Matrix (PairedIndex (m + 1)) (PairedIndex (m + 1)) ℂ :=
  fun p q ↦ if isBorderIndex m p then
      if isBorderIndex m q then 0 else -realBorder (extendedPolynomial m F L q)
    else if isBorderIndex m q then realBorder (extendedPolynomial m F L p)
    else skewForm (extendedPolynomial m F L p) (extendedPolynomial m F L q)

/-- The unmodified source paired family, with its unchanged last even polynomial and border. -/
def rawOddAugmentedGram (m : ℕ) : Matrix (PairedIndex (m + 1)) (PairedIndex (m + 1)) ℂ :=
  borderedGram m (pairedPolynomial m) (evenPolynomial m)

def borderUpper {ι : Type*} (u : ι → ℂ) : Matrix ι (Fin 2) ℂ :=
  fun p a ↦ if a = 0 then 0 else u p

def borderLower {ι : Type*} (u : ι → ℂ) : Matrix (Fin 2) ι ℂ :=
  fun a p ↦ if a = 0 then 0 else -u p

def lastBorderBlock (d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b ↦ if a = 0 then (if b = 1 then d else 0) else (if b = 0 then -d else 0)

/-- Exact block entries follow from the proved radical property, not a presumed normal form. -/
theorem borderedGram_reindex (m : ℕ) (F : PairedIndex m → Polynomial ℂ) (L : Polynomial ℂ)
    (hLF : ∀ p, skewForm L (F p) = 0) :
    (borderedGram m F L).submatrix (splitLastPair m).symm (splitLastPair m).symm =
      Matrix.fromBlocks (fun p q ↦ skewForm (F p) (F q))
        (borderUpper (fun p ↦ realBorder (F p)))
        (borderLower (fun p ↦ realBorder (F p))) (lastBorderBlock (realBorder L)) := by
  have hFL (p : PairedIndex m) : skewForm (F p) L = 0 := by
    rw [skewForm_antisymm L (F p), hLF, neg_zero]
  ext p q
  rcases p with p | a <;> rcases q with q | b
  · simp [Matrix.fromBlocks, Matrix.submatrix_apply, borderedGram, isBorderIndex, extendedPolynomial]
  · fin_cases b <;> simp [Matrix.fromBlocks, Matrix.submatrix_apply, borderedGram, isBorderIndex,
      extendedPolynomial, borderUpper, hFL]
  · fin_cases a <;> simp [Matrix.fromBlocks, Matrix.submatrix_apply, borderedGram, isBorderIndex,
      extendedPolynomial, borderLower, hLF]
  · fin_cases a <;> fin_cases b <;> simp [Matrix.fromBlocks, Matrix.submatrix_apply, borderedGram,
      isBorderIndex, extendedPolynomial, lastBorderBlock, skewForm_self]

/-- Coefficients subtracting only the final polynomial, never the border row. -/
def borderAdjustment {ι : Type*} (u : ι → ℂ) (d : ℂ) : Matrix ι (Fin 2) ℂ :=
  fun p a ↦ if a = 0 then -(u p / d) else 0

/-- This is a ROW basis transformation: its congruence is B M B^T. -/
def rowBasisBlock (m : ℕ) (u : PairedIndex m → ℂ) (d : ℂ) :
    Matrix (PairedIndex m ⊕ Fin 2) (PairedIndex m ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks 1 (borderAdjustment u d) 0 1

def oddRowBasis (m : ℕ) : Matrix (PairedIndex (m + 1)) (PairedIndex (m + 1)) ℂ :=
  (rowBasisBlock m (fun p ↦ realBorder (pairedPolynomial m p))
    (realBorder (evenPolynomial m))).submatrix (splitLastPair m) (splitLastPair m)

theorem rowBasisBlock_det (m : ℕ) (u : PairedIndex m → ℂ) (d : ℂ) :
    (rowBasisBlock m u d).det = 1 := by
  rw [rowBasisBlock, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem oddRowBasis_det (m : ℕ) : (oddRowBasis m).det = 1 := by
  rw [oddRowBasis, Matrix.det_submatrix_equiv_self, rowBasisBlock_det]

/-- Elementary elimination of the actual border vector by a determinant-one row matrix. -/
theorem rowBasisBlock_congruence (m : ℕ)
    (A : Matrix (PairedIndex m) (PairedIndex m) ℂ) (u : PairedIndex m → ℂ)
    (d : ℂ) (hd : d ≠ 0) :
    rowBasisBlock m u d *
        Matrix.fromBlocks A (borderUpper u) (borderLower u) (lastBorderBlock d) *
          (rowBasisBlock m u d).transpose = Matrix.fromBlocks A 0 0 (lastBorderBlock d) := by
  have hc₁ (p : PairedIndex m) : (-(u p / d)) * d = -u p := by
    rw [neg_mul, div_mul_cancel₀ _ hd]
  have hc₂ (p : PairedIndex m) : d * (u p / d) = u p := by
    rw [mul_comm, div_mul_cancel₀ _ hd]
  have hKL : borderAdjustment u d * borderLower u = 0 := by
    ext p q
    simp [Matrix.mul_apply, Fin.sum_univ_two, borderAdjustment, borderLower]
  have hKD : borderUpper u + borderAdjustment u d * lastBorderBlock d = 0 := by
    ext p a
    fin_cases a <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, borderUpper, borderAdjustment,
        lastBorderBlock, hc₁]
  have hDK : borderLower u + lastBorderBlock d * (borderAdjustment u d).transpose = 0 := by
    ext a p
    fin_cases a <;>
      simp [Matrix.mul_apply, borderLower, borderAdjustment, lastBorderBlock, hc₂]
  have hleft : rowBasisBlock m u d *
      Matrix.fromBlocks A (borderUpper u) (borderLower u) (lastBorderBlock d) =
      Matrix.fromBlocks A 0 (borderLower u) (lastBorderBlock d) := by
    rw [rowBasisBlock, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.zero_mul, zero_add]
    rw [hKL, hKD, add_zero]
  rw [hleft, rowBasisBlock, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  rw [hDK]

theorem rawOddAugmentedGram_reindex (m : ℕ) :
    (rawOddAugmentedGram m).submatrix (splitLastPair m).symm (splitLastPair m).symm =
      Matrix.fromBlocks (pairedGram m)
        (borderUpper (fun p ↦ realBorder (pairedPolynomial m p)))
        (borderLower (fun p ↦ realBorder (pairedPolynomial m p)))
        (lastBorderBlock (realBorder (evenPolynomial m))) :=
  borderedGram_reindex m (pairedPolynomial m) (evenPolynomial m) (lastEven_radical m)

theorem oddAugmentedGram_eq_bordered (m : ℕ) :
    oddAugmentedGram m = borderedGram m
      (fun p ↦ adjustBorder (evenPolynomial m) (pairedPolynomial m p)) (evenPolynomial m) := rfl

theorem oddAugmentedGram_reindex (m : ℕ) :
    (oddAugmentedGram m).submatrix (splitLastPair m).symm (splitLastPair m).symm =
      Matrix.fromBlocks (pairedGram m) 0 0 (lastBorderBlock (realBorder (evenPolynomial m))) := by
  let F : PairedIndex m → Polynomial ℂ := fun p ↦
    adjustBorder (evenPolynomial m) (pairedPolynomial m p)
  have hr (p : PairedIndex m) : skewForm (evenPolynomial m) (F p) = 0 :=
    lastEven_modified_zero m p
  have h := borderedGram_reindex m F (evenPolynomial m) hr
  have htop : (fun p q ↦ skewForm (F p) (F q)) = pairedGram m := by
    ext p q
    exact skewForm_adjustBorder _ _ _ (lastEven_radical m p) (lastEven_radical m q)
  have hb : (fun p ↦ realBorder (F p)) = 0 := by
    funext p
    exact realBorder_adjustBorder _ _ (realBorder_even_ne_zero m)
  rw [htop, hb] at h
  have hu : borderUpper (0 : PairedIndex m → ℂ) = 0 := by ext p a; simp [borderUpper]
  have hl : borderLower (0 : PairedIndex m → ℂ) = 0 := by ext a p; simp [borderLower]
  rw [hu, hl] at h
  rw [oddAugmentedGram_eq_bordered]
  simpa only [F] using h

/-- The actual row basis matrix carries the unmodified Gram matrix to the adjusted one. -/
theorem oddRowBasis_congruence (m : ℕ) :
    oddRowBasis m * rawOddAugmentedGram m * (oddRowBasis m).transpose = oddAugmentedGram m := by
  let e := splitLastPair m
  let u : PairedIndex m → ℂ := fun p ↦ realBorder (pairedPolynomial m p)
  let d := realBorder (evenPolynomial m)
  have hB : (oddRowBasis m).submatrix e.symm e.symm = rowBasisBlock m u d := by
    ext p q
    simp [oddRowBasis, Matrix.submatrix_apply, e, u, d]
  have hBT : (oddRowBasis m).transpose.submatrix e.symm e.symm =
      (rowBasisBlock m u d).transpose := by
    ext p q
    exact congrArg (fun A ↦ A q p) hB
  have hcomp : (oddRowBasis m * rawOddAugmentedGram m * (oddRowBasis m).transpose).submatrix
      e.symm e.symm = (oddAugmentedGram m).submatrix e.symm e.symm := by
    rw [← Matrix.submatrix_mul_equiv (oddRowBasis m * rawOddAugmentedGram m)
      (oddRowBasis m).transpose e.symm e.symm e.symm,
      ← Matrix.submatrix_mul_equiv (oddRowBasis m) (rawOddAugmentedGram m) e.symm e.symm e.symm,
      hB, hBT, rawOddAugmentedGram_reindex, oddAugmentedGram_reindex]
    exact rowBasisBlock_congruence m (pairedGram m) u d (realBorder_even_ne_zero m)
  ext p q
  have h := congrArg (fun A ↦ A (e p) (e q)) hcomp
  simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply] using h

theorem borderedGram_skew (m : ℕ) (F : PairedIndex m → Polynomial ℂ) (L : Polynomial ℂ)
    (p q : PairedIndex (m + 1)) : borderedGram m F L q p = -borderedGram m F L p q := by
  unfold borderedGram
  by_cases hp : isBorderIndex m p
  · by_cases hq : isBorderIndex m q <;> simp [hp, hq]
  · by_cases hq : isBorderIndex m q
    · simp [hp, hq]
    · simp only [hp, hq, ite_false]
      exact skewForm_antisymm _ _

/-- Determinant-one row congruence preserves the frozen full Pfaffian exactly. -/
theorem pfaffian_rawOddAugmentedGram_eq (m : ℕ) :
    pfaffian (rawOddAugmentedGram m) = pfaffian (oddAugmentedGram m) := by
  have h := pfaffian_congruence (rawOddAugmentedGram m) (oddRowBasis m)
    (borderedGram_skew m (pairedPolynomial m) (evenPolynomial m))
  rw [oddRowBasis_congruence, oddRowBasis_det, one_mul] at h
  exact h.symm

/-- The unmodified odd bordered Gaussian moment matrix has the source normalization. -/
theorem pfaffian_rawOddAugmentedGram (m : ℕ) :
    pfaffian (rawOddAugmentedGram m) =
      realBorder (evenPolynomial m) * ∏ i : Fin m, skewNorm i.val := by
  rw [pfaffian_rawOddAugmentedGram_eq, pfaffian_oddAugmentedGram]

theorem pfaffian_rawOddAugmentedGram_ne_zero (m : ℕ) :
    pfaffian (rawOddAugmentedGram m) ≠ 0 := by
  rw [pfaffian_rawOddAugmentedGram_eq]
  exact pfaffian_oddAugmentedGram_ne_zero m

end Paper.SkewOrthogonal
