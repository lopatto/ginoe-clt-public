/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.FeatureTransport

/-! # Finite atomic complex-pair updates of the actual odd Gram matrix

The update is the literal complex part of the source skew form: each atom has
coefficient 2i W(z) times the evaluation wedge. Mays, arXiv:1202.1218v1,
(148), Definition 4.26 and Proposition 4.27 give the conventions. This module
proves a finite matrix identity, not an ensemble or generating law.
-/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace Paper.SkewOrthogonal

/-- The literal raw odd source moment matrix with finitely many complex-pair atoms. -/
def rawOddAtomicGram {ι : Type*} (m : ℕ) (s : Finset ι) (c : ι → ℂ) (z : ι → ℂ) :
    Matrix (PairedIndex (m + 1)) (PairedIndex (m + 1)) ℂ :=
  rawOddAugmentedGram m + ∑ x ∈ s,
    (c x * (2 * Complex.I) * (complexWeight (z x) : ℂ)) •
      (Matrix.vecMulVec (rawOddEvaluation m (z x)) (rawOddEvaluation m (conj (z x))) -
        Matrix.vecMulVec (rawOddEvaluation m (conj (z x))) (rawOddEvaluation m (z x)))

/-- The same source moment update in the actual border-adjusted polynomial basis. -/
def adjustedOddAtomicGram {ι : Type*} (m : ℕ) (s : Finset ι) (c : ι → ℂ) (z : ι → ℂ) :
    Matrix (PairedIndex (m + 1)) (PairedIndex (m + 1)) ℂ :=
  oddAugmentedGram m + ∑ x ∈ s,
    (c x * (2 * Complex.I) * (complexWeight (z x) : ℂ)) •
      (Matrix.vecMulVec (adjustedOddEvaluation m (z x)) (adjustedOddEvaluation m (conj (z x))) -
        Matrix.vecMulVec (adjustedOddEvaluation m (conj (z x))) (adjustedOddEvaluation m (z x)))

/-- Congruence of a rank-two evaluation wedge. -/
theorem matrix_evaluation_wedge_congruence {κ : Type*} [Fintype κ]
    (B : Matrix κ κ ℂ) (u v : κ → ℂ) :
    B * (Matrix.vecMulVec u v - Matrix.vecMulVec v u) * B.transpose =
      Matrix.vecMulVec (B *ᵥ u) (B *ᵥ v) - Matrix.vecMulVec (B *ᵥ v) (B *ᵥ u) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- The SAME fixed row matrix carries all finite weighted updates correctly.
No assumption that the final even polynomial remains a weighted radical occurs. -/
theorem oddRowBasis_atomic_congruence {ι : Type*}
    (m : ℕ) (s : Finset ι) (c : ι → ℂ) (z : ι → ℂ) :
    oddRowBasis m * rawOddAtomicGram m s c z * (oddRowBasis m).transpose =
      adjustedOddAtomicGram m s c z := by
  unfold rawOddAtomicGram adjustedOddAtomicGram
  rw [Matrix.mul_add, Matrix.add_mul, oddRowBasis_congruence]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Matrix.mul_smul, Matrix.smul_mul, matrix_evaluation_wedge_congruence,
    oddRowBasis_mulVec_evaluation, oddRowBasis_mulVec_evaluation]

theorem rawOddAtomicGram_skew {ι : Type*}
    (m : ℕ) (s : Finset ι) (c : ι → ℂ) (z : ι → ℂ)
    (p q : PairedIndex (m + 1)) :
    rawOddAtomicGram m s c z q p = -rawOddAtomicGram m s c z p q := by
  have hb : rawOddAugmentedGram m q p = -rawOddAugmentedGram m p q :=
    borderedGram_skew m (pairedPolynomial m) (evenPolynomial m) p q
  simp only [rawOddAtomicGram, Matrix.add_apply, Matrix.sum_apply]
  rw [hb, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  change (c x * (2 * Complex.I) * (complexWeight (z x) : ℂ)) *
    (rawOddEvaluation m (z x) q * rawOddEvaluation m (conj (z x)) p -
      rawOddEvaluation m (conj (z x)) q * rawOddEvaluation m (z x) p) =
    -((c x * (2 * Complex.I) * (complexWeight (z x) : ℂ)) *
      (rawOddEvaluation m (z x) p * rawOddEvaluation m (conj (z x)) q -
        rawOddEvaluation m (conj (z x)) p * rawOddEvaluation m (z x) q))
  ring

/-- The actual finite perturbed raw and adjusted full Pfaffians agree exactly. -/
theorem pfaffian_rawOddAtomicGram_eq {ι : Type*}
    (m : ℕ) (s : Finset ι) (c : ι → ℂ) (z : ι → ℂ) :
    pfaffian (rawOddAtomicGram m s c z) = pfaffian (adjustedOddAtomicGram m s c z) := by
  have h := pfaffian_congruence (rawOddAtomicGram m s c z) (oddRowBasis m)
    (rawOddAtomicGram_skew m s c z)
  rw [oddRowBasis_atomic_congruence, oddRowBasis_det, one_mul] at h
  exact h.symm

/-- Genuine finite update ratios: both constant denominators are already proved nonzero. -/
theorem pfaffian_rawOddAtomicGram_ratio {ι : Type*}
    (m : ℕ) (s : Finset ι) (c : ι → ℂ) (z : ι → ℂ) :
    pfaffian (rawOddAtomicGram m s c z) / pfaffian (rawOddAugmentedGram m) =
      pfaffian (adjustedOddAtomicGram m s c z) / pfaffian (oddAugmentedGram m) := by
  rw [pfaffian_rawOddAtomicGram_eq, pfaffian_rawOddAugmentedGram_eq]

/-- The actual upper-half-plane skew weight is exactly the reflected source weight product. -/
theorem complexWeight_eq_polynomialWeight_product (z : ℂ) (hz : 0 ≤ z.im) :
    (complexWeight z : ℂ) = polynomialWeight z * polynomialWeight (conj z) := by
  rw [polynomialWeight_mul]
  have hs : z ^ 2 + (conj z) ^ 2 = ((2 * (z ^ 2).re : ℝ) : ℂ) := by
    rw [← map_pow]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
      ring
    · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im]
      ring
  rw [hs]
  have he : -((2 * (z ^ 2).re : ℝ) : ℂ) / 2 = ((-(z ^ 2).re : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp]
  simp only [Complex.conj_im, abs_neg, abs_of_nonneg hz]
  rw [Real.sqrt_mul_self (Kernel.erfc_nonneg _)]
  simp only [complexWeight, Complex.ofReal_mul]

end Paper.SkewOrthogonal
