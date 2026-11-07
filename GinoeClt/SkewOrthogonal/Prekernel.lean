/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.GramNormalization

/-! # Finite tau-zero prekernel identities

The polynomials and norms are those of Forrester–Nagao, arXiv:0806.0055v1,
Corollary 2, (4.41)–(4.42). Their even prekernel is (5.5), from (4.8).
The odd correction uses the actual border-adjusted polynomials of Mays,
arXiv:1202.1218v1, Definition 4.26. No ensemble identity is asserted here.
-/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace Paper.SkewOrthogonal

/-- The source paired polynomial numerator, before its nonzero skew norm. -/
def prekernelNumerator (j : ℕ) (z w : ℂ) : ℂ :=
  (evenPolynomial j).eval z * (oddPolynomial j).eval w -
    (oddPolynomial j).eval z * (evenPolynomial j).eval w

/-- The actual finite paired prekernel, without the scalar weight factors. -/
def pairedPrekernel (m : ℕ) (z w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m, prekernelNumerator j z w / skewNorm j

@[simp] theorem prekernelNumerator_zero (z w : ℂ) :
    prekernelNumerator 0 z w = w - z := by
  simp [prekernelNumerator, evenPolynomial, oddPolynomial_eq]

theorem prekernelNumerator_succ (j : ℕ) (z w : ℂ) :
    prekernelNumerator (j + 1) z w = (w - z) *
      ((z * w) ^ (2 * j + 2) + ((2 * j + 2 : ℕ) : ℂ) * (z * w) ^ (2 * j + 1)) := by
  have h₁ : 2 * (j + 1) = 2 * j + 2 := by omega
  have h₂ : 2 * j + 2 - 1 = 2 * j + 1 := by omega
  simp only [prekernelNumerator, oddPolynomial_eq, evenPolynomial,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X_pow, h₁, h₂]
  simp only [pow_succ, mul_pow]
  ring

/-- The fixed nonzero source denominator. -/
def prekernelConstant : ℂ := ((2 * Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

theorem prekernelConstant_ne_zero : prekernelConstant ≠ 0 := by
  simpa [skewNorm, prekernelConstant] using skewNorm_ne_zero 0

theorem prekernel_term_zero (z w : ℂ) :
    prekernelNumerator 0 z w / skewNorm 0 = (w - z) / prekernelConstant := by
  simp [skewNorm, prekernelConstant]

theorem prekernel_term_succ (j : ℕ) (z w : ℂ) :
    prekernelNumerator (j + 1) z w / skewNorm (j + 1) =
      (w - z) / prekernelConstant *
        ((z * w) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ) +
          (z * w) ^ (2 * j + 2) / ((2 * j + 2).factorial : ℂ)) := by
  rw [prekernelNumerator_succ]
  have h₁ : 2 * (j + 1) = 2 * j + 2 := by omega
  have h₂ : (2 * j + 2).factorial = (2 * j + 2) * (2 * j + 1).factorial := by
    simpa only [show 2 * j + 2 = (2 * j + 1) + 1 by omega] using
      Nat.factorial_succ (2 * j + 1)
  change (w - z) * _ / (prekernelConstant * ((2 * (j + 1)).factorial : ℂ)) = _
  rw [h₁, h₂, Nat.cast_mul]
  have hf : ((2 * j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * j + 1)
  have hn : ((2 * j + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 2 ≠ 0)
  field_simp [prekernelConstant_ne_zero, hf, hn]
  ring

/-- Even size, in a successor-indexed form that avoids truncated subtraction. -/
theorem pairedPrekernel_succ (m : ℕ) (z w : ℂ) :
    pairedPrekernel (m + 1) z w = (w - z) / prekernelConstant *
      ∑ k ∈ Finset.range (2 * m + 1), (z * w) ^ k / (k.factorial : ℂ) := by
  induction m with
  | zero => simp [pairedPrekernel, skewNorm, prekernelConstant]
  | succ m ih =>
    rw [pairedPrekernel, Finset.sum_range_succ]
    change pairedPrekernel (m + 1) z w + _ = _
    rw [ih, prekernel_term_succ]
    have h : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
    have hs : (∑ k ∈ Finset.range (2 * (m + 1) + 1),
        (z * w) ^ k / (k.factorial : ℂ)) =
        (∑ k ∈ Finset.range (2 * m + 1), (z * w) ^ k / (k.factorial : ℂ)) +
          (z * w) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ) +
          (z * w) ^ (2 * m + 2) / ((2 * m + 2).factorial : ℂ) := by
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hs]
    ring

/-- The source even-size truncation includes exactly powers zero through N-2. -/
theorem pairedPrekernel_eq (m : ℕ) (z w : ℂ) :
    pairedPrekernel m z w = (w - z) / prekernelConstant *
      ∑ k ∈ Finset.range (2 * m - 1), (z * w) ^ k / (k.factorial : ℂ) := by
  cases m with
  | zero => simp [pairedPrekernel]
  | succ m => simpa only [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] using
      pairedPrekernel_succ m z w

theorem even_factorial_split (j : ℕ) :
    (2 * j).factorial = (2 * j).doubleFactorial * (2 * j - 1).doubleFactorial := by
  cases j with
  | zero => simp [Nat.doubleFactorial]
  | succ j => simpa only [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      show 2 * j + 1 + 1 - 1 = 2 * j + 1 by omega] using
        Nat.factorial_eq_mul_doubleFactorial (2 * j + 1)

/-- The exact border-to-skew-norm ratio, including the zeroth moment. -/
theorem realBorder_div_skewNorm (j : ℕ) :
    realBorder (evenPolynomial j) / skewNorm j =
      1 / (2 * ((2 * j).doubleFactorial : ℂ)) := by
  rw [realBorder_even, skewNorm, even_factorial_split]
  push_cast
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'
  have hd : ((2 * j).doubleFactorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * j)).ne'
  have ho : ((2 * j - 1).doubleFactorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * j - 1)).ne'
  field_simp [hs, hd, ho]

/-- A single term of the odd-polynomial telescoping sum. -/
theorem odd_doubleFactorial_term (j : ℕ) (t : ℂ) :
    (oddPolynomial (j + 1)).eval t / ((2 * (j + 1)).doubleFactorial : ℂ) =
      t ^ (2 * j + 3) / ((2 * j + 2).doubleFactorial : ℂ) -
        t ^ (2 * j + 1) / ((2 * j).doubleFactorial : ℂ) := by
  have h₁ : 2 * (j + 1) = 2 * j + 2 := by omega
  have h₂ : 2 * j + 2 - 1 = 2 * j + 1 := by omega
  simp only [oddPolynomial_eq, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X_pow, h₁, h₂]
  have h₃ : 2 * j + 2 + 1 = 2 * j + 3 := by omega
  rw [h₃, Nat.doubleFactorial_add_two]
  push_cast
  have hd : ((2 * j).doubleFactorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * j)).ne'
  have hn : ((2 * j + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 2 ≠ 0)
  field_simp [hd, hn]

/-- The actual odd-polynomial sum telescopes to one endpoint. -/
theorem sum_odd_doubleFactorial (m : ℕ) (t : ℂ) :
    (∑ j ∈ Finset.range (m + 1),
      (oddPolynomial j).eval t / ((2 * j).doubleFactorial : ℂ)) =
        t ^ (2 * m + 1) / ((2 * m).doubleFactorial : ℂ) := by
  induction m with
  | zero => simp [oddPolynomial_eq, Nat.doubleFactorial]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, odd_doubleFactorial_term]
    have h₁ : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    have h₂ : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [h₁, h₂]
    ring

/-- The odd-size paired sum uses the actual border adjustment; its final
unchanged even polynomial is the radical and does not appear as a paired feature. -/
def oddPrekernel (m : ℕ) (z w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range m,
    ((adjustBorder (evenPolynomial m) (evenPolynomial j)).eval z * (oddPolynomial j).eval w -
      (oddPolynomial j).eval z * (adjustBorder (evenPolynomial m) (evenPolynomial j)).eval w) /
        skewNorm j

/-- Expansion of the genuine odd basis change, before evaluating its endpoint. -/
theorem oddPrekernel_expand (m : ℕ) (z w : ℂ) :
    oddPrekernel m z w = pairedPrekernel m z w +
      (w ^ (2 * m) * (∑ j ∈ Finset.range m,
        realBorder (evenPolynomial j) / skewNorm j * (oddPolynomial j).eval z) -
       z ^ (2 * m) * (∑ j ∈ Finset.range m,
        realBorder (evenPolynomial j) / skewNorm j * (oddPolynomial j).eval w)) /
          realBorder (evenPolynomial m) := by
  have hterm (j : ℕ) :
      ((adjustBorder (evenPolynomial m) (evenPolynomial j)).eval z * (oddPolynomial j).eval w -
        (oddPolynomial j).eval z * (adjustBorder (evenPolynomial m) (evenPolynomial j)).eval w) /
          skewNorm j = prekernelNumerator j z w / skewNorm j +
          (w ^ (2 * m) * (realBorder (evenPolynomial j) / skewNorm j * (oddPolynomial j).eval z) -
            z ^ (2 * m) * (realBorder (evenPolynomial j) / skewNorm j * (oddPolynomial j).eval w)) /
              realBorder (evenPolynomial m) := by
    simp only [adjustBorder, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, prekernelNumerator]
    have he (t : ℂ) : (evenPolynomial m).eval t = t ^ (2 * m) := by
      simp [evenPolynomial]
    rw [he z, he w]
    field_simp [skewNorm_ne_zero, realBorder_even_ne_zero]
    ring
  simp only [oddPrekernel, hterm, Finset.sum_add_distrib, pairedPrekernel]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The weighted odd-polynomial endpoint uses only actual Gaussian border moments. -/
theorem sum_border_odd_succ (m : ℕ) (t : ℂ) :
    (∑ j ∈ Finset.range (m + 1),
      realBorder (evenPolynomial j) / skewNorm j * (oddPolynomial j).eval t) =
        t ^ (2 * m + 1) / (2 * ((2 * m).doubleFactorial : ℂ)) := by
  simp_rw [realBorder_div_skewNorm]
  calc
    _ = (∑ j ∈ Finset.range (m + 1),
      (oddPolynomial j).eval t / ((2 * j).doubleFactorial : ℂ)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [sum_odd_doubleFactorial]; ring

theorem odd_endpoint_correction (m : ℕ) (z w : ℂ) :
    (w ^ (2 * (m + 1)) * (z ^ (2 * m + 1) / (2 * ((2 * m).doubleFactorial : ℂ))) -
      z ^ (2 * (m + 1)) * (w ^ (2 * m + 1) / (2 * ((2 * m).doubleFactorial : ℂ)))) /
        realBorder (evenPolynomial (m + 1)) =
      (w - z) / prekernelConstant *
        ((z * w) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)) := by
  have h₁ : 2 * (m + 1) = 2 * m + 2 := by omega
  have h₂ : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [realBorder_even, h₂, Nat.factorial_eq_mul_doubleFactorial (2 * m)]
  unfold prekernelConstant
  push_cast
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'
  have hd : ((2 * m).doubleFactorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * m)).ne'
  have ho : ((2 * m + 1).doubleFactorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * m + 1)).ne'
  field_simp [hs, hd, ho]
  rw [h₁]
  simp only [pow_succ, mul_pow]
  ring

/-- Odd size, with the exact extra endpoint produced by the Gaussian border. -/
theorem oddPrekernel_succ (m : ℕ) (z w : ℂ) :
    oddPrekernel (m + 1) z w = (w - z) / prekernelConstant *
      ∑ k ∈ Finset.range (2 * m + 2), (z * w) ^ k / (k.factorial : ℂ) := by
  rw [oddPrekernel_expand, pairedPrekernel_succ, sum_border_odd_succ,
    sum_border_odd_succ, odd_endpoint_correction]
  have hs : (∑ k ∈ Finset.range (2 * m + 2), (z * w) ^ k / (k.factorial : ℂ)) =
      (∑ k ∈ Finset.range (2 * m + 1), (z * w) ^ k / (k.factorial : ℂ)) +
        (z * w) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ) := by
    exact Finset.sum_range_succ _ _
  rw [hs]
  ring

/-- The odd-size truncation also includes exactly powers zero through N-2. -/
theorem oddPrekernel_eq (m : ℕ) (z w : ℂ) :
    oddPrekernel m z w = (w - z) / prekernelConstant *
      ∑ k ∈ Finset.range (2 * m), (z * w) ^ k / (k.factorial : ℂ) := by
  cases m with
  | zero => simp [oddPrekernel]
  | succ m => simpa only [show 2 * (m + 1) = 2 * m + 2 by omega] using
      oddPrekernel_succ m z w

/-- The range sum is exactly the sum of the already defined source paired features. -/
theorem pairedPrekernel_eq_basis_sum (m : ℕ) (z w : ℂ) :
    pairedPrekernel m z w = ∑ i : Fin m,
      ((pairedPolynomial m (i, 0)).eval z * (pairedPolynomial m (i, 1)).eval w -
        (pairedPolynomial m (i, 1)).eval z * (pairedPolynomial m (i, 0)).eval w) /
          skewNorm i.val := by
  simp only [pairedPolynomial, ↓reduceIte]
  exact (Fin.sum_univ_eq_sum_range
    (fun j ↦ prekernelNumerator j z w / skewNorm j) m).symm

/-- The odd range sum agrees with the previously reviewed, genuinely adjusted basis. -/
theorem oddPrekernel_eq_basis_sum (m : ℕ) (z w : ℂ) :
    oddPrekernel m z w = ∑ i : Fin m,
      ((oddBasisPolynomial m (some (i, 0))).eval z *
          (oddBasisPolynomial m (some (i, 1))).eval w -
        (oddBasisPolynomial m (some (i, 1))).eval z *
          (oddBasisPolynomial m (some (i, 0))).eval w) / skewNorm i.val := by
  simp only [oddBasisPolynomial_odd]
  change oddPrekernel m z w = ∑ i : Fin m,
    ((adjustBorder (evenPolynomial m) (evenPolynomial i.val)).eval z * (oddPolynomial i.val).eval w -
      (oddPolynomial i.val).eval z * (adjustBorder (evenPolynomial m) (evenPolynomial i.val)).eval w) /
        skewNorm i.val
  exact (Fin.sum_univ_eq_sum_range _ m).symm

end Paper.SkewOrthogonal
