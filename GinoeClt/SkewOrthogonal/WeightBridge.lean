/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.Prekernel
public import GinoeClt.Kernel.Definitions

/-! # Exact source polynomial weights and the frozen raw finite-N kernels

The weight and complex-kernel convention are Mays, arXiv:1202.1218v1,
Definition 4.16, (169), and Definition 4.26. The arguments here are raw complex
coordinates. Square-root matrix scaling and its product-area Jacobian remain
separate, as in `Kernel.rescale` and `Kernel.Scaling`.
-/
@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Paper.SkewOrthogonal

/-- The source polynomial weight uses the absolute imaginary part, including
when the polynomial argument is reflected to the lower half-plane. -/
def polynomialWeight (z : ℂ) : ℂ :=
  Complex.exp (-z ^ 2 / 2) *
    (Real.sqrt (Kernel.erfc (Real.sqrt 2 * |z.im|)) : ℂ)

/-- The source finite prekernel with the common all-parity cutoff. -/
def finitePrekernel (N : ℕ) (z w : ℂ) : ℂ :=
  (w - z) / prekernelConstant *
    ∑ k ∈ Finset.range (N - 1), (z * w) ^ k / (k.factorial : ℂ)

theorem pairedPrekernel_eq_finite (m : ℕ) (z w : ℂ) :
    pairedPrekernel m z w = finitePrekernel (2 * m) z w := pairedPrekernel_eq m z w

theorem oddPrekernel_eq_finite (m : ℕ) (z w : ℂ) :
    oddPrekernel m z w = finitePrekernel (2 * m + 1) z w := by
  simpa only [finitePrekernel, show 2 * m + 1 - 1 = 2 * m by omega] using
    oddPrekernel_eq m z w

theorem polynomialWeight_mul (z w : ℂ) :
    polynomialWeight z * polynomialWeight w =
      Complex.exp (-(z ^ 2 + w ^ 2) / 2) *
        (Real.sqrt (Kernel.erfc (Real.sqrt 2 * |z.im|) *
          Kernel.erfc (Real.sqrt 2 * |w.im|)) : ℂ) := by
  have he : Complex.exp (-z ^ 2 / 2) * Complex.exp (-w ^ 2 / 2) =
      Complex.exp (-(z ^ 2 + w ^ 2) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [polynomialWeight, polynomialWeight]
  calc
    _ = (Complex.exp (-z ^ 2 / 2) * Complex.exp (-w ^ 2 / 2)) *
        ((Real.sqrt (Kernel.erfc (Real.sqrt 2 * |z.im|)) : ℂ) *
          (Real.sqrt (Kernel.erfc (Real.sqrt 2 * |w.im|)) : ℂ)) := by ring
    _ = _ := by
      rw [he, ← Complex.ofReal_mul, ← Real.sqrt_mul (Kernel.erfc_nonneg _)]

/-- The unweighted finite sum and the actual source weight reproduce the exact
Gaussian/truncated-exponential expression at arbitrary complex arguments. -/
theorem weighted_finitePrekernel (N : ℕ) (z w : ℂ) :
    2 * polynomialWeight z * polynomialWeight w * finitePrekernel N z w =
      (1 / (Real.sqrt (2 * Real.pi) : ℂ)) * (w - z) *
        Complex.exp (-(z - w) ^ 2 / 2) *
        (Real.sqrt (Kernel.erfc (Real.sqrt 2 * |z.im|) *
          Kernel.erfc (Real.sqrt 2 * |w.im|)) : ℂ) *
        Kernel.truncatedExponential (N - 1) (z * w) := by
  have he : Complex.exp (-(z - w) ^ 2 / 2) * Complex.exp (-(z * w)) =
      Complex.exp (-(z ^ 2 + w ^ 2) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [show 2 * polynomialWeight z * polynomialWeight w =
      2 * (polynomialWeight z * polynomialWeight w) by ring, polynomialWeight_mul]
  unfold finitePrekernel Kernel.truncatedExponential prekernelConstant
  push_cast
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos)).ne'
  field_simp [hs]
  simp only [neg_div] at he
  rw [← he]
  ring

/-- Exact raw D kernel, with no scaling or Jacobian factor hidden in the weight. -/
theorem weighted_finitePrekernel_D (N : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    2 * polynomialWeight z * polynomialWeight w * finitePrekernel N z w = Kernel.D N z w := by
  simpa only [abs_of_nonneg hz, abs_of_nonneg hw, Kernel.D, Kernel.gaussianAmplitude] using
    weighted_finitePrekernel N z w

/-- Exact raw S kernel; the second polynomial argument is in the lower half-plane. -/
theorem weighted_finitePrekernel_S (N : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    2 * Complex.I * polynomialWeight z * polynomialWeight (conj w) *
      finitePrekernel N z (conj w) = Kernel.S N z w := by
  have h := weighted_finitePrekernel N z (conj w)
  simp only [Complex.conj_im, abs_neg, abs_of_nonneg hz, abs_of_nonneg hw] at h
  rw [show 2 * Complex.I * polynomialWeight z * polynomialWeight (conj w) *
      finitePrekernel N z (conj w) = Complex.I *
        (2 * polynomialWeight z * polynomialWeight (conj w) * finitePrekernel N z (conj w)) by ring,
    h]
  unfold Kernel.S Kernel.gaussianAmplitude
  ring

/-- Exact raw I kernel, retaining its negative sign and both reflected arguments. -/
theorem weighted_finitePrekernel_I (N : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    -2 * polynomialWeight (conj z) * polynomialWeight (conj w) *
      finitePrekernel N (conj z) (conj w) = Kernel.I N z w := by
  have h := weighted_finitePrekernel N (conj z) (conj w)
  simp only [Complex.conj_im, abs_neg, abs_of_nonneg hz, abs_of_nonneg hw] at h
  rw [show -2 * polynomialWeight (conj z) * polynomialWeight (conj w) *
      finitePrekernel N (conj z) (conj w) =
        -(2 * polynomialWeight (conj z) * polynomialWeight (conj w) *
          finitePrekernel N (conj z) (conj w)) by ring, h]
  unfold Kernel.I Kernel.gaussianAmplitude
  ring

/-- The actual even paired source sum reproduces the frozen raw D kernel. -/
theorem weighted_pairedPrekernel_D (m : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    2 * polynomialWeight z * polynomialWeight w * pairedPrekernel m z w = Kernel.D (2 * m) z w := by
  rw [pairedPrekernel_eq_finite]
  exact weighted_finitePrekernel_D _ _ _ hz hw

theorem weighted_pairedPrekernel_S (m : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    2 * Complex.I * polynomialWeight z * polynomialWeight (conj w) *
      pairedPrekernel m z (conj w) = Kernel.S (2 * m) z w := by
  rw [pairedPrekernel_eq_finite]
  exact weighted_finitePrekernel_S _ _ _ hz hw

theorem weighted_pairedPrekernel_I (m : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    -2 * polynomialWeight (conj z) * polynomialWeight (conj w) *
      pairedPrekernel m (conj z) (conj w) = Kernel.I (2 * m) z w := by
  rw [pairedPrekernel_eq_finite]
  exact weighted_finitePrekernel_I _ _ _ hz hw

/-- The actual odd adjusted source sum reproduces the frozen raw D kernel. -/
theorem weighted_oddPrekernel_D (m : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    2 * polynomialWeight z * polynomialWeight w * oddPrekernel m z w = Kernel.D (2 * m + 1) z w := by
  rw [oddPrekernel_eq_finite]
  exact weighted_finitePrekernel_D _ _ _ hz hw

theorem weighted_oddPrekernel_S (m : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    2 * Complex.I * polynomialWeight z * polynomialWeight (conj w) *
      oddPrekernel m z (conj w) = Kernel.S (2 * m + 1) z w := by
  rw [oddPrekernel_eq_finite]
  exact weighted_finitePrekernel_S _ _ _ hz hw

theorem weighted_oddPrekernel_I (m : ℕ) (z w : ℂ)
    (hz : 0 ≤ z.im) (hw : 0 ≤ w.im) :
    -2 * polynomialWeight (conj z) * polynomialWeight (conj w) *
      oddPrekernel m (conj z) (conj w) = Kernel.I (2 * m + 1) z w := by
  rw [oddPrekernel_eq_finite]
  exact weighted_finitePrekernel_I _ _ _ hz hw

end Paper.SkewOrthogonal
