/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.GaussianAmplitude
public import GinoeClt.Lambert.CorrectedTruncation

/-! # Exact leading kernels and their Gaussian moduli -/

@[expose] public section
noncomputable section
open Set
open scoped Real ComplexConjugate

namespace Paper.Kernel

def leadingSExponent (N : ℕ) (z w : ℂ) : ℂ :=
  -(N : ℂ) / 2 * (z - conj w) ^ 2 -
    (N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2)

def leadingDExponent (N : ℕ) (z w : ℂ) : ℂ :=
  -(N : ℂ) / 2 * (z - w) ^ 2 -
    (N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2)

def leadingD (N : ℕ) (z w : ℂ) : ℂ :=
  (w - z) / ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ) *
    Complex.exp (leadingDExponent N z w)

theorem sqrt_natCast_sq (N : ℕ) :
    ((Real.sqrt (N : ℝ) : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N), Complex.ofReal_natCast]

theorem rescale_sub (N : ℕ) (z w : ℂ) :
    rescale N z - rescale N w = (Real.sqrt (N : ℝ) : ℂ) * (z - w) := by
  unfold rescale
  ring

theorem conj_rescale (N : ℕ) (w : ℂ) :
    conj (rescale N w) = (Real.sqrt (N : ℝ) : ℂ) * conj w := by
  simp only [rescale, map_mul, Complex.conj_ofReal]

theorem rescale_sub_conj (N : ℕ) (z w : ℂ) :
    rescale N z - conj (rescale N w) =
      (Real.sqrt (N : ℝ) : ℂ) * (z - conj w) := by
  rw [conj_rescale]
  unfold rescale
  ring

theorem rescale_mul (N : ℕ) (z w : ℂ) :
    rescale N z * rescale N w = (N : ℂ) * (z * w) := by
  unfold rescale
  calc
    _ = ((Real.sqrt (N : ℝ) : ℂ) ^ 2) * (z * w) := by ring
    _ = _ := by rw [sqrt_natCast_sq]

theorem rescale_mul_conj (N : ℕ) (z w : ℂ) :
    rescale N z * conj (rescale N w) = (N : ℂ) * (z * conj w) := by
  rw [conj_rescale]
  unfold rescale
  calc
    _ = ((Real.sqrt (N : ℝ) : ℂ) ^ 2) * (z * conj w) := by ring
    _ = _ := by rw [sqrt_natCast_sq]

theorem sqrt_normalization (N : ℕ) :
    Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi * (N : ℝ)) =
      (2 * Real.pi) * Real.sqrt (N : ℝ) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), ← mul_assoc,
    ← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]

theorem S_rescale_eq_U {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    S N (rescale N z) (rescale N w) =
      U N z w * (1 + (gaussianAmplitudeError N z w : ℂ)) *
        truncatedExponential (N - 1) ((N : ℂ) * (z * conj w)) := by
  have hnf : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnorm := congrArg (fun x : ℝ => (x : ℂ)) (sqrt_normalization N)
  push_cast at hnorm
  have hs : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hnf).ne'
  have hy : (Real.sqrt (z.im * w.im) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hz hw)).ne'
  have he :
      -(rescale N z - conj (rescale N w)) ^ 2 / (2 : ℂ) =
        -(N : ℂ) / 2 * (z - conj w) ^ 2 := by
    rw [rescale_sub_conj, mul_pow, sqrt_natCast_sq]
    ring
  have hnum : conj (rescale N w) - rescale N z =
      (Real.sqrt (N : ℝ) : ℂ) * (conj w - z) := by
    rw [conj_rescale]
    unfold rescale
    ring
  rw [S, gaussianAmplitude_eq_leading_mul_one_add_error hN hz hw,
    he, hnum, rescale_mul_conj]
  unfold gaussianAmplitudeLeading U
  push_cast
  rw [show -(N : ℂ) / 2 * (z - conj w) ^ 2 -
      (N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2) =
      -(N : ℂ) / 2 * (z - conj w) ^ 2 +
      (-(N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2)) by ring, Complex.exp_add]
  have hscalar :
      (Real.sqrt (N : ℝ) : ℂ) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * (Real.sqrt (2 * Real.pi * N) : ℂ)) =
      (2 * (Real.pi : ℂ))⁻¹ := by
    rw [hnorm]
    field_simp
  calc
    _ = ((Real.sqrt (N : ℝ) : ℂ) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * (Real.sqrt (2 * Real.pi * N) : ℂ))) *
        (Complex.I * (conj w - z) / (Real.sqrt (z.im * w.im) : ℂ)) *
        Complex.exp (-(N : ℂ) / 2 * (z - conj w) ^ 2) *
        Complex.exp (-(N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2)) *
        (1 + (gaussianAmplitudeError N z w : ℂ)) *
        truncatedExponential (N - 1) ((N : ℂ) * (z * conj w)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hscalar]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem D_rescale_eq_leadingD {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    D N (rescale N z) (rescale N w) =
      leadingD N z w * (1 + (gaussianAmplitudeError N z w : ℂ)) *
        truncatedExponential (N - 1) ((N : ℂ) * (z * w)) := by
  have hnf : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnorm := congrArg (fun x : ℝ => (x : ℂ)) (sqrt_normalization N)
  push_cast at hnorm
  have hs : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hnf).ne'
  have hy : (Real.sqrt (z.im * w.im) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (mul_pos hz hw)).ne'
  have he :
      -(rescale N z - rescale N w) ^ 2 / (2 : ℂ) =
        -(N : ℂ) / 2 * (z - w) ^ 2 := by
    rw [rescale_sub, mul_pow, sqrt_natCast_sq]
    ring
  have hnum : rescale N w - rescale N z =
      (Real.sqrt (N : ℝ) : ℂ) * (w - z) := by
    exact rescale_sub N w z
  rw [D, gaussianAmplitude_eq_leading_mul_one_add_error hN hz hw,
    he, hnum, rescale_mul]
  unfold gaussianAmplitudeLeading leadingD leadingDExponent
  push_cast
  rw [show -(N : ℂ) / 2 * (z - w) ^ 2 -
      (N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2) =
      -(N : ℂ) / 2 * (z - w) ^ 2 +
      (-(N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2)) by ring, Complex.exp_add]
  have hscalar :
      (Real.sqrt (N : ℝ) : ℂ) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * (Real.sqrt (2 * Real.pi * N) : ℂ)) =
      (2 * (Real.pi : ℂ))⁻¹ := by
    rw [hnorm]
    field_simp
  calc
    _ = ((Real.sqrt (N : ℝ) : ℂ) /
        ((Real.sqrt (2 * Real.pi) : ℂ) * (Real.sqrt (2 * Real.pi * N) : ℂ))) *
        ((w - z) / (Real.sqrt (z.im * w.im) : ℂ)) *
        Complex.exp (-(N : ℂ) / 2 * (z - w) ^ 2) *
        Complex.exp (-(N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2)) *
        (1 + (gaussianAmplitudeError N z w : ℂ)) *
        truncatedExponential (N - 1) ((N : ℂ) * (z * w)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hscalar]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem leadingSExponent_re (N : ℕ) (z w : ℂ) :
    (leadingSExponent N z w).re = -(N : ℝ) / 2 * ‖z - w‖ ^ 2 := by
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  simp [leadingSExponent, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

theorem leadingDExponent_re (N : ℕ) (z w : ℂ) :
    (leadingDExponent N z w).re = -(N : ℝ) / 2 * ‖z - conj w‖ ^ 2 := by
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  simp [leadingDExponent, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

theorem leadingSExponent_tail_re (N : ℕ) (z w : ℂ) :
    (leadingSExponent N z w + (N : ℂ) * (1 - z * conj w)).re =
      (N : ℝ) * (1 - (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2) := by
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  simp [leadingSExponent, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

theorem leadingDExponent_tail_re (N : ℕ) (z w : ℂ) :
    (leadingDExponent N z w + (N : ℂ) * (1 - z * w)).re =
      (N : ℝ) * (1 - (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2) := by
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  simp [leadingDExponent, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

theorem norm_U {N : ℕ} {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖U N z w‖ = ‖conj w - z‖ /
      (2 * Real.pi * Real.sqrt (z.im * w.im)) *
        Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) := by
  have hd : 0 < 2 * Real.pi * Real.sqrt (z.im * w.im) := by positivity
  unfold U
  rw [norm_mul, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, Complex.norm_exp]
  change ‖conj w - z‖ / (2 * Real.pi * Real.sqrt (z.im * w.im)) *
      Real.exp (leadingSExponent N z w).re = _
  rw [leadingSExponent_re]

theorem norm_leadingD {N : ℕ} {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖leadingD N z w‖ = ‖w - z‖ /
      (2 * Real.pi * Real.sqrt (z.im * w.im)) *
        Real.exp (-(N : ℝ) / 2 * ‖z - conj w‖ ^ 2) := by
  have hd : 0 < 2 * Real.pi * Real.sqrt (z.im * w.im) := by positivity
  unfold leadingD
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
    Complex.norm_exp, leadingDExponent_re]

theorem one_add_gaussianAmplitudeError_bounds {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    0 ≤ 1 + gaussianAmplitudeError N z w ∧ 1 + gaussianAmplitudeError N z w ≤ 1 := by
  let a := erfcRelativeError (amplitudeArgument N z.im)
  let b := erfcRelativeError (amplitudeArgument N w.im)
  have ha0 : 0 ≤ 1 + a := erfc_one_add_error_nonneg (amplitudeArgument_pos hN hz)
  have hb0 : 0 ≤ 1 + b := erfc_one_add_error_nonneg (amplitudeArgument_pos hN hw)
  have ha1 : 1 + a ≤ 1 := by
    have := (erfcRelativeError_bounds (amplitudeArgument_pos hN hz)).2
    change a ≤ 0 at this
    linarith
  have hb1 : 1 + b ≤ 1 := by
    have := (erfcRelativeError_bounds (amplitudeArgument_pos hN hw)).2
    change b ≤ 0 at this
    linarith
  have hp : (1 + a) * (1 + b) ≤ 1 :=
    (mul_le_mul ha1 hb1 hb0 zero_le_one).trans_eq (by ring)
  have hs0 := Real.sqrt_nonneg ((1 + a) * (1 + b))
  have hs1 := Real.sqrt_le_one.mpr hp
  unfold gaussianAmplitudeError
  change 0 ≤ 1 + (Real.sqrt ((1 + a) * (1 + b)) - 1) ∧ _
  constructor <;> linarith

theorem norm_one_add_gaussianAmplitudeError_le_one {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖1 + (gaussianAmplitudeError N z w : ℂ)‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := one_add_gaussianAmplitudeError_bounds hN hz hw
  simpa only [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg h0] using h1

theorem U_diag (N : ℕ) {z : ℂ} (hz : 0 < z.im) :
    U N z z = ((1 / Real.pi : ℝ) : ℂ) := by
  have hnum : Complex.I * (conj z - z) = ((2 * z.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  have he : leadingSExponent N z z = 0 := by
    apply Complex.ext <;> simp [leadingSExponent, pow_two, Complex.mul_re, Complex.mul_im]
    ring
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  unfold U
  change Complex.I * (conj z - z) /
    ((2 * Real.pi * Real.sqrt (z.im * z.im) : ℝ) : ℂ) *
      Complex.exp (leadingSExponent N z z) = _
  rw [he, Complex.exp_zero, mul_one, hnum, ← pow_two, Real.sqrt_sq hz.le]
  push_cast
  field_simp

theorem norm_U_sq {N : ℕ} {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ‖U N z w‖ ^ 2 = 1 / Real.pi ^ 2 *
      Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) *
        (1 + ‖z - w‖ ^ 2 / (4 * z.im * w.im)) := by
  have hn : ‖conj w - z‖ ^ 2 = ‖z - w‖ ^ 2 + 4 * z.im * w.im := by
    simp_rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have he : Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) ^ 2 =
      Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [norm_U hz hw, mul_pow, div_pow, he, hn]
  rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hz.le hw.le)]
  field_simp
  ring

end Paper.Kernel
