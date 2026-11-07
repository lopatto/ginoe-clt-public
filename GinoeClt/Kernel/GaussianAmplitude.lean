/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.ErfcAsymptotic
public import GinoeClt.Kernel.BulkSeparation

/-! # Uniform relative error for the manuscript Gaussian amplitude -/

@[expose] public section
noncomputable section
open Set
open scoped Real

namespace Paper.Kernel

def amplitudeArgument (N : ℕ) (y : ℝ) : ℝ := Real.sqrt 2 * Real.sqrt (N : ℝ) * y

def gaussianAmplitudeError (N : ℕ) (z w : ℂ) : ℝ :=
  Real.sqrt ((1 + erfcRelativeError (amplitudeArgument N z.im)) *
    (1 + erfcRelativeError (amplitudeArgument N w.im))) - 1

def gaussianAmplitudeLeading (N : ℕ) (z w : ℂ) : ℝ :=
  Real.exp (-(N : ℝ) * (z.im ^ 2 + w.im ^ 2)) /
    (Real.sqrt (2 * Real.pi * (N : ℝ)) * Real.sqrt (z.im * w.im))

theorem amplitudeArgument_pos {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) :
    0 < amplitudeArgument N y := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  unfold amplitudeArgument
  positivity

theorem amplitudeArgument_sq (N : ℕ) (y : ℝ) :
    amplitudeArgument N y ^ 2 = 2 * (N : ℝ) * y ^ 2 := by
  rw [amplitudeArgument, mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
    Real.sq_sqrt (Nat.cast_nonneg N)]

theorem erfc_one_add_error_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 + erfcRelativeError x := by
  have hp : 0 < Real.exp (-(x ^ 2)) / (Real.sqrt Real.pi * x) :=
    div_pos (Real.exp_pos _) (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) hx)
  have hn := erfc_nonneg x
  rw [erfc_eq_leading_mul_one_add_error hx] at hn
  nlinarith

theorem amplitude_erfc_error_bound {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N)
    {y : ℝ} (hy : d ≤ y) :
    |erfcRelativeError (amplitudeArgument N y)| ≤ 1 / (4 * (N : ℝ) * d ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hy0 : 0 < y := hd.trans_le hy
  apply (abs_erfcRelativeError_le (amplitudeArgument_pos hN hy0)).trans
  apply one_div_le_one_div_of_le (by positivity : 0 < 4 * (N : ℝ) * d ^ 2)
  rw [amplitudeArgument_sq]
  have hs : d ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hd.le hy0.le).mpr hy
  nlinarith

theorem abs_gaussianAmplitudeError_le_errors {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    |gaussianAmplitudeError N z w| ≤
      |erfcRelativeError (amplitudeArgument N z.im)| +
        |erfcRelativeError (amplitudeArgument N w.im)| := by
  let a := erfcRelativeError (amplitudeArgument N z.im)
  let b := erfcRelativeError (amplitudeArgument N w.im)
  have ha : a ≤ 0 := (erfcRelativeError_bounds (amplitudeArgument_pos hN hz)).2
  have hb : b ≤ 0 := (erfcRelativeError_bounds (amplitudeArgument_pos hN hw)).2
  have ha0 : 0 ≤ 1 + a := erfc_one_add_error_nonneg (amplitudeArgument_pos hN hz)
  have hb0 : 0 ≤ 1 + b := erfc_one_add_error_nonneg (amplitudeArgument_pos hN hw)
  let p := (1 + a) * (1 + b)
  have hp0 : 0 ≤ p := mul_nonneg ha0 hb0
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb]
  have hs0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hs1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp1
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hps : p ≤ Real.sqrt p := by nlinarith
  change |Real.sqrt p - 1| ≤ |a| + |b|
  rw [abs_of_nonpos (by linarith : Real.sqrt p - 1 ≤ 0), abs_of_nonpos ha, abs_of_nonpos hb]
  dsimp only [p] at hps
  nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb]

theorem gaussianAmplitudeError_bound {d : ℝ} (hd : 0 < d) {N : ℕ} (hN : 1 ≤ N)
    {z w : ℂ} (hz : d ≤ z.im) (hw : d ≤ w.im) :
    |gaussianAmplitudeError N z w| ≤ 1 / (2 * (N : ℝ) * d ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  calc
    _ ≤ |erfcRelativeError (amplitudeArgument N z.im)| +
        |erfcRelativeError (amplitudeArgument N w.im)| :=
      abs_gaussianAmplitudeError_le_errors hN (hd.trans_le hz) (hd.trans_le hw)
    _ ≤ 1 / (4 * (N : ℝ) * d ^ 2) + 1 / (4 * (N : ℝ) * d ^ 2) :=
      add_le_add (amplitude_erfc_error_bound hd hN hz) (amplitude_erfc_error_bound hd hN hw)
    _ = _ := by ring


theorem im_rescale (N : ℕ) (z : ℂ) : (rescale N z).im = Real.sqrt (N : ℝ) * z.im := by
  simp [rescale, Complex.mul_im]

theorem gaussianAmplitudeLeading_nonneg (N : ℕ) (z w : ℂ) :
    0 ≤ gaussianAmplitudeLeading N z w := by
  unfold gaussianAmplitudeLeading
  positivity

theorem erfcLeading_product_eq_amplitudeLeading_sq {N : ℕ} {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    (Real.exp (-(amplitudeArgument N z.im ^ 2)) /
        (Real.sqrt Real.pi * amplitudeArgument N z.im)) *
      (Real.exp (-(amplitudeArgument N w.im ^ 2)) /
        (Real.sqrt Real.pi * amplitudeArgument N w.im)) =
      gaussianAmplitudeLeading N z w ^ 2 := by
  have hden :
      (Real.sqrt Real.pi * amplitudeArgument N z.im) *
          (Real.sqrt Real.pi * amplitudeArgument N w.im) =
        (Real.sqrt (2 * Real.pi * (N : ℝ)) * Real.sqrt (z.im * w.im)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi * (N : ℝ)),
      Real.sq_sqrt (mul_nonneg hz.le hw.le)]
    unfold amplitudeArgument
    calc
      _ = Real.sqrt Real.pi ^ 2 * Real.sqrt 2 ^ 2 * Real.sqrt (N : ℝ) ^ 2 *
          (z.im * w.im) := by ring
      _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt (by norm_num),
        Real.sq_sqrt (Nat.cast_nonneg N)]; ring
  have hexp (u : ℝ) : Real.exp u ^ 2 = Real.exp (u + u) := by
    simpa only [pow_two] using (Real.exp_add u u).symm
  have hnum :
      Real.exp (-(amplitudeArgument N z.im ^ 2)) *
          Real.exp (-(amplitudeArgument N w.im ^ 2)) =
        Real.exp (-(N : ℝ) * (z.im ^ 2 + w.im ^ 2)) ^ 2 := by
    rw [← Real.exp_add, hexp, amplitudeArgument_sq, amplitudeArgument_sq]
    congr 1
    ring
  rw [div_mul_div_comm, hden, hnum, ← div_pow]
  rfl

/-- Exact source Eq. 41; the relative error is the explicit product of the two
erfc relative factors. -/
theorem gaussianAmplitude_eq_leading_mul_one_add_error {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) :
    gaussianAmplitude (rescale N z) (rescale N w) =
      gaussianAmplitudeLeading N z w * (1 + gaussianAmplitudeError N z w) := by
  have hx := amplitudeArgument_pos hN hz
  have hy := amplitudeArgument_pos hN hw
  unfold gaussianAmplitude
  rw [im_rescale, im_rescale]
  have harg (y : ℝ) : Real.sqrt 2 * (Real.sqrt (N : ℝ) * y) = amplitudeArgument N y :=
    (mul_assoc _ _ _).symm
  rw [harg, harg]
  rw [erfc_eq_leading_mul_one_add_error hx, erfc_eq_leading_mul_one_add_error hy]
  have hp :
      (Real.exp (-(amplitudeArgument N z.im ^ 2)) /
          (Real.sqrt Real.pi * amplitudeArgument N z.im) *
          (1 + erfcRelativeError (amplitudeArgument N z.im))) *
        (Real.exp (-(amplitudeArgument N w.im ^ 2)) /
          (Real.sqrt Real.pi * amplitudeArgument N w.im) *
          (1 + erfcRelativeError (amplitudeArgument N w.im))) =
      ((Real.exp (-(amplitudeArgument N z.im ^ 2)) /
          (Real.sqrt Real.pi * amplitudeArgument N z.im)) *
        (Real.exp (-(amplitudeArgument N w.im ^ 2)) /
          (Real.sqrt Real.pi * amplitudeArgument N w.im))) *
        ((1 + erfcRelativeError (amplitudeArgument N z.im)) *
          (1 + erfcRelativeError (amplitudeArgument N w.im))) := by ring
  rw [hp, erfcLeading_product_eq_amplitudeLeading_sq hz hw,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (gaussianAmplitudeLeading_nonneg N z w)]
  unfold gaussianAmplitudeError
  ring

/-- The constant is exactly a function of d_A alone; N ≥ 1 already suffices. -/
theorem gaussianAmplitude_bulk_relative_error {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N : ℕ) (hN : 1 ≤ N) {z w : ℂ} (hz : z ∈ closure A) (hw : w ∈ closure A) :
    gaussianAmplitude (rescale N z) (rescale N w) =
        Real.exp (-(N : ℝ) * (z.im ^ 2 + w.im ^ 2)) /
          (Real.sqrt (2 * Real.pi * (N : ℝ)) * Real.sqrt (z.im * w.im)) *
            (1 + gaussianAmplitudeError N z w) ∧
      |gaussianAmplitudeError N z w| ≤ (1 / (2 * bulkDistance A ^ 2)) / (N : ℝ) := by
  have hd := bulkDistance_pos hA
  have hzy := bulkDistance_le_im hA hz
  have hwy := bulkDistance_le_im hA hw
  constructor
  · exact gaussianAmplitude_eq_leading_mul_one_add_error hN (hd.trans_le hzy) (hd.trans_le hwy)
  · apply (gaussianAmplitudeError_bound hd hN hzy hwy).trans_eq
    ring

end Paper.Kernel
