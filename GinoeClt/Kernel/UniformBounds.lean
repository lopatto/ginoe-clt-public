/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.ExponentialTail

/-! # Uniform bulk bounds for the actual leading and tail kernels -/

@[expose] public section
noncomputable section
open Set
open scoped Real ComplexConjugate

namespace Paper.Kernel

theorem prefactor_quotient_le {d y v : ℝ} (hd : 0 < d)
    (hy : d ≤ y) (hv : d ≤ v) {p : ℂ} (hp : ‖p‖ ≤ 2) :
    ‖p‖ / (2 * Real.pi * Real.sqrt (y * v)) ≤ 1 / (Real.pi * d) := by
  have hroot : d ≤ Real.sqrt (y * v) := by
    calc
      d = Real.sqrt (d ^ 2) := (Real.sqrt_sq hd.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by
        rw [pow_two]
        exact mul_le_mul hy hv hd.le (hd.trans_le hy).le)
  have hden : 2 * Real.pi * d ≤ 2 * Real.pi * Real.sqrt (y * v) :=
    mul_le_mul_of_nonneg_left hroot (by positivity)
  have hd0 : 0 < 2 * Real.pi * d := by positivity
  calc
    _ ≤ ‖p‖ / (2 * Real.pi * d) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hd0 hden
    _ ≤ 2 / (2 * Real.pi * d) := div_le_div_of_nonneg_right hp hd0.le
    _ = _ := by field_simp

theorem norm_sub_le_two {d : ℝ} (hd : 0 ≤ d) {z w : ℂ}
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d) : ‖w - z‖ ≤ 2 := by
  have hh := norm_sub_le w z
  linarith

theorem norm_U_prefactor_le {d : ℝ} (hd : 0 < d) {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d) :
    ‖Complex.I * (conj w - z) /
      ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ)‖ ≤ 1 / (Real.pi * d) := by
  have hz0 := hd.trans_le hzy
  have hw0 := hd.trans_le hwy
  have hden : 0 < 2 * Real.pi * Real.sqrt (z.im * w.im) := by positivity
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hden]
  exact prefactor_quotient_le hd hzy hwy
    (norm_sub_le_two hd.le hz (by simpa only [Complex.norm_conj] using hw))

theorem norm_D_prefactor_le {d : ℝ} (hd : 0 < d) {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d) :
    ‖(w - z) / ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ)‖ ≤
      1 / (Real.pi * d) := by
  have hz0 := hd.trans_le hzy
  have hw0 := hd.trans_le hwy
  have hden : 0 < 2 * Real.pi * Real.sqrt (z.im * w.im) := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  exact prefactor_quotient_le hd hzy hwy (norm_sub_le_two hd.le hz hw)

theorem norm_U_bulk_le {d : ℝ} (hd : 0 < d) {N : ℕ} {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d) :
    ‖U N z w‖ ≤ (1 / (Real.pi * d)) *
      Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) := by
  rw [norm_U (hd.trans_le hzy) (hd.trans_le hwy)]
  exact mul_le_mul_of_nonneg_right
    (prefactor_quotient_le hd hzy hwy
      (norm_sub_le_two hd.le hz (by simpa only [Complex.norm_conj] using hw)))
    (Real.exp_pos _).le

theorem norm_leadingD_bulk_le {d : ℝ} (hd : 0 < d) {N : ℕ} {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d) :
    ‖leadingD N z w‖ ≤ (1 / (Real.pi * d)) *
      Real.exp (-(2 * d ^ 2) * (N : ℝ)) := by
  have hdiff : 2 * d ≤ ‖z - conj w‖ := by
    have hh := (le_abs_self (z - conj w).im).trans (Complex.abs_im_le_norm (z - conj w))
    simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add] at hh
    linarith
  have hex : Real.exp (-(N : ℝ) / 2 * ‖z - conj w‖ ^ 2) ≤
      Real.exp (-(2 * d ^ 2) * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hs : (2 * d) ^ 2 ≤ ‖z - conj w‖ ^ 2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hdiff
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [norm_leadingD (hd.trans_le hzy) (hd.trans_le hwy)]
  exact mul_le_mul
    (prefactor_quotient_le hd hzy hwy (norm_sub_le_two hd.le hz hw)) hex
    (Real.exp_pos _).le (by positivity)

theorem bulk_pair_norm_bounds {d : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2) {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d) :
    d ≤ ‖z‖ ∧ d ≤ ‖w‖ ∧
      d ^ 2 ≤ ‖z * w‖ ∧ ‖z * w‖ ≤ (1 - d) ^ 2 ∧
      d ^ 2 ≤ ‖z * conj w‖ ∧ ‖z * conj w‖ ≤ (1 - d) ^ 2 := by
  have hzn : d ≤ ‖z‖ := hzy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hwn : d ≤ ‖w‖ := hwy.trans ((le_abs_self w.im).trans (Complex.abs_im_le_norm w))
  have hlo : d ^ 2 ≤ ‖z‖ * ‖w‖ := by
    rw [pow_two]
    exact mul_le_mul hzn hwn hd.le (norm_nonneg _)
  have hhi : ‖z‖ * ‖w‖ ≤ (1 - d) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hz hw (norm_nonneg _) (by linarith)
  simpa only [norm_mul, Complex.norm_conj] using ⟨hzn, hwn, hlo, hhi, hlo, hhi⟩

theorem norm_U_mul_tail_bulk_le {d C : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2)
    (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d)
    (hR : ‖Lambert.correctedTruncationError N (z * conj w)‖ ≤ C / (N : ℝ)) :
    ‖U N z w * truncationTail N (z * conj w)‖ ≤
      (1 / (Real.pi * d)) *
        ((1 + C) / (d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2))) *
          Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := by
  obtain ⟨hzn, hwn, _, _, hqlo, hqhi⟩ := bulk_pair_norm_bounds hd hdh hzy hwy hz hw
  have hnum := (norm_S_tail_numerator N (hd.trans_le hzn) (hd.trans_le hwn)).le.trans
    (entropy_bulk_decay hd hdh hzn hwn hz hw N)
  have ht := norm_exp_mul_truncationTail_le hd hdh hC hN hqlo hqhi hR hnum
  have he : U N z w * truncationTail N (z * conj w) =
      (Complex.I * (conj w - z) /
        ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ)) *
          (Complex.exp (leadingSExponent N z w) * truncationTail N (z * conj w)) := by
    unfold U leadingSExponent
    ring
  rw [he, norm_mul]
  exact (mul_le_mul (norm_U_prefactor_le hd hzy hwy hz hw) ht (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

theorem norm_leadingD_mul_tail_bulk_le {d C : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2)
    (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : d ≤ w.im)
    (hz : ‖z‖ ≤ 1 - d) (hw : ‖w‖ ≤ 1 - d)
    (hR : ‖Lambert.correctedTruncationError N (z * w)‖ ≤ C / (N : ℝ)) :
    ‖leadingD N z w * truncationTail N (z * w)‖ ≤
      (1 / (Real.pi * d)) *
        ((1 + C) / (d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2))) *
          Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := by
  obtain ⟨hzn, hwn, hqlo, hqhi, _, _⟩ := bulk_pair_norm_bounds hd hdh hzy hwy hz hw
  have hnum := (norm_D_tail_numerator N (hd.trans_le hzn) (hd.trans_le hwn)).le.trans
    (entropy_bulk_decay hd hdh hzn hwn hz hw N)
  have ht := norm_exp_mul_truncationTail_le hd hdh hC hN hqlo hqhi hR hnum
  have he : leadingD N z w * truncationTail N (z * w) =
      ((w - z) / ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ)) *
        (Complex.exp (leadingDExponent N z w) * truncationTail N (z * w)) := by
    unfold leadingD
    ring
  rw [he, norm_mul]
  exact (mul_le_mul (norm_D_prefactor_le hd hzy hwy hz hw) ht (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

end Paper.Kernel
