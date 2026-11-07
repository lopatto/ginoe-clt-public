/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Erfc
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Exact Gaussian-tail relative error -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Paper.Kernel

def gaussianWeightedTail (x : ℝ) : ℝ :=
  ∫ t in Ioi x, Real.exp (-(t ^ 2)) / t ^ 2

def gaussianTailPrimitive (t : ℝ) : ℝ := Real.exp (-(t ^ 2)) / (2 * t)

theorem weighted_gaussian_nonneg (t : ℝ) : 0 ≤ Real.exp (-(t ^ 2)) / t ^ 2 :=
  div_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem weighted_gaussian_le {x t : ℝ} (hx : 0 < x) (ht : x ≤ t) :
    Real.exp (-(t ^ 2)) / t ^ 2 ≤ Real.exp (-(t ^ 2)) / x ^ 2 := by
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (sq_pos_of_pos hx)
  exact (sq_le_sq₀ hx.le (hx.le.trans ht)).mpr ht

theorem integrableOn_weighted_gaussian {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2)) / t ^ 2) (Ioi x) := by
  apply (integrable_gaussian.integrableOn.div_const (x ^ 2)).mono'
  · exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-(t ^ 2)) / t ^ 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (weighted_gaussian_nonneg t)]
    exact weighted_gaussian_le hx ht.le

theorem gaussianWeightedTail_nonneg (x : ℝ) : 0 ≤ gaussianWeightedTail x :=
  integral_nonneg weighted_gaussian_nonneg

theorem hasDerivAt_gaussianTailPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt gaussianTailPrimitive
      (-Real.exp (-(t ^ 2)) - (Real.exp (-(t ^ 2)) / t ^ 2) / 2) t := by
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
      (Real.exp (-(t ^ 2)) * -(2 * t)) t := by
    simpa only [Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one] using (((hasDerivAt_id t).pow 2).neg).exp
  have hd : HasDerivAt (fun y : ℝ => 2 * y) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hh := hg.div hd (by positivity : (2 : ℝ) * t ≠ 0)
  apply hh.congr_deriv
  field_simp [ht.ne']

theorem tendsto_gaussianTailPrimitive :
    Tendsto gaussianTailPrimitive atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => (1 / 2 : ℝ) * t⁻¹) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds
    simpa using hc.mul (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  apply squeeze_zero' ?_ ?_ hi
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    change 0 ≤ Real.exp (-(t ^ 2)) / (2 * t)
    exact div_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) ht.le)
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    have hg : Real.exp (-(t ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg t))
    calc
      gaussianTailPrimitive t = Real.exp (-(t ^ 2)) / (2 * t) := rfl
      _ ≤ 1 / (2 * t) :=
        div_le_div_of_nonneg_right hg (mul_nonneg (by norm_num) ht.le)
      _ = (1 / 2 : ℝ) * t⁻¹ := by
        simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- The complete integration-by-parts identity, proved by improper FTC. -/
theorem gaussian_tail_integration_by_parts {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi x, Real.exp (-(t ^ 2))) =
      Real.exp (-(x ^ 2)) / (2 * x) - gaussianWeightedTail x / 2 := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Ioi x) :=
    integrable_gaussian.integrableOn
  have hw := integrableOn_weighted_gaussian hx
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hasDerivAt_gaussianTailPrimitive (hx.trans_le ht))
    (hg.neg.sub (hw.div_const 2)) tendsto_gaussianTailPrimitive
  have hn : IntegrableOn (fun t : ℝ => -Real.exp (-(t ^ 2))) (Ioi x) := hg.neg
  have hd : IntegrableOn (fun t : ℝ => (Real.exp (-(t ^ 2)) / t ^ 2) / 2) (Ioi x) := hw.div_const 2
  rw [integral_sub hn hd, integral_neg, integral_div] at hh
  change -(∫ t in Ioi x, Real.exp (-(t ^ 2))) - gaussianWeightedTail x / 2 =
    0 - Real.exp (-(x ^ 2)) / (2 * x) at hh
  linarith


theorem gaussian_tail_le {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi x, Real.exp (-(t ^ 2))) ≤ Real.exp (-(x ^ 2)) / (2 * x) := by
  rw [gaussian_tail_integration_by_parts hx]
  linarith [gaussianWeightedTail_nonneg x]

theorem gaussianWeightedTail_le {x : ℝ} (hx : 0 < x) :
    gaussianWeightedTail x ≤ Real.exp (-(x ^ 2)) / (2 * x ^ 3) := by
  have hh := integral_mono_ae (integrableOn_weighted_gaussian hx)
    (integrable_gaussian.integrableOn.div_const (x ^ 2))
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => weighted_gaussian_le hx ht.le)
  rw [integral_div] at hh
  calc
    gaussianWeightedTail x ≤ (∫ t in Ioi x, Real.exp (-(t ^ 2))) / x ^ 2 := hh
    _ ≤ (Real.exp (-(x ^ 2)) / (2 * x)) / x ^ 2 :=
      div_le_div_of_nonneg_right (gaussian_tail_le hx) (sq_nonneg x)
    _ = Real.exp (-(x ^ 2)) / (2 * x ^ 3) := by field_simp

/-- The explicit relative error is a weighted Gaussian tail ratio. Its assertions
are for positive x; no limiting or asymptotic convention is encoded in the definition. -/
def erfcRelativeError (x : ℝ) : ℝ :=
  -(x * gaussianWeightedTail x / Real.exp (-(x ^ 2)))

theorem erfc_eq_leading_mul_one_add_error {x : ℝ} (hx : 0 < x) :
    erfc x = Real.exp (-(x ^ 2)) / (Real.sqrt Real.pi * x) *
      (1 + erfcRelativeError x) := by
  rw [erfc, gaussian_tail_integration_by_parts hx]
  unfold erfcRelativeError
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hg : Real.exp (-(x ^ 2)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hp, hg, hx.ne']
  ring

theorem erfcRelativeError_bounds {x : ℝ} (hx : 0 < x) :
    -(1 / (2 * x ^ 2)) ≤ erfcRelativeError x ∧ erfcRelativeError x ≤ 0 := by
  have hg : 0 < Real.exp (-(x ^ 2)) := Real.exp_pos _
  have hw := gaussianWeightedTail_nonneg x
  have hh : x * gaussianWeightedTail x / Real.exp (-(x ^ 2)) ≤ 1 / (2 * x ^ 2) := by
    calc
      _ ≤ x * (Real.exp (-(x ^ 2)) / (2 * x ^ 3)) / Real.exp (-(x ^ 2)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (gaussianWeightedTail_le hx) hx.le) hg.le
      _ = _ := by field_simp [hg.ne', hx.ne']
  constructor
  · exact neg_le_neg hh
  · exact neg_nonpos.mpr (div_nonneg (mul_nonneg hx.le hw) hg.le)

theorem abs_erfcRelativeError_le {x : ℝ} (hx : 0 < x) :
    |erfcRelativeError x| ≤ 1 / (2 * x ^ 2) := by
  obtain ⟨hlo, hhi⟩ := erfcRelativeError_bounds hx
  rw [abs_of_nonpos hhi]
  linarith

/-- Manuscript Eq. 40, for every positive x, with its exact signed error bounds. -/
theorem erfc_relative_error {x : ℝ} (hx : 0 < x) :
    ∃ ε : ℝ, erfc x = Real.exp (-(x ^ 2)) / (Real.sqrt Real.pi * x) * (1 + ε) ∧
      -(1 / (2 * x ^ 2)) ≤ ε ∧ ε ≤ 0 :=
  ⟨erfcRelativeError x, erfc_eq_leading_mul_one_add_error hx, erfcRelativeError_bounds hx⟩

end Paper.Kernel
