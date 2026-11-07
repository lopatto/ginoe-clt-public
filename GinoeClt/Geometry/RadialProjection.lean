/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Normed.Group.RadialFunction
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The exact radial projection constant in planar area measure -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Paper.Geometry

lemma integral_abs_cos_Ioo : (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, |Real.cos θ|) = 4 := by
  have hc : Continuous (fun θ : ℝ => |Real.cos θ|) := continuous_abs.comp Real.continuous_cos
  have hp : Function.Periodic (fun θ : ℝ => |Real.cos θ|) Real.pi := by
    intro θ
    change |Real.cos (θ + Real.pi)| = |Real.cos θ|
    rw [Real.cos_add_pi, abs_neg]
  have hhalf : (∫ θ in -(Real.pi / 2)..Real.pi / 2, |Real.cos θ|) = 2 := by
    calc (∫ θ in -(Real.pi / 2)..Real.pi / 2, |Real.cos θ|) =
        ∫ θ in -(Real.pi / 2)..Real.pi / 2, Real.cos θ := by
          apply intervalIntegral.integral_congr
          intro θ hθ
          change |Real.cos θ| = Real.cos θ
          rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc (by
            simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 2)] using hθ))]
      _ = 2 := by rw [integral_cos]; norm_num
  have hd := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) (-(Real.pi / 2)) (fun a b => hc.intervalIntegrable a b)
  have hs := (hp.nat_mul 2).intervalIntegral_add_eq (-Real.pi) (-(Real.pi / 2))
  have hfull : (∫ θ in -Real.pi..Real.pi, |Real.cos θ|) = 4 := by
    calc (∫ θ in -Real.pi..Real.pi, |Real.cos θ|) =
        ∫ θ in -(Real.pi / 2)..-(Real.pi / 2) + 2 * Real.pi, |Real.cos θ| := by
          convert! hs using 1; ring
      _ = 2 * (∫ θ in -(Real.pi / 2)..Real.pi / 2, |Real.cos θ|) := by
        convert! hd using 1 <;> ring
      _ = 4 := by rw [hhalf]; norm_num
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  exact hfull

lemma radial_polar_value {J : ℂ → ℝ} (hJ : Function.IsRadial J) (r θ : ℝ) :
    J (Complex.polarCoord.symm (r, θ)) = J (r : ℂ) := by
  apply hJ
  change ‖Complex.polarCoord.symm (r, θ)‖ = ‖(r : ℂ)‖
  rw [Complex.norm_polarCoord_symm, Complex.norm_real, Real.norm_eq_abs]

lemma integral_norm_mul_radial {J : ℂ → ℝ} (hJ : Function.IsRadial J) :
    (∫ z : ℂ, ‖z‖ * J z) =
      (∫ r : ℝ in Ioi 0, r ^ 2 * J (r : ℂ)) * (2 * Real.pi) := by
  calc (∫ z : ℂ, ‖z‖ * J z) =
      ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (‖Complex.polarCoord.symm p‖ * J (Complex.polarCoord.symm p)) := by
          simpa only [_root_.polarCoord_target] using (Complex.integral_comp_polarCoord_symm
            (fun z : ℂ => ‖z‖ * J z)).symm
    _ = ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 ^ 2 * J (p.1 : ℂ)) * (1 : ℝ) := by
          apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
          rintro ⟨r, θ⟩ hp
          change r * (‖Complex.polarCoord.symm (r, θ)‖ * J (Complex.polarCoord.symm (r, θ))) =
            (r ^ 2 * J (r : ℂ)) * 1
          rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, radial_polar_value hJ]
          ring
    _ = _ := by
      rw [Measure.volume_eq_prod]
      have hh := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun r : ℝ => r ^ 2 * J (r : ℂ)) (fun _ : ℝ => (1 : ℝ)) (Ioi 0) (Ioo (-Real.pi) Real.pi)
      have hθ : (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
        rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo,
          max_eq_left (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi)]
        ring
      rw [hθ] at hh
      convert! hh using 1

lemma integral_abs_re_mul_radial {J : ℂ → ℝ} (hJ : Function.IsRadial J) :
    (∫ z : ℂ, |z.re| * J z) =
      (∫ r : ℝ in Ioi 0, r ^ 2 * J (r : ℂ)) * 4 := by
  calc (∫ z : ℂ, |z.re| * J z) =
      ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (|(Complex.polarCoord.symm p).re| * J (Complex.polarCoord.symm p)) := by
          simpa only [_root_.polarCoord_target] using (Complex.integral_comp_polarCoord_symm
            (fun z : ℂ => |z.re| * J z)).symm
    _ = ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 ^ 2 * J (p.1 : ℂ)) * |Real.cos p.2| := by
          apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
          rintro ⟨r, θ⟩ hp
          change r * (|(Complex.polarCoord.symm (r, θ)).re| * J (Complex.polarCoord.symm (r, θ))) =
            (r ^ 2 * J (r : ℂ)) * |Real.cos θ|
          rw [radial_polar_value hJ]
          simp only [Complex.polarCoord_symm_apply, Complex.mul_re, Complex.ofReal_re,
            Complex.add_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, sub_zero, add_zero, mul_one]
          rw [abs_mul, abs_of_pos hp.1]
          ring
    _ = _ := by
      rw [Measure.volume_eq_prod]
      have hh := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun r : ℝ => r ^ 2 * J (r : ℂ)) (fun θ : ℝ => |Real.cos θ|) (Ioi 0) (Ioo (-Real.pi) Real.pi)
      rw [integral_abs_cos_Ioo] at hh
      convert! hh using 1

lemma radial_abs_re_integral {J : ℂ → ℝ} (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) :
    (∫ z : ℂ, |z.re| * J z) = 2 / Real.pi := by
  have hw := (integral_norm_mul_radial hJ).symm.trans hmoment
  rw [integral_abs_re_mul_radial hJ]
  apply (eq_div_iff Real.pi_ne_zero).2
  nlinarith

/-- Exact normalization of the projection onto any unit vector. This uses the
first moment of J and does not require the kernel J itself to be integrable. -/
theorem radial_projection_integral {J : ℂ → ℝ} (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) {ν : ℂ} (hν : ‖ν‖ = 1) :
    (∫ z : ℂ, |inner ℝ z ν| * J z) = 2 / Real.pi := by
  let v : Circle := ⟨ν, mem_sphere_zero_iff_norm.mpr hν⟩
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := _root_.rotation v
  have he1 : e 1 = ν := by simp only [e, _root_.rotation_apply, mul_one]; rfl
  have hi : ∀ z : ℂ, inner ℝ (e z) ν = z.re := by
    intro z
    rw [← he1, e.inner_map_map]
    simp only [Complex.inner, one_mul, Complex.conj_re]
  have hJe : ∀ z : ℂ, J (e z) = J z := by
    intro z
    apply hJ
    exact e.norm_map z
  calc (∫ z : ℂ, |inner ℝ z ν| * J z) =
      ∫ z : ℂ, |inner ℝ (e z) ν| * J (e z) := by
        exact ((e.measurePreserving).integral_comp e.toHomeomorph.measurableEmbedding
          (fun z : ℂ => |inner ℝ z ν| * J z)).symm
    _ = ∫ z : ℂ, |z.re| * J z := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by change |inner ℝ (e z) ν| * J (e z) = |z.re| * J z; rw [hi, hJe])
    _ = _ := radial_abs_re_integral hJ hmoment

lemma integrable_firstMoment {J : ℂ → ℝ}
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) : Integrable (fun z => ‖z‖ * J z) := by
  apply Integrable.of_integral_ne_zero
  rw [hmoment]
  norm_num

lemma integrable_radial_projection {J : ℂ → ℝ} (hJm : Measurable J)
    (hJnn : ∀ z, 0 ≤ J z) (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1)
    {ν : ℂ} (hν : ‖ν‖ = 1) : Integrable (fun z => |inner ℝ z ν| * J z) := by
  refine (integrable_firstMoment hmoment).mono'
    ((continuous_abs.measurable.comp (continuous_id.inner continuous_const).measurable).mul hJm).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hJnn z))]
  apply mul_le_mul_of_nonneg_right _ (hJnn z)
  simpa only [hν, mul_one] using abs_real_inner_le_norm z ν

end Paper.Geometry
