/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.GaussianBounds
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Complex Gaussian endpoint integrals by angular averaging -/

@[expose] public section
noncomputable section
open MeasureTheory Set Complex
open scoped Real Topology

namespace Paper.Trace

theorem angular_exponential_shifted (α : ℂ) :
    (∫ θ : ℝ in (-Real.pi)..Real.pi,
      Complex.exp (α * Complex.exp ((θ : ℂ) * Complex.I))) = (2 * Real.pi : ℂ) := by
  have hs := intervalIntegral.integral_comp_sub_right
    (fun θ : ℝ => Complex.exp (α * Complex.exp ((θ : ℂ) * Complex.I)))
    (a := 0) (b := 2 * Real.pi) Real.pi
  rw [zero_sub, show 2 * Real.pi - Real.pi = Real.pi by ring] at hs
  rw [← hs]
  have he : (fun θ : ℝ => Complex.exp (α * Complex.exp (((θ - Real.pi : ℝ) : ℂ) * Complex.I))) =
      (fun θ : ℝ => Complex.exp ((-α) * Complex.exp ((θ : ℂ) * Complex.I))) := by
    funext θ
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    congr 1
    ring
  rw [he]
  exact GaussianIntegrals.angular_exponential (-α)

def endpointGaussian (a : ℝ) (β z : ℂ) : ℂ :=
  Complex.exp (((-a * ‖z‖ ^ 2 : ℝ) : ℂ) + β * z)

theorem norm_endpointGaussian_le {a : ℝ} (ha : 0 < a) (β z : ℂ) :
    ‖endpointGaussian a β z‖ ≤
      Real.exp (‖β‖ ^ 2 / (2 * a)) * Real.exp (-(a / 2) * ‖z‖ ^ 2) := by
  rw [endpointGaussian, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hr : (β * z).re ≤ ‖β‖ * ‖z‖ := by
    simpa only [norm_mul] using Complex.re_le_norm (β * z)
  have hy : ‖β‖ * ‖z‖ - (a / 2) * ‖z‖ ^ 2 ≤ ‖β‖ ^ 2 / (2 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    nlinarith [sq_nonneg (a * ‖z‖ - ‖β‖)]
  linarith

theorem integrable_endpointGaussian {a : ℝ} (ha : 0 < a) (β : ℂ) :
    Integrable (endpointGaussian a β) := by
  have hc : Continuous (endpointGaussian a β) := by
    unfold endpointGaussian
    fun_prop
  apply ((GaussianIntegrals.integrable_gaussian (by linarith : 0 < a / 2)).const_mul
    (Real.exp (‖β‖ ^ 2 / (2 * a)))).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => norm_endpointGaussian_le ha β z

theorem radial_gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ioi 0, r * Real.exp (-a * r ^ 2)) = 1 / (2 * a) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := a)
    (by norm_num) (by norm_num) ha
  norm_num [Real.rpow_two, Real.rpow_one, Real.rpow_neg_one] at h
  simpa only [neg_mul] using h.trans (by ring)

theorem integrableOn_radial_gaussian {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r * Real.exp (-a * r ^ 2)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [radial_gaussian_integral ha]
  exact one_div_ne_zero (by positivity)

theorem integrableOn_polar_transform {f : ℂ → ℂ} (hc : Continuous f)
    (hi : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hm : Continuous (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) :=
    continuous_fst.smul (hc.comp hp)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hl := Complex.lintegral_comp_polarCoord_symm (fun z : ℂ => ‖f z‖ₑ)
  rw [_root_.polarCoord_target] at hl
  have he : (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
      ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) = ∫⁻ z : ℂ, ‖f z‖ₑ := by
    calc
      (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
          ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) =
          ∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 • ‖f (Complex.polarCoord.symm p)‖ₑ := by
        refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
        intro p hpd
        dsimp only
        rw [enorm_smul, Real.enorm_eq_ofReal hpd.1.le]
        rfl
      _ = _ := hl
  rw [he]
  exact (hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral)

theorem endpointGaussian_polar (a : ℝ) (β : ℂ) (r θ : ℝ) :
    endpointGaussian a β (Complex.polarCoord.symm (r, θ)) =
      Real.exp (-a * r ^ 2) •
        Complex.exp ((β * (r : ℂ)) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [endpointGaussian, Complex.norm_polarCoord_symm, sq_abs,
    Complex.polarCoord_symm_apply, ← Complex.exp_ofReal_mul_I, Complex.exp_add,
    Complex.real_smul, Complex.ofReal_exp]
  congr 1
  congr 1
  ring

theorem angular_exponential_Ioo (α : ℂ) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
      Complex.exp (α * Complex.exp ((θ : ℂ) * Complex.I))) = (2 * Real.pi : ℂ) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  exact angular_exponential_shifted α

theorem integral_endpointGaussian {a : ℝ} (ha : 0 < a) (β : ℂ) :
    (∫ z : ℂ, endpointGaussian a β z) = ((Real.pi / a : ℝ) : ℂ) := by
  let F : (ℝ × ℝ) → ℂ := fun p => p.1 • endpointGaussian a β (Complex.polarCoord.symm p)
  have hc : Continuous (endpointGaussian a β) := by unfold endpointGaussian; fun_prop
  have hi : IntegrableOn F (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) :=
    integrableOn_polar_transform hc (integrable_endpointGaussian ha β)
  have hp : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hi
  have hang (r : ℝ) : (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, F (r, θ)) =
      (r * Real.exp (-a * r ^ 2)) • (2 * Real.pi : ℂ) := by
    dsimp only [F]
    simp_rw [endpointGaussian_polar, smul_smul]
    rw [integral_smul, angular_exponential_Ioo]
  calc
    (∫ z : ℂ, endpointGaussian a β z) =
        ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, F p := by
      have h := Complex.integral_comp_polarCoord_symm (endpointGaussian a β)
      rw [_root_.polarCoord_target] at h
      exact h.symm
    _ = ∫ r : ℝ in Ioi 0, ∫ θ : ℝ in Ioo (-Real.pi) Real.pi, F (r, θ) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact integral_prod F hp
    _ = ∫ r : ℝ in Ioi 0, (r * Real.exp (-a * r ^ 2)) • (2 * Real.pi : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hang
    _ = _ := by
      rw [integral_smul_const, radial_gaussian_integral ha, Complex.real_smul]
      have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      push_cast
      field_simp

end Paper.Trace
