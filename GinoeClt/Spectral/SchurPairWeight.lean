/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurPairCoordinates
public import GinoeClt.Kernel.Erfc
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The scalar Gaussian weight of a normalized real Schur pair

These are ordinary scalar Lebesgue integrals, with the manuscript's exact erfc
definition. No orthogonal Haar normalization or sector-density theorem is asserted.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace Paper.Spectral

def pairWeightIntegrand (y delta : ℝ) : ℝ :=
  delta / pairRadius y delta * Real.exp (-(delta ^ 2) / 2)

theorem integrable_half_gaussian : Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) := by
  convert! integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
  funext t
  congr 1
  ring

theorem hasDerivAt_pairRadius_delta {y : ℝ} (hy : 0 < y) (delta : ℝ) :
    HasDerivAt (pairRadius y) (delta / pairRadius y delta) delta := by
  have hn : delta ^ 2 + 4 * y ^ 2 ≠ 0 := by
    have hp : 0 < delta ^ 2 + 4 * y ^ 2 := by
      nlinarith only [sq_nonneg delta, sq_pos_of_pos hy]
    exact hp.ne'
  have hh := (((hasDerivAt_id delta).pow 2).add_const (4 * y ^ 2)).sqrt hn
  convert! hh using 1
  norm_num only [Pi.pow_apply, id_eq, pow_one, mul_one]
  change delta / pairRadius y delta = (2 * delta) / (2 * pairRadius y delta)
  field_simp

theorem integrable_pairWeightIntegrand {y : ℝ} (hy : 0 < y) :
    Integrable (pairWeightIntegrand y) := by
  have hr : Continuous (pairRadius y) := by unfold pairRadius; fun_prop
  have hc : Continuous (pairWeightIntegrand y) :=
    (continuous_id.div hr (fun t => (pairRadius_pos (delta := t) hy).ne')).mul (by fun_prop)
  apply integrable_half_gaussian.mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro t
  have hrat : |t / pairRadius y t| ≤ 1 := by
    rw [abs_div, abs_of_pos (pairRadius_pos hy)]
    exact (div_le_one (pairRadius_pos hy)).mpr (pairRadius_gt_abs hy).le
  rw [pairWeightIntegrand, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right hrat (Real.exp_pos _).le).trans_eq (one_mul _)

theorem pairRadius_zero {y : ℝ} (hy : 0 < y) : pairRadius y 0 = 2 * y := by
  unfold pairRadius
  rw [zero_pow (by decide), zero_add, show 4 * y ^ 2 = (2 * y) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

theorem pairWeight_integral_tail {y : ℝ} (hy : 0 < y) :
    (∫ delta in Ioi (0 : ℝ), pairWeightIntegrand y delta) =
      Real.exp (2 * y ^ 2) * ∫ t in Ioi (2 * y), Real.exp (-(t ^ 2) / 2) := by
  have hf : ContinuousOn (pairRadius y) (Ici 0) := by
    apply Continuous.continuousOn
    unfold pairRadius
    fun_prop
  have hft : Tendsto (pairRadius y) atTop atTop :=
    tendsto_atTop_mono
      (fun t => (le_abs_self t).trans (pairRadius_gt_abs (delta := t) hy).le) tendsto_id
  have heq (t : ℝ) :
      Real.exp (-(pairRadius y t ^ 2) / 2) * (t / pairRadius y t) =
        Real.exp (-(2 * y ^ 2)) * pairWeightIntegrand y t := by
    rw [pairRadius_sq, show -(t ^ 2 + 4 * y ^ 2) / 2 = -(2 * y ^ 2) + -(t ^ 2) / 2 by ring,
      Real.exp_add]
    unfold pairWeightIntegrand
    ring
  have hprod : IntegrableOn (fun t => Real.exp (-(pairRadius y t ^ 2) / 2) *
      (t / pairRadius y t)) (Ici 0) := by
    simpa only [heq] using
      ((integrable_pairWeightIntegrand hy).const_mul (Real.exp (-(2 * y ^ 2)))).integrableOn
  have hsub := integral_comp_mul_deriv_Ioi (f := pairRadius y)
    (f' := fun t => t / pairRadius y t) (g := fun t => Real.exp (-(t ^ 2) / 2)) (a := 0)
    hf hft (fun t _ => (hasDerivAt_pairRadius_delta hy t).hasDerivWithinAt)
    (by apply Continuous.continuousOn; fun_prop) integrable_half_gaussian.integrableOn hprod
  simp only [Function.comp_def, heq] at hsub
  rw [integral_const_mul, pairRadius_zero hy] at hsub
  calc
    (∫ t in Ioi (0 : ℝ), pairWeightIntegrand y t) =
        Real.exp (2 * y ^ 2) *
          (Real.exp (-(2 * y ^ 2)) * ∫ t in Ioi (0 : ℝ), pairWeightIntegrand y t) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ = _ := congrArg (fun r : ℝ => Real.exp (2 * y ^ 2) * r) hsub

/-- Exact rescaling to the manuscript's erfc tail, with ordinary scalar
Lebesgue measure and no orthogonal-group volume factor. -/
theorem half_gaussian_tail_erfc (y : ℝ) :
    (∫ t in Ioi (2 * y), Real.exp (-(t ^ 2) / 2)) =
      (Real.sqrt 2 * Real.sqrt Real.pi / 2) * Paper.Kernel.erfc (Real.sqrt 2 * y) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hf (t : ℝ) : Real.exp (-((Real.sqrt 2 * t) ^ 2) / 2) = Real.exp (-(t ^ 2)) := by
    congr 1
    rw [mul_pow, hs2]
    ring
  have hend : Real.sqrt 2 * (Real.sqrt 2 * y) = 2 * y := by
    rw [← mul_assoc, ← pow_two, hs2]
  have hscale := integral_comp_mul_left_Ioi' (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
    (Real.sqrt 2 * y) hs
  simp only [smul_eq_mul, hf, hend] at hscale
  rw [← hscale, Paper.Kernel.erfc]
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

theorem pairWeight_integral_erfc {y : ℝ} (hy : 0 < y) :
    (∫ delta in Ioi (0 : ℝ), pairWeightIntegrand y delta) =
      Real.exp (2 * y ^ 2) * (Real.sqrt 2 * Real.sqrt Real.pi / 2) *
        Paper.Kernel.erfc (Real.sqrt 2 * y) := by
  rw [pairWeight_integral_tail hy, half_gaussian_tail_erfc]
  ring

/-- The complete local pair-coordinate scalar Gaussian integral. Its factor
4*y*delta/s is explicit; no Haar or global Schur Jacobian is being asserted. -/
theorem pairCoordinate_weight_integral {y : ℝ} (hy : 0 < y) (a : ℝ) :
    Integrable (fun delta : ℝ => 4 * y * delta / pairRadius y delta *
      Real.exp (-(a ^ 2 + y ^ 2 + delta ^ 2 / 2))) ∧
      (∫ delta in Ioi (0 : ℝ), 4 * y * delta / pairRadius y delta *
        Real.exp (-(a ^ 2 + y ^ 2 + delta ^ 2 / 2))) =
        2 * Real.sqrt (2 * Real.pi) * y * Real.exp (y ^ 2 - a ^ 2) *
          Paper.Kernel.erfc (Real.sqrt 2 * y) := by
  have heq (delta : ℝ) :
      4 * y * delta / pairRadius y delta *
          Real.exp (-(a ^ 2 + y ^ 2 + delta ^ 2 / 2)) =
        (4 * y * Real.exp (-(a ^ 2 + y ^ 2))) * pairWeightIntegrand y delta := by
    rw [show -(a ^ 2 + y ^ 2 + delta ^ 2 / 2) =
      -(a ^ 2 + y ^ 2) + -(delta ^ 2) / 2 by ring, Real.exp_add]
    unfold pairWeightIntegrand
    ring
  refine ⟨?_, ?_⟩
  · simpa only [heq] using
      (integrable_pairWeightIntegrand hy).const_mul (4 * y * Real.exp (-(a ^ 2 + y ^ 2)))
  · simp_rw [heq]
    rw [integral_const_mul, pairWeight_integral_erfc hy,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have he : Real.exp (-(a ^ 2 + y ^ 2)) * Real.exp (2 * y ^ 2) =
        Real.exp (y ^ 2 - a ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = 2 * Real.sqrt 2 * Real.sqrt Real.pi * y *
          (Real.exp (-(a ^ 2 + y ^ 2)) * Real.exp (2 * y ^ 2)) *
            Paper.Kernel.erfc (Real.sqrt 2 * y) := by ring
      _ = _ := by rw [he]; ring

end Paper.Spectral
