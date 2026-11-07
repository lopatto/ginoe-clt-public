/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.VarianceSquared
public import GinoeClt.Geometry.PerimeterGaussian

/-! # The Gaussian variance expression and its exact boundary-length limit -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace Paper.Kernel

def gaussianVarianceExpression (A : Set ℂ) (N : ℕ) : ℝ :=
  (N : ℝ) / Real.pi * volume.real A - ((N : ℝ) ^ 2 / Real.pi ^ 2) *
    (∫ z in A, ∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2))

/-- Equation (13): the exact split of the whole-plane Gaussian into A and Aᶜ. -/
lemma gaussian_integral_split {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {N : ℕ} (hN : 0 < N) :
    (∫ z in A, ∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) =
      (Real.pi / (N : ℝ)) * volume.real A - Geometry.gaussianCrossing A 1 N := by
  let μ := (volume : Measure ℂ).restrict A
  let : IsFiniteMeasure μ := isFiniteMeasure_area hA
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcont : Continuous (Function.uncurry (fun z w : ℂ => Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2))) := by fun_prop
  have hprod := integrable_doubleKernel_of_continuous hA hcont
  have hsplit : ∀ z : ℂ, (∫ w in Aᶜ, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) =
      Real.pi / (N : ℝ) - (∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) := by
    intro z
    have hi := (Paper.GaussianIntegrals.integrable_gaussian hn).comp_sub_left z
    have hh := integral_add_compl hA.1.measurableSet hi
    have hfull : (∫ w : ℂ, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) = Real.pi / (N : ℝ) := by
      convert! (integral_sub_left_eq_self (μ := (volume : Measure ℂ))
        (fun u : ℂ => Real.exp (-(N : ℝ) * ‖u‖ ^ 2)) z).trans
          (Paper.GaussianIntegrals.gaussian_mass hn) using 1
    rw [hfull] at hh
    linarith
  have hci : Integrable (fun z : ℂ => ∫ w in Aᶜ, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) μ := by
    have hh := (integrable_const (Real.pi / (N : ℝ)) : Integrable (fun _ : ℂ => Real.pi / (N : ℝ)) μ).sub
      hprod.integral_prod_left
    convert! hh using 1
    ext z
    exact hsplit z
  have hcross : Geometry.gaussianCrossing A 1 N =
      (Real.pi / (N : ℝ)) * volume.real A -
        (∫ z in A, ∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) := by
    change (∫ z in A, ∫ w in Aᶜ, Real.exp (-(1 : ℝ) * (N : ℝ) * ‖z - w‖ ^ 2)) = _
    calc (∫ z in A, ∫ w in Aᶜ, Real.exp (-(1 : ℝ) * (N : ℝ) * ‖z - w‖ ^ 2)) =
        ∫ z in A, Real.pi / (N : ℝ) - (∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) := by
          apply integral_congr_ae
          filter_upwards with z
          convert! hsplit z using 1
          apply integral_congr_ae
          filter_upwards with w
          congr 1
          ring
      _ = _ := by
        rw [integral_sub (f := fun _ : ℂ => Real.pi / (N : ℝ))
          (g := fun z : ℂ => ∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2))
          (integrable_const _) (by convert! hprod.integral_prod_left using 1), integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
  linarith

lemma gaussianVarianceExpression_eq_crossing {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {N : ℕ} (hN : 0 < N) :
    gaussianVarianceExpression A N = ((N : ℝ) ^ 2 / Real.pi ^ 2) * Geometry.gaussianCrossing A 1 N := by
  rw [gaussianVarianceExpression, gaussian_integral_split hA hN]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The boundary-length variance constant for the actual analytic Gaussian
expression. Identifying it with count variance still requires the ensemble law. -/
theorem gaussianVarianceExpression_tendsto {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => gaussianVarianceExpression A N / Real.sqrt (N : ℝ)) atTop
      (𝓝 ((Paper.boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)))) := by
  have hh := (Geometry.unit_gaussian_crossing_tendsto hA).div_const (Real.pi ^ 2)
  have heq : (fun N : ℕ => gaussianVarianceExpression A N / Real.sqrt (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => ((N : ℝ) ^ (3 / 2 : ℝ) * Geometry.gaussianCrossing A 1 N) / Real.pi ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [gaussianVarianceExpression_eq_crossing hA hN]
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
    have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have hr : (N : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt (N : ℝ) ^ 3 := by
      rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) (Nat.cast_nonneg N)]
      exact Real.rpow_natCast _ 3
    rw [hr]
    field_simp
    rw [show Real.sqrt (N : ℝ) ^ 4 = (Real.sqrt (N : ℝ) ^ 2) ^ 2 by ring, hsq]
    ring
  have hout := hh.congr' heq.symm
  convert! hout using 1
  congr 1
  rw [show Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]]
  field_simp
  rw [Real.sq_sqrt Real.pi_pos.le]

end Paper.Kernel
