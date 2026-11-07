/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.FirstExit

/-! # Gaussian crossing integrals and free path leaves -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Paper.Trace

def gaussianCrossing (a : ℝ) (A : Set ℂ) : ℝ :=
  ∫ z in A, ∫ w in Aᶜ, Real.exp (-a * ‖w - z‖ ^ 2)

theorem integrable_gaussianCrossing {a : ℝ} (ha : 0 < a) (A : Set ℂ)
    (hA : volume A ≠ ⊤) :
    Integrable (fun p : ℂ × ℂ => Real.exp (-a * ‖p.2 - p.1‖ ^ 2))
      ((volume.restrict A).prod (volume.restrict Aᶜ)) := by
  let F : ℂ × ℂ → ℝ := fun p => Real.exp (-a * ‖p.2 - p.1‖ ^ 2)
  have hc : Continuous F := by dsimp [F]; fun_prop
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun z => (integrable_gaussian_sub ha z).integrableOn
  · have hm : AEStronglyMeasurable (fun z : ℂ => ∫ w in Aᶜ, ‖F (z, w)‖)
        (volume.restrict A) := hc.aestronglyMeasurable.norm.integral_prod_right'
    apply (integrableOn_const (C := Real.pi / a) hA).mono' hm
    filter_upwards with z
    rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
    have he : (fun w : ℂ => ‖F (z, w)‖) =
        (fun w : ℂ => Real.exp (-a * ‖w - z‖ ^ 2)) := by
      funext w
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    rw [he]
    exact (setIntegral_le_integral (integrable_gaussian_sub ha z)
      (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)).trans_eq
        (integral_gaussian_sub ha z)

theorem gaussianCrossing_nonneg (a : ℝ) (A : Set ℂ) : 0 ≤ gaussianCrossing a A :=
  integral_nonneg fun _ => integral_nonneg fun _ => (Real.exp_pos _).le

theorem gaussianCrossing_le {a : ℝ} (ha : 0 < a) (A : Set ℂ) (hA : volume A ≠ ⊤) :
    gaussianCrossing a A ≤ volume.real A * (Real.pi / a) := by
  have hi := (integrable_gaussianCrossing ha A hA).integral_prod_left
  calc
    gaussianCrossing a A ≤ ∫ _z in A, Real.pi / a := by
      apply integral_mono_ae hi (integrableOn_const hA)
      exact Filter.Eventually.of_forall fun z =>
        (setIntegral_le_integral (integrable_gaussian_sub ha z)
          (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)).trans_eq
            (integral_gaussian_sub ha z)
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

end Paper.Trace
