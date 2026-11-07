/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.Domain
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Finite polar calculus for the upper half of the Lambert inverse -/

@[expose] public section
noncomputable section
open Set
open scoped Real

namespace Paper.Lambert

def polarReal (θ v : ℝ) : ℝ := v * Real.cos (θ - v) / Real.sin (θ - v)

def polarRadius (θ v : ℝ) : ℝ :=
  v / Real.sin (θ - v) * Real.exp (polarReal θ v)

def polarPoint (θ v : ℝ) : ℂ := ⟨polarReal θ v, v⟩

def rayPoint (θ r : ℝ) : ℂ := ⟨r * Real.cos θ, r * Real.sin θ⟩

theorem sin_polar_positive {θ v : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hv : v ∈ Ioo (0 : ℝ) θ) : 0 < Real.sin (θ - v) :=
  Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hv.2) (by linarith [hθ.2, hv.1])

theorem hasDerivAt_polarReal (θ v : ℝ) (hs : Real.sin (θ - v) ≠ 0) :
    HasDerivAt (polarReal θ)
      ((Real.sin (θ - v) * Real.cos (θ - v) + v) / Real.sin (θ - v) ^ 2) v := by
  have ha : HasDerivAt (fun t : ℝ => θ - t) (-1) v := by
    simpa [Pi.sub_def, id_eq] using (hasDerivAt_const v θ).sub (hasDerivAt_id v)
  have hc : HasDerivAt (fun t : ℝ => Real.cos (θ - t)) (Real.sin (θ - v)) v := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (θ - v)).comp v ha
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (θ - t)) (-Real.cos (θ - v)) v := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (θ - v)).comp v ha
  have hn := (hasDerivAt_id v).mul hc
  have hh := hn.div hsin hs
  have he :
      (((1 : ℝ) * Real.cos (θ - v) + v * Real.sin (θ - v)) * Real.sin (θ - v) -
          (v * Real.cos (θ - v)) * -Real.cos (θ - v)) / Real.sin (θ - v) ^ 2 =
        (Real.sin (θ - v) * Real.cos (θ - v) + v) / Real.sin (θ - v) ^ 2 := by
    field_simp
    rw [Real.cos_sq']
    ring
  have h := hh.congr_deriv he
  unfold polarReal
  simpa only [Pi.div_apply, Pi.mul_apply, Pi.div_def, Pi.mul_def, id_eq] using h

theorem hasDerivAt_polarRadius (θ v : ℝ) (hs : Real.sin (θ - v) ≠ 0) :
    HasDerivAt (polarRadius θ)
      (Real.exp (polarReal θ v) *
        ((Real.sin (θ - v) + v * Real.cos (θ - v)) ^ 2 +
          v ^ 2 * Real.sin (θ - v) ^ 2) / Real.sin (θ - v) ^ 3) v := by
  have ha : HasDerivAt (fun t : ℝ => θ - t) (-1) v := by
    simpa [Pi.sub_def, id_eq] using (hasDerivAt_const v θ).sub (hasDerivAt_id v)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (θ - t)) (-Real.cos (θ - v)) v := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (θ - v)).comp v ha
  have hdiv := (hasDerivAt_id v).div hsin hs
  have hexp := (hasDerivAt_polarReal θ v hs).exp
  have hh := hdiv.mul hexp
  have h := hh.congr_deriv (g' := Real.exp (polarReal θ v) *
      ((Real.sin (θ - v) + v * Real.cos (θ - v)) ^ 2 +
        v ^ 2 * Real.sin (θ - v) ^ 2) / Real.sin (θ - v) ^ 3) (by
    simp only [Pi.div_apply, id_eq]
    field_simp [hs]
    ring_nf
    rw [Real.cos_sq']
    ring)
  unfold polarRadius
  simpa only [Pi.mul_def, Pi.div_def, id_eq] using h

theorem polarRadius_derivative_pos {θ v : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hv : v ∈ Ioo (0 : ℝ) θ) :
    0 < Real.exp (polarReal θ v) *
      ((Real.sin (θ - v) + v * Real.cos (θ - v)) ^ 2 +
        v ^ 2 * Real.sin (θ - v) ^ 2) / Real.sin (θ - v) ^ 3 := by
  have hs := sin_polar_positive hθ hv
  apply div_pos
  · apply mul_pos (Real.exp_pos _)
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sq_pos_of_pos hv.1) (sq_pos_of_pos hs))
  · exact pow_pos hs _

theorem strictMonoOn_polarRadius {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    StrictMonoOn (polarRadius θ) (Ioo (0 : ℝ) θ) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro v hv
    exact (hasDerivAt_polarRadius θ v (sin_polar_positive hθ hv).ne').continuousAt.continuousWithinAt
  · intro v hv
    have hv' : v ∈ Ioo (0 : ℝ) θ := by simpa only [interior_Ioo] using hv
    rw [(hasDerivAt_polarRadius θ v (sin_polar_positive hθ hv').ne').deriv]
    exact polarRadius_derivative_pos hθ hv'

theorem expMul_polarPoint (θ v : ℝ) (hs : Real.sin (θ - v) ≠ 0) :
    expMul (polarPoint θ v) = rayPoint θ (polarRadius θ v) := by
  have hc : Real.cos θ =
      Real.cos (θ - v) * Real.cos v - Real.sin (θ - v) * Real.sin v := by
    rw [← Real.cos_add]
    congr 1
    ring
  have hsin : Real.sin θ =
      Real.sin (θ - v) * Real.cos v + Real.cos (θ - v) * Real.sin v := by
    rw [← Real.sin_add]
    congr 1
    ring
  apply Complex.ext
  · rw [expMul_re]
    change Real.exp (polarReal θ v) * (polarReal θ v * Real.cos v - v * Real.sin v) =
      polarRadius θ v * Real.cos θ
    rw [hc]
    unfold polarRadius polarReal
    field_simp [hs]
  · rw [expMul, Complex.mul_im, Complex.exp_im, Complex.exp_re]
    change polarReal θ v * (Real.exp (polarReal θ v) * Real.sin v) +
      v * (Real.exp (polarReal θ v) * Real.cos v) = polarRadius θ v * Real.sin θ
    rw [hsin]
    unfold polarRadius polarReal
    field_simp [hs]
    ring

end Paper.Lambert
