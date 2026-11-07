/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.PolarCalculus
public import Mathlib.Topology.Order.IntermediateValue

/-! # Full positive-radius solvability of the Lambert polar parameter -/

@[expose] public section
noncomputable section
open Set
open scoped Real

namespace Paper.Lambert

@[simp] theorem polarRadius_zero (θ : ℝ) : polarRadius θ 0 = 0 := by simp [polarRadius]

theorem polarRadius_pos {θ v : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hv : v ∈ Ioo (0 : ℝ) θ) : 0 < polarRadius θ v :=
  mul_pos (div_pos hv.1 (sin_polar_positive hθ hv)) (Real.exp_pos _)

theorem continuousOn_polarRadius_Icc {θ b : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hb : b < θ) : ContinuousOn (polarRadius θ) (Icc (0 : ℝ) b) := by
  intro v hv
  have hs : 0 < Real.sin (θ - v) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hv.2]) (by linarith [hv.1, hθ.2])
  exact (hasDerivAt_polarRadius θ v hs.ne').continuousAt.continuousWithinAt

/-- An explicit finite endpoint exceeds any prescribed positive radius. -/
theorem exists_polarRadius_gt {θ r : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) (hr : 0 < r) :
    ∃ b ∈ Ioo (0 : ℝ) θ, r < polarRadius θ b := by
  let δ := min (θ / 4) (min (Real.pi / 4) (θ / (4 * (r + 1))))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (div_pos hθ.1 (by norm_num))
      (lt_min (div_pos Real.pi_pos (by norm_num)) (div_pos hθ.1 (by positivity)))
  have hδθ : δ ≤ θ / 4 := min_le_left _ _
  have hδπ : δ ≤ Real.pi / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ θ / (4 * (r + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hdr : δ * (4 * (r + 1)) ≤ θ := (le_div_iff₀ (by positivity : 0 < 4 * (r + 1))).mp hδr
  let b := θ - δ
  have hb0 : 0 < b := by dsimp only [b]; linarith [hθ.1]
  have hbθ : b < θ := by dsimp only [b]; linarith
  have hx : θ - b = δ := by dsimp only [b]; ring
  have hs : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos δ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hu : 0 ≤ polarReal θ b := by
    rw [polarReal, hx]
    exact div_nonneg (mul_nonneg hb0.le hc) hs.le
  have he : 1 ≤ Real.exp (polarReal θ b) := Real.one_le_exp_iff.mpr hu
  have hlow : b / Real.sin δ ≤ polarRadius θ b := by
    unfold polarRadius
    rw [hx]
    exact le_mul_of_one_le_right (div_nonneg hb0.le hs.le) he
  have hrs : r * Real.sin δ < b := by
    apply (mul_le_mul_of_nonneg_left (Real.sin_le hδ.le) hr.le).trans_lt
    dsimp only [b]
    nlinarith
  refine ⟨b, ⟨hb0, hbθ⟩, ?_⟩
  exact ((lt_div_iff₀ hs).mpr hrs).trans_le hlow

theorem existsUnique_polarRadius {θ r : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) (hr : 0 < r) :
    ∃! v : ℝ, v ∈ Ioo (0 : ℝ) θ ∧ polarRadius θ v = r := by
  obtain ⟨b, hb, hbr⟩ := exists_polarRadius_gt hθ hr
  obtain ⟨v, hv, hvr⟩ := intermediate_value_Ioo hb.1.le (continuousOn_polarRadius_Icc hθ hb.2)
    ⟨by simpa only [polarRadius_zero] using hr, hbr⟩
  have hvθ : v ∈ Ioo (0 : ℝ) θ := ⟨hv.1, hv.2.trans hb.2⟩
  refine ⟨v, ⟨hvθ, hvr⟩, ?_⟩
  rintro u ⟨hu, hur⟩
  exact (strictMonoOn_polarRadius hθ).injOn hu hvθ (hur.trans hvr.symm)

theorem polarPoint_mem_principalDomain {θ v : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hv : v ∈ Ioo (0 : ℝ) θ) : polarPoint θ v ∈ principalDomain := by
  constructor
  · change |v| < Real.pi
    rw [abs_of_pos hv.1]
    exact hv.2.trans hθ.2
  · have hIm : 0 < (expMul (polarPoint θ v)).im := by
      rw [expMul_polarPoint θ v (sin_polar_positive hθ hv).ne']
      exact mul_pos (polarRadius_pos hθ hv) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    rw [expMul_im] at hIm
    change 0 < Real.exp (polarReal θ v) * v * principalFactor (polarPoint θ v) at hIm
    exact (mul_pos_iff_of_pos_left (mul_pos (Real.exp_pos _) hv.1)).mp hIm

end Paper.Lambert
