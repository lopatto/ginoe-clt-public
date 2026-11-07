/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

The scalar [0,1] convolution estimate follows the narrowly adapted proof pattern
in human-ai-mathematics/kls-lean@33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/KLS/Geometry/Perimeter/Mollification.lean:116–142 (Apache-2.0).
-/
module

public import GinoeClt.Geometry.Mollification
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # A concrete smooth approximate identity and genuine L¹ convergence -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap Metric
open scoped NNReal ENNReal Topology Convolution Pointwise

namespace Paper.Geometry

def mollifierBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_right (by norm_num) (by positivity)

def mollifierKernel (n : ℕ) : ℂ → ℝ := (mollifierBump n).normed volume

def smoothIndicator (A : Set ℂ) (n : ℕ) : ℂ → ℝ := mollifiedIndicator A (mollifierKernel n)

lemma mollifierKernel_nonneg (n : ℕ) (x : ℂ) : 0 ≤ mollifierKernel n x :=
  (mollifierBump n).nonneg_normed x

lemma mollifierKernel_contDiff (n : ℕ) : ContDiff ℝ 1 (mollifierKernel n) :=
  (mollifierBump n).contDiff_normed

lemma mollifierKernel_compactSupport (n : ℕ) : HasCompactSupport (mollifierKernel n) :=
  (mollifierBump n).hasCompactSupport_normed

lemma mollifierKernel_integral (n : ℕ) : (∫ x, mollifierKernel n x) = 1 :=
  (mollifierBump n).integral_normed

lemma mollifierBump_rOut_le_two (n : ℕ) : (mollifierBump n).rOut ≤ 2 := by
  change 2 / ((n : ℝ) + 1) ≤ 2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma mollifierBump_rOut_tendsto : Tendsto (fun n => (mollifierBump n).rOut) atTop (𝓝 0) := by
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).const_mul 2
  convert hh using 1
  · ext n
    dsimp [mollifierBump]
    ring
  · simp

lemma indicator_mem_Icc (A : Set ℂ) (x : ℂ) : A.indicator (1 : ℂ → ℝ) x ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ A <;> simp [hx]

lemma smoothIndicator_contDiff {A : Set ℂ} (hA : MeasurableSet A) (n : ℕ) :
    ContDiff ℝ 1 (smoothIndicator A n) := by
  rw [smoothIndicator, mollifiedIndicator_eq_convolution_right]
  exact (mollifierKernel_compactSupport n).contDiff_convolution_right (L := lsmul ℝ ℝ)
    (locallyIntegrable_indicator hA) (mollifierKernel_contDiff n)

lemma smoothIndicator_mem_Icc {A : Set ℂ} (hA : MeasurableSet A) (n : ℕ) (x : ℂ) :
    smoothIndicator A n x ∈ Icc (0 : ℝ) 1 := by
  classical
  let b : ℂ → ℝ := A.indicator 1
  let η : ℂ → ℝ := mollifierKernel n
  have hηi : Integrable η := (mollifierBump n).integrable_normed
  have hb : Measurable b := measurable_one.indicator hA
  have heq : smoothIndicator A n x = ∫ t, b (x - t) * η t := by
    rw [smoothIndicator, mollifiedIndicator_eq_convolution_right, convolution_eq_swap]
    rfl
  have hint : Integrable (fun t => b (x - t) * η t) := by
    refine hηi.mono' ((hb.comp (measurable_const.sub measurable_id)).mul
      (mollifierKernel_contDiff n).continuous.measurable).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (indicator_mem_Icc A (x - t)).1,
      abs_of_nonneg (mollifierKernel_nonneg n t)]
    exact mul_le_of_le_one_left (mollifierKernel_nonneg n t) (indicator_mem_Icc A (x - t)).2
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact integral_nonneg (fun t => mul_nonneg (indicator_mem_Icc A (x - t)).1 (mollifierKernel_nonneg n t))
  · rw [heq]
    calc (∫ t, b (x - t) * η t) ≤ ∫ t, η t :=
        integral_mono hint hηi (fun t => mul_le_of_le_one_left (mollifierKernel_nonneg n t)
          (indicator_mem_Icc A (x - t)).2)
      _ = 1 := mollifierKernel_integral n

lemma smoothIndicator_support_bound {A : Set ℂ} {R : ℝ}
    (hR : ∀ x ∈ A, ‖x‖ ≤ R) (n : ℕ) {x : ℂ} (hx : smoothIndicator A n x ≠ 0) :
    ‖x‖ ≤ R + 2 := by
  classical
  have hs : x ∈ Function.support (A.indicator (1 : ℂ → ℝ) ⋆[lsmul ℝ ℝ, volume] mollifierKernel n) := by
    rw [← mollifiedIndicator_eq_convolution_right]
    exact hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp (support_convolution_subset (lsmul ℝ ℝ) hs)
  have hyA : y ∈ A := by
    by_contra hn
    exact hy (by simp [hn])
  have hz' : ‖z‖ ≤ 2 := by
    have hh : z ∈ ball (0 : ℂ) (mollifierBump n).rOut := by
      rwa [← (mollifierBump n).support_normed_eq (μ := volume)]
    have hzlt : ‖z‖ < (mollifierBump n).rOut := by
      simpa only [mem_ball, dist_zero_right] using hh
    exact hzlt.le.trans (mollifierBump_rOut_le_two n)
  exact (norm_add_le _ _).trans (by linarith [hR y hyA])

lemma smoothIndicator_hasCompactSupport {A : Set ℂ} (hb : Bornology.IsBounded A) (n : ℕ) :
    HasCompactSupport (smoothIndicator A n) := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℂ)
  have hs : Function.support (smoothIndicator A n) ⊆ closedBall (0 : ℂ) (R + 2) := by
    intro x hx
    simp only [mem_closedBall, dist_zero_right]
    exact smoothIndicator_support_bound (fun y hy => by simpa [mem_closedBall] using hR hy) n hx
  exact IsCompact.of_isClosed_subset (isCompact_closedBall _ _) isClosed_closure
    (closure_minimal hs isClosed_closedBall)

lemma smoothIndicator_ae_tendsto {A : Set ℂ} (hA : MeasurableSet A) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothIndicator A n x) atTop
      (𝓝 (A.indicator (1 : ℂ → ℝ) x)) := by
  have hratio : ∀ᶠ n : ℕ in atTop, (mollifierBump n).rOut ≤ 2 * (mollifierBump n).rIn := by
    filter_upwards with n
    dsimp [mollifierBump]
    ring_nf
    exact le_rfl
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure ℂ)) (φ := mollifierBump) mollifierBump_rOut_tendsto hratio
      (locallyIntegrable_indicator hA)
  simpa only [smoothIndicator, mollifierKernel, mollifiedIndicator_eq_convolution_left] using hh

/-- Genuine L¹ convergence follows from the native a.e. approximate identity
and a common finite-ball dominator. No boundary-volume-null premise is used. -/
theorem smoothIndicator_l1_tendsto {A : Set ℂ} (hA : MeasurableSet A) (hb : Bornology.IsBounded A) :
    Tendsto (fun n => ∫ x, |smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x|) atTop (𝓝 0) := by
  classical
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℂ)
  have hRn : ∀ x ∈ A, ‖x‖ ≤ R := fun x hx => by simpa [mem_closedBall] using hR hx
  let B : Set ℂ := closedBall 0 (R + 2)
  let bound : ℂ → ℝ := B.indicator 1
  have hbi : Integrable bound := by
    rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
    exact integrableOn_const (isCompact_closedBall (0 : ℂ) (R + 2)).measure_lt_top.ne
  have hbm : Measurable (A.indicator (1 : ℂ → ℝ)) := measurable_one.indicator hA
  have hFm : ∀ n, AEStronglyMeasurable (fun x => |smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x|) volume :=
    fun n => (continuous_abs.measurable.comp ((smoothIndicator_contDiff hA n).continuous.measurable.sub hbm)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂volume, ‖|smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x|‖ ≤ bound x := by
    intro n
    filter_upwards with x
    have hi := smoothIndicator_mem_Icc hA n x
    have hj := indicator_mem_Icc A x
    have hab : |smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]
    by_cases hxB : x ∈ B
    · simpa only [bound, Set.indicator_of_mem hxB, Pi.one_apply, Real.norm_eq_abs, abs_abs] using hab
    · have hm0 : smoothIndicator A n x = 0 := by
        by_contra hn
        exact hxB (by simpa only [B, mem_closedBall, dist_zero_right] using smoothIndicator_support_bound hRn n hn)
      have hb0 : A.indicator (1 : ℂ → ℝ) x = 0 := by
        apply Set.indicator_of_notMem
        intro hxA
        apply hxB
        simp only [B, mem_closedBall, dist_zero_right]
        linarith [hRn x hxA]
      simp only [hm0, hb0, sub_self, abs_zero, norm_zero, bound, Set.indicator_of_notMem hxB]
      exact le_rfl
  have hlim : ∀ᵐ x ∂volume, Tendsto
      (fun n => |smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [smoothIndicator_ae_tendsto hA] with x hx
    have hh : Tendsto (fun n => smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x) atTop (𝓝 0) := by
      simpa using hx.sub (tendsto_const_nhds (x := A.indicator (1 : ℂ → ℝ) x))
    simpa only [Real.norm_eq_abs, norm_zero] using hh.norm
  have hh := tendsto_integral_of_dominated_convergence (f := fun _ : ℂ => (0 : ℝ)) bound hFm hbi hbound hlim
  simpa using hh

end Paper.Geometry
