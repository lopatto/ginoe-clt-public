/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Definitions
public import GinoeClt.Probability.GaussianTail
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! # Gaussian method of moments on varying probability spaces -/

public section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal

namespace Paper.Probability

theorem memLp_nat_of_integrable_powers {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (k : ℕ) :
    MemLp X k μ := by
  rcases k with _ | k
  · simpa only [Nat.cast_zero] using memLp_zero_iff_aestronglyMeasurable.mpr hX.aestronglyMeasurable
  · apply (integrable_norm_rpow_iff hX.aestronglyMeasurable (by simp) (by simp)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, ← norm_pow] using
      (hint (k + 1)).norm

theorem memLp_id_map_of_integrable_powers {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (hint : ∀ k : ℕ, Integrable (fun ω ↦ X ω ^ k) μ) (k : ℕ) :
    MemLp id k (μ.map X) := by
  apply (memLp_map_measure_iff (by fun_prop) hX).mpr
  exact memLp_nat_of_integrable_powers hX hint k

theorem integral_pow_map {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEMeasurable X μ) (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂μ.map X) = ∫ ω, X ω ^ k ∂μ := by
  rw [integral_map hX (by fun_prop)]

theorem charFun_tendsto_of_gaussian_moments
    (μ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μ n)]
    (v : ℝ≥0) (hLp : ∀ n k : ℕ, MemLp id k (μ n))
    (hmom : ∀ k : ℕ, Tendsto (fun n ↦ ∫ x : ℝ, x ^ k ∂μ n) atTop
      (𝓝 (∫ x : ℝ, x ^ k ∂gaussianReal 0 v))) (t : ℝ) :
    Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun (gaussianReal 0 v) t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := (gaussian_taylor_moment_tendsto_zero v t).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  rcases eventually_atTop.mp hsmall with ⟨N, hN⟩
  let k : ℕ := 2 * N + 1
  have hsmallk := hN k (by dsimp [k]; omega)
  have heven : Even (k + 1) := by
    refine ⟨N + 1, ?_⟩
    dsimp [k]
    omega
  have hnorm (ν : Measure ℝ) :
      (∫ x : ℝ, ‖x‖ ^ (k + 1) ∂ν) = ∫ x : ℝ, x ^ (k + 1) ∂ν := by
    congr 1
    funext x
    rw [Real.norm_eq_abs, heven.pow_abs]
  let R (ν : Measure ℝ) : ℝ :=
    (∫ x : ℝ, ‖x‖ ^ (k + 1) ∂ν) * |t| ^ (k + 1) / (k.factorial : ℝ)
  let Q (ν : Measure ℝ) : ℂ :=
    ∑ j ∈ Finset.range (k + 1),
      (j.factorial : ℂ)⁻¹ * ((t : ℂ) * Complex.I) ^ j *
        (∫ x : ℝ, x ^ j ∂ν : ℝ)
  change R (gaussianReal 0 v) < ε / 4 at hsmallk
  have hR : Tendsto (fun n ↦ R (μ n)) atTop (𝓝 (R (gaussianReal 0 v))) := by
    dsimp only [R]
    simpa only [hnorm] using
      ((hmom (k + 1)).mul_const (|t| ^ (k + 1))).div_const (k.factorial : ℝ)
  have hQ : Tendsto (fun n ↦ Q (μ n)) atTop (𝓝 (Q (gaussianReal 0 v))) := by
    dsimp [Q]
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (hmom j))
  have hRsmall := hR.eventually
    (gt_mem_nhds (show R (gaussianReal 0 v) < R (gaussianReal 0 v) + ε / 4 by linarith))
  have hQsmall := Metric.tendsto_nhds.mp hQ (ε / 4) (by positivity)
  filter_upwards [hRsmall, hQsmall] with n hnR hnQ
  rw [dist_eq_norm] at hnQ ⊢
  have hrn := charFun_taylor_remainder_le (hLp n) k t
  have hrg := charFun_taylor_remainder_le (μ := gaussianReal 0 v)
    (fun j ↦ memLp_id_gaussianReal' (p := (j : ℕ)) (by simp)) k t
  change ‖charFun (μ n) t - Q (μ n)‖ ≤ R (μ n) at hrn
  change ‖charFun (gaussianReal 0 v) t - Q (gaussianReal 0 v)‖ ≤
    R (gaussianReal 0 v) at hrg
  have ht1 := dist_triangle (charFun (μ n) t) (Q (μ n)) (charFun (gaussianReal 0 v) t)
  have ht2 := dist_triangle (Q (μ n)) (Q (gaussianReal 0 v))
    (charFun (gaussianReal 0 v) t)
  simp only [dist_eq_norm] at ht1 ht2
  rw [norm_sub_rev (Q (gaussianReal 0 v)) (charFun (gaussianReal 0 v) t)] at ht2
  linarith

end Paper.Probability

namespace Paper

/-- The Gaussian method of moments is proved, not an external hypothesis. -/
theorem gaussianMomentCriterion : GaussianMomentCriterion := by
  intro Ω mΩ P hP X v _hv hX hint hmom
  have hmuMom : ∀ k : ℕ,
      Tendsto (fun n ↦ ∫ x : ℝ, x ^ k ∂(P n).map (X n)) atTop
        (𝓝 (∫ x : ℝ, x ^ k ∂gaussianReal 0 v)) := by
    intro k
    have heq : (fun n ↦ ∫ x : ℝ, x ^ k ∂(P n).map (X n)) =
        (fun n ↦ ∫ ω, X n ω ^ k ∂P n) := by
      funext n
      exact Probability.integral_pow_map (hX n) k
    rw [heq]
    exact hmom k
  apply TendstoInDistribution.of_tendsto_charFun hX (by fun_prop)
  intro t
  simpa only [Measure.map_id'] using
    Probability.charFun_tendsto_of_gaussian_moments
      (fun n ↦ (P n).map (X n)) v
      (fun n k ↦ Probability.memLp_id_map_of_integrable_powers (hX n) (hint n) k)
      hmuMom t

end Paper
