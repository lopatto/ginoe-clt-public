/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

The countable sandwich and limiting proof patterns are narrowly adapted from
human-ai-mathematics/kls-lean, revision 33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/Analysis/Graph/Area.lean, lines 624–856 (Apache-2.0).
The differentiability partition is native Mathlib and requires no C¹ assumption.
-/
module

public import GinoeClt.Geometry.GraphAreaPartition

/-! # Exact Euclidean Hausdorff length of a Lipschitz graph -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Paper.Geometry.GraphArea

lemma jacobian_nonneg (a : ℝ) : 0 ≤ jacobian a := norm_nonneg _

lemma jacobian_eq_sqrt (a : ℝ) : jacobian a = Real.sqrt (1 + a ^ 2) := by
  simpa [jacobian] using Complex.norm_add_mul_I 1 a

lemma abs_jacobian_sub_le (a b : ℝ) : |jacobian a - jacobian b| ≤ |a - b| := by
  have heq : ((1 : ℂ) + (a : ℂ) * Complex.I) - (1 + (b : ℂ) * Complex.I) =
      ((a - b : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simpa only [jacobian, heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs] using
    abs_norm_sub_norm_le ((1 : ℂ) + (a : ℂ) * Complex.I) (1 + (b : ℂ) * Complex.I)

lemma continuous_jacobian : Continuous jacobian := by unfold jacobian; fun_prop

lemma measurable_jacobian_deriv (f : ℝ → ℝ) :
    Measurable (fun x => ENNReal.ofReal (jacobian (deriv f x))) :=
  ENNReal.measurable_ofReal.comp (continuous_jacobian.measurable.comp (measurable_deriv f))

lemma continuous_graph {f : ℝ → ℝ} (hf : Continuous f) : Continuous (graph f) := by
  unfold graph; fun_prop

lemma measurableSet_graph_image {f : ℝ → ℝ} (hf : Continuous f) {E : Set ℝ}
    (hE : MeasurableSet E) : MeasurableSet (graph f '' E) :=
  hE.image_of_continuousOn_injOn (continuous_graph hf).continuousOn (graph_injective f).injOn

lemma lipschitzWith_graph {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith (1 + K) (graph f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have heq : graph f x - graph f y =
      ((x - y : ℝ) : ℂ) + ((f x - f y : ℝ) : ℂ) * Complex.I := by
    unfold graph
    push_cast
    ring
  have h1 := norm_add_le ((x - y : ℝ) : ℂ) (((f x - f y : ℝ) : ℂ) * Complex.I)
  have h2 := hf.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at h2
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h1
  rw [dist_eq_norm, heq, Real.dist_eq]
  push_cast at h1 ⊢
  nlinarith

/-- Countable approximation gives two global estimates even without a
continuous derivative. Ordinary derivatives are compared almost everywhere. -/
theorem graph_estimates {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ}
    (hS : MeasurableSet S) (hD : ∀ x ∈ S, DifferentiableAt ℝ f x)
    {ε : ℝ≥0} (hε : 0 < ε) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S) ≤
        ((1 + ε : ℝ≥0) : ℝ≥0∞) *
          ((∫⁻ x in S, ENNReal.ofReal (jacobian (deriv f x))) + ε * volume S) ∧
      (∫⁻ x in S, ENNReal.ofReal (jacobian (deriv f x))) ≤
        ((1 + ε : ℝ≥0) : ℝ≥0∞) *
          (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S) + ε * volume S := by
  obtain ⟨u, a, hum, hud, huu, _, hua, hderiv⟩ := exists_approximating_partition hS hD hε
  let J : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (jacobian (deriv f x))
  have hJm : Measurable J := measurable_jacobian_deriv f
  have himgd : Pairwise (Function.onFun Disjoint (fun n => graph f '' u n)) :=
    fun i j hij => Set.disjoint_image_of_injective (graph_injective f) (hud hij)
  have himgm : ∀ n, MeasurableSet (graph f '' u n) :=
    fun n => measurableSet_graph_image hf (hum n)
  have himg : graph f '' S = ⋃ n, graph f '' u n := by rw [← image_iUnion, huu]
  have hsplitμ : (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S) =
      ∑' n, (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' u n) := by
    rw [himg, measure_iUnion himgd himgm]
  have hsplitI : ∫⁻ x in S, J x = ∑' n, ∫⁻ x in u n, J x := by
    rw [← huu, lintegral_iUnion hum hud]
  have hsplitM : volume S = ∑' n, volume (u n) := by rw [← huu, measure_iUnion hud hum]
  have hJcmp : ∀ n, ∀ᵐ x ∂volume.restrict (u n),
      ENNReal.ofReal (jacobian (a n)) ≤ J x + ε := by
    intro n
    filter_upwards [hderiv n] with x hx
    have hnorm := abs_jacobian_sub_le (a n) (deriv f x)
    have hreal : jacobian (a n) ≤ jacobian (deriv f x) + (ε : ℝ) := by
      rw [abs_sub_comm] at hx
      linarith [(abs_le.mp hnorm).2]
    calc ENNReal.ofReal (jacobian (a n)) ≤
        ENNReal.ofReal (jacobian (deriv f x) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hreal
      _ = J x + ε := by
        rw [ENNReal.ofReal_add (jacobian_nonneg _) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hJcmp' : ∀ n, ∀ᵐ x ∂volume.restrict (u n),
      J x ≤ ENNReal.ofReal (jacobian (a n)) + ε := by
    intro n
    filter_upwards [hderiv n] with x hx
    have hnorm := abs_jacobian_sub_le (deriv f x) (a n)
    have hreal : jacobian (deriv f x) ≤ jacobian (a n) + (ε : ℝ) := by
      linarith [(abs_le.mp hnorm).2]
    calc J x ≤ ENNReal.ofReal (jacobian (a n) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (jacobian (a n)) + ε := by
        rw [ENNReal.ofReal_add (jacobian_nonneg _) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  constructor
  · rw [hsplitμ]
    have hterm : ∀ n,
        (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' u n) ≤
          ((1 + ε : ℝ≥0) : ℝ≥0∞) * ((∫⁻ x in u n, J x) + ε * volume (u n)) := by
      intro n
      have h1 := hausdorffMeasure_graph_le (hua n)
      have h2 : ENNReal.ofReal (jacobian (a n)) * volume (u n) ≤
          (∫⁻ x in u n, J x) + ε * volume (u n) := by
        calc ENNReal.ofReal (jacobian (a n)) * volume (u n) =
            ∫⁻ x in u n, ENNReal.ofReal (jacobian (a n)) := (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in u n, (J x + ε) := lintegral_mono_ae (hJcmp n)
          _ = (∫⁻ x in u n, J x) + ε * volume (u n) := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      exact h1.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (by positivity))
    simpa only [ENNReal.tsum_mul_left, ENNReal.tsum_add, ← hsplitI, ← hsplitM]
      using ENNReal.tsum_le_tsum hterm
  · rw [hsplitI]
    have hterm : ∀ n, (∫⁻ x in u n, J x) ≤
        ((1 + ε : ℝ≥0) : ℝ≥0∞) *
          (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' u n) + ε * volume (u n) := by
      intro n
      have h1 := le_hausdorffMeasure_graph (hua n)
      calc (∫⁻ x in u n, J x) ≤
          ∫⁻ x in u n, (ENNReal.ofReal (jacobian (a n)) + ε) :=
            lintegral_mono_ae (hJcmp' n)
        _ = ENNReal.ofReal (jacobian (a n)) * volume (u n) + ε * volume (u n) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, setLIntegral_const]
        _ ≤ _ := add_le_add h1 le_rfl
    simpa only [ENNReal.tsum_mul_left, ENNReal.tsum_add, ← hsplitμ, ← hsplitM]
      using ENNReal.tsum_le_tsum hterm

private lemma tendsto_one_add :
    Tendsto (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous (fun ε : ℝ≥0 => ((1 + ε : ℝ≥0) : ℝ≥0∞)) :=
    ENNReal.continuous_coe.comp (continuous_const.add continuous_id)
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

private lemma tendsto_small_error {M : ℝ≥0∞} (hM : M ≠ ⊤) :
    Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * M) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
  have hm := ENNReal.Tendsto.mul hc (Or.inr hM) tendsto_const_nhds (Or.inr (by simp))
  simpa using hm

/-- Finite parameter measure permits the approximation error to vanish.
Only continuity and differentiability at the selected points are used here. -/
theorem hausdorffMeasure_graph_of_differentiableAt {f : ℝ → ℝ} (hf : Continuous f)
    {S : Set ℝ} (hS : MeasurableSet S) (hD : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hfin : volume S ≠ ⊤) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S) =
      ∫⁻ x in S, ENNReal.ofReal (jacobian (deriv f x)) := by
  let A : ℝ≥0∞ := (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S)
  let I : ℝ≥0∞ := ∫⁻ x in S, ENNReal.ofReal (jacobian (deriv f x))
  let M : ℝ≥0∞ := volume S
  have herr : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * M) (𝓝[>] 0) (𝓝 0) :=
    tendsto_small_error hfin
  have hest : ∀ ε : ℝ≥0, 0 < ε →
      A ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) * (I + ε * M) ∧
      I ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) * A + ε * M := by
    intro ε hε
    exact graph_estimates hf hS hD hε
  have hupper : Tendsto (fun ε : ℝ≥0 =>
      ((1 + ε : ℝ≥0) : ℝ≥0∞) * (I + ε * M)) (𝓝[>] 0) (𝓝 I) := by
    have hp := ENNReal.Tendsto.mul tendsto_one_add (Or.inl one_ne_zero)
      ((tendsto_const_nhds (x := I) (f := 𝓝[>] (0 : ℝ≥0))).add herr) (Or.inr (by simp))
    simpa using hp
  have hlower : Tendsto (fun ε : ℝ≥0 =>
      ((1 + ε : ℝ≥0) : ℝ≥0∞) * A + ε * M) (𝓝[>] 0) (𝓝 A) := by
    have hp := ENNReal.Tendsto.mul tendsto_one_add (Or.inl one_ne_zero)
      (tendsto_const_nhds (x := A) (f := 𝓝[>] (0 : ℝ≥0))) (Or.inr (by simp))
    simpa using hp.add herr
  apply le_antisymm
  · refine ge_of_tendsto hupper ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hest ε hε).1
  · refine ge_of_tendsto hlower ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hest ε hε).2

/-- Exact Euclidean Hausdorff length of a Lipschitz graph over any measurable
set of finite parameter measure. The nondifferentiability set contributes zero. -/
theorem hausdorffMeasure_graph {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' E) =
      ∫⁻ x in E, ENNReal.ofReal (Real.sqrt (1 + (deriv f x) ^ 2)) := by
  let D : Set ℝ := {x | DifferentiableAt ℝ f x}
  let S : Set ℝ := E ∩ D
  have hDm : MeasurableSet D := measurableSet_of_differentiableAt ℝ f
  have hSm : MeasurableSet S := hE.inter hDm
  have hDae : ∀ᵐ x ∂volume, x ∈ D := hf.ae_differentiableAt
  have hDnull : volume Dᶜ = 0 := mem_ae_iff.mp hDae
  have hbad : volume (E \ D) = 0 := measure_mono_null (fun x hx => hx.2) hDnull
  have hbadimg : (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' (E \ D)) = 0 := by
    have hle := (lipschitzWith_graph hf).hausdorffMeasure_image_le (d := 1) (by norm_num) (E \ D)
    rw [ENNReal.rpow_one, hausdorffMeasure_real, hbad, mul_zero] at hle
    exact le_antisymm hle bot_le
  have himg : (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S) =
      (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' E) := by
    apply measure_eq_measure_of_null_sdiff (Set.image_mono inter_subset_left)
    apply measure_mono_null _ hbadimg
    rintro z ⟨⟨x, hx, rfl⟩, hnot⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hxD
    exact hnot ⟨x, ⟨hx, hxD⟩, rfl⟩
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  have harea := hausdorffMeasure_graph_of_differentiableAt hf.continuous hSm
    (fun x hx => hx.2) hSfin
  have hES : E =ᵐ[volume] S := by
    filter_upwards [hDae] with x hx
    simp [S, hx]
  have hrestrict : volume.restrict E = volume.restrict S := Measure.restrict_congr_set hES
  calc (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' E) =
      (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' S) := himg.symm
    _ = ∫⁻ x in S, ENNReal.ofReal (jacobian (deriv f x)) := harea
    _ = ∫⁻ x in E, ENNReal.ofReal (jacobian (deriv f x)) := by rw [← hrestrict]
    _ = _ := by simp_rw [jacobian_eq_sqrt]

end Paper.Geometry.GraphArea
