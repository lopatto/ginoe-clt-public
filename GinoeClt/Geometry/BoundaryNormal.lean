/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.GraphGaussGreen
public import GinoeClt.Geometry.BoundaryCharts
public import Mathlib.Analysis.Normed.Affine.Isometry

/-! # Actual outward chart normals and rigid-coordinate transport -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ComplexConjugate

namespace Paper.Geometry

lemma unit_mul_conj {c : ℂ} (hc : ‖c‖ = 1) : c * conj c = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  simp

/-- Complex multiplication by a unit-norm scalar as a standard real linear isometry. -/
def unitRotation (c : ℂ) (hc : ‖c‖ = 1) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv :=
    { toFun := fun z => c * z
      invFun := fun z => conj c * z
      left_inv := by intro z; change conj c * (c * z) = z; rw [← mul_assoc, mul_comm (conj c) c, unit_mul_conj hc, one_mul]
      right_inv := by intro z; change c * (conj c * z) = z; rw [← mul_assoc, unit_mul_conj hc, one_mul]
      map_add' := by intro x y; ring
      map_smul' := by intro r z; change c * ((r : ℂ) * z) = (r : ℂ) * (c * z); ring }
  norm_map' := by intro z; change ‖c * z‖ = ‖z‖; rw [norm_mul, hc, one_mul]

/-- Standard epigraph coordinates to the physical chart, with the original rotation convention. -/
def chartAffine (p c : ℂ) (hc : ‖c‖ = 1) : ℂ ≃ᵃⁱ[ℝ] ℂ :=
  (unitRotation (conj c) (by simpa only [Complex.norm_conj] using hc)).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ p)

@[simp] lemma chartAffine_apply (p c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    chartAffine p c hc z = conj c * z + p := by simp [chartAffine, unitRotation]

@[simp] lemma chartAffine_symm_apply (p c : ℂ) (hc : ‖c‖ = 1) (w : ℂ) :
    (chartAffine p c hc).symm w = c * (w - p) := by
  apply (chartAffine p c hc).injective
  rw [(chartAffine p c hc).apply_symm_apply, chartAffine_apply,
    ← mul_assoc, mul_comm (conj c) c, unit_mul_conj hc, one_mul, sub_add_cancel]

lemma chartAffine_coords (p c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    c * (chartAffine p c hc z - p) = z := by
  rw [chartAffine_apply, add_sub_cancel_right, ← mul_assoc, unit_mul_conj hc, one_mul]

lemma chartAffine_graph (p c : ℂ) (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    chartAffine p c hc (GraphArea.graph f x) = chartPt p c f x := by
  rw [chartAffine_apply]
  unfold chartPt GraphArea.graph
  ring

lemma measurePreserving_chartAffine (p c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (chartAffine p c hc) (volume : Measure ℂ) volume :=
  (measurePreserving_add_right (volume : Measure ℂ) p).comp
    (unitRotation (conj c) (by simpa only [Complex.norm_conj] using hc)).measurePreserving

lemma measurePreserving_chartAffine_h1 (p c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (chartAffine p c hc) (Measure.hausdorffMeasure 1 : Measure ℂ)
      (Measure.hausdorffMeasure 1 : Measure ℂ) := by
  refine ⟨(chartAffine p c hc).continuous.measurable, ?_⟩
  have hm := (chartAffine p c hc).isometry.map_hausdorffMeasure (d := 1) (Or.inl (by norm_num))
  simpa only [Set.range_eq_univ.mpr (chartAffine p c hc).surjective, Measure.restrict_univ] using hm

/-- The genuine chart normal. It is defined off the chart as well, solely for
measurability and integration; local Gauss–Green certifies its boundary meaning. -/
def chartNormal (p c : ℂ) (f : ℝ → ℝ) (w : ℂ) : ℂ :=
  conj c * GraphArea.graphNormal f (c * (w - p)).re

lemma measurable_chartNormal (p c : ℂ) (f : ℝ → ℝ) : Measurable (chartNormal p c f) := by
  have hm : Measurable (fun w : ℂ => (c * (w - p)).re) := by fun_prop
  exact measurable_const.mul ((GraphArea.measurable_graphNormal f).comp hm)

lemma chartNormal_norm (p c : ℂ) (hc : ‖c‖ = 1) (f : ℝ → ℝ) (w : ℂ) :
    ‖chartNormal p c f w‖ = 1 := by
  rw [chartNormal, norm_mul, Complex.norm_conj, hc, GraphArea.graphNormal_norm, one_mul]

lemma chartNormal_chartAffine (p c : ℂ) (hc : ‖c‖ = 1) (f : ℝ → ℝ) (z : ℂ) :
    chartNormal p c f (chartAffine p c hc z) = conj c * GraphArea.graphNormal f z.re := by
  rw [chartNormal, chartAffine_coords]

lemma inner_rotation (c u n : ℂ) : inner ℝ (c * u) n = inner ℝ u (conj c * n) := by
  rw [Complex.inner, Complex.inner, map_mul]
  congr 1
  ring

lemma chart_graph_eq_frontier {A : Set ℂ} (hA : IsOpen A) {p c : ℂ} {r h : ℝ}
    {K : ℝ≥0} {f : ℝ → ℝ} (hch : IsChartAt A p c r h K f) :
    chartAffine p c hch.1 '' (GraphArea.graph f '' Ioo (-r) r) = frontier A ∩ chartBox p c r h := by
  ext w
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rw [chartAffine_graph]
    refine ⟨chartPt_mem_frontier hA hch (abs_lt.mpr hx), ?_⟩
    change |(c * (chartPt p c f x - p)).re| < r ∧ |(c * (chartPt p c f x - p)).im| < h
    rw [re_mul_chartPt_sub hch.1, im_mul_chartPt_sub hch.1]
    exact ⟨abs_lt.mpr hx, hch.2.2.2.2.2.1 x (abs_lt.mpr hx)⟩
  · intro hw
    refine ⟨GraphArea.graph f (c * (w - p)).re, ?_, ?_⟩
    · exact ⟨(c * (w - p)).re, abs_lt.mp hw.2.1, rfl⟩
    · rw [chartAffine_graph]
      exact (eq_chartPt_of_frontier hA hch hw.1 hw.2).symm

/-- Scalar Gauss–Green in the actual rotated Lipschitz chart. The test is
localized by its genuine compact support, and the boundary integral uses H¹. -/
theorem integral_chart_eq_boundary_flux {A : Set ℂ} (hA : IsOpen A)
    {p c : ℂ} {r h : ℝ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hch : IsChartAt A p c r h K f) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ chartBox p c r h) (u : ℂ) :
    (∫ w in A, fderiv ℝ φ w u) =
      ∫ w in frontier A, φ w * inner ℝ u (chartNormal p c f w)
        ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
  classical
  let T : ℂ ≃ᵃⁱ[ℝ] ℂ := chartAffine p c hch.1
  let ψ : ℂ → ℝ := fun z => φ (T z)
  let F : ℂ → ℝ := fun w => φ w * inner ℝ u (chartNormal p c f w)
  have hTcd : ContDiff ℝ 1 T := by
    change ContDiff ℝ 1 (fun z : ℂ => chartAffine p c hch.1 z)
    simp_rw [chartAffine_apply]
    fun_prop
  have hψ : ContDiff ℝ 1 ψ := hφ.comp hTcd
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph T.toHomeomorph
  have hD : ∀ z : ℂ, fderiv ℝ ψ z (c * u) = fderiv ℝ φ (T z) u := by
    intro z
    have hdT : HasFDerivAt T
        (unitRotation (conj c) (by simpa only [Complex.norm_conj] using hch.1)).toContinuousLinearEquiv.toContinuousLinearMap z := by
      have hd := ((unitRotation (conj c)
        (by simpa only [Complex.norm_conj] using hch.1)).toContinuousLinearEquiv.hasFDerivAt (x := z)).add_const p
      convert! hd using 1
    have hd := (hφ.differentiable one_ne_zero _).hasFDerivAt.comp z hdT
    have hdψ : fderiv ℝ ψ z = (fderiv ℝ φ (T z)).comp
        (unitRotation (conj c) (by simpa only [Complex.norm_conj] using hch.1)).toContinuousLinearEquiv.toContinuousLinearMap := by
      convert! hd.fderiv using 1
    rw [hdψ, ContinuousLinearMap.comp_apply]
    change fderiv ℝ φ (T z) (conj c * (c * u)) = _
    rw [← mul_assoc, mul_comm (conj c) c, unit_mul_conj hch.1, one_mul]
  have htrace : Function.support (fun x => ψ (GraphArea.graph f x)) ⊆ Ioo (-r) r := by
    intro x hx
    have hb := hsupp (subset_tsupport φ hx)
    have hb' : |x| < r := by
      have hh := hb.1
      rw [chartAffine_coords] at hh
      simpa [GraphArea.graph] using hh
    exact abs_lt.mp hb'
  have hstd := GraphArea.integral_epigraph_eq_graph_flux hch.2.2.2.1 measurableSet_Ioo
    (by simp [Real.volume_Ioo]) hψ hψc htrace (c * u)
  have hdomain : (∫ z in T ⁻¹' A, fderiv ℝ φ (T z) u) =
      ∫ z in GraphArea.epigraph f, fderiv ℝ φ (T z) u := by
    rw [← integral_indicator (hA.measurableSet.preimage T.continuous.measurable),
      ← integral_indicator (GraphArea.isOpen_epigraph hch.2.2.2.1.continuous).measurableSet]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hb : T z ∈ chartBox p c r h
    · have hmem : T z ∈ A ↔ z ∈ GraphArea.epigraph f := by
        have hm := hch.2.2.2.2.2.2 (T z) hb.1 hb.2
        rw [chartAffine_coords] at hm
        exact hm
      simp only [Set.indicator_apply, mem_preimage, hmem]
    · have hn : T z ∉ tsupport φ := fun ht => hb (hsupp ht)
      have hz : fderiv ℝ φ (T z) u = 0 := by rw [fderiv_of_notMem_tsupport ℝ hn]; rfl
      simp [Set.indicator_apply, hz]
  have hlast : (∫ w in frontier A ∩ chartBox p c r h, F w
      ∂(Measure.hausdorffMeasure 1 : Measure ℂ)) =
      ∫ w in frontier A, F w ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
    have hh := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (Measure.hausdorffMeasure 1 : Measure ℂ).restrict (frontier A))
      (s := chartBox p c r h) (f := F) (fun w hw => by
        have hn : w ∉ tsupport φ := fun ht => hw (hsupp ht)
        simp only [F, image_eq_zero_of_notMem_tsupport hn, zero_mul])
    rw [Measure.restrict_restrict (isOpen_chartBox p c r h).measurableSet,
      inter_comm (chartBox p c r h) (frontier A)] at hh
    exact hh
  calc (∫ w in A, fderiv ℝ φ w u) = ∫ z in T ⁻¹' A, fderiv ℝ φ (T z) u :=
      ((measurePreserving_chartAffine p c hch.1).setIntegral_preimage_emb
        T.toHomeomorph.measurableEmbedding _ A).symm
    _ = ∫ z in GraphArea.epigraph f, fderiv ℝ φ (T z) u := hdomain
    _ = ∫ z in GraphArea.epigraph f, fderiv ℝ ψ z (c * u) := by
      apply setIntegral_congr_fun (GraphArea.isOpen_epigraph hch.2.2.2.1.continuous).measurableSet
      intro z _
      exact (hD z).symm
    _ = ∫ z in GraphArea.graph f '' Ioo (-r) r,
        ψ z * inner ℝ (c * u) (GraphArea.graphNormal f z.re)
          ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := hstd
    _ = ∫ z in GraphArea.graph f '' Ioo (-r) r, F (T z)
          ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
      apply setIntegral_congr_fun (GraphArea.measurableSet_graph_image hch.2.2.2.1.continuous measurableSet_Ioo)
      intro z _
      dsimp only [ψ, F, T]
      rw [chartNormal_chartAffine, ← inner_rotation]
    _ = ∫ w in T '' (GraphArea.graph f '' Ioo (-r) r), F w
          ∂(Measure.hausdorffMeasure 1 : Measure ℂ) :=
      ((measurePreserving_chartAffine_h1 p c hch.1).setIntegral_image_emb
        T.toHomeomorph.measurableEmbedding F _).symm
    _ = ∫ w in frontier A ∩ chartBox p c r h, F w
          ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
      rw [show T '' (GraphArea.graph f '' Ioo (-r) r) = frontier A ∩ chartBox p c r h from
        chart_graph_eq_frontier hA hch]
    _ = _ := hlast

end Paper.Geometry
