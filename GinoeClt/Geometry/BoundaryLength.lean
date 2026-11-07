/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.BoundaryCharts
public import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Finite positive Euclidean boundary length -/

public section
open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace Paper.Geometry

theorem lipschitz_chartProjection (c p : ℂ) (hc : ‖c‖ = 1) :
    LipschitzWith 1 (fun w : ℂ ↦ (c * (w - p)).re) := by
  refine LipschitzWith.of_dist_le_mul fun w v ↦ ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  have hre : (c * (w - p)).re - (c * (v - p)).re = (c * (w - v)).re := by
    rw [← Complex.sub_re]
    congr 1
    ring
  rw [hre, dist_eq_norm]
  exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hc, one_mul])

theorem chart_boundary_measure_lt_top {A : Set ℂ} (hA : IsOpen A)
    {p c : ℂ} {r h : ℝ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hch : IsChartAt A p c r h K f) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A ∩ chartBox p c r h) < ⊤ := by
  have hsub : frontier A ∩ chartBox p c r h ⊆
      chartPt p c f '' Ioo (-r) r := by
    intro w hw
    refine ⟨(c * (w - p)).re, abs_lt.mp hw.2.1, ?_⟩
    exact (eq_chartPt_of_frontier hA hch hw.1 hw.2).symm
  apply lt_of_le_of_lt (measure_mono hsub)
  have hLip := lipschitzWith_chartPt (p := p) hch.1 hch.2.2.2.1
  apply lt_of_le_of_lt (hLip.hausdorffMeasure_image_le (d := 1) (by norm_num) _)
  rw [ENNReal.rpow_one, hausdorffMeasure_real]
  exact ENNReal.mul_lt_top (by simp) (by simp [Real.volume_Ioo])

theorem chart_boundary_measure_pos {A : Set ℂ} (hA : IsOpen A)
    {p c : ℂ} {r h : ℝ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hch : IsChartAt A p c r h K f) :
    0 < (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) := by
  have hsub : Ioo (-r) r ⊆
      (fun w : ℂ ↦ (c * (w - p)).re) '' frontier A := by
    intro x hx
    refine ⟨chartPt p c f x, chartPt_mem_frontier hA hch (abs_lt.mpr hx), ?_⟩
    exact re_mul_chartPt_sub hch.1 f x
  have hinterval : 0 < (Measure.hausdorffMeasure 1 : Measure ℝ) (Ioo (-r) r) := by
    rw [hausdorffMeasure_real, Real.volume_Ioo]
    apply ENNReal.ofReal_pos.mpr
    linarith [hch.2.1]
  have hbound := (lipschitz_chartProjection c p hch.1).hausdorffMeasure_image_le
    (d := 1) (by norm_num) (frontier A)
  have hle : (Measure.hausdorffMeasure 1 : Measure ℝ) (Ioo (-r) r) ≤
      (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) :=
    (measure_mono hsub).trans (by simpa using hbound)
  exact hinterval.trans_le hle

theorem boundary_measure_lt_top_of_charts {A : Set ℂ} (hA : IsOpen A)
    (hb : Bornology.IsBounded A)
    (hcharts : ∀ p ∈ frontier A, Paper.LipschitzBoundaryChart A p) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) < ⊤ := by
  classical
  choose c r h K f hch using
    (fun p : frontier A ↦ exists_global_chart (hcharts p p.property))
  let U (p : frontier A) : Set ℂ := chartBox p (c p) (r p) (h p)
  have hU : ∀ p, IsOpen (U p) := fun p ↦ isOpen_chartBox _ _ _ _
  have hcover : frontier A ⊆ ⋃ p : frontier A, U p := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    change |(c ⟨p, hp⟩ * (p - p)).re| < r ⟨p, hp⟩ ∧
      |(c ⟨p, hp⟩ * (p - p)).im| < h ⟨p, hp⟩
    simpa only [sub_self, mul_zero, Complex.zero_re, Complex.zero_im, abs_zero] using
      And.intro (hch ⟨p, hp⟩).2.1 (hch ⟨p, hp⟩).2.2.1
  obtain ⟨t, ht⟩ := (frontier_isCompact hb).elim_finite_subcover U hU hcover
  let V (p : frontier A) : Set ℂ := frontier A ∩ U p
  have hcover' : frontier A ⊆ ⋃ p ∈ t, V p := by
    intro p hp
    rcases mem_iUnion.mp (ht hp) with ⟨q, hq⟩
    rcases mem_iUnion.mp hq with ⟨hqt, hpU⟩
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hqt, hp, hpU⟩⟩
  calc
    _ ≤ (Measure.hausdorffMeasure 1 : Measure ℂ) (⋃ p ∈ t, V p) :=
      measure_mono hcover'
    _ ≤ ∑ p ∈ t, (Measure.hausdorffMeasure 1 : Measure ℂ) (V p) :=
      measure_biUnion_finset_le t V
    _ < ⊤ := ENNReal.sum_lt_top.mpr
      (fun p _ ↦ chart_boundary_measure_lt_top hA (hch p))

end Paper.Geometry

namespace Paper

theorem admissible_isBounded {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    Bornology.IsBounded A := by
  have hsub : A ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hnorm := (hA.2.2.1 (subset_closure hz)).1
    simpa only [Metric.mem_ball, dist_zero_right] using hnorm
  exact Metric.isBounded_ball.subset hsub

/-- Finiteness and strict positivity are conclusions from the domain hypotheses. -/
theorem boundaryLengthRegular_of_admissible {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) : BoundaryLengthRegular A := by
  have hfinite : boundaryMeasure A < ⊤ :=
    Geometry.boundary_measure_lt_top_of_charts hA.1 (admissible_isBounded hA) hA.2.2.2
  have hnotuniv : A ≠ Set.univ := by
    intro h
    have hbad := (hA.2.2.1 (by simp [h] : (0 : ℂ) ∈ closure A)).2
    simp at hbad
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨hA.2.1.nonempty, hnotuniv⟩
  obtain ⟨c, r, h, K, f, hch⟩ := Geometry.exists_global_chart (hA.2.2.2 p hp)
  have hpos : 0 < boundaryMeasure A := Geometry.chart_boundary_measure_pos hA.1 hch
  refine ⟨(boundaryMeasure A).toNNReal, ENNReal.coe_toNNReal hfinite.ne, ?_⟩
  exact ENNReal.toNNReal_pos hpos.ne' hfinite.ne

end Paper
