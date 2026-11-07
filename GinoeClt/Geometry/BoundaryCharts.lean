/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

Elementary chart lemmas adapted from QuanyuTang's Apache-2.0 development,
https://github.com/QuanyuTang/polya-neumann-simply-connected-formalization-Palomar-version-v2
at f07f1c7051862ba146429db6eda5dc4e8b020f74,
RequestProject/BoundaryChart.lean and JordanWinding.lean.
Only local Lipschitz graph geometry is used here.
-/
module

public import GinoeClt.Definitions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! # Local boundary charts with Euclidean complex coordinates -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology NNReal

namespace Paper.Geometry

def IsChartAt (Ω : Set ℂ) (p c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ) : Prop :=
  ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ LipschitzWith K f ∧ f 0 = 0 ∧ (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

/-- A local-on-the-interval chart has the same globally Lipschitz chart data. -/
theorem exists_global_chart {A : Set ℂ} {p : ℂ}
    (hlocal : Paper.LipschitzBoundaryChart A p) :
    ∃ (c : ℂ) (r h : ℝ) (K : ℝ≥0) (f : ℝ → ℝ), IsChartAt A p c r h K f := by
  rcases hlocal with ⟨c, r, h, K, f, hc, hr, hh, hf, hf0, hfb, hA⟩
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  refine ⟨c, r, h, K, g, hc, hr, hh, hg, ?_, ?_, ?_⟩
  · rw [← heq (by constructor <;> linarith)]
    exact hf0
  · intro x hx
    rw [← heq (abs_lt.mp hx)]
    exact hfb x hx
  · intro w hx hy
    rw [← heq (abs_lt.mp hx)]
    exact hA w hx hy

/-- In a Lipschitz chart box, points strictly below the graph are not in the closure. -/
lemma chart_notMem_closure {Ω : Set ℂ} {c p : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
    {w : ℂ} (hr : |(c * (w - p)).re| < r) (hh : |(c * (w - p)).im| < h)
    (hlt : (c * (w - p)).im < f (c * (w - p)).re) : w ∉ closure Ω := by
  have hg : Continuous fun v : ℂ => c * (v - p) := by fun_prop
  set U : Set ℂ := {v | |(c * (v - p)).re| < r} ∩ {v | |(c * (v - p)).im| < h} ∩
    {v | (c * (v - p)).im < f (c * (v - p)).re} with hU
  have hUo : IsOpen U := by
    refine ((isOpen_lt ?_ continuous_const).inter (isOpen_lt ?_ continuous_const)).inter
      (isOpen_lt ?_ ?_)
    · exact (Complex.continuous_re.comp hg).abs
    · exact (Complex.continuous_im.comp hg).abs
    · exact Complex.continuous_im.comp hg
    · exact hf.continuous.comp (Complex.continuous_re.comp hg)
  have hdisj : Disjoint U Ω := by
    rw [Set.disjoint_left]
    rintro v ⟨⟨hv1, hv2⟩, hv3⟩ hvΩ
    exact absurd ((hΩ v hv1 hv2).mp hvΩ) (not_lt.mpr hv3.le)
  exact fun hw => Set.disjoint_left.mp (hdisj.closure_right hUo) ⟨⟨hr, hh⟩, hlt⟩ hw

/-- In a Lipschitz chart box, boundary points lie on the graph. -/
lemma chart_frontier_graph {Ω : Set ℂ} (hΩo : IsOpen Ω) {c p : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
    {w : ℂ} (hw : w ∈ frontier Ω) (hr : |(c * (w - p)).re| < r)
    (hh : |(c * (w - p)).im| < h) : (c * (w - p)).im = f (c * (w - p)).re := by
  rw [hΩo.frontier_eq] at hw
  have h1 : (c * (w - p)).im ≤ f (c * (w - p)).re :=
    not_lt.mp fun hlt => hw.2 ((hΩ w hr hh).mpr hlt)
  refine le_antisymm h1 (not_lt.mp fun hlt => ?_)
  exact chart_notMem_closure hf hΩ hr hh hlt hw.1

/-- The graph point of a chart with abscissa `x`. -/
def chartPt (p c : ℂ) (f : ℝ → ℝ) (x : ℝ) : ℂ := p + conj c * ((x : ℂ) + (f x : ℂ) * Complex.I)

lemma mul_chartPt_sub {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    c * (chartPt p c f x - p) = (x : ℂ) + (f x : ℂ) * Complex.I := by
  have : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [chartPt, add_sub_cancel_left, ← mul_assoc, this, one_mul]

lemma re_mul_chartPt_sub {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    (c * (chartPt p c f x - p)).re = x := by
  rw [mul_chartPt_sub hc]; simp

lemma im_mul_chartPt_sub {p c : ℂ} (hc : ‖c‖ = 1) (f : ℝ → ℝ) (x : ℝ) :
    (c * (chartPt p c f x - p)).im = f x := by
  rw [mul_chartPt_sub hc]; simp

lemma chartPt_zero {p c : ℂ} {f : ℝ → ℝ} (hf0 : f 0 = 0) : chartPt p c f 0 = p := by
  simp [chartPt, hf0]

lemma norm_mul_sub {c : ℂ} (hc : ‖c‖ = 1) (w p : ℂ) : ‖c * (w - p)‖ = ‖w - p‖ := by
  rw [norm_mul, hc, one_mul]

/-- A point is determined by its chart coordinates. -/
lemma eq_of_mul_sub_eq {c p w w' : ℂ} (hc : ‖c‖ = 1) (h : c * (w - p) = c * (w' - p)) :
    w = w' := by
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  have := mul_left_cancel₀ hc0 h
  linear_combination this

lemma eq_of_re_im_eq {c p w w' : ℂ} (hc : ‖c‖ = 1) (hre : (c * (w - p)).re = (c * (w' - p)).re)
    (him : (c * (w - p)).im = (c * (w' - p)).im) : w = w' :=
  eq_of_mul_sub_eq hc (Complex.ext hre him)

/-- The graph map of a chart is `(1 + K)`-Lipschitz. -/
lemma lipschitzWith_chartPt {p c : ℂ} (hc : ‖c‖ = 1) {K : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) : LipschitzWith (1 + K) (chartPt p c f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hcc : ‖conj c‖ = 1 := by rw [Complex.norm_conj, hc]
  simp only [chartPt, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hcc, one_mul]
  have h1 : ‖((x : ℂ) + (f x : ℂ) * Complex.I) - ((y : ℂ) + (f y : ℂ) * Complex.I)‖ ≤
      ‖((x - y : ℝ) : ℂ)‖ + ‖((f x - f y : ℝ) : ℂ) * Complex.I‖ := by
    have : ((x : ℂ) + (f x : ℂ) * Complex.I) - ((y : ℂ) + (f y : ℂ) * Complex.I) =
        ((x - y : ℝ) : ℂ) + ((f x - f y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact norm_add_le _ _
  have h2 : |f x - f y| ≤ K * |x - y| := by
    have := hf.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at h1
  push_cast
  rw [Real.norm_eq_abs]
  nlinarith

lemma continuous_chartPt {p c : ℂ} {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (chartPt p c f) := by
  unfold chartPt; fun_prop

/-- The open chart box. -/
def chartBox (p c : ℂ) (r h : ℝ) : Set ℂ :=
  {w | |(c * (w - p)).re| < r ∧ |(c * (w - p)).im| < h}

lemma isOpen_chartBox (p c : ℂ) (r h : ℝ) : IsOpen (chartBox p c r h) := by
  have hg : Continuous fun w : ℂ => c * (w - p) := by fun_prop
  exact (isOpen_lt (Complex.continuous_re.comp hg).abs continuous_const).inter
    (isOpen_lt (Complex.continuous_im.comp hg).abs continuous_const)

/-- A ball around the centre inside the box. -/
lemma ball_subset_chartBox {p c : ℂ} (hc : ‖c‖ = 1) {r h : ℝ} :
    ball p (min r h) ⊆ chartBox p c r h := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hn := norm_mul_sub hc w p
  refine ⟨lt_of_le_of_lt (Complex.abs_re_le_norm _) ?_,
    lt_of_le_of_lt (Complex.abs_im_le_norm _) ?_⟩
  · rw [hn]; exact lt_of_lt_of_le hw (min_le_left _ _)
  · rw [hn]; exact lt_of_lt_of_le hw (min_le_right _ _)

/-- Graph points of a chart are boundary points. -/
lemma chartPt_mem_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {x : ℝ} (hx : |x| < r) :
    chartPt p c f x ∈ frontier Ω := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  rw [hΩo.frontier_eq]
  have hfx := hfb x hx
  refine ⟨?_, ?_⟩
  · -- limit of points above the graph
    rw [mem_closure_iff_nhds]
    intro U hU
    have hcont : Continuous fun s : ℝ => chartPt p c f x + (s : ℂ) * (conj c * Complex.I) := by
      fun_prop
    have ht : Tendsto (fun s : ℝ => chartPt p c f x + (s : ℂ) * (conj c * Complex.I))
        (𝓝[>] 0) (𝓝 (chartPt p c f x)) := by
      have := hcont.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < h - |f x| := by
      have : (0 : ℝ) < h - |f x| := by linarith
      exact eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds this)
    have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, chartPt p c f x + (s : ℂ) * (conj c * Complex.I) ∈ U :=
      ht hU
    obtain ⟨s, hsU, hs, hspos⟩ := (hev.and (hsmall.and self_mem_nhdsWithin)).exists
    refine ⟨_, hsU, ?_⟩
    have hcc : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    have hcoord : c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p) =
        (x : ℂ) + ((f x + s : ℝ) : ℂ) * Complex.I := by
      have := mul_chartPt_sub (p := p) hc f x
      rw [add_sub_right_comm, mul_add, this]
      have h2 : c * ((s : ℂ) * (conj c * Complex.I)) = (s : ℂ) * Complex.I * (c * conj c) := by
        ring
      rw [h2, hcc]; push_cast; ring
    have hre : (c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p)).re = x := by
      rw [hcoord]; simp
    have him : (c * (chartPt p c f x + (s : ℂ) * (conj c * Complex.I) - p)).im = f x + s := by
      rw [hcoord]; simp
    have hspos' : (0 : ℝ) < s := hspos
    have hfx' := abs_lt.mp hfx
    have habs : |f x + s| < h := by
      rw [abs_lt]; constructor
      · linarith
      · linarith [le_abs_self (f x)]
    refine (hΩ _ (by rw [hre]; exact hx) (by rw [him]; exact habs)).mpr ?_
    rw [hre, him]; linarith
  · intro hmem
    have := (hΩ _ (by rw [re_mul_chartPt_sub hc]; exact hx)
      (by rw [im_mul_chartPt_sub hc]; exact hfx)).mp hmem
    rw [re_mul_chartPt_sub hc, im_mul_chartPt_sub hc] at this
    exact lt_irrefl _ this

/-- Boundary points in a chart box are graph points. -/
lemma eq_chartPt_of_frontier {Ω : Set ℂ} (hΩo : IsOpen Ω) {p c : ℂ} {r h : ℝ} {K : NNReal}
    {f : ℝ → ℝ} (hch : IsChartAt Ω p c r h K f) {w : ℂ} (hw : w ∈ frontier Ω)
    (hbox : w ∈ chartBox p c r h) : w = chartPt p c f (c * (w - p)).re := by
  obtain ⟨hc, hr, hh, hf, hf0, hfb, hΩ⟩ := hch
  have hgr := chart_frontier_graph hΩo hf hΩ hw hbox.1 hbox.2
  refine eq_of_re_im_eq (p := p) hc ?_ ?_
  · rw [re_mul_chartPt_sub hc]
  · rw [im_mul_chartPt_sub hc, hgr]

lemma frontier_isCompact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) : IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hb.closure.subset frontier_subset_closure)


end Paper.Geometry
