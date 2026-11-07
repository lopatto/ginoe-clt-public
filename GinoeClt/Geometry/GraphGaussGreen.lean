/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

The compact-support comparison is narrowly adapted from
human-ai-mathematics/kls-lean, revision 33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/Analysis/Graph/Divergence.lean:244–269 (Apache-2.0).
-/
module

public import GinoeClt.Geometry.GraphMeasure
public import GinoeClt.Geometry.GraphShear
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Scalar Gauss–Green on an actual Lipschitz epigraph -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Paper.Geometry.GraphArea

lemma hasCompactSupport_comp_of_norm_le {F : ℂ → ℝ} (hF : HasCompactSupport F)
    {γ : ℝ → ℂ} (C : ℝ) (hle : ∀ x, ‖x‖ ≤ C + ‖γ x‖) :
    HasCompactSupport (fun x => F (γ x)) := by
  obtain ⟨M, hM⟩ := hF.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hsub : Function.support (fun x => F (γ x)) ⊆ Metric.closedBall (0 : ℝ) (C + M) := by
    intro x hx
    have hγ : γ x ∈ tsupport F := subset_tsupport _ hx
    have hnorm : ‖γ x‖ ≤ M := by simpa [Metric.mem_closedBall] using hM hγ
    have hbound := hle x
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ) (C + M))
    isClosed_closure (closure_minimal hsub Metric.isClosed_closedBall)

/-- The derivative of any compactly supported real Lipschitz function integrates
to zero. This is the native absolutely-continuous FTC, not a C¹ specialization. -/
theorem integral_deriv_lipschitz_eq_zero {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hgc : HasCompactSupport g) : ∫ x, deriv g x = 0 := by
  obtain ⟨M, hM⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let R : ℝ := max M 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right M 0]
  have hnot : ∀ x : ℝ, R ≤ |x| → x ∉ tsupport g := by
    intro x hx hmem
    have hbound : |x| ≤ M := by simpa [Metric.mem_closedBall, Real.dist_eq] using hM hmem
    dsimp [R] at hx
    linarith [le_max_left M 0]
  have hzero : g R = 0 ∧ g (-R) = 0 := by
    constructor
    · exact image_eq_zero_of_notMem_tsupport (hnot R (by rw [abs_of_pos hR]))
    · exact image_eq_zero_of_notMem_tsupport (hnot (-R) (by rw [abs_neg, abs_of_pos hR]))
  have hint : (∫ x, deriv g x) = ∫ x in (-R)..R, deriv g x := by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply deriv_of_notMem_tsupport
    apply hnot
    by_contra! hsmall
    apply hx
    exact ⟨(abs_lt.mp hsmall).1, (abs_lt.mp hsmall).2.le⟩
  rw [hint, (hg.lipschitzOnWith (s := uIcc (-R) R)).absolutelyContinuousOnInterval.integral_deriv_eq_sub,
    hzero.1, hzero.2, sub_self]

lemma graphShear_fibre {f : ℝ → ℝ} (hf : Continuous f) (x t : ℝ) :
    graphShear hf (x, t) = graph f x + (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [graph, add_comm]

lemma graphShear_fibre_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => graphShear hf (x, s)) Complex.I t := by
  simp_rw [graphShear_fibre]
  change HasDerivAt (fun s : ℝ => graph f x + s • Complex.I) Complex.I t
  convert! (((hasDerivAt_id t).smul_const Complex.I).const_add (graph f x)) using 1; simp

lemma hasCompactSupport_graphShear_fibre {f : ℝ → ℝ} (hf : Continuous f)
    {ψ : ℂ → ℝ} (hψc : HasCompactSupport ψ) (x : ℝ) :
    HasCompactSupport (fun t : ℝ => ψ (graphShear hf (x, t))) := by
  apply hasCompactSupport_comp_of_norm_le hψc ‖graph f x‖
  intro t
  have heq : (t : ℂ) * Complex.I = graphShear hf (x, t) - graph f x := by
    rw [graphShear_fibre, add_sub_cancel_left]
  calc ‖t‖ = ‖(t : ℂ) * Complex.I‖ := by simp
    _ = ‖graphShear hf (x, t) - graph f x‖ := by rw [heq]
    _ ≤ ‖graphShear hf (x, t)‖ + ‖graph f x‖ := norm_sub_le _ _
    _ = _ := add_comm _ _

lemma integrable_fderiv_test {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (v : ℂ) : Integrable (fun z => fderiv ℝ ψ z v) := by
  have hc : Continuous (fun z => fderiv ℝ ψ z v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp (hψ.continuous_fderiv one_ne_zero)
  exact hc.integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ v)

lemma integral_fibre_vertical {f : ℝ → ℝ} (hf : Continuous f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), fderiv ℝ ψ (graphShear hf (x, t)) Complex.I) =
      - ψ (graph f x) := by
  have hpath : ContDiff ℝ 1 (fun t : ℝ => graphShear hf (x, t)) := by
    simp_rw [graphShear_fibre]
    change ContDiff ℝ 1 (fun t : ℝ => graph f x + t • Complex.I)
    fun_prop
  have hslice : ContDiff ℝ 1 (fun t : ℝ => ψ (graphShear hf (x, t))) := hψ.comp hpath
  have hd : ∀ t : ℝ, deriv (fun s => ψ (graphShear hf (x, s))) t =
      fderiv ℝ ψ (graphShear hf (x, t)) Complex.I := by
    intro t
    exact ((hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
      (graphShear_fibre_hasDerivAt hf x t)).deriv
  calc (∫ t in Ioi (0 : ℝ), fderiv ℝ ψ (graphShear hf (x, t)) Complex.I) =
      ∫ t in Ioi (0 : ℝ), deriv (fun s => ψ (graphShear hf (x, s))) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        exact (hd t).symm
    _ = - ψ (graphShear hf (x, 0)) :=
      HasCompactSupport.integral_Ioi_deriv_eq hslice (hasCompactSupport_graphShear_fibre hf hψc x) 0
    _ = _ := by rw [graphShear_zero]

/-- The vertical boundary identity on the open upper epigraph; continuity of
the graph height suffices for this component. -/
theorem integral_epigraph_vertical {f : ℝ → ℝ} (hf : Continuous f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    (∫ z in epigraph f, fderiv ℝ ψ z Complex.I) = - ∫ x, ψ (graph f x) := by
  have hint : Integrable (fun p : ℝ × ℝ => fderiv ℝ ψ (graphShear hf p) Complex.I) :=
    (measurePreserving_graphShear hf).integrable_comp_of_integrable
      (integrable_fderiv_test hψ hψc Complex.I)
  have hFTC := integral_fibre_vertical hf hψ hψc
  rw [← setIntegral_epigraph hf (fun z => fderiv ℝ ψ z Complex.I), Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint.integrableOn), setIntegral_univ]
  simp_rw [hFTC]
  exact integral_neg _

lemma hasCompactSupport_graphShear_slice {f : ℝ → ℝ} (hf : Continuous f)
    {ψ : ℂ → ℝ} (hψc : HasCompactSupport ψ) (t : ℝ) :
    HasCompactSupport (fun x : ℝ => ψ (graphShear hf (x, t))) := by
  apply hasCompactSupport_comp_of_norm_le hψc 0
  intro x
  simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (graphShear hf (x, t))

lemma graphShear_slice_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f)
    (t x : ℝ) (hx : DifferentiableAt ℝ f x) :
    HasDerivAt (fun y : ℝ => graphShear hf (y, t))
      ((1 : ℂ) + ((deriv f x : ℝ) : ℂ) * Complex.I) x := by
  have hre : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
    convert! Complex.ofRealCLM.hasFDerivAt.hasDerivAt using 1
  have hfi : HasDerivAt (fun y : ℝ => (f y : ℂ)) ((deriv f x : ℝ) : ℂ) x := by
    convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt using 1
  have hd := (hre.add (hfi.mul_const Complex.I)).add_const ((t : ℂ) * Complex.I)
  convert! hd using 1
  funext y
  rw [graphShear_fibre]
  rfl

lemma ae_deriv_graphShear_slice {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (t : ℝ) :
    ∀ᵐ x ∂volume, deriv (fun y => ψ (graphShear hf.continuous (y, t))) x =
      fderiv ℝ ψ (graphShear hf.continuous (x, t)) 1 +
        deriv f x * fderiv ℝ ψ (graphShear hf.continuous (x, t)) Complex.I := by
  filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
  have hd := (hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt x
    (graphShear_slice_hasDerivAt hf.continuous t x hx)
  calc deriv (fun y => ψ (graphShear hf.continuous (y, t))) x =
      fderiv ℝ ψ (graphShear hf.continuous (x, t))
        (1 + ((deriv f x : ℝ) : ℂ) * Complex.I) := by convert! hd.deriv using 1
    _ = _ := by
      change (fderiv ℝ ψ (graphShear hf.continuous (x, t))) (1 + deriv f x • Complex.I) = _
      rw [map_add, map_smul, smul_eq_mul]

lemma integral_tangential_slice_eq_zero {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (t : ℝ) :
    (∫ x, fderiv ℝ ψ (graphShear hf.continuous (x, t)) 1 +
      deriv f x * fderiv ℝ ψ (graphShear hf.continuous (x, t)) Complex.I) = 0 := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero
  have hpath : LipschitzWith (1 + K) (fun x => graphShear hf.continuous (x, t)) := by
    simpa only [add_zero, graphShear_fibre] using
      (lipschitzWith_graph hf).add (LipschitzWith.const ((t : ℂ) * Complex.I))
  calc (∫ x, fderiv ℝ ψ (graphShear hf.continuous (x, t)) 1 +
        deriv f x * fderiv ℝ ψ (graphShear hf.continuous (x, t)) Complex.I) =
      ∫ x, deriv (fun y => ψ (graphShear hf.continuous (y, t))) x :=
        by
          apply integral_congr_ae
          filter_upwards [ae_deriv_graphShear_slice hf hψ t] with x hx
          exact hx.symm
    _ = 0 := integral_deriv_lipschitz_eq_zero (hL.comp hpath)
      (hasCompactSupport_graphShear_slice hf.continuous hψc t)

/-- The horizontal identity uses the ordinary derivative of the Lipschitz
height only almost everywhere; all Fubini steps have proved integrability. -/
theorem integral_epigraph_horizontal {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    (∫ z in epigraph f, fderiv ℝ ψ z 1) = ∫ x, deriv f x * ψ (graph f x) := by
  let X : ℝ × ℝ → ℝ := fun p => fderiv ℝ ψ (graphShear hf.continuous p) 1
  let Y : ℝ × ℝ → ℝ := fun p => fderiv ℝ ψ (graphShear hf.continuous p) Complex.I
  let P : ℝ × ℝ → ℝ := fun p => deriv f p.1 * Y p
  have hX : Integrable X := (measurePreserving_graphShear hf.continuous).integrable_comp_of_integrable
    (integrable_fderiv_test hψ hψc 1)
  have hY : Integrable Y := (measurePreserving_graphShear hf.continuous).integrable_comp_of_integrable
    (integrable_fderiv_test hψ hψc Complex.I)
  have hP : Integrable P := hY.bdd_mul
    ((measurable_deriv f).comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun p => norm_deriv_le_of_lipschitz hf))
  have hA : Integrable (fun p => X p + P p) := hX.add hP
  have hmeq : (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi (0 : ℝ)) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hAr : Integrable (fun p => X p + P p)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    rw [← hmeq]
    exact hA.integrableOn
  have hAzero : (∫ p in univ ×ˢ Ioi (0 : ℝ), X p + P p) = 0 := by
    rw [hmeq, integral_prod_symm _ hAr]
    have hz : ∀ t : ℝ, (∫ x, X (x, t) + P (x, t)) = 0 :=
      integral_tangential_slice_eq_zero hf hψ hψc
    simp_rw [hz]
    simp
  have hPvalue : (∫ p in univ ×ˢ Ioi (0 : ℝ), P p) =
      - ∫ x, deriv f x * ψ (graph f x) := by
    rw [Measure.volume_eq_prod, setIntegral_prod _
      (by rw [← Measure.volume_eq_prod]; exact hP.integrableOn), setIntegral_univ]
    change (∫ x, ∫ t in Ioi (0 : ℝ), deriv f x *
      fderiv ℝ ψ (graphShear hf.continuous (x, t)) Complex.I) = _
    simp_rw [integral_const_mul, integral_fibre_vertical hf.continuous hψ hψc, mul_neg]
    exact integral_neg _
  have hsum : (∫ p in univ ×ˢ Ioi (0 : ℝ), X p + P p) =
      (∫ p in univ ×ˢ Ioi (0 : ℝ), X p) + (∫ p in univ ×ˢ Ioi (0 : ℝ), P p) :=
    integral_add hX.integrableOn hP.integrableOn
  have hXvalue : (∫ p in univ ×ˢ Ioi (0 : ℝ), X p) = ∫ z in epigraph f, fderiv ℝ ψ z 1 :=
    setIntegral_epigraph hf.continuous (fun z : ℂ => fderiv ℝ ψ z 1)
  rw [hAzero, hPvalue, hXvalue] at hsum
  linarith

lemma integrable_graph_test {f : ℝ → ℝ} (hf : Continuous f)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => ψ (graph f x)) := by
  have hs : HasCompactSupport (fun x => ψ (graph f x)) := by
    simpa only [graphShear_zero] using hasCompactSupport_graphShear_slice hf hψc 0
  exact (hψ.comp (continuous_graph hf)).integrable_of_hasCompactSupport hs

/-- The full scalar directional identity before normal normalization. -/
theorem integral_epigraph_direction {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (u : ℂ) :
    (∫ z in epigraph f, fderiv ℝ ψ z u) =
      ∫ x, ψ (graph f x) * (deriv f x * u.re - u.im) := by
  have hu : u = u.re • (1 : ℂ) + u.im • Complex.I := by apply Complex.ext <;> simp
  have hfun : (fun z => fderiv ℝ ψ z u) = fun z =>
      u.re * fderiv ℝ ψ z 1 + u.im * fderiv ℝ ψ z Complex.I := by
    funext z
    conv_lhs => rw [hu]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : Integrable (fun x => ψ (graph f x)) := integrable_graph_test hf.continuous hψ.continuous hψc
  have hfg : Integrable (fun x => deriv f x * ψ (graph f x)) :=
    hg.bdd_mul (measurable_deriv f).aestronglyMeasurable
      (ae_of_all _ (fun _ => norm_deriv_le_of_lipschitz hf))
  rw [hfun, integral_add
    ((integrable_fderiv_test hψ hψc 1).const_mul u.re).integrableOn
    ((integrable_fderiv_test hψ hψc Complex.I).const_mul u.im).integrableOn,
    integral_const_mul, integral_const_mul, integral_epigraph_horizontal hf hψ hψc,
    integral_epigraph_vertical hf.continuous hψ hψc]
  have heq : (fun x => ψ (graph f x) * (deriv f x * u.re - u.im)) =
      fun x => u.re * (deriv f x * ψ (graph f x)) - u.im * ψ (graph f x) := by
    funext x
    ring
  rw [heq, integral_sub (hfg.const_mul _) (hg.const_mul _), integral_const_mul, integral_const_mul]
  ring

lemma one_le_jacobian (a : ℝ) : 1 ≤ jacobian a := by
  rw [jacobian_eq_sqrt]
  have h : (1 : ℝ) ≤ 1 + a ^ 2 := by nlinarith [sq_nonneg a]
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h

lemma jacobian_pos (a : ℝ) : 0 < jacobian a := lt_of_lt_of_le zero_lt_one (one_le_jacobian a)

/-- The outward normal of the upper epigraph, defined at all parameters.
Its value on the null nondifferentiability set does not affect integration. -/
def graphNormal (f : ℝ → ℝ) (x : ℝ) : ℂ :=
  (jacobian (deriv f x))⁻¹ • (((deriv f x : ℝ) : ℂ) - Complex.I)

lemma norm_slope_normal (a : ℝ) : ‖(a : ℂ) - Complex.I‖ = jacobian a := by
  simp [jacobian, Complex.norm_eq_sqrt_sq_add_sq, add_comm]

lemma graphNormal_norm (f : ℝ → ℝ) (x : ℝ) : ‖graphNormal f x‖ = 1 := by
  rw [graphNormal, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (jacobian_pos _)),
    norm_slope_normal, inv_mul_cancel₀ (jacobian_pos _).ne']

lemma measurable_graphNormal (f : ℝ → ℝ) : Measurable (graphNormal f) := by
  have hd : Measurable (deriv f) := measurable_deriv f
  have hJ : Measurable (fun x => (jacobian (deriv f x))⁻¹) :=
    (continuous_jacobian.measurable.comp hd).inv
  exact hJ.smul ((Complex.measurable_ofReal.comp hd).sub measurable_const)

lemma inner_graphNormal (f : ℝ → ℝ) (u : ℂ) (x : ℝ) :
    inner ℝ u (graphNormal f x) =
      (jacobian (deriv f x))⁻¹ * (deriv f x * u.re - u.im) := by
  rw [graphNormal, real_inner_smul_right, Complex.inner]
  simp [Complex.mul_re]

/-- The local H¹ flux formula on a finite measurable graph piece containing
the support of the boundary trace. No existence or agreement of global normals
is assumed here. -/
theorem integral_epigraph_eq_graph_flux {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hsupp : Function.support (fun x => ψ (graph f x)) ⊆ E) (u : ℂ) :
    (∫ z in epigraph f, fderiv ℝ ψ z u) =
      ∫ z in graph f '' E, ψ z * inner ℝ u (graphNormal f z.re)
        ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
  have hn : Measurable (fun z : ℂ => graphNormal f z.re) :=
    (measurable_graphNormal f).comp Complex.measurable_re
  have hF : Measurable (fun z : ℂ => ψ z * inner ℝ u (graphNormal f z.re)) :=
    hψ.continuous.measurable.mul ((innerSL ℝ u).continuous.measurable.comp hn)
  rw [setIntegral_graph hf hE hfin hF.aestronglyMeasurable]
  have hpoint : ∀ x : ℝ,
      jacobian (deriv f x) • (ψ (graph f x) * inner ℝ u (graphNormal f (graph f x).re)) =
        ψ (graph f x) * (deriv f x * u.re - u.im) := by
    intro x
    have hJ : jacobian (deriv f x) ≠ 0 := (jacobian_pos _).ne'
    simp only [graph, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero,
      inner_graphNormal, smul_eq_mul]
    field_simp
  simp_rw [hpoint]
  rw [integral_epigraph_direction hf hψ hψc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : ψ (graph f x) = 0 := by
    by_contra hne
    exact hx (hsupp hne)
  rw [hz, zero_mul]

end Paper.Geometry.GraphArea
