/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.BoundaryNormal
public import GinoeClt.Geometry.BoundaryLength
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Compatible chart normals and Gauss–Green for the frozen Lipschitz domains -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ComplexConjugate Manifold

namespace Paper.Geometry

/-- The actual finite boundary measure; ambient planar H¹ is not asserted
locally finite. -/
def boundarySurface (A : Set ℂ) : Measure ℂ :=
  (Measure.hausdorffMeasure 1 : Measure ℂ).restrict (frontier A)

lemma integrable_chartNormal_component {A : Set ℂ}
    (hfin : (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) < ⊤)
    (p c : ℂ) (hc : ‖c‖ = 1) (f : ℝ → ℝ) (u : ℂ) :
    Integrable (fun w => inner ℝ u (chartNormal p c f w)) (boundarySurface A) := by
  let : IsFiniteMeasure (boundarySurface A) := ⟨by simpa [boundarySurface] using hfin⟩
  have hm : Measurable (fun w => inner ℝ u (chartNormal p c f w)) :=
    (innerSL ℝ u).continuous.measurable.comp (measurable_chartNormal p c f)
  apply (integrable_const ‖u‖).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro w
  simpa only [Real.norm_eq_abs, chartNormal_norm p c hc, mul_one] using
    abs_real_inner_le_norm u (chartNormal p c f w)

/-- Local scalar Gauss–Green identifies the two actual chart normals almost
everywhere on an overlap. The finite measure is H¹ restricted to the boundary. -/
theorem chartNormal_ae_eq_on_overlap {A : Set ℂ} (hA : IsOpen A)
    (hfin : (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) < ⊤)
    {p c p' c' : ℂ} {r h r' h' : ℝ} {K K' : ℝ≥0} {f g : ℝ → ℝ}
    (hch : IsChartAt A p c r h K f) (hch' : IsChartAt A p' c' r' h' K' g) :
    ∀ᵐ w ∂boundarySurface A, w ∈ chartBox p c r h ∩ chartBox p' c' r' h' →
      chartNormal p c f w = chartNormal p' c' g w := by
  have hAE : ∀ u : ℂ, ∀ᵐ w ∂boundarySurface A,
      w ∈ chartBox p c r h ∩ chartBox p' c' r' h' →
        inner ℝ u (chartNormal p c f w) - inner ℝ u (chartNormal p' c' g w) = 0 := by
    intro u
    have hi := integrable_chartNormal_component hfin p c hch.1 f u
    have hj := integrable_chartNormal_component hfin p' c' hch'.1 g u
    apply ((isOpen_chartBox p c r h).inter (isOpen_chartBox p' c' r' h')).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hi.sub hj).locallyIntegrable.locallyIntegrableOn _)
    intro φ hφ hφc hsupp
    have hpi : Integrable (fun w => φ w * inner ℝ u (chartNormal p c f w)) (boundarySurface A) := by
      simpa only [smul_eq_mul] using
        hi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hpj : Integrable (fun w => φ w * inner ℝ u (chartNormal p' c' g w)) (boundarySurface A) := by
      simpa only [smul_eq_mul] using
        hj.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have heq : (∫ w, φ w * inner ℝ u (chartNormal p c f w) ∂boundarySurface A) =
        ∫ w, φ w * inner ℝ u (chartNormal p' c' g w) ∂boundarySurface A :=
      (integral_chart_eq_boundary_flux hA hch (hφ.of_le (by simp)) hφc
        (hsupp.trans inter_subset_left) u).symm.trans
      (integral_chart_eq_boundary_flux hA hch' (hφ.of_le (by simp)) hφc
        (hsupp.trans inter_subset_right) u)
    change (∫ w, φ w * (inner ℝ u (chartNormal p c f w) - inner ℝ u (chartNormal p' c' g w))
      ∂boundarySurface A) = 0
    simp_rw [mul_sub]
    rw [integral_sub hpi hpj, sub_eq_zero]
    exact heq
  filter_upwards [hAE 1, hAE Complex.I] with w h1 hI
  intro hw
  apply Complex.ext
  · have hh := sub_eq_zero.mp (h1 hw)
    simpa [Complex.inner] using hh
  · have hh := sub_eq_zero.mp (hI hw)
    simpa [Complex.inner, Complex.mul_re] using hh

lemma integral_fderiv_compact_eq_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (u : ℂ) : (∫ w, fderiv ℝ φ w u) = 0 := by
  have hd := GraphArea.integrable_fderiv_test hφ hφc u
  have hv : Integrable φ (volume : Measure ℂ) := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := fun _ : ℂ => (1 : ℝ)) (g := φ) (v := u)
    (by simp) (by simpa using hd) (by simpa using hv)
    (fun _ _ => differentiableAt_const _) (fun w _ => hφ.differentiable one_ne_zero w)
  simpa using hh

/-- Finite smooth localization assembles the actual chart formulas. Normal
agreement is used to prove that the resulting normal has unit norm almost everywhere. -/
theorem exists_gaussGreen_of_finite_charts {A : Set ℂ} (hA : IsOpen A)
    (hfin : (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) < ⊤)
    {ι : Type*} [Fintype ι] (p c : ι → ℂ) (r h : ι → ℝ) (K : ι → ℝ≥0) (f : ι → ℝ → ℝ)
    (hch : ∀ i, IsChartAt A (p i) (c i) (r i) (h i) (K i) (f i))
    (hcover : frontier A ⊆ ⋃ i, chartBox (p i) (c i) (r i) (h i)) :
    ∃ ν : ℂ → ℂ, Measurable ν ∧ (∀ᵐ w ∂boundarySurface A, ‖ν w‖ = 1) ∧
      ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ u : ℂ,
        (∫ w in A, fderiv ℝ φ w u) =
          ∫ w in frontier A, φ w * inner ℝ u (ν w)
            ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
  classical
  let U : Bool ⊕ ι → Set ℂ := Sum.elim (fun b => cond b A (closure A)ᶜ)
    (fun i => chartBox (p i) (c i) (r i) (h i))
  have hUo : ∀ j, IsOpen (U j) := by
    rintro (b | i)
    · cases b
      · exact isClosed_closure.isOpen_compl
      · exact hA
    · exact isOpen_chartBox _ _ _ _
  have hUc : (univ : Set ℂ) ⊆ ⋃ j, U j := by
    intro w _
    by_cases hwA : w ∈ A
    · exact mem_iUnion.mpr ⟨Sum.inl true, hwA⟩
    · by_cases hwcl : w ∈ closure A
      · have hwfr : w ∈ frontier A := by rw [hA.frontier_eq]; exact ⟨hwcl, hwA⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hwfr)
        exact mem_iUnion.mpr ⟨Sum.inr i, hi⟩
      · exact mem_iUnion.mpr ⟨Sum.inl false, hwcl⟩
  obtain ⟨ρ, hρsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ℂ)) isClosed_univ U hUo hUc
  have hρcd : ∀ j, ContDiff ℝ 1 (ρ j) := fun j => (ρ j).contMDiff.contDiff.of_le (by simp)
  have hρsum : ∀ w : ℂ, ∑ j, ρ j w = 1 := by
    intro w
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ w)
  have hρbool : ∀ (b : Bool) (w : ℂ), w ∈ frontier A → ρ (Sum.inl b) w = 0 := by
    intro b w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hb := hρsub (Sum.inl b) hs
    cases b
    · exact hb (frontier_subset_closure hw)
    · rw [hA.frontier_eq] at hw
      exact hw.2 hb
  let N : Bool ⊕ ι → ℂ → ℂ := Sum.elim (fun _ _ => 0) (fun i => chartNormal (p i) (c i) (f i))
  let ν : ℂ → ℂ := fun w => ∑ j, ρ j w • N j w
  have hNm : ∀ j, Measurable (N j) := by
    rintro (b | i)
    · exact measurable_const
    · exact measurable_chartNormal _ _ _
  have hνm : Measurable ν :=
    Finset.measurable_sum _ (fun j _ => (hρcd j).continuous.measurable.smul (hNm j))
  have hcompat : ∀ᵐ w ∂boundarySurface A, ∀ i j,
      w ∈ chartBox (p i) (c i) (r i) (h i) ∩ chartBox (p j) (c j) (r j) (h j) →
        chartNormal (p i) (c i) (f i) w = chartNormal (p j) (c j) (f j) w :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => chartNormal_ae_eq_on_overlap hA hfin (hch i) (hch j)))
  have hνnorm : ∀ᵐ w ∂boundarySurface A, ‖ν w‖ = 1 := by
    have hfront : ∀ᵐ w ∂boundarySurface A, w ∈ frontier A :=
      ae_restrict_mem isClosed_frontier.measurableSet
    filter_upwards [hcompat, hfront] with w hwc hw
    obtain ⟨i, hwi⟩ := mem_iUnion.mp (hcover hw)
    have heq : ν w = chartNormal (p i) (c i) (f i) w := by
      calc
        ν w = ∑ j, ρ j w • chartNormal (p i) (c i) (f i) w := by
          apply Finset.sum_congr rfl
          rintro (b | k) _
          · simp [N, hρbool b w hw]
          · by_cases hz : ρ (Sum.inr k) w = 0
            · simp [hz]
            · have hwk := hρsub (Sum.inr k) (subset_tsupport _ hz)
              exact congrArg (fun n : ℂ => ρ (Sum.inr k) w • n) (hwc k i ⟨hwk, hwi⟩)
        _ = (∑ j, ρ j w) • chartNormal (p i) (c i) (f i) w := Finset.sum_smul.symm
        _ = _ := by rw [hρsum, one_smul]
    rw [heq, chartNormal_norm _ _ (hch i).1]
  refine ⟨ν, hνm, hνnorm, ?_⟩
  intro φ hφ hφc u
  let G : Bool ⊕ ι → ℂ → ℝ := fun j w => ρ j w * φ w
  have hGcd : ∀ j, ContDiff ℝ 1 (G j) := fun j => (hρcd j).mul hφ
  have hGc : ∀ j, HasCompactSupport (G j) := fun _ => hφc.mul_left
  have hGts : ∀ j, tsupport (G j) ⊆ U j := fun j => tsupport_mul_subset_left.trans (hρsub j)
  have hGsum : φ = fun w => ∑ j, G j w := by
    funext w
    dsimp only [G]
    rw [← Finset.sum_mul, hρsum, one_mul]
  have hvol : ∀ j, IntegrableOn (fun w => fderiv ℝ (G j) w u) A volume :=
    fun j => (GraphArea.integrable_fderiv_test (hGcd j) (hGc j) u).integrableOn
  have hNint : ∀ j, Integrable (fun w => inner ℝ u (N j w)) (boundarySurface A) := by
    rintro (b | i)
    · simp [N]
    · exact integrable_chartNormal_component hfin _ _ (hch i).1 _ u
  have hbd : ∀ j, Integrable (fun w => G j w * inner ℝ u (N j w)) (boundarySurface A) := by
    intro j
    simpa only [smul_eq_mul] using
      (hNint j).locallyIntegrable.integrable_smul_left_of_hasCompactSupport (hGcd j).continuous (hGc j)
  have hblock : ∀ j, (∫ w in A, fderiv ℝ (G j) w u) =
      ∫ w, G j w * inner ℝ u (N j w) ∂boundarySurface A := by
    rintro (b | i)
    · change (∫ w in A, fderiv ℝ (G (Sum.inl b)) w u) =
        ∫ w, G (Sum.inl b) w * inner ℝ u (0 : ℂ) ∂boundarySurface A
      simp only [inner_zero_right, mul_zero, integral_zero]
      cases b
      · apply setIntegral_eq_zero_of_forall_eq_zero
        intro w hw
        have hn : w ∉ tsupport (G (Sum.inl false)) := by
          intro hs
          exact (hGts (Sum.inl false) hs) (subset_closure hw)
        rw [fderiv_of_notMem_tsupport ℝ hn]
        rfl
      · have heq : (∫ w in A, fderiv ℝ (G (Sum.inl true)) w u) =
            ∫ w, fderiv ℝ (G (Sum.inl true)) w u := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro w hw
          rw [fderiv_of_notMem_tsupport ℝ (fun hs => hw (hGts (Sum.inl true) hs))]
          rfl
        rw [heq, integral_fderiv_compact_eq_zero (hGcd _) (hGc _) u]
    · exact integral_chart_eq_boundary_flux hA (hch i) (hGcd _) (hGc _) (hGts _) u
  have hderiv : ∀ w, fderiv ℝ φ w u = ∑ j, fderiv ℝ (G j) w u := by
    intro w
    conv_lhs => rw [hGsum]
    rw [fderiv_fun_sum (fun j _ => (hGcd j).differentiable one_ne_zero w)]
    simp only [sum_apply]
  have hboundary : ∀ w, (∑ j, G j w * inner ℝ u (N j w)) = φ w * inner ℝ u (ν w) := by
    intro w
    dsimp only [ν, G]
    rw [inner_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_right]
    ring
  calc (∫ w in A, fderiv ℝ φ w u) = ∫ w in A, ∑ j, fderiv ℝ (G j) w u :=
      setIntegral_congr_fun hA.measurableSet (fun w _ => hderiv w)
    _ = ∑ j, ∫ w in A, fderiv ℝ (G j) w u := integral_finsetSum _ (fun j _ => hvol j)
    _ = ∑ j, ∫ w, G j w * inner ℝ u (N j w) ∂boundarySurface A :=
      Finset.sum_congr rfl (fun j _ => hblock j)
    _ = ∫ w, ∑ j, G j w * inner ℝ u (N j w) ∂boundarySurface A :=
      (integral_finsetSum _ (fun j _ => hbd j)).symm
    _ = _ := integral_congr_ae (ae_of_all _ hboundary)

/-- Bounded open domains with the original Lipschitz charts admit a measurable
unit boundary normal and scalar Gauss–Green for every compactly supported C¹ test. -/
theorem exists_gaussGreen_of_lipschitz_charts {A : Set ℂ} (hA : IsOpen A)
    (hb : Bornology.IsBounded A)
    (hcharts : ∀ p ∈ frontier A, Paper.LipschitzBoundaryChart A p) :
    ∃ ν : ℂ → ℂ, Measurable ν ∧ (∀ᵐ w ∂boundarySurface A, ‖ν w‖ = 1) ∧
      ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ u : ℂ,
        (∫ w in A, fderiv ℝ φ w u) =
          ∫ w in frontier A, φ w * inner ℝ u (ν w)
            ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
  classical
  choose c r h K f hch using
    (fun p : frontier A => exists_global_chart (hcharts p p.property))
  let U (p : frontier A) : Set ℂ := chartBox p (c p) (r p) (h p)
  have hU : ∀ p, IsOpen (U p) := fun p => isOpen_chartBox _ _ _ _
  have hcover : frontier A ⊆ ⋃ p : frontier A, U p := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    change |(c ⟨p, hp⟩ * (p - p)).re| < r ⟨p, hp⟩ ∧
      |(c ⟨p, hp⟩ * (p - p)).im| < h ⟨p, hp⟩
    simpa only [sub_self, mul_zero, Complex.zero_re, Complex.zero_im, abs_zero] using
      And.intro (hch ⟨p, hp⟩).2.1 (hch ⟨p, hp⟩).2.2.1
  obtain ⟨t, ht⟩ := (frontier_isCompact hb).elim_finite_subcover U hU hcover
  refine exists_gaussGreen_of_finite_charts hA (boundary_measure_lt_top_of_charts hA hb hcharts)
    (fun q : ↥t => q.val.val) (fun q => c q.val) (fun q => r q.val) (fun q => h q.val)
    (fun q => K q.val) (fun q => f q.val) (fun q => hch q.val) ?_
  intro w hw
  obtain ⟨p, hp⟩ := mem_iUnion.mp (ht hw)
  obtain ⟨hpt, hwp⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨⟨p, hpt⟩, hwp⟩

/-- The precise scalar Lipschitz Gauss–Green input for the manuscript,
proved from its frozen admissibility hypotheses with no external assumption. -/
theorem exists_boundaryNormal_of_admissible {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) :
    ∃ ν : ℂ → ℂ, Measurable ν ∧ (∀ᵐ w ∂boundarySurface A, ‖ν w‖ = 1) ∧
      ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ u : ℂ,
        (∫ w in A, fderiv ℝ φ w u) =
          ∫ w in frontier A, φ w * inner ℝ u (ν w)
            ∂(Measure.hausdorffMeasure 1 : Measure ℂ) :=
  exists_gaussGreen_of_lipschitz_charts hA.1 (Paper.admissible_isBounded hA) hA.2.2.2

end Paper.Geometry
