/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.Mollification
public import Mathlib.MeasureTheory.Group.LIntegral

/-! # The directional boundary mass bounds actual mollified derivatives -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ENNReal Topology Convolution

namespace Paper.Geometry

/-- The actual directional perimeter associated to the proved outward normal. -/
def directionalPerimeter (A : Set ℂ) (hA : Paper.IsAdmissibleLipschitzDomain A) (u : ℂ) : ℝ :=
  ∫ y, |inner ℝ u (boundaryNormal A hA y)| ∂boundarySurface A

lemma boundarySurface_lt_top {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) :
    (boundarySurface A) univ < ⊤ := by
  simpa [boundarySurface] using
    boundary_measure_lt_top_of_charts hA.1 (Paper.admissible_isBounded hA) hA.2.2.2

lemma integrable_boundaryNormal_component {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    (u : ℂ) : Integrable (fun y => inner ℝ u (boundaryNormal A hA y)) (boundarySurface A) := by
  let : IsFiniteMeasure (boundarySurface A) := ⟨boundarySurface_lt_top hA⟩
  have hm : Measurable (fun y => inner ℝ u (boundaryNormal A hA y)) :=
    (innerSL ℝ u).continuous.measurable.comp (boundaryNormal_spec hA).1
  apply (integrable_const ‖u‖).mono' hm.aestronglyMeasurable
  filter_upwards [(boundaryNormal_spec hA).2.1] with y hy
  simpa only [Real.norm_eq_abs, hy, mul_one] using abs_real_inner_le_norm u (boundaryNormal A hA y)

lemma directionalPerimeter_nonneg {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) (u : ℂ) :
    0 ≤ directionalPerimeter A hA u := integral_nonneg (fun _ => abs_nonneg _)

lemma integrable_boundary_kernel {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {η : ℂ → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η) (x u : ℂ) :
    Integrable (fun y => η (x - y) * |inner ℝ u (boundaryNormal A hA y)|) (boundarySurface A) := by
  simpa only [smul_eq_mul, Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, id_eq] using
    (integrable_boundaryNormal_component hA u).norm.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hη.comp (continuous_const.sub continuous_id)) (hηc.comp_homeomorph (Homeomorph.subLeft x))

lemma abs_mollifiedIndicator_fderiv_le {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηnn : ∀ x, 0 ≤ η x) (x u : ℂ) :
    |fderiv ℝ (mollifiedIndicator A η) x u| ≤
      ∫ y, η (x - y) * |inner ℝ u (boundaryNormal A hA y)| ∂boundarySurface A := by
  rw [mollifiedIndicator_fderiv_eq_boundary hA hη hηc]
  rw [abs_neg]
  calc |∫ y in frontier A, η (x - y) * inner ℝ u (boundaryNormal A hA y)
      ∂(Measure.hausdorffMeasure 1 : Measure ℂ)| ≤
      ∫ y, |η (x - y) * inner ℝ u (boundaryNormal A hA y)| ∂boundarySurface A :=
        abs_integral_le_integral_abs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [abs_mul, abs_of_nonneg (hηnn _)]

/-- Tonelli and unit kernel mass bound the genuine L¹ norm of every directional
derivative. The normal component and all boundary integrands are integrable. -/
theorem mollifiedIndicator_fderiv_l1_le {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηnn : ∀ x, 0 ≤ η x) (hηmass : ∫ x, η x = 1) (u : ℂ) :
    Integrable (fun x => fderiv ℝ (mollifiedIndicator A η) x u) ∧
      (∫ x, |fderiv ℝ (mollifiedIndicator A η) x u|) ≤ directionalPerimeter A hA u := by
  let : IsFiniteMeasure (boundarySurface A) := ⟨boundarySurface_lt_top hA⟩
  let a : ℂ → ℝ := fun y => inner ℝ u (boundaryNormal A hA y)
  have ham : Measurable a := (innerSL ℝ u).continuous.measurable.comp (boundaryNormal_spec hA).1
  have hai : Integrable (fun y => |a y|) (boundarySurface A) := by
    simpa only [Real.norm_eq_abs] using (integrable_boundaryNormal_component hA u).norm
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  have hηmass' : ∫⁻ x, ENNReal.ofReal (η x) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hηi (ae_of_all _ hηnn), hηmass]
    simp
  have hmassshift : ∀ y : ℂ, (∫⁻ x, ENNReal.ofReal (η (x - y))) = 1 := by
    intro y
    exact (lintegral_sub_right_eq_self (μ := (volume : Measure ℂ))
      (fun x : ℂ => ENNReal.ofReal (η x)) y).trans hηmass'
  have hkm : Measurable (fun q : ℂ × ℂ =>
      ENNReal.ofReal (η (q.1 - q.2)) * ENNReal.ofReal |a q.2|) :=
    (ENNReal.measurable_ofReal.comp (hη.continuous.measurable.comp
      (measurable_fst.sub measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (ham.comp measurable_snd)))
  have hpoint : ∀ x : ℂ, ENNReal.ofReal |fderiv ℝ (mollifiedIndicator A η) x u| ≤
      ∫⁻ y, ENNReal.ofReal (η (x - y)) * ENNReal.ofReal |a y| ∂boundarySurface A := by
    intro x
    have hi := integrable_boundary_kernel hA hη.continuous hηc x u
    have hnn : ∀ y, 0 ≤ η (x - y) * |a y| := fun y => mul_nonneg (hηnn _) (abs_nonneg _)
    calc ENNReal.ofReal |fderiv ℝ (mollifiedIndicator A η) x u| ≤
        ENNReal.ofReal (∫ y, η (x - y) * |a y| ∂boundarySurface A) :=
          ENNReal.ofReal_le_ofReal (abs_mollifiedIndicator_fderiv_le hA hη hηc hηnn x u)
      _ = _ := by
        rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnn)]
        apply lintegral_congr
        intro y
        exact ENNReal.ofReal_mul (hηnn _)
  have hL : (∫⁻ x, ENNReal.ofReal |fderiv ℝ (mollifiedIndicator A η) x u|) ≤
      ENNReal.ofReal (directionalPerimeter A hA u) := by
    calc (∫⁻ x, ENNReal.ofReal |fderiv ℝ (mollifiedIndicator A η) x u|) ≤
        ∫⁻ x, ∫⁻ y, ENNReal.ofReal (η (x - y)) * ENNReal.ofReal |a y| ∂boundarySurface A :=
          lintegral_mono hpoint
      _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (η (x - y)) * ENNReal.ofReal |a y| ∂volume
          ∂boundarySurface A := lintegral_lintegral_swap hkm.aemeasurable
      _ = ∫⁻ y, ENNReal.ofReal |a y| ∂boundarySurface A := by
        apply lintegral_congr
        intro y
        have hm : Measurable (fun x : ℂ => ENNReal.ofReal (η (x - y))) :=
          (ENNReal.measurable_ofReal.comp hη.continuous.measurable).comp
            (measurable_id.sub measurable_const)
        rw [lintegral_mul_const (f := fun x : ℂ => ENNReal.ofReal (η (x - y))) _ hm,
          hmassshift, one_mul]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hai (ae_of_all _ (fun y => abs_nonneg (a y)))).symm
  have hcd : ContDiff ℝ 1 (mollifiedIndicator A η) := by
    rw [mollifiedIndicator_eq_convolution_right]
    exact hηc.contDiff_convolution_right (L := lsmul ℝ ℝ) (locallyIntegrable_indicator hA.1.measurableSet) hη
  have hDm : Continuous (fun x => fderiv ℝ (mollifiedIndicator A η) x u) :=
    (ContinuousLinearMap.apply ℝ ℝ u).continuous.comp (hcd.continuous_fderiv one_ne_zero)
  have hiD : Integrable (fun x => fderiv ℝ (mollifiedIndicator A η) x u) := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    change (∫⁻ x, ‖fderiv ℝ (mollifiedIndicator A η) x u‖ₑ) < ⊤
    simpa only [← ofReal_norm, Real.norm_eq_abs] using
      hL.trans_lt (ENNReal.ofReal_lt_top)
  refine ⟨hiD, ?_⟩
  rw [show (fun x => |fderiv ℝ (mollifiedIndicator A η) x u|) =
    (fun x => ‖fderiv ℝ (mollifiedIndicator A η) x u‖) from funext (fun _ => (Real.norm_eq_abs _).symm)]
  have hnorm : ENNReal.ofReal (∫ x, ‖fderiv ℝ (mollifiedIndicator A η) x u‖) ≤
      ENNReal.ofReal (directionalPerimeter A hA u) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hiD]
    simpa only [← ofReal_norm, Real.norm_eq_abs] using hL
  exact (ENNReal.ofReal_le_ofReal_iff (directionalPerimeter_nonneg hA u)).mp hnorm

end Paper.Geometry
