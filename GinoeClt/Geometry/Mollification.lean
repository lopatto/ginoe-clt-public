/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

The indicator/convolution and reflected-test proof patterns are narrowly adapted
from human-ai-mathematics/kls-lean, revision 33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/KLS/Geometry/Perimeter/{Mollification,MollifiedBoundary}.lean
(especially MollifiedBoundary:31–113), Apache-2.0. The domain input here is the
proved Lipschitz Gauss–Green theorem, with no smooth-domain premise.
-/
module

public import GinoeClt.Geometry.GaussGreen
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! # Mollified indicators and their genuine scalar boundary derivatives -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ENNReal Topology Convolution

namespace Paper.Geometry

/-- The literal scalar mollification of the domain indicator. -/
def mollifiedIndicator (A : Set ℂ) (η : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, η (x - y) * A.indicator (1 : ℂ → ℝ) y

lemma locallyIntegrable_indicator {A : Set ℂ} (hA : MeasurableSet A) :
    LocallyIntegrable (A.indicator (1 : ℂ → ℝ)) volume := by
  classical
  intro x
  obtain ⟨s, hs, hsfin⟩ := (volume : Measure ℂ).finiteAt_nhds x
  refine ⟨s, hs, Measure.integrableOn_of_bounded hsfin.ne
    (measurable_one.indicator hA).aestronglyMeasurable (M := 1) ?_⟩
  filter_upwards with y
  by_cases hy : y ∈ A
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

lemma mollifiedIndicator_eq_convolution_right (A : Set ℂ) (η : ℂ → ℝ) :
    mollifiedIndicator A η = A.indicator (1 : ℂ → ℝ) ⋆[lsmul ℝ ℝ, volume] η := by
  funext x
  rw [convolution_def]
  simp only [mollifiedIndicator, lsmul_apply, smul_eq_mul]
  exact integral_congr_ae (ae_of_all _ (fun y => mul_comm _ _))

lemma mollifiedIndicator_eq_convolution_left (A : Set ℂ) (η : ℂ → ℝ) :
    mollifiedIndicator A η = η ⋆[lsmul ℝ ℝ, volume] A.indicator (1 : ℂ → ℝ) := by
  funext x
  rw [convolution_eq_swap]
  rfl

/-- The derivative is computed from native compact convolution differentiation;
the domain indicator is merely measurable and locally integrable here. -/
theorem mollifiedIndicator_fderiv {A : Set ℂ} (hA : MeasurableSet A)
    {η : ℂ → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (x u : ℂ) :
    fderiv ℝ (mollifiedIndicator A η) x u = ∫ y in A, fderiv ℝ η (x - y) u := by
  classical
  have hloc := locallyIntegrable_indicator hA
  have hD := hηc.hasFDerivAt_convolution_right (L := lsmul ℝ ℝ) hloc hη x
  rw [mollifiedIndicator_eq_convolution_right, hD.fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hloc (hηc.fderiv ℝ)
      (hη.continuous_fderiv one_ne_zero) x u, convolution_def]
  have hind : ∀ y : ℂ,
      (lsmul ℝ ℝ) (A.indicator (1 : ℂ → ℝ) y) (fderiv ℝ η (x - y) u) =
        A.indicator (fun y => fderiv ℝ η (x - y) u) y := by
    intro y
    by_cases hy : y ∈ A
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  rw [integral_congr_ae (ae_of_all _ hind), integral_indicator hA]

/-- A fixed normal witness obtained from the proved Lipschitz Gauss–Green theorem. -/
def boundaryNormal (A : Set ℂ) (hA : Paper.IsAdmissibleLipschitzDomain A) : ℂ → ℂ :=
  (exists_boundaryNormal_of_admissible hA).choose

theorem boundaryNormal_spec {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) :
    Measurable (boundaryNormal A hA) ∧
      (∀ᵐ y ∂boundarySurface A, ‖boundaryNormal A hA y‖ = 1) ∧
      ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ u : ℂ,
        (∫ y in A, fderiv ℝ φ y u) =
          ∫ y in frontier A, φ y * inner ℝ u (boundaryNormal A hA y)
            ∂(Measure.hausdorffMeasure 1 : Measure ℂ) :=
  (exists_boundaryNormal_of_admissible hA).choose_spec

/-- The literal mollified indicator has the boundary derivative prescribed by
the manuscript's distributional identity, for every compact C¹ kernel. -/
theorem mollifiedIndicator_fderiv_eq_boundary {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) {η : ℂ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (x u : ℂ) :
    fderiv ℝ (mollifiedIndicator A η) x u =
      -∫ y in frontier A, η (x - y) * inner ℝ u (boundaryNormal A hA y)
        ∂(Measure.hausdorffMeasure 1 : Measure ℂ) := by
  let ηx : ℂ → ℝ := fun y => η (x - y)
  have hcd : ContDiff ℝ 1 ηx := hη.comp (contDiff_const.sub contDiff_id)
  have hcs : HasCompactSupport ηx := hηc.comp_homeomorph (Homeomorph.subLeft x)
  have hd : ∀ y : ℂ, fderiv ℝ ηx y u = - fderiv ℝ η (x - y) u := by
    intro y
    have h1 : HasFDerivAt (fun z : ℂ => x - z) (-(ContinuousLinearMap.id ℝ ℂ)) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := (hη.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y h1
    have heq : (fderiv ℝ η (x - y)).comp (-(ContinuousLinearMap.id ℝ ℂ)) =
        -(fderiv ℝ η (x - y)) := by ext v; simp
    rw [heq] at h2
    have hh : fderiv ℝ ηx y = -(fderiv ℝ η (x - y)) := by convert! h2.fderiv using 1
    rw [hh]
    rfl
  have hGG := (boundaryNormal_spec hA).2.2 ηx hcd hcs u
  have hneg : (∫ y in A, fderiv ℝ ηx y u) = -∫ y in A, fderiv ℝ η (x - y) u := by
    rw [← integral_neg]
    exact setIntegral_congr_fun hA.1.measurableSet (fun y _ => hd y)
  rw [hneg] at hGG
  rw [mollifiedIndicator_fderiv hA.1.measurableSet hη hηc]
  linarith

end Paper.Geometry
