/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

Narrowly adapted proof patterns from human-ai-mathematics/kls-lean,
revision 33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/Analysis/Graph/Integral.lean:78–178 (Apache-2.0).
The area identity here is the proved Lipschitz formula at finite parameter measure.
-/
module

public import GinoeClt.Geometry.GraphAreaFormula
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Weighted measure and integral of a genuine Lipschitz graph -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace Paper.Geometry.GraphArea

/-- The actual weighted parameter measure pushes forward to Euclidean H¹ on
the graph piece. Only the parameter set, not the whole real line, is finite. -/
theorem map_graph_withDensity {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤) :
    Measure.map (graph f)
      ((volume.withDensity (fun x => ENNReal.ofReal (jacobian (deriv f x)))).restrict E) =
        (Measure.hausdorffMeasure 1 : Measure ℂ).restrict (graph f '' E) := by
  have hgm : Measurable (graph f) := (continuous_graph hf.continuous).measurable
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hgm hB, Measure.restrict_apply (hB.preimage hgm),
    withDensity_apply _ ((hB.preimage hgm).inter hE), Measure.restrict_apply hB]
  have hS : MeasurableSet ((graph f) ⁻¹' B ∩ E) := (hB.preimage hgm).inter hE
  have hSf : volume ((graph f) ⁻¹' B ∩ E) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  have harea : (Measure.hausdorffMeasure 1 : Measure ℂ)
      (graph f '' ((graph f) ⁻¹' B ∩ E)) =
      ∫⁻ x in ((graph f) ⁻¹' B ∩ E), ENNReal.ofReal (jacobian (deriv f x)) := by
    simpa only [jacobian_eq_sqrt] using hausdorffMeasure_graph hf hS hSf
  rw [← harea]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨hxB, hxE⟩, rfl⟩
    exact ⟨hxB, ⟨x, hxE, rfl⟩⟩
  · rintro ⟨hzB, x, hxE, rfl⟩
    exact ⟨x, ⟨hzB, hxE⟩, rfl⟩

/-- Surface integration over the graph is ordinary parameter integration with
the actual Euclidean Jacobian. This respects the totalized Bochner integral. -/
theorem setIntegral_graph {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ⊤)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℂ → V}
    (hF : AEStronglyMeasurable F
      ((Measure.hausdorffMeasure 1 : Measure ℂ).restrict (graph f '' E))) :
    (∫ z in graph f '' E, F z ∂(Measure.hausdorffMeasure 1 : Measure ℂ)) =
      ∫ x in E, jacobian (deriv f x) • F (graph f x) := by
  have hmap := map_graph_withDensity hf hE hfin
  have hgm : Measurable (graph f) := (continuous_graph hf.continuous).measurable
  have hJm : Measurable (fun x => (jacobian (deriv f x)).toNNReal) :=
    (continuous_jacobian.measurable.comp (measurable_deriv f)).real_toNNReal
  rw [← hmap] at hF ⊢
  rw [integral_map hgm.aemeasurable hF, restrict_withDensity hE,
    show (fun x => ENNReal.ofReal (jacobian (deriv f x))) =
      (fun x => (((jacobian (deriv f x)).toNNReal : ℝ≥0) : ℝ≥0∞)) from rfl,
    integral_withDensity_eq_integral_smul hJm]
  apply integral_congr_ae
  filter_upwards with x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (jacobian_nonneg _)]

end Paper.Geometry.GraphArea
