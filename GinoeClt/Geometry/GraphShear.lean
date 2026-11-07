/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

The shear homeomorphism and Fubini proof are narrowly adapted from
human-ai-mathematics/kls-lean, revision 33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/Analysis/Graph/Divergence.lean:137–152,203–217 (Apache-2.0).
-/
module

public import GinoeClt.Geometry.GraphArea
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Prod

/-! # The continuous measure-preserving planar graph shear -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace Paper.Geometry.GraphArea

/-- The upper epigraph convention agrees with the frozen boundary charts. -/
def epigraph (f : ℝ → ℝ) : Set ℂ := {z | f z.re < z.im}

lemma isOpen_epigraph {f : ℝ → ℝ} (hf : Continuous f) : IsOpen (epigraph f) :=
  isOpen_lt (hf.comp Complex.continuous_re) Complex.continuous_im

/-- Translation in each vertical fibre, with its actual continuous inverse. -/
def shearHomeomorph {f : ℝ → ℝ} (hf : Continuous f) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1, p.2 + f p.1)
  invFun p := (p.1, p.2 - f p.1)
  left_inv := by rintro ⟨x, t⟩; simp
  right_inv := by rintro ⟨x, t⟩; simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst))

theorem measurePreserving_shearHomeomorph {f : ℝ → ℝ} (hf : Continuous f) :
    MeasurePreserving (shearHomeomorph hf) (volume : Measure (ℝ × ℝ)) volume := by
  have hm : Measurable (shearHomeomorph hf) :=
    measurable_fst.prodMk (measurable_snd.add (hf.measurable.comp measurable_fst))
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hm hB, Measure.volume_eq_prod,
    Measure.prod_apply (hm hB), Measure.prod_apply hB]
  apply lintegral_congr
  intro x
  change volume ((fun t : ℝ => t + f x) ⁻¹' (Prod.mk x ⁻¹' B)) = volume (Prod.mk x ⁻¹' B)
  exact measure_preimage_add_right _ _ _

/-- The graph shear in Euclidean complex coordinates. Product coordinates are
used only for volume/Fubini, never as a substitute for Euclidean graph length. -/
def graphShear {f : ℝ → ℝ} (hf : Continuous f) : (ℝ × ℝ) ≃ₜ ℂ :=
  (shearHomeomorph hf).trans Complex.equivRealProdCLM.symm.toHomeomorph

@[simp] lemma graphShear_re {f : ℝ → ℝ} (hf : Continuous f) (p : ℝ × ℝ) :
    (graphShear hf p).re = p.1 := rfl

@[simp] lemma graphShear_im {f : ℝ → ℝ} (hf : Continuous f) (p : ℝ × ℝ) :
    (graphShear hf p).im = p.2 + f p.1 := rfl

@[simp] lemma graphShear_zero {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    graphShear hf (x, 0) = graph f x := by
  apply Complex.ext <;> simp [graph]

theorem measurePreserving_graphShear {f : ℝ → ℝ} (hf : Continuous f) :
    MeasurePreserving (graphShear hf) (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
  (MeasurePreserving.symm Complex.measurableEquivRealProd
    Complex.volume_preserving_equiv_real_prod).comp (measurePreserving_shearHomeomorph hf)

lemma preimage_epigraph_graphShear {f : ℝ → ℝ} (hf : Continuous f) :
    graphShear hf ⁻¹' epigraph f = Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
  ext p
  simp only [mem_preimage, epigraph, mem_ofPred_eq, graphShear_re, graphShear_im,
    mem_prod, mem_univ, mem_Ioi, true_and]
  constructor <;> intro h <;> linarith

/-- Exact volume change of variables on the open epigraph, for arbitrary
Bochner integrands. Integrability is checked separately before using Fubini. -/
theorem setIntegral_epigraph {f : ℝ → ℝ} (hf : Continuous f)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : ℂ → V) :
    (∫ p in Set.univ ×ˢ Set.Ioi (0 : ℝ), F (graphShear hf p)
      ∂(volume : Measure (ℝ × ℝ))) = ∫ z in epigraph f, F z := by
  rw [← preimage_epigraph_graphShear hf]
  exact (measurePreserving_graphShear hf).setIntegral_preimage_emb
    (graphShear hf).measurableEmbedding F (epigraph f)

end Paper.Geometry.GraphArea
