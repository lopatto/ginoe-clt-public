/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

The image comparison and sandwich proof patterns are narrowly adapted from
human-ai-mathematics/kls-lean, revision 33fff6ea218ae07e42115bd1eacfcf7d39c534cb,
FunctionalInequalities/Analysis/Graph/Area.lean, lines 502–616 (Apache-2.0).
This planar specialization uses native one-dimensional Hausdorff scaling.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section
@[expose] public section
open MeasureTheory Set
open scoped NNReal ENNReal

namespace Paper.Geometry.GraphArea

/-- The unrotated planar graph in the usual Euclidean complex norm. -/
def graph (f : ℝ → ℝ) (x : ℝ) : ℂ := (x : ℂ) + (f x : ℂ) * Complex.I

/-- The linear graph with real slope `a`. -/
def linearGraph (a x : ℝ) : ℂ := x • (1 + (a : ℂ) * Complex.I)

/-- The exact Euclidean length expansion of a linear graph. -/
def jacobian (a : ℝ) : ℝ := ‖(1 : ℂ) + (a : ℂ) * Complex.I‖

lemma graph_injective (f : ℝ → ℝ) : Function.Injective (graph f) := by
  intro x y h
  simpa [graph] using congrArg Complex.re h

lemma linearGraph_injective (a : ℝ) : Function.Injective (linearGraph a) := by
  intro x y h
  simpa [linearGraph] using congrArg Complex.re h

lemma norm_sub_le_graph (f : ℝ → ℝ) (x y : ℝ) :
    ‖x - y‖ ≤ ‖graph f x - graph f y‖ := by
  simpa [graph, Real.norm_eq_abs] using Complex.abs_re_le_norm (graph f x - graph f y)

lemma norm_sub_le_linearGraph (a x y : ℝ) :
    ‖x - y‖ ≤ ‖linearGraph a x - linearGraph a y‖ := by
  simpa [linearGraph, Real.norm_eq_abs] using
    Complex.abs_re_le_norm (linearGraph a x - linearGraph a y)

lemma hausdorffMeasure_linearGraph (a : ℝ) (E : Set ℝ) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (linearGraph a '' E) =
      ENNReal.ofReal (jacobian a) * volume E := by
  change (Measure.hausdorffMeasure 1 : Measure ℂ)
      ((fun x : ℝ => x • ((1 : ℂ) + (a : ℂ) * Complex.I)) '' E) = _
  rw [hausdorffMeasure_smul_right_image, hausdorffMeasure_real, ENNReal.smul_def,
    smul_eq_mul]
  congr 1
  exact ENNReal.ofReal_coe_nnreal.symm

/-- Hausdorff image comparison through an injective reference parametrization. -/
lemma hausdorffMeasure_image_le_of_norm_le {f₁ f₂ : ℝ → ℂ} {E : Set ℝ} {K : ℝ≥0}
    (hinj : Set.InjOn f₂ E)
    (hle : ∀ x ∈ E, ∀ y ∈ E, ‖f₁ x - f₁ y‖ ≤ (K : ℝ) * ‖f₂ x - f₂ y‖) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (f₁ '' E) ≤
      (K : ℝ≥0∞) * (Measure.hausdorffMeasure 1 : Measure ℂ) (f₂ '' E) := by
  classical
  have himg : (f₁ ∘ Function.invFunOn f₂ E) '' (f₂ '' E) = f₁ '' E := by
    rw [← Set.image_comp]
    refine Set.image_congr fun x hx => ?_
    simp only [Function.comp_apply, hinj.leftInvOn_invFunOn hx]
  rw [← himg]
  have hLip : LipschitzOnWith K (f₁ ∘ Function.invFunOn f₂ E) (f₂ '' E) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro x ⟨y, hy, rfl⟩ x' ⟨y', hy', rfl⟩
    simp only [Function.comp_apply, hinj.leftInvOn_invFunOn hy, hinj.leftInvOn_invFunOn hy']
    rw [dist_eq_norm, dist_eq_norm]
    exact hle y hy y' hy'
  simpa only [ENNReal.rpow_one] using hLip.hausdorffMeasure_image_le (d := 1) (by norm_num)

lemma norm_graph_sub_linearGraph_le {f : ℝ → ℝ} {a : ℝ} {E : Set ℝ} {ε : ℝ≥0}
    (h : ApproximatesLinearOn f (a • ContinuousLinearMap.id ℝ ℝ) E ε)
    {x y : ℝ} (hx : x ∈ E) (hy : y ∈ E) :
    ‖(graph f x - graph f y) - (linearGraph a x - linearGraph a y)‖ ≤
      (ε : ℝ) * ‖x - y‖ := by
  have heq : (graph f x - graph f y) - (linearGraph a x - linearGraph a y) =
      ((f x - f y - a * (x - y) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [graph, linearGraph]; ring
  rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    using h x hx y hy

/-- Upper measure sandwich for any scalar graph uniformly approximated by a line. -/
theorem hausdorffMeasure_graph_le {f : ℝ → ℝ} {a : ℝ} {E : Set ℝ} {ε : ℝ≥0}
    (h : ApproximatesLinearOn f (a • ContinuousLinearMap.id ℝ ℝ) E ε) :
    (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' E) ≤
      ((1 + ε : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (jacobian a) * volume E := by
  have hcmp : ∀ x ∈ E, ∀ y ∈ E,
      ‖graph f x - graph f y‖ ≤ (1 + ε : ℝ≥0) * ‖linearGraph a x - linearGraph a y‖ := by
    intro x hx y hy
    have h1 := norm_graph_sub_linearGraph_le h hx hy
    have h2 := norm_sub_le_linearGraph a x y
    have h3 := norm_add_le
      ((graph f x - graph f y) - (linearGraph a x - linearGraph a y))
      (linearGraph a x - linearGraph a y)
    rw [sub_add_cancel] at h3
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h2 ε.coe_nonneg]
  have hle := hausdorffMeasure_image_le_of_norm_le (linearGraph_injective a).injOn hcmp
  simpa only [hausdorffMeasure_linearGraph, mul_assoc] using hle

/-- Reverse measure sandwich; no regularity, measurability or nonemptiness is needed. -/
theorem le_hausdorffMeasure_graph {f : ℝ → ℝ} {a : ℝ} {E : Set ℝ} {ε : ℝ≥0}
    (h : ApproximatesLinearOn f (a • ContinuousLinearMap.id ℝ ℝ) E ε) :
    ENNReal.ofReal (jacobian a) * volume E ≤
      ((1 + ε : ℝ≥0) : ℝ≥0∞) * (Measure.hausdorffMeasure 1 : Measure ℂ) (graph f '' E) := by
  have hcmp : ∀ x ∈ E, ∀ y ∈ E,
      ‖linearGraph a x - linearGraph a y‖ ≤ (1 + ε : ℝ≥0) * ‖graph f x - graph f y‖ := by
    intro x hx y hy
    have h1 := norm_graph_sub_linearGraph_le h hx hy
    have h2 := norm_sub_le_graph f x y
    have h3 := norm_add_le
      ((linearGraph a x - linearGraph a y) - (graph f x - graph f y))
      (graph f x - graph f y)
    rw [sub_add_cancel] at h3
    rw [norm_sub_rev] at h1
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h2 ε.coe_nonneg]
  have hle := hausdorffMeasure_image_le_of_norm_le (graph_injective f).injOn hcmp
  rwa [hausdorffMeasure_linearGraph] at hle

end Paper.Geometry.GraphArea
