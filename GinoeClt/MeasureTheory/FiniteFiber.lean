/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.MeasureTheory.CountableLocalInjectivity
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Countable injectivity pieces and actual fiber multiplicity. -/

@[expose] public section
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Paper.MeasureTheory

theorem tsum_image_indicator_eq_fiber_encard {α β : Type*}
    (f : α → β) (P : ℕ → Set α)
    (hd : Pairwise fun i j => Disjoint (P i) (P j))
    (hi : ∀ n, InjOn f (P n)) (g : β → ℝ≥0∞) (y : β) :
    (∑' n, (f '' P n).indicator g y) =
      (({x | x ∈ ⋃ n, P n ∧ f x = y}).encard : ℝ≥0∞) * g y := by
  classical
  have hd' : Set.univ.PairwiseDisjoint (fun n => P n ∩ f ⁻¹' {y}) := by
    intro i _ j _ hij
    exact (hd hij).mono inter_subset_left inter_subset_left
  change _ = ((((⋃ n, P n) ∩ f ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) * g y
  rw [Set.iUnion_inter, ← ENNReal.tsum_set_const]
  rw [ENNReal.tsum_biUnion (f := fun _ : α => g y) hd']
  apply tsum_congr
  intro n
  rw [ENNReal.tsum_set_const,
    ← ((hi n).mono inter_subset_left).encard_image,
    Set.image_inter_preimage]
  by_cases hy : y ∈ f '' P n
  · simp [hy]
  · simp [hy]

theorem lintegral_abs_det_mul_eq_lintegral_fiber_encard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E) (P : ℕ → Set E)
    (hP : ∀ n, MeasurableSet (P n))
    (hd : Pairwise fun i j => Disjoint (P i) (P j))
    (hi : ∀ n, InjOn f (P n))
    (hf' : ∀ x ∈ ⋃ n, P n, HasFDerivWithinAt f (f' x) (⋃ n, P n) x)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in ⋃ n, P n, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ) =
      ∫⁻ y, (({x | x ∈ ⋃ n, P n ∧ f x = y}).encard : ℝ≥0∞) * g y ∂μ := by
  have hfP : ∀ n x, x ∈ P n → HasFDerivWithinAt f (f' x) (P n) x := by
    intro n x hx
    exact (hf' x (mem_iUnion.mpr ⟨n, hx⟩)).mono (subset_iUnion P n)
  have himage : ∀ n, MeasurableSet (f '' P n) := fun n =>
    measurable_image_of_fderivWithin (hP n) (hfP n) (hi n)
  calc
    _ = ∑' n, ∫⁻ x in P n, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ :=
      lintegral_iUnion hP hd _
    _ = ∑' n, ∫⁻ y in f '' P n, g y ∂μ := by
      apply tsum_congr
      intro n
      exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul μ
        (hP n) (hfP n) (hi n) g).symm
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator g y ∂μ := by
      apply tsum_congr
      intro n
      exact (lintegral_indicator (himage n) g).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator g y ∂μ :=
      (lintegral_tsum fun n => (hg.indicator (himage n)).aemeasurable).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      exact tsum_image_indicator_eq_fiber_encard f P hd hi g y

/-- A constant finite multiplicity follows only from the literal fiber-cardinality
hypothesis on the actual image. No Schur multiplicity is assumed by this lemma. -/
theorem lintegral_abs_det_mul_eq_constant_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E) (P : ℕ → Set E)
    (hP : ∀ n, MeasurableSet (P n))
    (hd : Pairwise fun i j => Disjoint (P i) (P j))
    (hi : ∀ n, InjOn f (P n))
    (hf' : ∀ x ∈ ⋃ n, P n, HasFDerivWithinAt f (f' x) (⋃ n, P n) x)
    (d : ℕ)
    (hcard : ∀ y ∈ f '' (⋃ n, P n),
      ({x | x ∈ ⋃ n, P n ∧ f x = y}).encard = (d : ℕ∞))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in ⋃ n, P n, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ) =
      (d : ℝ≥0∞) * ∫⁻ y in f '' (⋃ n, P n), g y ∂μ := by
  rw [lintegral_abs_det_mul_eq_lintegral_fiber_encard μ f f' P hP hd hi hf' g hg]
  have himage : MeasurableSet (f '' (⋃ n, P n)) := by
    rw [Set.image_iUnion]
    apply MeasurableSet.iUnion
    intro n
    apply measurable_image_of_fderivWithin (f' := f') (hP n) _ (hi n)
    intro x hx
    exact (hf' x (mem_iUnion.mpr ⟨n, hx⟩)).mono (subset_iUnion P n)
  rw [← lintegral_const_mul (d : ℝ≥0∞) hg, ← lintegral_indicator himage]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ f '' (⋃ n, P n)
  · rw [hcard y hy, Set.indicator_of_mem hy]
    simp
  · have hfempty : {x | x ∈ ⋃ n, P n ∧ f x = y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, hx.1, hx.2⟩
    rw [hfempty]
    simp [hy]

/-- Finite-to-one change of variables from actual local nonsingularity and
a completely explicit constant cardinality of the actual fibers. -/
theorem lintegral_abs_det_mul_eq_constant_fiber_of_strict_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E) {s : Set E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0)
    (d : ℕ)
    (hcard : ∀ y ∈ f '' s, ({x | x ∈ s ∧ f x = y}).encard = (d : ℕ∞))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ) =
      (d : ℝ≥0∞) * ∫⁻ y in f '' s, g y ∂μ := by
  obtain ⟨P, hP, hd, hPs, hi⟩ :=
    exists_measurable_injective_partition_of_strict_derivative f f' hs hf' hdet
  have hfP : ∀ x ∈ ⋃ n, P n,
      HasFDerivWithinAt f (f' x) (⋃ n, P n) x := by
    rw [hPs]
    intro x hx
    exact (hf' x hx).hasFDerivAt.hasFDerivWithinAt
  have hcardP : ∀ y ∈ f '' (⋃ n, P n),
      ({x | x ∈ ⋃ n, P n ∧ f x = y}).encard = (d : ℕ∞) := by
    simpa only [hPs] using hcard
  simpa only [hPs] using
    lintegral_abs_det_mul_eq_constant_fiber μ f f' P hP hd hi hfP d hcardP g hg

end Paper.MeasureTheory
