/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.MeasureTheory.FiniteFiber
@[expose] public section
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal BigOperators
namespace Paper.MeasureTheory

/-- Counts the LITERAL disjoint family fiber, preserving infinite cardinalities.
Different chart labels count as distinct points, even when chart images overlap. -/
theorem sum_fiber_encard_ennreal {I α β : Type*} [Fintype I]
    (f : I → α → β) (s : I → Set α) (y : β) :
    (∑ i : I, (({x : α | x ∈ s i ∧ f i x = y}).encard : ℝ≥0∞)) =
      (({p : I × α | p.2 ∈ s p.1 ∧ f p.1 p.2 = y}).encard : ℝ≥0∞) := by
  classical
  let T : I → Set (I × α) := fun i ↦ ({i} : Set I) ×ˢ {x | x ∈ s i ∧ f i x = y}
  have hT : Set.univ.PairwiseDisjoint T := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro p hi hj
    exact hij ((Set.mem_singleton_iff.mp hi.1).symm.trans (Set.mem_singleton_iff.mp hj.1))
  have hu : {p : I × α | p.2 ∈ s p.1 ∧ f p.1 p.2 = y} = ⋃ i, T i := by
    ext p
    simp [T]
  have hsum := ENNReal.tsum_biUnion (f := fun _ : I × α ↦ (1 : ℝ≥0∞)) hT
  rw [hu]
  simpa only [T, ENNReal.tsum_set_one, Set.encard_prod, Set.encard_singleton,
    one_mul, tsum_fintype] using hsum.symm

/-- The same literal equality in ℕ∞, without converting infinite fibers to junk Nat.card values. -/
theorem sum_fiber_encard {I α β : Type*} [Fintype I]
    (f : I → α → β) (s : I → Set α) (y : β) :
    (∑ i : I, ({x : α | x ∈ s i ∧ f i x = y}).encard) =
      ({p : I × α | p.2 ∈ s p.1 ∧ f p.1 p.2 = y}).encard := by
  apply ENat.toENNReal_inj.mp
  change ENat.toENNRealRingHom (∑ i : I, ({x : α | x ∈ s i ∧ f i x = y}).encard) = _
  rw [_root_.map_sum]
  exact sum_fiber_encard_ennreal f s y

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual fiber multiplicity times a measurable weight is measurable, by the
PROVED countable injectivity partition and actual measurable images. -/
theorem measurable_fiber_encard_mul_of_partition
    (f : E → E) (f' : E → E →L[ℝ] E) (P : ℕ → Set E)
    (hP : ∀ n, MeasurableSet (P n))
    (hd : Pairwise fun i j ↦ Disjoint (P i) (P j)) (hi : ∀ n, InjOn f (P n))
    (hf' : ∀ x ∈ ⋃ n, P n, HasFDerivWithinAt f (f' x) (⋃ n, P n) x)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun y ↦ (({x | x ∈ ⋃ n, P n ∧ f x = y}).encard : ℝ≥0∞) * g y) := by
  have himage (n : ℕ) : MeasurableSet (f '' P n) := by
    apply measurable_image_of_fderivWithin (f' := f') (hP n) _ (hi n)
    intro x hx
    exact (hf' x (mem_iUnion.mpr ⟨n,hx⟩)).mono (subset_iUnion P n)
  have hm : Measurable (fun y ↦ ∑' n, (f '' P n).indicator g y) := by
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact .iSup fun t ↦ t.measurable_fun_sum fun n _ ↦ hg.indicator (himage n)
  have he : (fun y ↦ ∑' n, (f '' P n).indicator g y) =
      fun y ↦ (({x | x ∈ ⋃ n, P n ∧ f x = y}).encard : ℝ≥0∞) * g y := by
    funext y
    exact tsum_image_indicator_eq_fiber_encard f P hd hi g y
  rw [he] at hm
  exact hm

/-- The image measurability required later is proved, not a new family assumption. -/
theorem measurable_image_of_strict_derivative_det_ne_zero
    (f : E → E) (f' : E → E →L[ℝ] E) {s : Set E} (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) : MeasurableSet (f '' s) := by
  obtain ⟨P,hP,hd,hPs,hi⟩ :=
    exists_measurable_injective_partition_of_strict_derivative f f' hs hf' hdet
  rw [← hPs, Set.image_iUnion]
  apply MeasurableSet.iUnion
  intro n
  apply measurable_image_of_fderivWithin (f' := f') (hP n) _ (hi n)
  intro x hx
  have hxs : x ∈ s := by
    rw [← hPs]
    exact mem_iUnion.mpr ⟨n,hx⟩
  exact (hf' x hxs).hasFDerivAt.hasFDerivWithinAt

/-- Finite-family COV with the actual TOTAL fiber cardinality. There is no
chartwise constant-cardinality premise, nor any disjoint-image premise. -/
theorem sum_lintegral_abs_det_mul_eq_total_fiber
    {I : Type*} [Fintype I]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : I → E → E) (f' : I → E → E →L[ℝ] E) (s : I → Set E)
    (hs : ∀ i, MeasurableSet (s i))
    (hf' : ∀ i x, x ∈ s i → HasStrictFDerivAt (f i) (f' i x) x)
    (hdet : ∀ i x, x ∈ s i → (f' i x).det ≠ 0)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∑ i : I, ∫⁻ x in s i, ENNReal.ofReal |(f' i x).det| * g (f i x) ∂μ) =
      ∫⁻ y, (({p : I × E | p.2 ∈ s p.1 ∧ f p.1 p.2 = y}).encard : ℝ≥0∞) * g y ∂μ := by
  classical
  choose P hP hd hPs hi using fun i ↦
    exists_measurable_injective_partition_of_strict_derivative (f i) (f' i) (hs i) (hf' i) (hdet i)
  have hfp (i : I) : ∀ x ∈ ⋃ n, P i n,
      HasFDerivWithinAt (f i) (f' i x) (⋃ n, P i n) x := by
    rw [hPs i]
    intro x hx
    exact (hf' i x hx).hasFDerivAt.hasFDerivWithinAt
  have hm (i : I) :
      Measurable (fun y ↦ (({x | x ∈ s i ∧ f i x = y}).encard : ℝ≥0∞) * g y) := by
    simpa only [hPs i] using
      measurable_fiber_encard_mul_of_partition (f i) (f' i) (P i) (hP i) (hd i) (hi i) (hfp i) g hg
  calc
    _ = ∑ i : I, ∫⁻ y, (({x | x ∈ s i ∧ f i x = y}).encard : ℝ≥0∞) * g y ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi'
      simpa only [hPs i] using lintegral_abs_det_mul_eq_lintegral_fiber_encard μ
        (f i) (f' i) (P i) (hP i) (hd i) (hi i) (hfp i) g hg
    _ = ∫⁻ y, ∑ i : I, (({x | x ∈ s i ∧ f i x = y}).encard : ℝ≥0∞) * g y ∂μ :=
      (lintegral_finsetSum Finset.univ (fun i _ ↦ hm i)).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [← Finset.sum_mul, sum_fiber_encard_ennreal f s y]

/-- Constant TOTAL finite multiplicity over the actual family image. hTotalCard
is only an explicit generic prerequisite; it is NOT established for any Schur atlas here. -/
theorem sum_lintegral_abs_det_mul_eq_constant_total_fiber
    {I : Type*} [Fintype I]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : I → E → E) (f' : I → E → E →L[ℝ] E) (s : I → Set E)
    (hs : ∀ i, MeasurableSet (s i))
    (hf' : ∀ i x, x ∈ s i → HasStrictFDerivAt (f i) (f' i x) x)
    (hdet : ∀ i x, x ∈ s i → (f' i x).det ≠ 0)
    (d : ℕ)
    (hTotalCard : ∀ y ∈ ⋃ i, f i '' s i,
      ({p : I × E | p.2 ∈ s p.1 ∧ f p.1 p.2 = y}).encard = (d : ℕ∞))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∑ i : I, ∫⁻ x in s i, ENNReal.ofReal |(f' i x).det| * g (f i x) ∂μ) =
      (d : ℝ≥0∞) * ∫⁻ y in ⋃ i, f i '' s i, g y ∂μ := by
  classical
  rw [sum_lintegral_abs_det_mul_eq_total_fiber μ f f' s hs hf' hdet g hg]
  have himage : MeasurableSet (⋃ i, f i '' s i) :=
    MeasurableSet.iUnion fun i ↦ measurable_image_of_strict_derivative_det_ne_zero
      (f i) (f' i) (hs i) (hf' i) (hdet i)
  rw [← lintegral_const_mul (d : ℝ≥0∞) hg, ← lintegral_indicator himage]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ ⋃ i, f i '' s i
  · rw [hTotalCard y hy, Set.indicator_of_mem hy]
    simp
  · have hempty : {p : I × E | p.2 ∈ s p.1 ∧ f p.1 p.2 = y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hy (mem_iUnion.mpr ⟨p.1,⟨p.2,hp.1,hp.2⟩⟩)
    rw [hempty]
    simp [hy]

end FiniteDimensional
end Paper.MeasureTheory
