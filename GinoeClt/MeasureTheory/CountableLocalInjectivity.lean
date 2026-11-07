/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Borel injectivity partitions from actual local injectivity. -/
@[expose] public section
noncomputable section
open Set

namespace Paper.MeasureTheory

theorem exists_measurable_injective_partition
    {E F : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (f : E → F) {s : Set E}
    (hs : MeasurableSet s)
    (hlocal : ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ InjOn f U) :
    ∃ P : ℕ → Set E, (∀ n, MeasurableSet (P n)) ∧
      (Pairwise fun i j => Disjoint (P i) (P j)) ∧
      (⋃ n, P n) = s ∧ ∀ n, InjOn f (P n) := by
  classical
  by_cases hn : s.Nonempty
  · let : Nonempty s := hn.to_subtype
    let U : s → Set E := fun x => (hlocal x.val x.property).choose
    have hU : ∀ x : s, IsOpen (U x) ∧ x.val ∈ U x ∧ InjOn f (U x) :=
      fun x => (hlocal x.val x.property).choose_spec
    have hcover : s ⊆ ⋃ x : s, U x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩
    obtain ⟨a, ha⟩ :=
      (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover U
        (fun x => (hU x).1) hcover
    let V : ℕ → Set E := fun n => s ∩ U (a n)
    have hV : ∀ n, MeasurableSet (V n) := fun n =>
      hs.inter (hU (a n)).1.measurableSet
    have hVs : (⋃ n, V n) = s := by
      apply Subset.antisymm
      · exact iUnion_subset fun n => inter_subset_left
      · intro x hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp (ha hx)
        exact mem_iUnion.mpr ⟨n, hx, hn⟩
    refine ⟨disjointed V, fun n => MeasurableSet.disjointed hV n,
      disjoint_disjointed V, ?_, ?_⟩
    · rw [iUnion_disjointed, hVs]
    · intro n
      apply (hU (a n)).2.2.mono
      exact (disjointed_subset V n).trans inter_subset_right
  · have hs0 : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    subst s
    refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, ?_, by simp, ?_⟩
    · intro i j hij
      simp
    · intro n x hx
      exact False.elim hx

theorem exists_measurable_injective_partition_of_strict_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → E) (f' : E → E →L[ℝ] E) {s : Set E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasStrictFDerivAt f (f' x) x)
    (hdet : ∀ x ∈ s, (f' x).det ≠ 0) :
    ∃ P : ℕ → Set E, (∀ n, MeasurableSet (P n)) ∧
      (Pairwise fun i j => Disjoint (P i) (P j)) ∧
      (⋃ n, P n) = s ∧ ∀ n, InjOn f (P n) := by
  apply exists_measurable_injective_partition f hs
  intro x hx
  let L := (f' x).toContinuousLinearEquivOfDetNeZero (hdet x hx)
  have hL : HasStrictFDerivAt f (L : E →L[ℝ] E) x := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      using hf' x hx
  let e := hL.toOpenPartialHomeomorph f
  exact ⟨e.source, e.open_source, hL.mem_toOpenPartialHomeomorph_source, e.injOn⟩

end Paper.MeasureTheory
