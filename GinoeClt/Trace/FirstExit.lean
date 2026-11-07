/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.AnchoredIntegral
public import Mathlib.Data.Finset.Max

/-! # The first-exit partition of the anchored cycle domain -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Paper.Trace

def firstExitDomain (A : Set ℂ) (n : ℕ) (j : Fin n) : Set (Fin (n + 1) → ℂ) :=
  {x | x 0 ∈ A ∧ (∀ i : Fin n, i < j → x i.succ ∈ A) ∧ x j.succ ∉ A}

theorem measurableSet_firstExitDomain {A : Set ℂ} (hA : MeasurableSet A)
    (n : ℕ) (j : Fin n) : MeasurableSet (firstExitDomain A n j) := by
  have hp : MeasurableSet {x : Fin (n + 1) → ℂ | ∀ i : Fin n, i < j → x i.succ ∈ A} := by
    have he : {x : Fin (n + 1) → ℂ | ∀ i : Fin n, i < j → x i.succ ∈ A} =
        ⋂ i : Fin n, {x : Fin (n + 1) → ℂ | i < j → x i.succ ∈ A} := by
      ext x
      simp
    rw [he]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hij : i < j
    · simp only [hij, true_implies]
      exact hA.preimage (measurable_pi_apply i.succ)
    · simp [hij]
  exact (hA.preimage (measurable_pi_apply 0)).inter
    (hp.inter (hA.preimage (measurable_pi_apply j.succ)).compl)

theorem pairwise_disjoint_firstExitDomain (A : Set ℂ) (n : ℕ) :
    Pairwise (fun i j : Fin n => Disjoint (firstExitDomain A n i) (firstExitDomain A n j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact hx.2.2 (hy.2.1 i h)
  · exact hy.2.2 (hx.2.1 j h)

theorem anchoredDomain_eq_inside_union_firstExit (A : Set ℂ) (n : ℕ) :
    {x : Fin (n + 1) → ℂ | x 0 ∈ A} =
      Set.univ.pi (fun _ : Fin (n + 1) => A) ∪ ⋃ j : Fin n, firstExitDomain A n j := by
  classical
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_univ_pi, firstExitDomain, Set.mem_ofPred_eq]
  constructor
  · intro hx
    by_cases hall : ∀ i : Fin n, x i.succ ∈ A
    · left
      exact Fin.cases hx (fun i => hall i)
    · right
      let B : Finset (Fin n) := Finset.univ.filter (fun i => x i.succ ∉ A)
      have hB : B.Nonempty := by
        push Not at hall
        obtain ⟨j, hj⟩ := hall
        exact ⟨j, by simp [B, hj]⟩
      let j : Fin n := B.min' hB
      refine ⟨j, hx, ?_, ?_⟩
      · intro i hij
        by_contra hi
        have hji : j ≤ i := Finset.min'_le B i (by simp [B, hi])
        exact (not_le_of_gt hij) hji
      · exact (Finset.mem_filter.mp (Finset.min'_mem B hB)).2
  · rintro (hx | ⟨j, hj⟩)
    · exact hx 0
    · exact hj.1

theorem firstExitDomain_subset_anchor (A : Set ℂ) (n : ℕ) (j : Fin n) :
    firstExitDomain A n j ⊆ {x | x 0 ∈ A} := fun _ hx => hx.1

theorem inside_subset_anchor (A : Set ℂ) (n : ℕ) :
    Set.univ.pi (fun _ : Fin (n + 1) => A) ⊆ {x | x 0 ∈ A} := by
  intro x hx
  exact hx 0 (Set.mem_univ _)

theorem integral_inside_eq_anchor_sub_firstExit {A : Set ℂ} (hA : MeasurableSet A)
    (n : ℕ) (f : (Fin (n + 1) → ℂ) → ℂ)
    (hf : IntegrableOn f {x | x 0 ∈ A}) :
    (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A), f x) =
      (∫ x in {x | x 0 ∈ A}, f x) - ∑ j : Fin n, ∫ x in firstExitDomain A n j, f x := by
  have hi := hf.mono_set (inside_subset_anchor A n)
  have hj (j : Fin n) := hf.mono_set (firstExitDomain_subset_anchor A n j)
  have hu : IntegrableOn f (⋃ j : Fin n, firstExitDomain A n j) :=
    hf.mono_set (iUnion_subset fun j => firstExitDomain_subset_anchor A n j)
  have hd : Disjoint (Set.univ.pi (fun _ : Fin (n + 1) => A))
      (⋃ j : Fin n, firstExitDomain A n j) := by
    apply Set.disjoint_left.mpr
    intro x hx hxe
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxe
    exact hxj.2.2 (hx j.succ (Set.mem_univ _))
  have hs : (∫ x in ⋃ j : Fin n, firstExitDomain A n j, f x) =
      ∑ j : Fin n, ∫ x in firstExitDomain A n j, f x :=
    integral_iUnion_fintype (fun j => measurableSet_firstExitDomain hA n j)
      (pairwise_disjoint_firstExitDomain A n) hj
  have he : (∫ x in {x | x 0 ∈ A}, f x) =
      (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A), f x) +
        ∑ j : Fin n, ∫ x in firstExitDomain A n j, f x := by
    rw [anchoredDomain_eq_inside_union_firstExit A n,
      setIntegral_union hd (MeasurableSet.iUnion fun j => measurableSet_firstExitDomain hA n j)
        hi hu, hs]
  exact eq_sub_iff_add_eq.mpr he.symm

theorem cycleIntegral_eq_anchor_sub_firstExit {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) :
    (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A), Complex.exp (cycleExponent a x)) =
      ((volume.real A : ℝ) : ℂ) * (((Real.pi / a : ℝ) : ℂ)) ^ n -
        ∑ j : Fin n, ∫ x in firstExitDomain A n j, Complex.exp (cycleExponent a x) := by
  have h := integral_inside_eq_anchor_sub_firstExit hA n _
    (anchored_cycle_integral ha n A hfin).1
  rw [(anchored_cycle_integral ha n A hfin).2] at h
  exact h

end Paper.Trace
