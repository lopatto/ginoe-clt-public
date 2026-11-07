/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MeasureTheory

/-- A literal product of measure sums is the sum over every subset of coordinates,
with ν in the selected positions and μ in the complement. Empty indices included. -/
theorem pi_add_eq_sum_selected {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] :
    Measure.pi (fun _ : ι => μ+ν) =
      ∑ s : Finset ι, Measure.pi (fun i : ι => if i ∈ s then ν else μ) := by
  classical
  have hrect (s : Finset ι) (t : ι → Set X) :
      (Measure.pi (fun i : ι => if i ∈ s then ν else μ)) (Set.pi Set.univ t) =
        (∏ i ∈ s, ν (t i)) * ∏ i ∈ sᶜ, μ (t i) := by
    have : ∀ i : ι, SigmaFinite (if i ∈ s then ν else μ) := fun i => by
      split <;> infer_instance
    rw [Measure.pi_pi]
    have he (i : ι) : (if i ∈ s then ν else μ) (t i) =
        if i ∈ s then ν (t i) else μ (t i) := by
      by_cases hi : i ∈ s <;> simp only [hi,ite_true,ite_false]
    simp_rw [he]
    have hplus : Finset.univ.filter (fun i : ι => i ∈ s) = s := by ext i; simp
    have hminus : Finset.univ.filter (fun i : ι => i ∉ s) = sᶜ := by ext i; simp
    rw [Finset.prod_ite,hplus,hminus]
  apply Measure.pi_eq
  intro t ht
  rw [Measure.finsetSum_apply]
  calc
    _ = ∑ s : Finset ι, (∏ i ∈ s, ν (t i)) * ∏ i ∈ sᶜ, μ (t i) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hrect s t
    _ = ∏ i : ι, (ν (t i)+μ (t i)) := (Fintype.prod_add (fun i => ν (t i)) (fun i => μ (t i))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Measure.add_apply]
      exact add_comm _ _

/-- L1 under the product of the sum measure is EXACTLY L1 under every selected
coordinate product. In particular no signed integral is split before L1. -/
theorem integrable_pi_add_iff {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → X) → ℂ) :
    Integrable F (Measure.pi (fun _ : ι => μ+ν)) ↔
      ∀ s : Finset ι, Integrable F (Measure.pi (fun i : ι => if i ∈ s then ν else μ)) := by
  rw [pi_add_eq_sum_selected μ ν,integrable_finsetSum_measure]
  simp only [Finset.mem_univ,forall_true_left]

/-- The genuine complex Bochner integral expansion, including zero measures,
empty index families, and integrable functions of arbitrary sign. -/
theorem integral_pi_add_eq_sum_selected {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → X) → ℂ) (hF : Integrable F (Measure.pi (fun _ : ι => μ+ν))) :
    (∫ x, F x ∂Measure.pi (fun _ : ι => μ+ν)) =
      ∑ s : Finset ι, ∫ x, F x ∂Measure.pi (fun i : ι => if i ∈ s then ν else μ) := by
  have hs := (integrable_pi_add_iff μ ν F).mp hF
  rw [pi_add_eq_sum_selected μ ν]
  exact integral_finsetSum_measure (fun s hs' => hs s)

end MeasureTheory
