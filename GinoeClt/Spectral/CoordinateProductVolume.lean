/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Logic.Equiv.Set
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace Paper.Spectral

/-- The complementary coordinates are literal original cell indices. -/
abbrev CoordinateRemainder {A C : Type*} [Fintype A] [DecidableEq C] (f : A → C) :=
  {c : C // c ∉ (Finset.univ.image f : Finset C)}

/-- A genuine finite index permutation, with no scalar rescaling. -/
def coordinateJoinIndex {A C : Type*} [Fintype A] [DecidableEq C]
    (f : A → C) (hf : Function.Injective f) :
    A ⊕ CoordinateRemainder f ≃ C := by
  classical
  let eRange : Set.range f ≃ (Finset.univ.image f : Finset C) :=
    Equiv.subtypeEquivRight (fun c => by simp [Set.mem_range])
  exact (Equiv.sumCongr ((Equiv.ofInjective f hf).trans eRange)
    (Equiv.refl (CoordinateRemainder f))).trans
      (Equiv.sumCompl (fun c : C => c ∈ (Finset.univ.image f : Finset C)))

@[simp] theorem coordinateJoinIndex_inl {A C : Type*} [Fintype A] [DecidableEq C] (f : A → C)
    (hf : Function.Injective f) (a : A) : coordinateJoinIndex f hf (Sum.inl a) = f a := rfl

@[simp] theorem coordinateJoinIndex_inr {A C : Type*} [Fintype A] [DecidableEq C] (f : A → C)
    (hf : Function.Injective f) (c : CoordinateRemainder f) :
    coordinateJoinIndex f hf (Sum.inr c) = c.val := rfl

/-- The first output reads the selected literal cells and the second all remaining cells. -/
def coordinateSplit {A C : Type*} [Fintype A] [DecidableEq C] (f : A → C) (x : C → ℝ) :
    (A → ℝ) × (CoordinateRemainder f → ℝ) :=
  (fun a => x (f a), fun c => x c.val)

/-- Ordinary Pi Lebesgue volume is exactly the product volume after a cell permutation. -/
theorem volume_preserving_coordinateSplit {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (f : A → C) (hf : Function.Injective f) :
    MeasurePreserving (coordinateSplit f) volume volume := by
  let e := coordinateJoinIndex f hf
  have h₁ := volume_measurePreserving_piCongrLeft
    (fun _ : A ⊕ CoordinateRemainder f => ℝ) e.symm
  have h₂ := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : A ⊕ CoordinateRemainder f => ℝ)
  have he : (MeasurableEquiv.sumPiEquivProdPi (fun _ : A ⊕ CoordinateRemainder f => ℝ)) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : A ⊕ CoordinateRemainder f => ℝ) e.symm) =
      coordinateSplit f := by
    funext x
    apply Prod.ext
    · funext a
      change (MeasurableEquiv.piCongrLeft (fun _ : A ⊕ CoordinateRemainder f => ℝ) e.symm x) (.inl a) = x (f a)
      have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
        (β := fun _ : A ⊕ CoordinateRemainder f => ℝ) x (e (.inl a))
      simp only [Equiv.symm_apply_apply] at h
      simpa only [e, coordinateJoinIndex_inl] using h
    · funext c
      change (MeasurableEquiv.piCongrLeft (fun _ : A ⊕ CoordinateRemainder f => ℝ) e.symm x) (.inr c) = x c.val
      have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
        (β := fun _ : A ⊕ CoordinateRemainder f => ℝ) x (e (.inr c))
      simp only [Equiv.symm_apply_apply] at h
      simpa only [e, coordinateJoinIndex_inr] using h
  simpa only [he] using h₂.comp h₁

end Paper.Spectral
