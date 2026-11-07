/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.SelectedPairDeterminants
public import Mathlib.Data.Finset.Sum

/-! # The exact selected-subset regrouping for finite atomic Pfaffian updates -/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace Paper.SkewOrthogonal

/-- A selected m-subset of baseline and atom labels is equivalently a missing
baseline set and an equally large selected atom set. No combinatorial factor occurs. -/
theorem sum_powersetCard_disjSum_compl {A : Type*} [AddCommMonoid A]
    (m r : ℕ) (F : Finset (Fin m ⊕ Fin r) → A) :
    (∑ U ∈ (Finset.univ : Finset (Fin m ⊕ Fin r)).powersetCard m, F U) =
      ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∑ S ∈ (Finset.univ : Finset (Fin r)).powersetCard T.card, F (Tᶜ.disjSum S) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun U _ ↦ ⟨U.toLeftᶜ, U.toRight⟩)
    (fun P _ ↦ P.1ᶜ.disjSum P.2) ?_ ?_ ?_ ?_ ?_
  · intro U hU
    refine Finset.mem_sigma.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    have hc := (Finset.mem_powersetCard.mp hU).2
    have hs := Finset.card_toLeft_add_card_toRight (u := U)
    have hl : U.toLeft.card ≤ m := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ U.toLeft)
    simp only [Finset.card_compl, Fintype.card_fin]
    omega
  · intro P hP
    rcases Finset.mem_sigma.mp hP with ⟨hT, hS⟩
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    have hc := (Finset.mem_powersetCard.mp hS).2
    have ht : P.1.card ≤ m := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ P.1)
    rw [Finset.card_disjSum, Finset.card_compl, Fintype.card_fin, hc]
    omega
  · intro U hU
    simpa only [compl_compl] using Finset.toLeft_disjSum_toRight (u := U)
  · intro P hP
    simp
  · intro U hU
    simp only [compl_compl, Finset.toLeft_disjSum_toRight]

end Paper.SkewOrthogonal
