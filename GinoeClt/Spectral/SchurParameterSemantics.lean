/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurWordRegularity
@[expose] public section
noncomputable section
open scoped Matrix
namespace Paper.Spectral

/-- Equality of actual physical parameters recovers the actual head and tail matrices. -/
theorem schurParameterPhysical_head_tail_eq {d m : ℕ}
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin (d+m) × Fin (d+m) → ℝ)
    (h : schurParameterPhysical d m K L x = schurParameterPhysical d m K L y) :
    K (schurHeadInput (schurCellCoordinateEquiv ℝ d m x)) =
        K (schurHeadInput (schurCellCoordinateEquiv ℝ d m y)) ∧
      L (schurTailInput (schurCellCoordinateEquiv ℝ d m x)) =
        L (schurTailInput (schurCellCoordinateEquiv ℝ d m y)) := by
  have he := congrArg (fun M : Matrix (Fin (d+m)) (Fin (d+m)) ℝ =>
    M.submatrix (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d+m)) finSumFinEquiv) h
  rw [schurParameterPhysical_submatrix,schurParameterPhysical_submatrix] at he
  constructor
  · have hh := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₁₁) he
    change K (schurHeadInput (schurCellCoordinateEquiv ℝ d m x)) =
      K (schurHeadInput (schurCellCoordinateEquiv ℝ d m y)) at hh
    exact hh
  · have ht := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₂₂) he
    change L (schurTailInput (schurCellCoordinateEquiv ℝ d m x)) =
      L (schurTailInput (schurCellCoordinateEquiv ℝ d m y)) at ht
    exact ht

/-- The normalization predicates and ordered head roots depend on the actual matrix K,
rather than on its redundant angular raw cells. No spectrum simplicity is required. -/
theorem schurWordParameter_semantics_eq (w : List Bool) :
    ∀ (p q : SchurWordCells w), schurWordParameter w p = schurWordParameter w q →
      (SchurWordPositive w p ↔ SchurWordPositive w q) ∧
      (SchurWordPairGaps w p ↔ SchurWordPairGaps w q) ∧
      schurWordHeadRoots w p = schurWordHeadRoots w q := by
  induction w with
  | nil => intro p q _; exact ⟨Iff.rfl,Iff.rfl,rfl⟩
  | cons tag w ih =>
    cases tag <;> intro p q h
    · let xp := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let xq := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) q
      let hp := schurHeadInput xp
      let hq := schurHeadInput xq
      let tp := schurTailInput xp
      let tq := schurTailInput xq
      obtain ⟨hh,ht⟩ := schurParameterPhysical_head_tail_eq
        scalarHeadParameter (schurWordParameter w) p q h
      have ha : hp (0,0) = hq (0,0) := by
        have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) hh
        change hp (0,0) = hq (0,0) at he
        exact he
      have hi := ih tp tq ht
      refine ⟨hi.1,hi.2.1,?_⟩
      change ((hp (0,0) : ℂ) :: schurWordHeadRoots w tp) =
        ((hq (0,0) : ℂ) :: schurWordHeadRoots w tq)
      rw [ha,hi.2.2]
    · let xp := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let xq := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) q
      let hp := schurHeadInput xp
      let hq := schurHeadInput xq
      let tp := schurTailInput xp
      let tq := schurTailInput xq
      obtain ⟨hh,ht⟩ := schurParameterPhysical_head_tail_eq
        pairHeadParameter (schurWordParameter w) p q h
      have ha : hp (0,0) = hq (0,0) := by
        have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hh
        change hp (0,0) = hq (0,0) at he
        exact he
      have hb : hp (0,1) = hq (0,1) := by
        have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hh
        change hp (0,1) = hq (0,1) at he
        exact he
      have hc : hp (1,0) = hq (1,0) := by
        have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hh
        change -hp (1,0) = -hq (1,0) at he
        exact neg_injective he
      have hi := ih tp tq ht
      refine ⟨?_,?_,?_⟩
      · change (0 < hp (1,0) ∧ hp (1,0) ≤ hp (0,1) ∧ SchurWordPositive w tp) ↔
          (0 < hq (1,0) ∧ hq (1,0) ≤ hq (0,1) ∧ SchurWordPositive w tq)
        rw [hc,hb,hi.1]
      · change (hp (1,0) < hp (0,1) ∧ SchurWordPairGaps w tp) ↔
          (hq (1,0) < hq (0,1) ∧ SchurWordPairGaps w tq)
        rw [hc,hb,hi.2.1]
      · change (schurRoot (hp (0,0)) (hp (0,1)) (hp (1,0)) :: schurWordHeadRoots w tp) =
          (schurRoot (hq (0,0)) (hq (0,1)) (hq (1,0)) :: schurWordHeadRoots w tq)
        rw [ha,hb,hc,hi.2.2]

theorem schurWordOrdered_congr_parameter (w : List Bool) (p q : SchurWordCells w)
    (h : schurWordParameter w p = schurWordParameter w q) :
    SchurWordOrdered w p ↔ SchurWordOrdered w q := by
  unfold SchurWordOrdered
  rw [(schurWordParameter_semantics_eq w p q h).2.2]

end Paper.Spectral
