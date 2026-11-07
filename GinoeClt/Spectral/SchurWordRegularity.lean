/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWordSeparation
public import GinoeClt.Spectral.SchurWordMeasure

/-! Consequences of the literal nonzero word Jacobian. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

/-- Every normalized pair has a strict off-diagonal gap; scalar blocks add no condition. -/
def SchurWordPairGaps : (w : List Bool) → SchurWordCells w → Prop
  | [], _ => True
  | false::w, p =>
      SchurWordPairGaps w (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p))
  | true::w, p =>
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      h (1,0) < h (0,1) ∧ SchurWordPairGaps w (schurTailInput x)

/-- The actual regular locus excludes every degenerate pair gap. -/
theorem schurWordPairGaps_of_regular (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p →
      LinearMap.det (schurWordDifferential w p) ≠ 0 → SchurWordPairGaps w p := by
  induction w with
  | nil => intro p hp hd; trivial
  | cons tag w ih =>
    cases tag <;> intro p hp hd
    · rw [det_schurWordDifferential_false w p] at hd
      exact ih _ hp (mul_ne_zero_iff.mp hd).2
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      obtain ⟨hc, hcb, ht⟩ := hp
      rw [det_schurWordDifferential_true w p] at hd
      have htail := (mul_ne_zero_iff.mp hd).2
      have hgap := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hd).1).2
      change h (1,0) < h (0,1) ∧ SchurWordPairGaps w t
      refine ⟨lt_of_le_of_ne hcb ?_, ih t ht htail⟩
      intro he
      apply hgap
      change 2 * (h (0,1) - h (1,0)) = 0
      rw [← he, sub_self, mul_zero]

/-- A regular point makes the actual full commutator linear map injective. -/
theorem schurWordDifferential_injective (w : List Bool) (p : SchurWordCells w)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0) :
    Function.Injective (schurWordDifferential w p) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hk
  exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)

/-- At a regular word, its actual angle and matrix maps jointly determine all
raw cells. No abstract coordinate or measure normalization is used. -/
theorem schurWord_joint_injective (w : List Bool) (p : SchurWordCells w)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0) :
    Function.Injective (fun x : SchurWordCells w => (schurWordOmega w x, schurWordParameter w x)) := by
  intro x y hxy
  have hΩ : schurWordOmega w x = schurWordOmega w y := congrArg Prod.fst hxy
  have hK : schurWordParameter w x = schurWordParameter w y := congrArg Prod.snd hxy
  apply schurWordDifferential_injective w p hd
  change Matrix.vec (schurWordParameter w x + schurWordOmega w x * schurWordParameter w p -
    schurWordParameter w p * schurWordOmega w x) =
    Matrix.vec (schurWordParameter w y + schurWordOmega w y * schurWordParameter w p -
      schurWordParameter w p * schurWordOmega w y)
  rw [hΩ, hK]

/-- In particular zero-angle regular free parameters are fixed by their actual matrix. -/
theorem schurWord_cells_eq_of_parameter_eq (w : List Bool) (p x y : SchurWordCells w)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0)
    (hx : schurWordOmega w x = 0) (hy : schurWordOmega w y = 0)
    (hK : schurWordParameter w x = schurWordParameter w y) : x = y :=
  schurWord_joint_injective w p hd (Prod.ext (hx.trans hy.symm) hK)

end Paper.Spectral
