/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFreeGaussianIntegration
public import GinoeClt.Spectral.SchurFullRoots
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix
namespace Paper.Spectral

/-- The entire genuine representative vector is continuous, also at collisions. -/
theorem continuous_schurWordHeadRootVector (w : List Bool) :
    Continuous (fun p : SchurWordCells w => schurWordHeadRootAt w p) :=
  continuous_pi (continuous_schurWordHeadRootAt w)

theorem measurable_schurWordPairRatio (w : List Bool) :
    Measurable (schurWordPairRatio w) := by
  induction w with
  | nil => exact measurable_const
  | cons tag w ih =>
    cases tag
    · exact ih.comp (continuous_schur_tail_cells 1 (schurWordSize w)).measurable
    · have hb := (continuous_schur_head_cell 2 (schurWordSize w) (0,1)).measurable
      have hc := (continuous_schur_head_cell 2 (schurWordSize w) (1,0)).measurable
      have hr := (hb.sub hc).div (Real.continuous_sqrt.measurable.comp (hb.mul hc))
      have ht := ih.comp (continuous_schur_tail_cells 2 (schurWordSize w)).measurable
      simpa only [schurWordPairRatio,Function.comp_def,Pi.mul_apply,Pi.div_apply,Pi.sub_apply] using! hr.mul ht

theorem schurWordPairRatio_nonneg (w : List Bool) :
    ∀ p : SchurWordCells w, SchurWordPositive w p → 0 ≤ schurWordPairRatio w p := by
  induction w with
  | nil => intro p hp; exact zero_le_one
  | cons tag w ih =>
    cases tag <;> intro p hp
    · exact ih _ hp
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      exact mul_nonneg (div_nonneg (sub_nonneg.mpr hp.2.1) (Real.sqrt_nonneg _))
        (ih t hp.2.2)

theorem scalarStepFree_headRootAt (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ) :
    schurWordHeadRootAt (false::w) (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U) =
      Fin.cons (a : ℂ) (schurWordHeadRootAt w t) := by
  simp only [schurWordHeadRootAt,schurStepFreeCells_coordinates,
    schurHeadInput_free,schurTailInput_free]

theorem pairStepFree_headRootAt (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ) :
    schurWordHeadRootAt (true::w) (schurStepFreeCells (pairFreeInput a b c) t U) =
      Fin.cons (schurRoot a b c) (schurWordHeadRootAt w t) := by
  simp [schurWordHeadRootAt,schurStepFreeCells_coordinates,
    schurHeadInput_free,schurTailInput_free,pairFreeInput,Function.flip_def]

theorem scalarStepFree_pairRatio (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ) :
    schurWordPairRatio (false::w) (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U) =
      schurWordPairRatio w t := by
  simp only [schurWordPairRatio,schurStepFreeCells_coordinates,schurTailInput_free]

theorem pairStepFree_pairRatio (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ) :
    schurWordPairRatio (true::w) (schurStepFreeCells (pairFreeInput a b c) t U) =
      ((b-c)/Real.sqrt (b*c))*schurWordPairRatio w t := by
  simp [schurWordPairRatio,schurStepFreeCells_coordinates,
    schurHeadInput_free,schurTailInput_free,pairFreeInput,Function.flip_def]

/-- These are the actual, original weak source positivity conditions in the
literal free coordinates. No regularity or ordering condition is added. -/
theorem scalarFree_positive_iff (w : List Bool) (y : SchurWordFreeIndex (false::w) → ℝ) :
    SchurWordPositive (false::w) (schurWordFreeCells (false::w) y) ↔
      SchurWordPositive w (schurWordFreeCells w (scalarFreeSplit w y).2.2) := by
  rw [scalarFreeCells_eq_step]
  exact scalarStepFree_positive_iff w ((scalarFreeSplit w y).1 0)
    (schurWordFreeCells w (scalarFreeSplit w y).2.2)
    (fun i j => (scalarFreeSplit w y).2.1 (j,i))

theorem pairFree_positive_iff (w : List Bool) (y : SchurWordFreeIndex (true::w) → ℝ) :
    SchurWordPositive (true::w) (schurWordFreeCells (true::w) y) ↔
      0 < (pairFreeSplit w y).1 2 ∧
        (pairFreeSplit w y).1 2 ≤ (pairFreeSplit w y).1 1 ∧
          SchurWordPositive w (schurWordFreeCells w (pairFreeSplit w y).2.2) := by
  rw [pairFreeCells_eq_step]
  exact pairStepFree_positive_iff w ((pairFreeSplit w y).1 0)
    ((pairFreeSplit w y).1 1) ((pairFreeSplit w y).1 2)
    (schurWordFreeCells w (pairFreeSplit w y).2.2)
    (fun i j => (pairFreeSplit w y).2.1 (j,i))

theorem scalarFree_headRootAt (w : List Bool) (y : SchurWordFreeIndex (false::w) → ℝ) :
    schurWordHeadRootAt (false::w) (schurWordFreeCells (false::w) y) =
      Fin.cons ((scalarFreeSplit w y).1 0 : ℂ)
        (schurWordHeadRootAt w (schurWordFreeCells w (scalarFreeSplit w y).2.2)) := by
  rw [scalarFreeCells_eq_step]
  exact scalarStepFree_headRootAt w ((scalarFreeSplit w y).1 0)
    (schurWordFreeCells w (scalarFreeSplit w y).2.2)
    (fun i j => (scalarFreeSplit w y).2.1 (j,i))

theorem pairFree_headRootAt (w : List Bool) (y : SchurWordFreeIndex (true::w) → ℝ) :
    schurWordHeadRootAt (true::w) (schurWordFreeCells (true::w) y) =
      Fin.cons (schurRoot ((pairFreeSplit w y).1 0) ((pairFreeSplit w y).1 1)
        ((pairFreeSplit w y).1 2))
        (schurWordHeadRootAt w (schurWordFreeCells w (pairFreeSplit w y).2.2)) := by
  rw [pairFreeCells_eq_step]
  exact pairStepFree_headRootAt w ((pairFreeSplit w y).1 0)
    ((pairFreeSplit w y).1 1) ((pairFreeSplit w y).1 2)
    (schurWordFreeCells w (pairFreeSplit w y).2.2)
    (fun i j => (pairFreeSplit w y).2.1 (j,i))

theorem scalarFree_pairRatio (w : List Bool) (y : SchurWordFreeIndex (false::w) → ℝ) :
    schurWordPairRatio (false::w) (schurWordFreeCells (false::w) y) =
      schurWordPairRatio w (schurWordFreeCells w (scalarFreeSplit w y).2.2) := by
  rw [scalarFreeCells_eq_step]
  exact scalarStepFree_pairRatio w ((scalarFreeSplit w y).1 0)
    (schurWordFreeCells w (scalarFreeSplit w y).2.2)
    (fun i j => (scalarFreeSplit w y).2.1 (j,i))

theorem pairFree_pairRatio (w : List Bool) (y : SchurWordFreeIndex (true::w) → ℝ) :
    schurWordPairRatio (true::w) (schurWordFreeCells (true::w) y) =
      (((pairFreeSplit w y).1 1-(pairFreeSplit w y).1 2)/
        Real.sqrt ((pairFreeSplit w y).1 1*(pairFreeSplit w y).1 2)) *
        schurWordPairRatio w (schurWordFreeCells w (pairFreeSplit w y).2.2) := by
  rw [pairFreeCells_eq_step]
  exact pairStepFree_pairRatio w ((pairFreeSplit w y).1 0)
    ((pairFreeSplit w y).1 1) ((pairFreeSplit w y).1 2)
    (schurWordFreeCells w (pairFreeSplit w y).2.2)
    (fun i j => (pairFreeSplit w y).2.1 (j,i))

end Paper.Spectral
