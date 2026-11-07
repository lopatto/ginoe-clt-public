/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.CoordinateProductVolume
public import GinoeClt.Spectral.SchurCoordinateProjection
public import Mathlib.Algebra.BigOperators.Pi
@[expose] public section
noncomputable section
open MeasureTheory
namespace Paper.Spectral

/-- A literal subtype of the original raw cells, complementary to the angle-reading cells. -/
abbrev SchurWordFreeIndex (w : List Bool) := CoordinateRemainder (schurWordAngleCell w)

/-- EXACT existing native angles plus the unscaled remaining raw cells. -/
def schurWordCoordinateSplit (w : List Bool) (x : SchurWordCells w) :
    SchurWordAngles w × (SchurWordFreeIndex w → ℝ) :=
  (schurWordAngleMap w x,fun p => x p.val)

/-- Ordinary product volume, not an abstract Haar measure on a kernel. -/
theorem volume_preserving_schurWordCoordinateSplit (w : List Bool) :
    MeasurePreserving (schurWordCoordinateSplit w) volume volume := by
  have h := volume_preserving_coordinateSplit (schurWordAngleCell w) (schurWordAngleCell_injective w)
  have he : coordinateSplit (schurWordAngleCell w) = schurWordCoordinateSplit w := by
    funext x
    apply Prod.ext
    · funext a
      exact (schurWordAngleCell_spec w a x).symm
    · rfl
  simpa only [he] using h


/-- The actual parameter matrix ignores every selected angular raw cell. -/
theorem schurWordParameter_eq_of_free_cells_eq (w : List Bool)
    (x y : SchurWordCells w)
    (h : ∀ c : SchurWordFreeIndex w, x c.val = y c.val) :
    schurWordParameter w x = schurWordParameter w y := by
  classical
  have hx := congrArg (schurWordParameter w) (pi_eq_sum_univ' x)
  have hy := congrArg (schurWordParameter w) (pi_eq_sum_univ' y)
  rw [map_sum] at hx hy
  rw [hx,hy]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul,map_smul]
  by_cases hc : c ∈ (Finset.univ.image (schurWordAngleCell w))
  · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hc
    subst c
    rw [schurWordParameter_single_angleCell]
    simp only [smul_zero]
  · rw [h ⟨c,hc⟩]

/-- Complete literal remaining cells by setting all angular cells to zero. -/
def schurWordFreeCells (w : List Bool) (y : SchurWordFreeIndex w → ℝ) :
    SchurWordCells w := fun c =>
  if hc : c ∈ Finset.univ.image (schurWordAngleCell w) then 0 else y ⟨c,hc⟩

theorem schurWordAngleMap_freeCells (w : List Bool)
    (y : SchurWordFreeIndex w → ℝ) :
    schurWordAngleMap w (schurWordFreeCells w y) = 0 := by
  classical
  funext a
  rw [schurWordAngleCell_spec]
  simp [schurWordFreeCells]

theorem schurWordParameter_eq_freeCells (w : List Bool) (x : SchurWordCells w) :
    schurWordParameter w x =
      schurWordParameter w (schurWordFreeCells w (fun c => x c.val)) := by
  classical
  apply schurWordParameter_eq_of_free_cells_eq
  intro c
  simp [schurWordFreeCells,c.property]

end Paper.Spectral
