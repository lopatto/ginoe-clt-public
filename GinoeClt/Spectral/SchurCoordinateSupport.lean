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

@[simp] theorem schurCellCoordinateEquiv_single (d m : ℕ)
    (p : SchurStepIndex (Fin d) (Fin m)) (t : ℝ) :
    schurCellCoordinateEquiv ℝ d m (Pi.single (schurCellEquiv d m p) t) = Pi.single p t := by
  funext q
  by_cases h : q = p
  · subst q
    simp [schurCellCoordinateEquiv_apply]
  · have hn : schurCellEquiv d m q ≠ schurCellEquiv d m p :=
      fun he => h ((schurCellEquiv d m).injective he)
    simp [schurCellCoordinateEquiv_apply, h, hn]

/-- An actual lower single-cell input with zero parameter contribution stays zero after physical assembly. -/
theorem schurParameterPhysical_single_lower_zero {d m : ℕ}
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (j : Fin d) (i : Fin m) (t : ℝ) :
    schurParameterPhysical d m K L (Pi.single (schurCellEquiv d m (.inl (j,i))) t) = 0 := by
  let v : SchurStepIndex (Fin d) (Fin m) → ℝ := Pi.single (.inl (j,i)) t
  have hh : schurHeadInput v = 0 := by funext p; simp [v,schurHeadInput]
  have ht : schurTailInput v = 0 := by funext p; simp [v,schurTailInput]
  have hu : schurUpperInput v = 0 := by
    funext i j
    change v (.inr (.inr (.inr (j,i)))) = 0
    simp [v]
  have hp : schurParameterPhysical d m K L (Pi.single (schurCellEquiv d m (.inl (j,i))) t) =
      schurPhysicalBlock (0 : Matrix (Fin d) (Fin d) ℝ)
        (0 : Matrix (Fin m) (Fin m) ℝ) (0 : Matrix (Fin d) (Fin m) ℝ) := by
    rw [schurParameterPhysical_eq,schurCellCoordinateEquiv_single]
    change schurPhysicalBlock (K (schurHeadInput v)) (L (schurTailInput v)) (schurUpperInput v) = _
    rw [hh,ht,hu]
    simp only [map_zero]
  rw [hp]
  unfold schurPhysicalBlock
  rw [Matrix.fromBlocks_zero]
  rfl

/-- An actual tail single-cell input with zero parameter contribution stays zero after physical assembly. -/
theorem schurParameterPhysical_single_tail_zero {d m : ℕ}
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (c : Fin m × Fin m) (t : ℝ) (hL : L (Pi.single c t) = 0) :
    schurParameterPhysical d m K L (Pi.single (schurCellEquiv d m (.inr (.inr (.inl c)))) t) = 0 := by
  let v : SchurStepIndex (Fin d) (Fin m) → ℝ := Pi.single (.inr (.inr (.inl c))) t
  have hh : schurHeadInput v = 0 := by funext p; simp [v,schurHeadInput]
  have ht : schurTailInput v = Pi.single c t := by funext p; simp [v,schurTailInput,Pi.single_apply]
  have hu : schurUpperInput v = 0 := by
    funext i j
    change v (.inr (.inr (.inr (j,i)))) = 0
    simp [v]
  have hp : schurParameterPhysical d m K L (Pi.single (schurCellEquiv d m (.inr (.inr (.inl c)))) t) =
      schurPhysicalBlock (0 : Matrix (Fin d) (Fin d) ℝ)
        (0 : Matrix (Fin m) (Fin m) ℝ) (0 : Matrix (Fin d) (Fin m) ℝ) := by
    rw [schurParameterPhysical_eq,schurCellCoordinateEquiv_single]
    change schurPhysicalBlock (K (schurHeadInput v)) (L (schurTailInput v)) (schurUpperInput v) = _
    rw [hh,ht,hu]
    rw [map_zero,hL]
  rw [hp]
  unfold schurPhysicalBlock
  rw [Matrix.fromBlocks_zero]
  rfl

/-- An actual head single-cell input with zero parameter contribution stays zero after physical assembly. -/
theorem schurParameterPhysical_single_head_zero {d m : ℕ}
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (c : Fin d × Fin d) (t : ℝ) (hK : K (Pi.single c t) = 0) :
    schurParameterPhysical d m K L (Pi.single (schurCellEquiv d m (.inr (.inl c))) t) = 0 := by
  let v : SchurStepIndex (Fin d) (Fin m) → ℝ := Pi.single (.inr (.inl c)) t
  have hh : schurHeadInput v = Pi.single c t := by funext p; simp [v,schurHeadInput,Pi.single_apply]
  have ht : schurTailInput v = 0 := by funext p; simp [v,schurTailInput]
  have hu : schurUpperInput v = 0 := by
    funext i j
    change v (.inr (.inr (.inr (j,i)))) = 0
    simp [v]
  have hp : schurParameterPhysical d m K L (Pi.single (schurCellEquiv d m (.inr (.inl c))) t) =
      schurPhysicalBlock (0 : Matrix (Fin d) (Fin d) ℝ)
        (0 : Matrix (Fin m) (Fin m) ℝ) (0 : Matrix (Fin d) (Fin m) ℝ) := by
    rw [schurParameterPhysical_eq,schurCellCoordinateEquiv_single]
    change schurPhysicalBlock (K (schurHeadInput v)) (L (schurTailInput v)) (schurUpperInput v) = _
    rw [hh,ht,hu]
    rw [hK,map_zero]
  rw [hp]
  unfold schurPhysicalBlock
  rw [Matrix.fromBlocks_zero]
  rfl

theorem pairHeadParameter_single_angle_zero (t : ℝ) :
    pairHeadParameter (Pi.single (1,1) t) = 0 := by
  rw [pairHeadParameter_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schurBlock]

end Paper.Spectral
