/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.CayleyRestriction
public import Mathlib.Algebra.Star.Module

/-! # Ordinary independent real coordinates on the native skew-adjoint matrix module -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

abbrev SkewMatrix (N : ℕ) := skewAdjoint (Matrix (Fin N) (Fin N) ℝ)
abbrev SkewIndex (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

theorem skewMatrix_transpose (N : ℕ) (Ω : SkewMatrix N) :
    (Ω : Matrix (Fin N) (Fin N) ℝ)ᵀ = -(Ω : Matrix (Fin N) (Fin N) ℝ) := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (skewAdjoint.star_val_eq (x := Ω))

def skewCoordinates (N : ℕ) (Ω : SkewMatrix N) : SkewIndex N → ℝ :=
  fun p => (Ω : Matrix (Fin N) (Fin N) ℝ) p.val.2 p.val.1


def skewFromCoordinates (N : ℕ) (x : SkewIndex N → ℝ) : SkewMatrix N :=
  ⟨Matrix.of (fun i j =>
      if h : j < i then x ⟨(j, i), h⟩
      else if h : i < j then -x ⟨(i, j), h⟩ else 0), by
    rw [skewAdjoint.mem_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    by_cases hji : j < i
    · have hij : ¬i < j := not_lt_of_ge hji.le
      simp [hji, hij]
    · by_cases hij : i < j
      · simp [hji, hij]
      · simp [hji, hij]⟩

@[simp] theorem skewCoordinates_fromCoordinates (N : ℕ) (x : SkewIndex N → ℝ) :
    skewCoordinates N (skewFromCoordinates N x) = x := by
  funext p
  simp [skewCoordinates, skewFromCoordinates, p.property]

@[simp] theorem skewFromCoordinates_coordinates (N : ℕ) (Ω : SkewMatrix N) :
    skewFromCoordinates N (skewCoordinates N Ω) = Ω := by
  apply Subtype.ext
  ext i j
  have hs := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M i j)
    (skewMatrix_transpose N Ω)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hs
  by_cases hji : j < i
  · simp [skewFromCoordinates, skewCoordinates, hji]
  · by_cases hij : i < j
    · simp [skewFromCoordinates, skewCoordinates, hji, hij, hs]
    · have he : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      have hz : (Ω : Matrix (Fin N) (Fin N) ℝ) i i = 0 := by linarith
      simp [skewFromCoordinates, skewCoordinates, hz]

/-- The native skew-adjoint module has exactly the ordinary lower-triangular
real coordinates; the map includes every skew matrix, also in dimensions0/1. -/
def skewCoordinateEquiv (N : ℕ) : (SkewIndex N → ℝ) ≃ₗ[ℝ] SkewMatrix N where
  toFun := skewFromCoordinates N
  invFun := skewCoordinates N
  left_inv := skewCoordinates_fromCoordinates N
  right_inv := skewFromCoordinates_coordinates N
  map_add' x y := by
    apply Subtype.ext
    ext i j
    by_cases hji : j < i
    · simp [skewFromCoordinates, hji]
    · by_cases hij : i < j
      · simp [skewFromCoordinates, hji, hij, add_comm]
      · simp [skewFromCoordinates, hji, hij]
  map_smul' r x := by
    apply Subtype.ext
    ext i j
    by_cases hji : j < i
    · simp [skewFromCoordinates, hji]
    · by_cases hij : i < j
      · simp [skewFromCoordinates, hji, hij]
      · simp [skewFromCoordinates, hji, hij]


end Paper.Spectral
