/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-! # The correctly normalized real matrix Cayley map -/

@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

lemma dotProduct_skew_mulVec_zero (N : ℕ) (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : Bᵀ = -B) (v : Fin N → ℝ) : v ⬝ᵥ (B *ᵥ v) = 0 := by
  have hh := Matrix.dotProduct_transpose_mulVec B v v
  rw [hB, Matrix.neg_mulVec, dotProduct_neg] at hh
  linarith

lemma one_sub_skew_isUnit (N : ℕ) (B : Matrix (Fin N) (Fin N) ℝ)
    (hB : Bᵀ = -B) : IsUnit (1 - B) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : (1 - B) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have hv : x - y = B *ᵥ (x - y) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hz
    exact sub_eq_zero.mp hz
  apply dotProduct_self_eq_zero.mp
  calc
    (x - y) ⬝ᵥ (x - y) = (x - y) ⬝ᵥ (B *ᵥ (x - y)) := congrArg (fun z => (x - y) ⬝ᵥ z) hv
    _ = 0 := dotProduct_skew_mulVec_zero N B hB (x - y)

def cayleyMatrix (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (1 - (1 / 2 : ℝ) • Ω)⁻¹ * (1 + (1 / 2 : ℝ) • Ω)

lemma cayley_denominator_isUnit (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hΩ : Ωᵀ = -Ω) : IsUnit (1 - (1 / 2 : ℝ) • Ω) := by
  apply one_sub_skew_isUnit
  rw [Matrix.transpose_smul, hΩ, smul_neg]

lemma cayleyMatrix_zero (N : ℕ) : cayleyMatrix N 0 = 1 := by
  simp [cayleyMatrix]

lemma cayleyMatrix_orthogonal (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hΩ : Ωᵀ = -Ω) : cayleyMatrix N Ω * (cayleyMatrix N Ω)ᵀ = 1 := by
  let B : Matrix (Fin N) (Fin N) ℝ := (1 / 2 : ℝ) • Ω
  let A : Matrix (Fin N) (Fin N) ℝ := 1 - B
  let P : Matrix (Fin N) (Fin N) ℝ := 1 + B
  have hB : Bᵀ = -B := by dsimp only [B]; rw [Matrix.transpose_smul, hΩ, smul_neg]
  have hA := one_sub_skew_isUnit N B hB
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hAP : Aᵀ = P := by simp only [A, P, Matrix.transpose_sub, Matrix.transpose_one, hB, sub_neg_eq_add]
  have hPA : Pᵀ = A := by simp only [A, P, Matrix.transpose_add, Matrix.transpose_one, hB, sub_eq_add_neg]
  have hPd : IsUnit P.det := by rw [← hAP, Matrix.det_transpose]; exact hAd
  have hcomm : P * A = A * P := by
    dsimp only [P, A]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one]
    abel
  change (A⁻¹ * P) * (A⁻¹ * P)ᵀ = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hPA, hAP]
  calc
    _ = A⁻¹ * (P * A) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = A⁻¹ * (A * P) * P⁻¹ := by rw [hcomm]
    _ = (A⁻¹ * A) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul A hAd, Matrix.mul_nonsing_inv P hPd, Matrix.one_mul]

end Paper.Spectral
