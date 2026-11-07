/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SkewCoordinates
public import Mathlib.LinearAlgebra.Determinant

/-! Congruence gives honest automorphisms of the native skew-adjoint module. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

def skewCongruenceLM (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    SkewMatrix N →ₗ[ℝ] SkewMatrix N where
  toFun H := ⟨Aᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * A, by
    rw [skewAdjoint.mem_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.transpose_transpose, skewMatrix_transpose N H,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]⟩
  map_add' H K := by
    apply Subtype.ext
    change Aᵀ * ((H : Matrix (Fin N) (Fin N) ℝ) + K) * A =
      Aᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * A +
        Aᵀ * (K : Matrix (Fin N) (Fin N) ℝ) * A
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r H := by
    apply Subtype.ext
    change Aᵀ * (r • (H : Matrix (Fin N) (Fin N) ℝ)) * A =
      r • (Aᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * A)
    rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem skewCongruenceLM_apply (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (H : SkewMatrix N) :
    (skewCongruenceLM N A H : Matrix (Fin N) (Fin N) ℝ) =
      Aᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * A := rfl

def skewCongruenceEquiv (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A) : SkewMatrix N ≃ₗ[ℝ] SkewMatrix N where
  toFun := skewCongruenceLM N A
  invFun := skewCongruenceLM N A⁻¹
  left_inv H := by
    have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    apply Subtype.ext
    change A⁻¹ᵀ * (Aᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * A) * A⁻¹ = H
    calc
      _ = (A * A⁻¹)ᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * (A * A⁻¹) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv A hAd]; simp
  right_inv H := by
    have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    apply Subtype.ext
    change Aᵀ * (A⁻¹ᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * A⁻¹) * A = H
    calc
      _ = (A⁻¹ * A)ᵀ * (H : Matrix (Fin N) (Fin N) ℝ) * (A⁻¹ * A) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul A hAd]; simp
  map_add' H K := (skewCongruenceLM N A).map_add H K
  map_smul' r H := (skewCongruenceLM N A).map_smul r H

def skewCoordinateCongruence (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A) : (SkewIndex N → ℝ) ≃ₗ[ℝ] (SkewIndex N → ℝ) :=
  (skewCoordinateEquiv N).trans
    ((skewCongruenceEquiv N A hA).trans (skewCoordinateEquiv N).symm)

theorem det_skewCoordinateCongruence_ne_zero (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : IsUnit A) :
    LinearMap.det (skewCoordinateCongruence N A hA).toLinearMap ≠ 0 :=
  (skewCoordinateCongruence N A hA).isUnit_det'.ne_zero

end Paper.Spectral
