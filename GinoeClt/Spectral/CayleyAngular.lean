/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.CayleyGeneralDifferential
public import GinoeClt.Spectral.SkewCongruence
import Mathlib.Tactic.FunProp

/-! Actual angular differentials in the independent skew coordinates. -/
@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

theorem cayleyMatrix_mul_denominator (N : ℕ)
    (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit (1 - (1 / 2 : ℝ) • Ω)) :
    cayleyMatrix N Ω * (1 - (1 / 2 : ℝ) • Ω) = 1 + (1 / 2 : ℝ) • Ω := by
  let A := (1 : Matrix (Fin N) (Fin N) ℝ) - (1 / 2 : ℝ) • Ω
  let P := (1 : Matrix (Fin N) (Fin N) ℝ) + (1 / 2 : ℝ) • Ω
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hc : P * A = A * P := by
    dsimp only [P, A]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one]
    abel
  change A⁻¹ * P * A = P
  rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAd,
    Matrix.one_mul]

theorem cayley_transpose_mul_inverse_denominator (N : ℕ)
    (Ω : Matrix (Fin N) (Fin N) ℝ) (hΩ : Ωᵀ = -Ω) :
    (cayleyMatrix N Ω)ᵀ * (1 - (1 / 2 : ℝ) • Ω)⁻¹ =
      ((1 - (1 / 2 : ℝ) • Ω)⁻¹)ᵀ := by
  let A := (1 : Matrix (Fin N) (Fin N) ℝ) - (1 / 2 : ℝ) • Ω
  let P := (1 : Matrix (Fin N) (Fin N) ℝ) + (1 / 2 : ℝ) • Ω
  let C := cayleyMatrix N Ω
  have hA : IsUnit A := cayley_denominator_isUnit N Ω hΩ
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hAt : Aᵀ = P := by
    simp only [A, P, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      hΩ, smul_neg, sub_neg_eq_add]
  have hCA : C * A = P := cayleyMatrix_mul_denominator N Ω hA
  have ht : Aᵀ * Cᵀ = A := by
    simpa only [Matrix.transpose_mul, ← hAt, Matrix.transpose_transpose] using
      congrArg Matrix.transpose hCA
  have hIA : A⁻¹ᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv A hAd, Matrix.transpose_one]
  have hCt : Cᵀ = A⁻¹ᵀ * A := by
    calc
      _ = (A⁻¹ᵀ * Aᵀ) * Cᵀ := by rw [hIA, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ht]
  change Cᵀ * A⁻¹ = A⁻¹ᵀ
  rw [hCt, Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAd, Matrix.mul_one]

theorem cayley_angular_sandwich (N : ℕ)
    (Ω H : Matrix (Fin N) (Fin N) ℝ) (hΩ : Ωᵀ = -Ω) :
    (cayleyMatrix N Ω)ᵀ *
        matrixSandwichCLM N (1 - (1 / 2 : ℝ) • Ω)⁻¹
          (1 - (1 / 2 : ℝ) • Ω)⁻¹ H =
      ((1 - (1 / 2 : ℝ) • Ω)⁻¹)ᵀ * H * (1 - (1 / 2 : ℝ) • Ω)⁻¹ := by
  rw [matrixSandwichCLM_apply]
  calc
    _ = ((cayleyMatrix N Ω)ᵀ * (1 - (1 / 2 : ℝ) • Ω)⁻¹) * H *
        (1 - (1 / 2 : ℝ) • Ω)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [cayley_transpose_mul_inverse_denominator N Ω hΩ]

theorem cayley_inverse_denominator_isUnit (N : ℕ) (Ω : SkewMatrix N) :
    IsUnit ((1 : Matrix (Fin N) (Fin N) ℝ) -
      (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹ := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply Matrix.isUnit_nonsing_inv_det
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (cayley_denominator_isUnit N Ω (skewMatrix_transpose N Ω))

def cayleyAngularEquiv (N : ℕ) (Ω : SkewMatrix N) :
    (SkewIndex N → ℝ) ≃ₗ[ℝ] (SkewIndex N → ℝ) :=
  skewCoordinateCongruence N
    ((1 : Matrix (Fin N) (Fin N) ℝ) - (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
    (cayley_inverse_denominator_isUnit N Ω)

theorem cayleyAngularEquiv_matrix (N : ℕ) (Ω : SkewMatrix N) (x : SkewIndex N → ℝ) :
    (skewFromCoordinates N (cayleyAngularEquiv N Ω x) : Matrix (Fin N) (Fin N) ℝ) =
      (((1 : Matrix (Fin N) (Fin N) ℝ) -
        (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹)ᵀ *
          (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ) *
            ((1 : Matrix (Fin N) (Fin N) ℝ) -
              (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹ := by
  change (skewFromCoordinates N (skewCoordinates N
    (skewCongruenceLM N
      ((1 : Matrix (Fin N) (Fin N) ℝ) -
        (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
      (skewFromCoordinates N x))) : Matrix (Fin N) (Fin N) ℝ) = _
  rw [skewFromCoordinates_coordinates]
  rfl

theorem cayleyAngularEquiv_tangent (N : ℕ) (Ω : SkewMatrix N) (x : SkewIndex N → ℝ) :
    (skewFromCoordinates N (cayleyAngularEquiv N Ω x) : Matrix (Fin N) (Fin N) ℝ) =
      (cayleyMatrix N Ω)ᵀ *
        matrixSandwichCLM N
          ((1 : Matrix (Fin N) (Fin N) ℝ) -
            (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
          ((1 : Matrix (Fin N) (Fin N) ℝ) -
            (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
          (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ) := by
  rw [cayleyAngularEquiv_matrix]
  exact (cayley_angular_sandwich N Ω (skewFromCoordinates N x)
    (skewMatrix_transpose N Ω)).symm

theorem det_cayleyAngularEquiv_ne_zero (N : ℕ) (Ω : SkewMatrix N) :
    LinearMap.det (cayleyAngularEquiv N Ω).toLinearMap ≠ 0 :=
  (cayleyAngularEquiv N Ω).isUnit_det'.ne_zero

def cayleyAngularJacobian (N : ℕ) (Ω : SkewMatrix N) : ℝ :=
  |LinearMap.det (cayleyAngularEquiv N Ω).toLinearMap|

theorem cayleyAngularJacobian_pos (N : ℕ) (Ω : SkewMatrix N) :
    0 < cayleyAngularJacobian N Ω :=
  abs_pos.mpr (det_cayleyAngularEquiv_ne_zero N Ω)

theorem cayley_conjugationDerivative_coordinates (N : ℕ) (Ω : SkewMatrix N)
    (T K : Matrix (Fin N) (Fin N) ℝ) (x : SkewIndex N → ℝ) :
    conjugationDerivative N (cayleyMatrix N Ω) T
      (matrixSandwichCLM N
        ((1 : Matrix (Fin N) (Fin N) ℝ) -
          (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
        ((1 : Matrix (Fin N) (Fin N) ℝ) -
          (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
        (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ), K) =
      cayleyMatrix N Ω *
        (K + (skewFromCoordinates N (cayleyAngularEquiv N Ω x) :
            Matrix (Fin N) (Fin N) ℝ) * T -
          T * (skewFromCoordinates N (cayleyAngularEquiv N Ω x) :
            Matrix (Fin N) (Fin N) ℝ)) *
        (cayleyMatrix N Ω)ᵀ := by
  let C := cayleyMatrix N Ω
  let H : Matrix (Fin N) (Fin N) ℝ := skewFromCoordinates N x
  let G : Matrix (Fin N) (Fin N) ℝ :=
    skewFromCoordinates N (cayleyAngularEquiv N Ω x)
  have hC : C * Cᵀ = 1 := cayleyMatrix_orthogonal N Ω (skewMatrix_transpose N Ω)
  have hG : G = Cᵀ *
      matrixSandwichCLM N
        ((1 : Matrix (Fin N) (Fin N) ℝ) -
          (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
        ((1 : Matrix (Fin N) (Fin N) ℝ) -
          (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹ H :=
    cayleyAngularEquiv_tangent N Ω x
  have hH : matrixSandwichCLM N
        ((1 : Matrix (Fin N) (Fin N) ℝ) -
          (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹
        ((1 : Matrix (Fin N) (Fin N) ℝ) -
          (1 / 2 : ℝ) • (Ω : Matrix (Fin N) (Fin N) ℝ))⁻¹ H = C * G := by
    rw [hG, ← Matrix.mul_assoc, hC, Matrix.one_mul]
  change conjugationDerivative N C T
    (matrixSandwichCLM N _ _ H, K) = C * (K + G * T - T * G) * Cᵀ
  rw [hH]
  exact conjugationDerivative_skew N C T G K
    (skewMatrix_transpose N (skewFromCoordinates N (cayleyAngularEquiv N Ω x)))

theorem cayleyAngularEquiv_zero_apply (N : ℕ) (x : SkewIndex N → ℝ) :
    cayleyAngularEquiv N 0 x = x := by
  apply (skewCoordinateEquiv N).injective
  apply Subtype.ext
  change (skewFromCoordinates N (cayleyAngularEquiv N 0 x) :
    Matrix (Fin N) (Fin N) ℝ) = (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ)
  rw [cayleyAngularEquiv_matrix]
  simp

theorem cayleyAngularEquiv_zero (N : ℕ) :
    cayleyAngularEquiv N 0 = LinearEquiv.refl ℝ (SkewIndex N → ℝ) := by
  apply LinearEquiv.ext
  intro x
  exact cayleyAngularEquiv_zero_apply N x

theorem cayleyAngularJacobian_zero (N : ℕ) : cayleyAngularJacobian N 0 = 1 := by
  simp [cayleyAngularJacobian, cayleyAngularEquiv_zero]

theorem continuous_skewFromCoordinates_matrix (N : ℕ) :
    Continuous (fun x : SkewIndex N → ℝ =>
      (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  dsimp only [skewFromCoordinates, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem continuous_cayleyInverseDenominator_coordinates (N : ℕ) :
    Continuous (fun x : SkewIndex N → ℝ =>
      ((1 : Matrix (Fin N) (Fin N) ℝ) -
        (1 / 2 : ℝ) • (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ))⁻¹) := by
  have hA : Continuous (fun x : SkewIndex N → ℝ =>
      (1 : Matrix (Fin N) (Fin N) ℝ) -
        (1 / 2 : ℝ) • (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ)) :=
    continuous_const.sub ((continuous_skewFromCoordinates_matrix N).const_smul (1 / 2 : ℝ))
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasStrictFDerivAt_matrixInverse N _
    (cayley_denominator_isUnit N _ (skewMatrix_transpose N (skewFromCoordinates N x)))).continuousAt.comp_of_eq
      hA.continuousAt rfl

theorem continuous_cayleyAngularJacobian_coordinates (N : ℕ) :
    Continuous (fun x : SkewIndex N → ℝ => cayleyAngularJacobian N (skewFromCoordinates N x)) := by
  let I : (SkewIndex N → ℝ) → Matrix (Fin N) (Fin N) ℝ := fun x =>
    ((1 : Matrix (Fin N) (Fin N) ℝ) -
      (1 / 2 : ℝ) • (skewFromCoordinates N x : Matrix (Fin N) (Fin N) ℝ))⁻¹
  have hI : Continuous I := continuous_cayleyInverseDenominator_coordinates N
  have hM : Continuous (fun x : SkewIndex N → ℝ =>
      LinearMap.toMatrix' (cayleyAngularEquiv N (skewFromCoordinates N x)).toLinearMap) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    let H : Matrix (Fin N) (Fin N) ℝ := skewFromCoordinates N (Pi.single j 1)
    change Continuous (fun x => ((I x)ᵀ * H * I x) i.val.2 i.val.1)
    fun_prop
  have heq : (fun x : SkewIndex N → ℝ =>
      cayleyAngularJacobian N (skewFromCoordinates N x)) =
      fun x => |(LinearMap.toMatrix'
        (cayleyAngularEquiv N (skewFromCoordinates N x)).toLinearMap).det| := by
    funext x
    rw [LinearMap.det_toMatrix']
    rfl
  rw [heq]
  exact hM.matrix_det.abs

end Paper.Spectral
