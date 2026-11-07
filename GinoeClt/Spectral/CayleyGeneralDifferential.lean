/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.CayleyDifferential
import Mathlib.Tactic.Abel

/-! Actual strict inverse differentiation at every invertible matrix. -/
@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise
namespace Paper.Spectral

def matrixSandwichCLM (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ := by
  letI : IsNormableSpace ℝ (Matrix (Fin N) (Fin N) ℝ) :=
    isNormableSpace_of_finiteDimensional (𝕜 := ℝ) (E := Matrix (Fin N) (Fin N) ℝ)
  exact ((matrixMulCLM N).flip B).comp (matrixMulCLM N A)

lemma matrixSandwichCLM_apply (N : ℕ) (A B H : Matrix (Fin N) (Fin N) ℝ) :
    matrixSandwichCLM N A B H = A * H * B := rfl

lemma matrixOperatorCLE_mul (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixOperatorCLE N (A * B) = matrixOperatorCLE N A * matrixOperatorCLE N B := by
  change Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (A * B) = _
  exact map_mul _ A B

theorem hasStrictFDerivAt_matrixInverse (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : IsUnit A) :
    HasStrictFDerivAt (fun M : Matrix (Fin N) (Fin N) ℝ => M⁻¹)
      (-(matrixSandwichCLM N A⁻¹ A⁻¹)) A := by
  let e := matrixOperatorCLE N
  let O := EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)
  have hU : IsUnit (e A) :=
    IsUnit.map (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)) hA
  obtain ⟨u, hu⟩ := hU
  have hi : (↑u⁻¹ : O) = e A⁻¹ := by
    change (↑u⁻¹ : O) = matrixOperatorCLE N A⁻¹
    rw [matrixOperatorCLE_inv, ← hu, Ring.inverse_unit]
  have hOp := hasStrictFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu, hi] at hOp
  have hh := e.symm.toContinuousLinearMap.hasStrictFDerivAt.comp A
    (hOp.comp A e.toContinuousLinearMap.hasStrictFDerivAt)
  convert! hh using 1
  · funext M
    change M⁻¹ = e.symm (Ring.inverse (e M))
    rw [← matrixOperatorCLE_inv]
    exact (e.symm_apply_apply M⁻¹).symm
  · apply ContinuousLinearMap.ext
    intro H
    change -(A⁻¹ * H * A⁻¹) = e.symm (-(e A⁻¹ * e H * e A⁻¹))
    rw [map_neg, ← matrixOperatorCLE_mul, ← matrixOperatorCLE_mul, e.symm_apply_apply]

theorem cayleyMatrix_add_one (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit (1 - (1 / 2 : ℝ) • Ω)) :
    cayleyMatrix N Ω + 1 = (2 : ℝ) • (1 - (1 / 2 : ℝ) • Ω)⁻¹ := by
  let A := (1 : Matrix (Fin N) (Fin N) ℝ) - (1 / 2 : ℝ) • Ω
  let P := (1 : Matrix (Fin N) (Fin N) ℝ) + (1 / 2 : ℝ) • Ω
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hsum : P + A = (2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    dsimp only [P, A]
    rw [two_smul]
    abel
  change A⁻¹ * P + 1 = (2 : ℝ) • A⁻¹
  calc
    _ = A⁻¹ * P + A⁻¹ * A := by rw [Matrix.nonsing_inv_mul A hAd]
    _ = A⁻¹ * (P + A) := (Matrix.mul_add _ _ _).symm
    _ = _ := by rw [hsum, Matrix.mul_smul, Matrix.mul_one]

/-- The normalized Cayley derivative is an actual sandwich by the inverse denominator. -/
theorem hasStrictFDerivAt_cayleyMatrix (N : ℕ)
    (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit (1 - (1 / 2 : ℝ) • Ω)) :
    HasStrictFDerivAt (cayleyMatrix N)
      (matrixSandwichCLM N (1 - (1 / 2 : ℝ) • Ω)⁻¹
        (1 - (1 / 2 : ℝ) • Ω)⁻¹) Ω := by
  let h : ℝ := 1 / 2
  let A := (1 : Matrix (Fin N) (Fin N) ℝ) - h • Ω
  let P := (1 : Matrix (Fin N) (Fin N) ℝ) + h • Ω
  have hs := (hasStrictFDerivAt_id (𝕜 := ℝ) Ω).const_smul h
  have hm := hs.const_sub (1 : Matrix (Fin N) (Fin N) ℝ)
  have hp := hs.const_add (1 : Matrix (Fin N) (Fin N) ℝ)
  have hi := hasStrictFDerivAt_matrixInverse N A hA
  have hh := (matrixMulCLM N).hasStrictFDerivAt_of_bilinear (hi.comp Ω hm) hp
  have hc := cayleyMatrix_add_one N Ω hA
  change A⁻¹ * P + 1 = (2 : ℝ) • A⁻¹ at hc
  have hc' : 1 + A⁻¹ * P = (2 : ℝ) • A⁻¹ := by
    simpa only [add_comm] using hc
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro H
  change A⁻¹ * H * A⁻¹ =
    A⁻¹ * (h • H) + (-(A⁻¹ * (-(h • H)) * A⁻¹)) * P
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Matrix.mul_smul, Matrix.smul_mul]
  calc
    A⁻¹ * H * A⁻¹ = h • ((A⁻¹ * H) * ((2 : ℝ) • A⁻¹)) := by
      simp only [Matrix.mul_smul, smul_smul]
      norm_num [h]
    _ = h • ((A⁻¹ * H) * (1 + A⁻¹ * P)) := by rw [hc']
    _ = _ := by
      simp only [Matrix.mul_add, Matrix.mul_one, smul_add, Matrix.mul_assoc]

theorem hasStrictFDerivAt_cayleyMatrix_of_skew (N : ℕ)
    (Ω : Matrix (Fin N) (Fin N) ℝ) (hΩ : Ωᵀ = -Ω) :
    HasStrictFDerivAt (cayleyMatrix N)
      (matrixSandwichCLM N (1 - (1 / 2 : ℝ) • Ω)⁻¹
        (1 - (1 / 2 : ℝ) • Ω)⁻¹) Ω :=
  hasStrictFDerivAt_cayleyMatrix N Ω (cayley_denominator_isUnit N Ω hΩ)

end Paper.Spectral
