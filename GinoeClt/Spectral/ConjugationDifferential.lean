/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Abel

/-! # The differential of orthogonal matrix conjugation

All maps use the existing finite-dimensional matrix topology. No global norm
instance is introduced, and no nonlinear Schur chart/Jacobian is asserted.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

def matrixMulCLM (N : ℕ) : Matrix (Fin N) (Fin N) ℝ →L[ℝ]
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ := by
  let M := Matrix (Fin N) (Fin N) ℝ
  let c : (M →ₗ[ℝ] M) ≃ₗ[ℝ] (M →L[ℝ] M) := LinearMap.toContinuousLinearMap
  exact (c.toLinearMap.comp (LinearMap.mul ℝ M)).toContinuousLinearMap

lemma matrixMulCLM_apply (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixMulCLM N A B = A * B := rfl

def matrixTransposeCLM (N : ℕ) : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ :=
  (Matrix.transposeLinearEquiv (Fin N) (Fin N) ℝ ℝ).toLinearMap.toContinuousLinearMap

lemma matrixTransposeCLM_apply (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixTransposeCLM N A = Aᵀ := rfl

def conjugationDerivative (N : ℕ) (Q T : Matrix (Fin N) (Fin N) ℝ) :
    (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) →L[ℝ]
      Matrix (Fin N) (Fin N) ℝ :=
  letI : IsNormableSpace ℝ (Matrix (Fin N) (Fin N) ℝ) :=
    isNormableSpace_of_finiteDimensional (𝕜 := ℝ) (E := Matrix (Fin N) (Fin N) ℝ)
  let B := matrixMulCLM N
  let F := ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)
  let G := ContinuousLinearMap.snd ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)
  (B.flip Qᵀ).comp ((B.flip T).comp F) +
    (B.flip Qᵀ).comp ((B Q).comp G) +
    (B (Q * T)).comp ((matrixTransposeCLM N).comp F)

lemma conjugationDerivative_apply (N : ℕ) (Q T H K : Matrix (Fin N) (Fin N) ℝ) :
    conjugationDerivative N Q T (H, K) = H * T * Qᵀ + Q * K * Qᵀ + Q * T * Hᵀ := rfl

theorem hasStrictFDerivAt_conjugation (N : ℕ) (Q T : Matrix (Fin N) (Fin N) ℝ) :
    HasStrictFDerivAt (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ =>
      p.1 * p.2 * p.1ᵀ) (conjugationDerivative N Q T) (Q, T) := by
  let : IsNormableSpace ℝ (Matrix (Fin N) (Fin N) ℝ) :=
    isNormableSpace_of_finiteDimensional (𝕜 := ℝ) (E := Matrix (Fin N) (Fin N) ℝ)
  let B := matrixMulCLM N
  have h₁ := B.hasStrictFDerivAt_of_bilinear
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (Q, T)))
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (Q, T)))
  have h₂ := (matrixTransposeCLM N).hasStrictFDerivAt.comp (Q, T)
    (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (Q, T)))
  have hh := B.hasStrictFDerivAt_of_bilinear h₁ h₂
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro p
  rcases p with ⟨H, K⟩
  change H * T * Qᵀ + Q * K * Qᵀ + Q * T * Hᵀ =
    Q * T * Hᵀ + (Q * K + H * T) * Qᵀ
  rw [Matrix.add_mul]
  abel

theorem hasFDerivAt_conjugation (N : ℕ) (Q T : Matrix (Fin N) (Fin N) ℝ) :
    HasFDerivAt (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ =>
      p.1 * p.2 * p.1ᵀ) (conjugationDerivative N Q T) (Q, T) :=
  (hasStrictFDerivAt_conjugation N Q T).hasFDerivAt

lemma conjugationDerivative_skew (N : ℕ)
    (Q T Ω K : Matrix (Fin N) (Fin N) ℝ) (hΩ : Ωᵀ = -Ω) :
    conjugationDerivative N Q T (Q * Ω, K) = Q * (K + Ω * T - T * Ω) * Qᵀ := by
  rw [conjugationDerivative_apply]
  simp only [Matrix.transpose_mul, hΩ, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

lemma conjugationDerivative_tangent (N : ℕ)
    (Q T H K : Matrix (Fin N) (Fin N) ℝ) (hQ : Q * Qᵀ = 1)
    (hTangent : Qᵀ * H + Hᵀ * Q = 0) :
    conjugationDerivative N Q T (H, K) =
      Q * (K + (Qᵀ * H) * T - T * (Qᵀ * H)) * Qᵀ := by
  have hΩ : (Qᵀ * H)ᵀ = -(Qᵀ * H) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    apply (eq_neg_iff_add_eq_zero).mpr
    simpa only [add_comm] using hTangent
  have hH : H = Q * (Qᵀ * H) := by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  calc
    _ = conjugationDerivative N Q T (Q * (Qᵀ * H), K) :=
      congrArg (fun L => conjugationDerivative N Q T (L, K)) hH
    _ = _ := conjugationDerivative_skew N Q T (Qᵀ * H) K hΩ

end Paper.Spectral
