/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.CayleyDifferential
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # The actual local skew/orthogonal Cayley correspondence -/

@[expose] public section
noncomputable section
open Set
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

lemma cayley_orthogonal_iff_skew (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit (1 - (1 / 2 : ℝ) • Ω)) :
    cayleyMatrix N Ω * (cayleyMatrix N Ω)ᵀ = 1 ↔ Ωᵀ = -Ω := by
  constructor
  · intro hC
    let B : Matrix (Fin N) (Fin N) ℝ := (1 / 2 : ℝ) • Ω
    let A : Matrix (Fin N) (Fin N) ℝ := 1 - B
    let P : Matrix (Fin N) (Fin N) ℝ := 1 + B
    have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hAC : A * cayleyMatrix N Ω = P := by
      change A * (A⁻¹ * P) = P
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hAd, Matrix.one_mul]
    have hPP : P * Pᵀ = A * Aᵀ := by
      calc
        _ = (A * cayleyMatrix N Ω) * (A * cayleyMatrix N Ω)ᵀ := by rw [hAC]
        _ = A * (cayleyMatrix N Ω * (cayleyMatrix N Ω)ᵀ) * Aᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hC, Matrix.mul_one]
    ext i j
    have hi := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M i j) hPP
    simp only [A, P, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply] at hi
    simp only [B, Matrix.smul_apply, smul_eq_mul] at hi
    change Ω j i = -Ω i j
    linarith
  · exact cayleyMatrix_orthogonal N Ω

lemma isOpen_cayley_unit_denominator (N : ℕ) :
    IsOpen {Ω : Matrix (Fin N) (Fin N) ℝ | IsUnit (1 - (1 / 2 : ℝ) • Ω)} := by
  simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have h : Continuous (fun Ω : Matrix (Fin N) (Fin N) ℝ => (1 : Matrix (Fin N) (Fin N) ℝ) - (1 / 2 : ℝ) • Ω) := by
    fun_prop
  exact isOpen_ne.preimage h.matrix_det

/-- Restriction is to an ambient OPEN unit-denominator set, not to the skew subspace. -/
def cayleyUnitLocalHomeomorph (N : ℕ) :
    OpenPartialHomeomorph (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) :=
  (cayleyLocalHomeomorph N).restrOpen
    {Ω | IsUnit (1 - (1 / 2 : ℝ) • Ω)} (isOpen_cayley_unit_denominator N)

lemma cayleyUnitLocalHomeomorph_apply (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ) :
    cayleyUnitLocalHomeomorph N Ω = cayleyMatrix N Ω := rfl

lemma zero_mem_cayleyUnitLocalHomeomorph_source (N : ℕ) :
    (0 : Matrix (Fin N) (Fin N) ℝ) ∈ (cayleyUnitLocalHomeomorph N).source := by
  refine ⟨zero_mem_cayleyLocalHomeomorph_source N, ?_⟩
  change IsUnit (1 - (1 / 2 : ℝ) • (0 : Matrix (Fin N) (Fin N) ℝ))
  simp

lemma one_mem_cayleyUnitLocalHomeomorph_target (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℝ) ∈ (cayleyUnitLocalHomeomorph N).target := by
  have hh := (cayleyUnitLocalHomeomorph N).map_source (zero_mem_cayleyUnitLocalHomeomorph_source N)
  simpa only [cayleyUnitLocalHomeomorph_apply, cayleyMatrix_zero] using hh

lemma cayleyUnitLocalHomeomorph_isImage (N : ℕ) :
    (cayleyUnitLocalHomeomorph N).IsImage
      {Ω | Ωᵀ = -Ω} {Q | Q * Qᵀ = 1} := by
  intro Ω hΩ
  change cayleyMatrix N Ω * (cayleyMatrix N Ω)ᵀ = 1 ↔ Ωᵀ = -Ω
  exact cayley_orthogonal_iff_skew N Ω hΩ.2

/-- Genuine relative bijectivity; skew matrices need not be ambient-open. -/
theorem cayley_relative_bijOn (N : ℕ) :
    Set.BijOn (cayleyMatrix N)
      ((cayleyUnitLocalHomeomorph N).source ∩ {Ω | Ωᵀ = -Ω})
      ((cayleyUnitLocalHomeomorph N).target ∩ {Q | Q * Qᵀ = 1}) :=
  (cayleyUnitLocalHomeomorph_isImage N).toPartialEquiv.restr.bijOn

end Paper.Spectral
