/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

public import GinoeClt.Spectral.CayleyMatrix
public import GinoeClt.Spectral.ConjugationDifferential
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! # Strict differentiation of the normalized Cayley map -/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

def matrixOperatorCLE (N : ℕ) : Matrix (Fin N) (Fin N) ℝ ≃L[ℝ]
    (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma matrixOperatorCLE_one (N : ℕ) : matrixOperatorCLE N 1 = 1 := by
  change Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) 1 = 1
  exact map_one _

lemma matrixOperatorCLE_inv (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixOperatorCLE N A⁻¹ = Ring.inverse (matrixOperatorCLE N A) := by
  change Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) A⁻¹ =
    Ring.inverse (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) A)
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact map_ringInverse (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toRingEquiv A

/-- Actual matrix inversion has strict derivative -id at the identity,
transported through a native continuous operator-algebra equivalence. -/
theorem hasStrictFDerivAt_matrixInverse_one (N : ℕ) :
    HasStrictFDerivAt (fun A : Matrix (Fin N) (Fin N) ℝ => A⁻¹)
      (-(ContinuousLinearMap.id ℝ (Matrix (Fin N) (Fin N) ℝ))) 1 := by
  let e := matrixOperatorCLE N
  let O := EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)
  have hOp : HasStrictFDerivAt (Ring.inverse : O → O) (-(ContinuousLinearMap.id ℝ O)) (e 1) := by
    rw [show e 1 = 1 from matrixOperatorCLE_one N]
    convert! hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (1 : Oˣ) using 1
  have hh := e.symm.toContinuousLinearMap.hasStrictFDerivAt.comp (1 : Matrix (Fin N) (Fin N) ℝ)
    (hOp.comp (1 : Matrix (Fin N) (Fin N) ℝ) e.toContinuousLinearMap.hasStrictFDerivAt)
  convert! hh using 1
  · funext A
    change A⁻¹ = e.symm (Ring.inverse (e A))
    rw [← matrixOperatorCLE_inv]
    exact (e.symm_apply_apply A⁻¹).symm
  · apply ContinuousLinearMap.ext
    intro H
    change -H = e.symm (-(e H))
    rw [map_neg, e.symm_apply_apply]

/-- The half factor makes the actual Cayley differential at zero exactly id. -/
theorem hasStrictFDerivAt_cayleyMatrix_zero (N : ℕ) :
    HasStrictFDerivAt (cayleyMatrix N)
      (ContinuousLinearMap.id ℝ (Matrix (Fin N) (Fin N) ℝ)) 0 := by
  let h := (1 / 2 : ℝ)
  have hs := (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : Matrix (Fin N) (Fin N) ℝ)).const_smul h
  have hm := hs.const_sub (1 : Matrix (Fin N) (Fin N) ℝ)
  have hp := hs.const_add (1 : Matrix (Fin N) (Fin N) ℝ)
  have hi : HasStrictFDerivAt (fun A : Matrix (Fin N) (Fin N) ℝ => A⁻¹)
      (-(ContinuousLinearMap.id ℝ (Matrix (Fin N) (Fin N) ℝ))) (1 - h • (0 : Matrix (Fin N) (Fin N) ℝ)) := by
    simpa only [smul_zero, sub_zero] using hasStrictFDerivAt_matrixInverse_one N
  have hh := (matrixMulCLM N).hasStrictFDerivAt_of_bilinear (hi.comp 0 hm) hp
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro H
  change H = (1 - h • (0 : Matrix (Fin N) (Fin N) ℝ))⁻¹ * (h • H) +
    (-(-(h • H))) * (1 + h • (0 : Matrix (Fin N) (Fin N) ℝ))
  simp only [smul_zero, sub_zero, add_zero, inv_one, Matrix.one_mul, Matrix.mul_one, neg_neg]
  rw [← add_smul]
  norm_num [h]

/-- An actual native ambient local inverse; restriction to skew/orthogonal
coordinates and global chart coverage are separate obligations. -/
def cayleyLocalHomeomorph (N : ℕ) :
    OpenPartialHomeomorph (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph
    (f' := ContinuousLinearEquiv.refl ℝ (Matrix (Fin N) (Fin N) ℝ))
    (cayleyMatrix N) (hasStrictFDerivAt_cayleyMatrix_zero N)

lemma cayleyLocalHomeomorph_apply (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    cayleyLocalHomeomorph N A = cayleyMatrix N A := rfl

lemma zero_mem_cayleyLocalHomeomorph_source (N : ℕ) :
    (0 : Matrix (Fin N) (Fin N) ℝ) ∈ (cayleyLocalHomeomorph N).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ (Matrix (Fin N) (Fin N) ℝ))
    (hasStrictFDerivAt_cayleyMatrix_zero N)

lemma one_mem_cayleyLocalHomeomorph_target (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℝ) ∈ (cayleyLocalHomeomorph N).target := by
  have hh := (cayleyLocalHomeomorph N).map_source (zero_mem_cayleyLocalHomeomorph_source N)
  simpa only [cayleyLocalHomeomorph_apply, cayleyMatrix_zero] using hh

lemma cayleyLocalHomeomorph_symm_one (N : ℕ) :
    (cayleyLocalHomeomorph N).symm (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  have hh := (cayleyLocalHomeomorph N).left_inv (zero_mem_cayleyLocalHomeomorph_source N)
  simpa only [cayleyLocalHomeomorph_apply, cayleyMatrix_zero] using hh

end Paper.Spectral
