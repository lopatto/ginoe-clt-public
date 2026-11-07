/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.ConjugationDifferential
public import GinoeClt.Spectral.SylvesterBlocks
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases

/-! # The coordinate Jacobian of one normalized real Schur pair

Output coordinates are exactly (A00,A10,A01,A11); input increments are
(da,db,dc,theta). This is a finite coordinate statement, not a Haar-volume
normalization or a full Schur change-of-variables theorem.
-/

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

def pairCoordinates {R : Type*} (M : Matrix (Fin 2) (Fin 2) R) : Fin 4 → R :=
  ![M 0 0, M 1 0, M 0 1, M 1 1]

def pairJacobianMatrix {R : Type*} [CommRing R] (b c : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, c - b; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, b - c]

def pairSkew (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -theta; theta, 0]

lemma pairSkew_transpose (theta : ℝ) : (pairSkew theta)ᵀ = -pairSkew theta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairSkew]

/-- The actual ambient conjugation differential has the stated column-major
coordinate matrix, with no volume convention hidden in the determinant. -/
theorem conjugationDerivative_pair_coordinates (a b c da db dc theta : ℝ) :
    pairCoordinates (conjugationDerivative 2 1 (schurBlock a b c)
      (pairSkew theta, schurBlock da db dc)) =
      pairJacobianMatrix b c *ᵥ ![da, db, dc, theta] := by
  rw [conjugationDerivative_apply]
  ext i
  fin_cases i <;>
    norm_num [pairCoordinates, pairJacobianMatrix, pairSkew, schurBlock,
      Matrix.mulVec, Matrix.vecMul, Matrix.transpose_apply, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem det_pairJacobianMatrix {R : Type*} [CommRing R] (b c : R) :
    (pairJacobianMatrix b c).det = 2 * (b - c) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [pairJacobianMatrix, Matrix.det_fin_three, Fin.sum_univ_succ,
    Matrix.submatrix_apply,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 by decide,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 by decide,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 by decide]
  ring

theorem abs_det_pairJacobianMatrix (b c : ℝ) (hcb : c ≤ b) :
    |(pairJacobianMatrix b c).det| = 2 * (b - c) := by
  rw [det_pairJacobianMatrix, abs_of_nonneg (by positivity)]

def pairRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos theta, -Real.sin theta; Real.sin theta, Real.cos theta]

@[simp] theorem pairRotation_zero : pairRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairRotation]

theorem hasDerivAt_pairRotation_zero : HasDerivAt pairRotation (pairSkew 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [pairRotation, pairSkew] using Real.hasDerivAt_cos 0
  · simpa [pairRotation, pairSkew, Pi.neg_def] using (Real.hasDerivAt_sin 0).neg
  · simpa [pairRotation, pairSkew] using Real.hasDerivAt_sin 0
  · simpa [pairRotation, pairSkew] using Real.hasDerivAt_cos 0

def pairParameterLinear : (Fin 4 → ℝ) →ₗ[ℝ]
    (Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) where
  toFun x := (pairSkew (x 3), schurBlock (x 0) (x 1) (x 2))
  map_add' x y := by
    apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [pairSkew, schurBlock] <;> abel
  map_smul' r x := by
    apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [pairSkew, schurBlock]

def pairParameterCLM : (Fin 4 → ℝ) →L[ℝ]
    (Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ) :=
  pairParameterLinear.toContinuousLinearMap

lemma pairParameterCLM_apply (x : Fin 4 → ℝ) :
    pairParameterCLM x = (pairSkew (x 3), schurBlock (x 0) (x 1) (x 2)) := rfl

def pairCoordinatesLinear : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := pairCoordinates
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

def pairCoordinatesCLM : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] (Fin 4 → ℝ) :=
  pairCoordinatesLinear.toContinuousLinearMap

lemma pairCoordinatesCLM_apply (M : Matrix (Fin 2) (Fin 2) ℝ) :
    pairCoordinatesCLM M = pairCoordinates M := rfl

def pairParameterMap (x : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ :=
  (pairRotation (x 3), schurBlock (x 0) (x 1) (x 2))

def pairChart (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  pairCoordinates (pairRotation (x 3) * schurBlock (x 0) (x 1) (x 2) * (pairRotation (x 3))ᵀ)

def pairJacobianCLM (b c : ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  (Matrix.toLin' (pairJacobianMatrix b c)).toContinuousLinearMap

lemma pairJacobianCLM_apply (b c : ℝ) (x : Fin 4 → ℝ) :
    pairJacobianCLM b c x = pairJacobianMatrix b c *ᵥ x := rfl

theorem hasFDerivAt_pairParameterMap_zero (a b c : ℝ) :
    HasFDerivAt pairParameterMap pairParameterCLM ![a, b, c, 0] := by
  let x0 : Fin 4 → ℝ := ![a, b, c, 0]
  let M := Matrix (Fin 2) (Fin 2) ℝ
  let dT : (Fin 4 → ℝ) →L[ℝ] M := (ContinuousLinearMap.snd ℝ M M).comp pairParameterCLM
  let dR : (Fin 4 → ℝ) →L[ℝ] M :=
    (ContinuousLinearMap.toSpanSingleton ℝ (pairSkew 1)).comp (ContinuousLinearMap.proj 3)
  have hT : HasFDerivAt (fun x : Fin 4 → ℝ => schurBlock (x 0) (x 1) (x 2)) dT x0 :=
    dT.hasFDerivAt
  have hRot : HasFDerivAt (fun x : Fin 4 → ℝ => pairRotation (x 3)) dR x0 := by
    convert! hasDerivAt_pairRotation_zero.hasFDerivAt.comp x0
      (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x0) using 1
  have hD : dR.prod dT = pairParameterCLM := by
    apply ContinuousLinearMap.ext
    intro x
    apply Prod.ext
    · change (x 3 : ℝ) • pairSkew 1 = pairSkew (x 3)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pairSkew]
    · rfl
  exact (hRot.prodMk hT).congr_fderiv hD

/-- The actual nonlinear rotation-conjugation pair chart has the exact
coordinate Jacobian matrix at theta=0, in the specified input/output orders. -/
theorem hasFDerivAt_pairChart_zero (a b c : ℝ) :
    HasFDerivAt pairChart (pairJacobianCLM b c) ![a, b, c, 0] := by
  let x0 : Fin 4 → ℝ := ![a, b, c, 0]
  have hp := hasFDerivAt_pairParameterMap_zero a b c
  have hpt : pairParameterMap x0 = (1, schurBlock a b c) := by
    simp [pairParameterMap, x0]
  have hc0 : HasFDerivAt
      (fun p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ => p.1 * p.2 * p.1ᵀ)
      (conjugationDerivative 2 1 (schurBlock a b c)) (pairParameterMap x0) := by
    rw [hpt]
    exact hasFDerivAt_conjugation 2 1 (schurBlock a b c)
  have hc := hc0.comp x0 hp
  have hh := pairCoordinatesCLM.hasFDerivAt.comp x0 hc
  have hD : pairCoordinatesCLM.comp
      ((conjugationDerivative 2 1 (schurBlock a b c)).comp pairParameterCLM) =
        pairJacobianCLM b c := by
    apply ContinuousLinearMap.ext
    intro x
    change pairCoordinates (conjugationDerivative 2 1 (schurBlock a b c)
        (pairSkew (x 3), schurBlock (x 0) (x 1) (x 2))) =
      pairJacobianMatrix b c *ᵥ x
    have hx : ![x 0, x 1, x 2, x 3] = x := by
      ext i
      fin_cases i <;> rfl
    rw [conjugationDerivative_pair_coordinates, hx]
  convert! hh.congr_fderiv hD using 1

theorem pairRotation_mem_orthogonal (theta : ℝ) :
    pairRotation theta ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff _ _]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairRotation, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      nlinarith only [Real.sin_sq_add_cos_sq theta]

theorem fderiv_pairChart_zero (a b c : ℝ) :
    fderiv ℝ pairChart ![a, b, c, 0] = pairJacobianCLM b c :=
  (hasFDerivAt_pairChart_zero a b c).fderiv

/-- Determinant of the actual nonlinear coordinate derivative, with respect
to the ordinary standard input/output coordinate bases. -/
theorem det_fderiv_pairChart_zero (a b c : ℝ) :
    (LinearMap.toMatrix' (fderiv ℝ pairChart ![a, b, c, 0]).toLinearMap).det =
      2 * (b - c) := by
  rw [fderiv_pairChart_zero]
  change (LinearMap.toMatrix' (Matrix.toLin' (pairJacobianMatrix b c))).det = _
  rw [LinearMap.toMatrix'_toLin', det_pairJacobianMatrix]

theorem abs_det_fderiv_pairChart_zero (a b c : ℝ) (hcb : c ≤ b) :
    |(LinearMap.toMatrix' (fderiv ℝ pairChart ![a, b, c, 0]).toLinearMap).det| =
      2 * (b - c) := by
  rw [det_fderiv_pairChart_zero, abs_of_nonneg (by positivity)]

theorem det_fderiv_pairChart_zero_ne_zero (a b c : ℝ) (hcb : c < b) :
    (LinearMap.toMatrix' (fderiv ℝ pairChart ![a, b, c, 0]).toLinearMap).det ≠ 0 := by
  rw [det_fderiv_pairChart_zero]
  positivity

end Paper.Spectral
