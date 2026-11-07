/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWordChart

/-! Literal independent angular slots for a fixed scalar/pair Schur word. -/
@[expose] public section
noncomputable section
open scoped Matrix

namespace Paper.Spectral

variable {d m : ℕ}

/-- Copy the lower-left angular entries, head angles and tail angles; free slots are zero. -/
def schurAngularStepCoordinates
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ)) :
    Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ →ₗ[ℝ]
      (SchurStepIndex (Fin d) (Fin m) → ℝ) where
  toFun M
    | .inl (j, i) => M (.inr i) (.inl j)
    | .inr (.inl p) => s M.toBlocks₁₁ p
    | .inr (.inr (.inl p)) => t M.toBlocks₂₂ p
    | .inr (.inr (.inr _)) => 0
  map_add' A B := by
    funext p
    rcases p with p | p | p | p
    · rfl
    · exact congrFun (s.map_add A.toBlocks₁₁ B.toBlocks₁₁) p
    · exact congrFun (t.map_add A.toBlocks₂₂ B.toBlocks₂₂) p
    · simp
  map_smul' r M := by
    funext p
    rcases p with p | p | p | p
    · rfl
    · exact congrFun (s.map_smul r M.toBlocks₁₁) p
    · exact congrFun (t.map_smul r M.toBlocks₂₂) p
    · simp

/-- The angular section in the actual physical column-row cells. -/
def schurAngularSectionStep
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ)) :
    Matrix (Fin (d + m)) (Fin (d + m)) ℝ →ₗ[ℝ]
      (Fin (d + m) × Fin (d + m) → ℝ) :=
  (schurCellCoordinateEquiv ℝ d m).symm.toLinearMap.comp
    ((schurAngularStepCoordinates s t).comp
      (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).symm.toLinearMap)

@[simp] theorem schurAngularSectionStep_coordinates
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) :
    schurCellCoordinateEquiv ℝ d m (schurAngularSectionStep s t M) =
      schurAngularStepCoordinates s t (M.submatrix finSumFinEquiv finSumFinEquiv) :=
  (schurCellCoordinateEquiv ℝ d m).apply_symm_apply _

@[simp] theorem schurLowerInput_angularCoordinates
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) :
    schurLowerInput (schurAngularStepCoordinates s t M) = M.toBlocks₂₁ := rfl

@[simp] theorem schurHeadInput_angularCoordinates
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) :
    schurHeadInput (schurAngularStepCoordinates s t M) = s M.toBlocks₁₁ := rfl

@[simp] theorem schurTailInput_angularCoordinates
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) :
    schurTailInput (schurAngularStepCoordinates s t M) = t M.toBlocks₂₂ := rfl

@[simp] theorem schurUpperInput_angularCoordinates
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) :
    schurUpperInput (schurAngularStepCoordinates s t M) = 0 := rfl

/-- The unique within-pair angle is slot(1,1), read from the actual lower entry. -/
def pairAngularSection : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 × Fin 2 → ℝ) :=
  (LinearMap.single ℝ (fun _ : Fin 2 × Fin 2 => ℝ) (1, 1)).comp
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) (1 : Fin 2)))

@[simp] theorem pairAngularSection_apply (M : Matrix (Fin 2) (Fin 2) ℝ) :
    pairAngularSection M = Pi.single (1, 1) (M 1 0) := rfl

/-- A concrete section, not an arbitrary chosen inverse. -/
def schurWordAngularSection : (w : List Bool) →
    Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ →ₗ[ℝ]
      (Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ)
  | [] => 0
  | false :: w => schurAngularSectionStep 0 (schurWordAngularSection w)
  | true :: w => schurAngularSectionStep pairAngularSection (schurWordAngularSection w)

theorem submatrix_preserves_skew {ι κ : Type*} (M : Matrix ι ι ℝ)
    (hM : Mᵀ = -M) (f : κ → ι) : (M.submatrix f f)ᵀ = -(M.submatrix f f) := by
  ext i j
  exact congrArg (fun A : Matrix ι ι ℝ => A (f i) (f j)) hM

/-- A step reconstructs the whole skew matrix once its two diagonal blocks do. -/
theorem schurAngularSectionStep_rightInverse
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin (d + m)) (Fin (d + m)) ℝ) (hM : Mᵀ = -M)
    (hhead : ω (s (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁)
    (htail : η (t (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂) =
      (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂) :
    schurOmegaPhysical d m ω η (schurAngularSectionStep s t M) = M := by
  apply (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).symm.injective
  change (schurOmegaPhysical d m ω η (schurAngularSectionStep s t M)).submatrix
    finSumFinEquiv finSumFinEquiv = M.submatrix finSumFinEquiv finSumFinEquiv
  rw [schurOmegaPhysical_submatrix, schurAngularSectionStep_coordinates]
  change Matrix.fromBlocks
    (ω (s (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁))
    (-((M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁)ᵀ)
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
    (η (t (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂)) = _
  rw [hhead, htail]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · have h := congrArg (fun A : Matrix (Fin (d + m)) (Fin (d + m)) ℝ =>
      A (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j))) hM
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    change -M (finSumFinEquiv (.inr j)) (finSumFinEquiv (.inl i)) =
      M (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j))
    linarith
  · rfl
  · rfl

/-- The angular section leaves no free Schur matrix entry. -/
theorem schurAngularSectionStep_parameter_zero
    (K : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (L : (Fin m × Fin m → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (s : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d × Fin d → ℝ))
    (t : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (Fin m × Fin m → ℝ))
    (M : Matrix (Fin (d + m)) (Fin (d + m)) ℝ)
    (hhead : K (s (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁) = 0)
    (htail : L (t (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂) = 0) :
    schurParameterPhysical d m K L (schurAngularSectionStep s t M) = 0 := by
  apply (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).symm.injective
  change (schurParameterPhysical d m K L (schurAngularSectionStep s t M)).submatrix
    finSumFinEquiv finSumFinEquiv = 0
  rw [schurParameterPhysical_submatrix, schurAngularSectionStep_coordinates]
  change Matrix.fromBlocks
    (K (s (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁)) 0 0
    (L (t (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂)) = 0
  rw [hhead, htail]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem scalar_skew_eq_zero (M : Matrix (Fin 1) (Fin 1) ℝ) (hM : Mᵀ = -M) : M = 0 := by
  have h := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℝ => A 0 0) hM
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  change M 0 0 = 0
  linarith

theorem pairHeadOmega_angularSection (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : Mᵀ = -M) :
    pairHeadOmega (pairAngularSection M) = M := by
  simp only [pairHeadOmega_apply, pairAngularSection_apply, Pi.single_eq_same]
  have h (i j : Fin 2) : M j i = -M i j :=
    congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairSkew] <;>
    linarith [h 0 0, h 0 1, h 1 0, h 1 1]

theorem pairHeadParameter_angularSection (M : Matrix (Fin 2) (Fin 2) ℝ) :
    pairHeadParameter (pairAngularSection M) = 0 := by
  rw [pairHeadParameter_apply, pairAngularSection_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [schurBlock]

/-- Every skew matrix is recovered from the literal word angular slots. -/
theorem schurWordOmega_angularSection (w : List Bool) :
    ∀ (M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ),
      Mᵀ = -M → schurWordOmega w (schurWordAngularSection w M) = M := by
  induction w with
  | nil =>
    intro M hM
    change (0 : Matrix (Fin 0) (Fin 0) ℝ) = M
    exact Subsingleton.elim _ _
  | cons b w ih =>
    cases b <;> intro M hM
    · apply schurAngularSectionStep_rightInverse (d := 1) (m := schurWordSize w)
        0 (schurWordOmega w) 0 (schurWordAngularSection w) M hM
      · exact (scalar_skew_eq_zero _
          (submatrix_preserves_skew M hM (fun i : Fin 1 =>
            finSumFinEquiv (.inl i : Fin 1 ⊕ Fin (schurWordSize w))))).symm
      · exact ih _ (submatrix_preserves_skew M hM (fun i : Fin (schurWordSize w) =>
          finSumFinEquiv (.inr i : Fin 1 ⊕ Fin (schurWordSize w))))
    · apply schurAngularSectionStep_rightInverse (d := 2) (m := schurWordSize w)
        pairHeadOmega (schurWordOmega w) pairAngularSection (schurWordAngularSection w) M hM
      · exact pairHeadOmega_angularSection _
          (submatrix_preserves_skew M hM (fun i : Fin 2 =>
            finSumFinEquiv (.inl i : Fin 2 ⊕ Fin (schurWordSize w))))
      · exact ih _ (submatrix_preserves_skew M hM (fun i : Fin (schurWordSize w) =>
          finSumFinEquiv (.inr i : Fin 2 ⊕ Fin (schurWordSize w))))

/-- The same section contributes zero free matrix for every raw input matrix. -/
theorem schurWordParameter_angularSection (w : List Bool) :
    ∀ (M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ),
      schurWordParameter w (schurWordAngularSection w M) = 0 := by
  induction w with
  | nil => intro M; simp [schurWordParameter]
  | cons b w ih =>
    cases b <;> intro M
    · apply schurAngularSectionStep_parameter_zero (d := 1) (m := schurWordSize w)
        scalarHeadParameter (schurWordParameter w) 0 (schurWordAngularSection w) M
      · simp
      · exact ih _
    · apply schurAngularSectionStep_parameter_zero (d := 2) (m := schurWordSize w)
        pairHeadParameter (schurWordParameter w) pairAngularSection (schurWordAngularSection w) M
      · exact pairHeadParameter_angularSection _
      · exact ih _

/-- The proved concrete section as a map from the native skew-adjoint module. -/
def schurWordAngularRightInverse (w : List Bool) :
    SkewMatrix (schurWordSize w) →ₗ[ℝ]
      (Fin (schurWordSize w) × Fin (schurWordSize w) → ℝ) :=
  (schurWordAngularSection w).comp
    (skewAdjoint.submodule ℝ (Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)).subtype

@[simp] theorem schurWordOmegaSkew_rightInverse (w : List Bool)
    (M : SkewMatrix (schurWordSize w)) :
    schurWordOmegaSkew w (schurWordAngularRightInverse w M) = M := by
  apply Subtype.ext
  exact schurWordOmega_angularSection w M (skewMatrix_transpose _ M)

@[simp] theorem schurWordParameter_rightInverse (w : List Bool)
    (M : SkewMatrix (schurWordSize w)) :
    schurWordParameter w (schurWordAngularRightInverse w M) = 0 :=
  schurWordParameter_angularSection w M

end Paper.Spectral
