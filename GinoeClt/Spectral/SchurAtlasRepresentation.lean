/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.BoundedAngularPartition
public import GinoeClt.Spectral.SchurAngleInsertion
public import GinoeClt.Spectral.ConjugationVolume
@[expose] public section
noncomputable section
open Set
open scoped Matrix Matrix.Norms.Elementwise Kronecker
namespace Paper.Spectral

/-- The actual assigned orthogonal frame of a chart label and raw word cells. -/
def schurAtlasFrame (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ :=
  boundedAngularFrame (schurWordSize w) (centers z.1) (schurWordAngleMap w z.2)

/-- The actual translated word matrix, with the SAME parameter map K. -/
def schurAtlasMatrix (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ :=
  schurAtlasFrame w centers z * schurWordParameter w z.2 * (schurAtlasFrame w centers z)ᵀ

/-- Literal column-major cells of the actual translated word matrix. -/
def schurAtlasCells (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) : SchurWordCells w :=
  Matrix.vec (schurAtlasMatrix w centers z)

/-- Complete physical source: assigned bounded angles, positive/ordered word and actual regularity. -/
def schurAtlasSource (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) : Prop :=
  schurWordAngleMap w z.2 ∈ boundedAngularPiece centers z.1 ∧
    SchurWordPositive w z.2 ∧ SchurWordOrdered w z.2 ∧
      LinearMap.det (schurWordDifferential w z.2) ≠ 0

theorem skewFromCoordinates_schurWordAngleMap (w : List Bool) (x : SchurWordCells w) :
    (skewFromCoordinates (schurWordSize w) (schurWordAngleMap w x) :
      Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordOmega w x := by
  have h := (skewCoordinateEquiv (schurWordSize w)).apply_symm_apply (schurWordOmegaSkew w x)
  change skewFromCoordinates (schurWordSize w) (schurWordAngleMap w x) =
    schurWordOmegaSkew w x at h
  exact congrArg Subtype.val h

theorem schurAtlasFrame_eq_word (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    schurAtlasFrame w centers z =
      (centers z.1 : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) *
        cayleyMatrix (schurWordSize w) (schurWordOmega w z.2) := by
  unfold schurAtlasFrame boundedAngularFrame
  rw [skewFromCoordinates_schurWordAngleMap]

theorem schurAtlasMatrix_eq_translatedChart (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    schurAtlasMatrix w centers z =
      (centers z.1 : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) *
        schurWordChart w z.2 * (centers z.1 : Matrix _ _ ℝ)ᵀ := by
  simp only [schurAtlasMatrix,schurAtlasFrame_eq_word,schurWordChart,
    Matrix.transpose_mul,Matrix.mul_assoc]

theorem schurAtlasCells_eq_translatedChart (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    schurAtlasCells w centers z =
      Matrix.toLin' ((centers z.1 : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) ⊗ₖ
        (centers z.1 : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))
          (schurWordChartCells w z.2) := by
  change Matrix.vec (schurAtlasMatrix w centers z) = _ *ᵥ Matrix.vec (schurWordChart w z.2)
  rw [schurAtlasMatrix_eq_translatedChart]
  exact (orthogonalConjugation_kronecker_action (schurWordSize w) (centers z.1)
    (schurWordChart w z.2)).symm

theorem schurAtlasFrame_orthogonal (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    schurAtlasFrame w centers z ∈ Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ := by
  let Q := centers z.1
  let Ω := skewFromCoordinates (schurWordSize w) (schurWordAngleMap w z.2)
  let C := cayleyMatrix (schurWordSize w) Ω
  have hC : C * Cᵀ = 1 := cayleyMatrix_orthogonal (schurWordSize w) Ω
    (skewMatrix_transpose (schurWordSize w) Ω)
  have hQ : (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) * (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff _ _).mp Q.property
  apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
  change ((Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) * C) * ((Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) * C)ᵀ = 1
  rw [Matrix.transpose_mul]
  calc
    _ = (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) * (C * Cᵀ) * (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hC,Matrix.mul_one,hQ]

/-- A fixed actual regular parameter K and ANY orthogonal frame have unique assigned raw coordinates.
No Schur-map fiber cardinality or ensemble identity is assumed. -/
theorem existsUnique_schurAtlas_frame_parameter (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (p : SchurWordCells w) (hp : SchurWordPositive w p) (ho : SchurWordOrdered w p)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0)
    (R : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ) :
    ∃! z : Fin (m+1) × SchurWordCells w,
      schurAtlasSource w centers z ∧
        schurAtlasFrame w centers z = (R : Matrix _ _ ℝ) ∧
        schurWordParameter w z.2 = schurWordParameter w p := by
  have hR := (Matrix.mem_orthogonalGroup_iff _ _).mp R.property
  obtain ⟨b,hb,hbu⟩ := existsUnique_boundedAngularPair centers hcover (R : Matrix _ _ ℝ) hR
  obtain ⟨x,hx,hxu⟩ := existsUnique_schurWord_angle_parameter w p hd b.2
  have hs := schurWord_source_congr_parameter w x p hx.2
  refine ⟨(b.1,x),?_,?_⟩
  · refine ⟨⟨?_,hs.1.mpr hp,hs.2.1.mpr ho,hs.2.2.2.mpr hd⟩,?_,hx.2⟩
    · change schurWordAngleMap w x ∈ boundedAngularPiece centers b.1
      rw [hx.1]
      exact hb.1
    · change boundedAngularFrame (schurWordSize w) (centers b.1) (schurWordAngleMap w x) = R
      rw [hx.1]
      exact hb.2
  · rintro ⟨j,y⟩ hy
    have hya : schurWordAngleMap w y ∈ boundedAngularPiece centers j := hy.1.1
    have hyR : boundedAngularFrame (schurWordSize w) (centers j) (schurWordAngleMap w y) = R := hy.2.1
    have hb' : (j,schurWordAngleMap w y) = b :=
      hbu (j,schurWordAngleMap w y) ⟨hya,hyR⟩
    have hyx : y = x := hxu y ⟨congrArg Prod.snd hb',hy.2.2⟩
    apply Prod.ext
    · have hj : j = b.1 := congrArg (fun t : Fin (m+1) × SchurWordAngles w => t.1) hb'
      exact hj
    · exact hyx

end Paper.Spectral
