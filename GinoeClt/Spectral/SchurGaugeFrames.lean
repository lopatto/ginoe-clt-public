/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurWordRegularity
public import GinoeClt.Spectral.SchurBlockGauge
@[expose] public section
noncomputable section
open scoped Matrix
namespace Paper.Spectral

/-- Actual scalar sign on a nonzero Schur head. -/
def schurGaugeHead (d : ℕ) (b : Bool) : Matrix (Fin d) (Fin d) ℝ := if b then -1 else 1

/-- Literal physical block diagonal head sign and tail frame. -/
def schurGaugeExtension (d m : ℕ) (x : Bool × Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (d+m)) (Fin (d+m)) ℝ := upperBlockMatrix (schurGaugeHead d x.1) 0 x.2

theorem schurGaugeExtension_injective (d m : ℕ) (hd : 0 < d) :
    Function.Injective (schurGaugeExtension d m) := by
  intro x y he
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d+m))
  have hb : Matrix.fromBlocks (schurGaugeHead d x.1) 0 0 x.2 =
      Matrix.fromBlocks (schurGaugeHead d y.1) 0 0 y.2 := ρ.injective he
  have hhead := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₁₁) hb
  have htail := congrArg (fun M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ => M.toBlocks₂₂) hb
  simp only [Matrix.toBlocks_fromBlocks₁₁] at hhead
  simp only [Matrix.toBlocks_fromBlocks₂₂] at htail
  have h00 := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M ⟨0,hd⟩ ⟨0,hd⟩) hhead
  have hbit : x.1 = y.1 := by
    rcases x with ⟨b,D⟩
    rcases y with ⟨c,E⟩
    cases b <;> cases c
    · rfl
    · have hf : (1 : ℝ) = -1 := by simpa [schurGaugeHead] using h00
      norm_num at hf
    · have hf : (-1 : ℝ) = 1 := by simpa [schurGaugeHead] using h00
      norm_num at hf
    · rfl
  exact Prod.ext hbit htail

theorem schurGaugeHead_orthogonal (d : ℕ) (b : Bool) :
    schurGaugeHead d b ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
  cases b <;> simp [schurGaugeHead]

theorem schurGaugeExtension_orthogonal (d m : ℕ) (b : Bool)
    (D : Matrix (Fin m) (Fin m) ℝ) (hD : D ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    schurGaugeExtension d m (b,D) ∈ Matrix.orthogonalGroup (Fin (d+m)) ℝ := by
  let H := schurGaugeHead d b
  let P : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.fromBlocks H 0 0 D
  have hH : H * Hᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp (schurGaugeHead_orthogonal d b)
  have hDD : D * Dᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hD
  have hP : P * Pᵀ = 1 := by
    simp only [P, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, hH, hDD,
      Matrix.fromBlocks_one]
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d+m))
  apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
  change ρ P * ρ Pᵀ = 1
  rw [← map_mul, hP, map_one]

/-- The actual finite family of all block sign frames, without chartwise multiplicity claims. -/
def schurWordGaugeFrames (w : List Bool) :
    Finset (Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) := by
  classical
  exact match w with
  | [] => {1}
  | false::v => (Finset.univ ×ˢ schurWordGaugeFrames v).image (schurGaugeExtension 1 (schurWordSize v))
  | true::v => (Finset.univ ×ˢ schurWordGaugeFrames v).image (schurGaugeExtension 2 (schurWordSize v))

theorem card_schurWordGaugeFrames (w : List Bool) :
    (schurWordGaugeFrames w).card = 2 ^ w.length := by
  classical
  induction w with
  | nil => simp [schurWordGaugeFrames]
  | cons b w ih =>
    cases b
    · change (((Finset.univ : Finset Bool) ×ˢ schurWordGaugeFrames w).image
        (schurGaugeExtension 1 (schurWordSize w))).card = 2 ^ (w.length+1)
      rw [Finset.card_image_of_injective _ (schurGaugeExtension_injective 1 (schurWordSize w) (by decide)),
        Finset.card_product, Finset.card_univ, Fintype.card_bool, ih, pow_succ]
      ring
    · change (((Finset.univ : Finset Bool) ×ˢ schurWordGaugeFrames w).image
        (schurGaugeExtension 2 (schurWordSize w))).card = 2 ^ (w.length+1)
      rw [Finset.card_image_of_injective _ (schurGaugeExtension_injective 2 (schurWordSize w) (by decide)),
        Finset.card_product, Finset.card_univ, Fintype.card_bool, ih, pow_succ]
      ring

theorem schurWordGaugeFrames_orthogonal (w : List Bool) :
    ∀ Q ∈ schurWordGaugeFrames w, Q ∈ Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ := by
  classical
  induction w with
  | nil =>
    intro Q hQ
    have he : Q = 1 := by simpa [schurWordGaugeFrames] using hQ
    rw [he]
    exact one_mem _
  | cons b w ih =>
    cases b <;> intro Q hQ
    · obtain ⟨⟨b,D⟩,hprod,rfl⟩ := Finset.mem_image.mp hQ
      exact schurGaugeExtension_orthogonal _ _ b D (ih D (Finset.mem_product.mp hprod).2)
    · obtain ⟨⟨b,D⟩,hprod,rfl⟩ := Finset.mem_image.mp hQ
      exact schurGaugeExtension_orthogonal _ _ b D (ih D (Finset.mem_product.mp hprod).2)

end Paper.Spectral
