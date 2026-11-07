/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurCoordinateSupport
@[expose] public section
noncomputable section
open scoped Matrix
namespace Paper.Spectral

@[simp] theorem schurWordAngleMap_apply (w : List Bool) (x : SchurWordCells w)
    (a : SkewIndex (schurWordSize w)) :
    schurWordAngleMap w x a = schurWordOmega w x a.val.2 a.val.1 := rfl

/-- Every native lower angle reads exactly ONE actual raw parameter cell,
with coefficient +1. This is stronger than an abstract linear splitting. -/
theorem schurWordAngleMap_is_free_coordinate (w : List Bool) :
    ∀ a : SkewIndex (schurWordSize w),
      ∃ c : Fin (schurWordSize w) × Fin (schurWordSize w),
        (∀ t : ℝ, schurWordParameter w (Pi.single c t) = 0) ∧
          ∀ x : SchurWordCells w, schurWordAngleMap w x a = x c := by
  induction w with
  | nil => intro a; exact Fin.elim0 a.val.1
  | cons tag w ih =>
    cases tag <;> intro a
    · change SkewIndex (1+schurWordSize w) at a
      rcases a with ⟨⟨j,i⟩,hji⟩
      obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin (schurWordSize w) ≃ Fin (1+schurWordSize w)).surjective j
      obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin (schurWordSize w) ≃ Fin (1+schurWordSize w)).surjective i
      rcases j with j | j <;> rcases i with i | i
      · fin_cases j
        fin_cases i
        change (0 : ℕ) < 0 at hji
        omega
      · refine ⟨schurCellEquiv 1 (schurWordSize w) (.inl (j,i)),?_,?_⟩
        · intro t
          exact schurParameterPhysical_single_lower_zero scalarHeadParameter (schurWordParameter w) j i t
        · intro x
          have hΩ := congrArg (fun M : Matrix (Fin 1 ⊕ Fin (schurWordSize w))
            (Fin 1 ⊕ Fin (schurWordSize w)) ℝ => M (.inr i) (.inl j))
            (schurOmegaPhysical_submatrix (0 : (Fin 1 × Fin 1 → ℝ) →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℝ) (schurWordOmega w) x)
          change schurWordOmega (false::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) =
            schurCellCoordinateEquiv ℝ 1 (schurWordSize w) x (.inl (j,i)) at hΩ
          change schurWordOmega (false::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = x (schurCellEquiv 1 (schurWordSize w) (.inl (j,i))) at hΩ
          change schurWordOmega (false::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = x (schurCellEquiv 1 (schurWordSize w) (.inl (j,i)))
          exact hΩ
      · change 1 + j.val < i.val at hji
        have hi := i.isLt
        omega
      · have htail : j < i := by
          change 1 + j.val < 1 + i.val at hji
          omega
        let a : SkewIndex (schurWordSize w) := ⟨(j,i),htail⟩
        obtain ⟨c,hk,hc⟩ := ih a
        refine ⟨schurCellEquiv 1 (schurWordSize w) (.inr (.inr (.inl c))),?_,?_⟩
        · intro t
          exact schurParameterPhysical_single_tail_zero scalarHeadParameter (schurWordParameter w) c t (hk t)
        · intro x
          have hΩ := congrArg (fun M : Matrix (Fin 1 ⊕ Fin (schurWordSize w))
            (Fin 1 ⊕ Fin (schurWordSize w)) ℝ => M (.inr i) (.inr j))
            (schurOmegaPhysical_submatrix (0 : (Fin 1 × Fin 1 → ℝ) →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℝ) (schurWordOmega w) x)
          change schurWordOmega (false::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) =
            schurWordOmega w (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) x)) i j at hΩ
          change schurWordOmega (false::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) = x (schurCellEquiv 1 (schurWordSize w) (.inr (.inr (.inl c))))
          have h := hc (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) x))
          change schurWordOmega w (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) x)) i j = x (schurCellEquiv 1 (schurWordSize w) (.inr (.inr (.inl c)))) at h
          exact hΩ.trans h
    · change SkewIndex (2+schurWordSize w) at a
      rcases a with ⟨⟨j,i⟩,hji⟩
      obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin 2 ⊕ Fin (schurWordSize w) ≃ Fin (2+schurWordSize w)).surjective j
      obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin 2 ⊕ Fin (schurWordSize w) ≃ Fin (2+schurWordSize w)).surjective i
      rcases j with j | j <;> rcases i with i | i
      · fin_cases j <;> fin_cases i
        · change (0 : ℕ) < 0 at hji
          omega
        · refine ⟨schurCellEquiv 2 (schurWordSize w) (.inr (.inl (1,1))),?_,?_⟩
          · intro t
            exact schurParameterPhysical_single_head_zero pairHeadParameter (schurWordParameter w) (1,1) t (pairHeadParameter_single_angle_zero t)
          · intro x
            have hΩ := congrArg (fun M : Matrix (Fin 2 ⊕ Fin (schurWordSize w))
              (Fin 2 ⊕ Fin (schurWordSize w)) ℝ => M (.inl 1) (.inl 0))
              (schurOmegaPhysical_submatrix pairHeadOmega (schurWordOmega w) x)
            change schurWordOmega (true::w) x (finSumFinEquiv (.inl 1)) (finSumFinEquiv (.inl 0)) =
              schurCellCoordinateEquiv ℝ 2 (schurWordSize w) x (.inr (.inl (1,1))) at hΩ
            change schurWordOmega (true::w) x (finSumFinEquiv (.inl 1)) (finSumFinEquiv (.inl 0)) = x (schurCellEquiv 2 (schurWordSize w) (.inr (.inl (1,1)))) at hΩ
            change schurWordOmega (true::w) x (finSumFinEquiv (.inl 1)) (finSumFinEquiv (.inl 0)) = x (schurCellEquiv 2 (schurWordSize w) (.inr (.inl (1,1))))
            exact hΩ
        · change (1 : ℕ) < 0 at hji
          omega
        · change (1 : ℕ) < 1 at hji
          omega
      · refine ⟨schurCellEquiv 2 (schurWordSize w) (.inl (j,i)),?_,?_⟩
        · intro t
          exact schurParameterPhysical_single_lower_zero pairHeadParameter (schurWordParameter w) j i t
        · intro x
          have hΩ := congrArg (fun M : Matrix (Fin 2 ⊕ Fin (schurWordSize w))
            (Fin 2 ⊕ Fin (schurWordSize w)) ℝ => M (.inr i) (.inl j))
            (schurOmegaPhysical_submatrix pairHeadOmega (schurWordOmega w) x)
          change schurWordOmega (true::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) =
            schurCellCoordinateEquiv ℝ 2 (schurWordSize w) x (.inl (j,i)) at hΩ
          change schurWordOmega (true::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = x (schurCellEquiv 2 (schurWordSize w) (.inl (j,i))) at hΩ
          change schurWordOmega (true::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = x (schurCellEquiv 2 (schurWordSize w) (.inl (j,i)))
          exact hΩ
      · change 2 + j.val < i.val at hji
        have hi := i.isLt
        omega
      · have htail : j < i := by
          change 2 + j.val < 2 + i.val at hji
          omega
        let a : SkewIndex (schurWordSize w) := ⟨(j,i),htail⟩
        obtain ⟨c,hk,hc⟩ := ih a
        refine ⟨schurCellEquiv 2 (schurWordSize w) (.inr (.inr (.inl c))),?_,?_⟩
        · intro t
          exact schurParameterPhysical_single_tail_zero pairHeadParameter (schurWordParameter w) c t (hk t)
        · intro x
          have hΩ := congrArg (fun M : Matrix (Fin 2 ⊕ Fin (schurWordSize w))
            (Fin 2 ⊕ Fin (schurWordSize w)) ℝ => M (.inr i) (.inr j))
            (schurOmegaPhysical_submatrix pairHeadOmega (schurWordOmega w) x)
          change schurWordOmega (true::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) =
            schurWordOmega w (schurTailInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) x)) i j at hΩ
          change schurWordOmega (true::w) x (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) = x (schurCellEquiv 2 (schurWordSize w) (.inr (.inr (.inl c))))
          have h := hc (schurTailInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) x))
          change schurWordOmega w (schurTailInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) x)) i j = x (schurCellEquiv 2 (schurWordSize w) (.inr (.inr (.inl c)))) at h
          exact hΩ.trans h

/-- Coordinate-reading consequence, with the parameter-kernel property proved above. -/
theorem schurWordAngleMap_is_coordinate (w : List Bool)
    (a : SkewIndex (schurWordSize w)) :
    ∃ c : Fin (schurWordSize w) × Fin (schurWordSize w),
      ∀ x : SchurWordCells w, schurWordAngleMap w x a = x c := by
  obtain ⟨c,_,hc⟩ := schurWordAngleMap_is_free_coordinate w a
  exact ⟨c,hc⟩

/-- A chosen literal cell, backed by the complete coordinate-reading theorem. -/
def schurWordAngleCell (w : List Bool) (a : SkewIndex (schurWordSize w)) :
    Fin (schurWordSize w) × Fin (schurWordSize w) :=
  Classical.choose (schurWordAngleMap_is_free_coordinate w a)

theorem schurWordAngleCell_spec (w : List Bool) (a : SkewIndex (schurWordSize w))
    (x : SchurWordCells w) : schurWordAngleMap w x a = x (schurWordAngleCell w a) :=
  (Classical.choose_spec (schurWordAngleMap_is_free_coordinate w a)).2 x

/-- An angular coordinate is absent from the actual Schur parameter matrix. -/
theorem schurWordParameter_single_angleCell (w : List Bool)
    (a : SkewIndex (schurWordSize w)) (t : ℝ) :
    schurWordParameter w (Pi.single (schurWordAngleCell w a) t) = 0 :=
  (Classical.choose_spec (schurWordAngleMap_is_free_coordinate w a)).1 t

/-- Distinct native angles read distinct original cells. -/
theorem schurWordAngleCell_injective (w : List Bool) : Function.Injective (schurWordAngleCell w) := by
  classical
  intro a b hab
  by_contra hne
  let y : SchurWordAngles w := Pi.single a 1
  let x := schurWordAngleSection w y
  have he : schurWordAngleMap w x a = schurWordAngleMap w x b :=
    (schurWordAngleCell_spec w a x).trans
      ((congrArg x hab).trans (schurWordAngleCell_spec w b x).symm)
  have h : y a = y b := by simpa only [x, schurWordAngleMap_section] using he
  simp [y, Ne.symm hne] at h

end Paper.Spectral
