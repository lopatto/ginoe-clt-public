/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurCoordinateVolume
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix
namespace Paper.Spectral

/-- Characterize the chosen coordinate complement WITHOUT unfolding Classical.choose. -/
theorem schurWord_not_mem_angleCell_iff (w : List Bool)
    (c : Fin (schurWordSize w) × Fin (schurWordSize w)) :
    c ∉ Finset.univ.image (schurWordAngleCell w) ↔
      schurWordOmega w (Pi.single c (1 : ℝ)) = 0 := by
  classical
  constructor
  · intro hc
    have ha : schurWordAngleMap w (Pi.single c (1 : ℝ)) = 0 := by
      funext a
      rw [schurWordAngleCell_spec]
      have hne : schurWordAngleCell w a ≠ c := by
        intro he
        exact hc (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,he⟩)
      simp [hne]
    have hs : schurWordOmegaSkew w (Pi.single c (1 : ℝ)) = 0 := by
      apply (skewCoordinateEquiv (schurWordSize w)).symm.injective
      change (skewCoordinateEquiv (schurWordSize w)).symm
        (schurWordOmegaSkew w (Pi.single c (1 : ℝ))) = 0 at ha
      simpa only [map_zero] using ha
    exact congrArg Subtype.val hs
  · intro hΩ hc
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hc
    have h := schurWordAngleCell_spec w a (Pi.single c (1 : ℝ))
    rw [schurWordAngleMap_apply,hΩ,ha] at h
    simp at h

/-- Exact block characterization, independent of invertibility or word positivity. -/
theorem schurOmegaPhysical_eq_zero_iff {d n : ℕ}
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin n × Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (x : Fin (d+n) × Fin (d+n) → ℝ) :
    schurOmegaPhysical d n ω η x = 0 ↔
      ω (schurHeadInput (schurCellCoordinateEquiv ℝ d n x)) = 0 ∧
      schurLowerInput (schurCellCoordinateEquiv ℝ d n x) = 0 ∧
      η (schurTailInput (schurCellCoordinateEquiv ℝ d n x)) = 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin (d+n)) (Fin (d+n)) ℝ =>
      M.submatrix finSumFinEquiv finSumFinEquiv) h
    rw [schurOmegaPhysical_submatrix] at he
    change Matrix.fromBlocks _ _ _ _ = 0 at he
    have hb := Matrix.fromBlocks_inj.mp (he.trans Matrix.fromBlocks_zero.symm)
    exact ⟨hb.1,hb.2.2.1,hb.2.2.2⟩
  · rintro ⟨hh,hl,ht⟩
    apply (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv finSumFinEquiv).symm.injective
    change (schurOmegaPhysical d n ω η x).submatrix finSumFinEquiv finSumFinEquiv = 0
    rw [schurOmegaPhysical_submatrix]
    change Matrix.fromBlocks _ _ _ _ = 0
    rw [hh,hl,ht]
    simp

/-- A literal step index is free exactly in the head/tail/upper cases below. -/
def SchurOmegaFreeStep {d n : ℕ}
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin n × Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    SchurStepIndex (Fin d) (Fin n) → Prop
  | .inl _ => False
  | .inr (.inl h) => ω (Pi.single h 1) = 0
  | .inr (.inr (.inl t)) => η (Pi.single t 1) = 0
  | .inr (.inr (.inr _)) => True

theorem schurOmegaPhysical_single_eq_zero_iff {d n : ℕ}
    (ω : (Fin d × Fin d → ℝ) →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (η : (Fin n × Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (c : SchurStepIndex (Fin d) (Fin n)) :
    schurOmegaPhysical d n ω η (Pi.single (schurCellEquiv d n c) (1 : ℝ)) = 0 ↔
      SchurOmegaFreeStep ω η c := by
  classical
  rw [schurOmegaPhysical_eq_zero_iff,schurCellCoordinateEquiv_single]
  rcases c with ⟨j,i⟩ | h | t | u
  · constructor
    · intro hc
      have he := congrArg (fun M : Matrix (Fin n) (Fin d) ℝ => M i j) hc.2.1
      change (Pi.single (.inl (j,i)) (1 : ℝ) : SchurStepIndex (Fin d) (Fin n) → ℝ) (.inl (j,i)) = 0 at he
      simp at he
    · exact False.elim
  · have hh : schurHeadInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inl h)) (1 : ℝ)) = Pi.single h 1 := by
      funext p; simp [schurHeadInput,Pi.single_apply]
    have hl : schurLowerInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inl h)) (1 : ℝ)) = 0 := by
      funext i j
      change (Pi.single (.inr (.inl h)) (1 : ℝ) : SchurStepIndex (Fin d) (Fin n) → ℝ) (.inl (j,i)) = 0
      simp
    have ht : schurTailInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inl h)) (1 : ℝ)) = 0 := by
      funext p; simp [schurTailInput]
    simp [SchurOmegaFreeStep,hh,hl,ht]
  · have hh : schurHeadInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inr (.inl t))) (1 : ℝ)) = 0 := by
      funext p; simp [schurHeadInput]
    have hl : schurLowerInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inr (.inl t))) (1 : ℝ)) = 0 := by
      funext i j
      change (Pi.single (.inr (.inr (.inl t))) (1 : ℝ) : SchurStepIndex (Fin d) (Fin n) → ℝ) (.inl (j,i)) = 0
      simp
    have ht : schurTailInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inr (.inl t))) (1 : ℝ)) = Pi.single t 1 := by
      funext p; simp [schurTailInput,Pi.single_apply]
    simp [SchurOmegaFreeStep,hh,hl,ht]
  · have hh : schurHeadInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inr (.inr u))) (1 : ℝ)) = 0 := by
      funext p; simp [schurHeadInput]
    have hl : schurLowerInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inr (.inr u))) (1 : ℝ)) = 0 := by
      funext i j
      change (Pi.single (.inr (.inr (.inr u))) (1 : ℝ) : SchurStepIndex (Fin d) (Fin n) → ℝ) (.inl (j,i)) = 0
      simp
    have ht : schurTailInput (R := ℝ) (ι := Fin d) (κ := Fin n) (Pi.single (.inr (.inr (.inr u))) (1 : ℝ)) = 0 := by
      funext p; simp [schurTailInput]
    simp [SchurOmegaFreeStep,hh,hl,ht]

/-- No lower cell is free; every scalar head and upper cell is free. -/
def ScalarFreeStep (w : List Bool) : SchurStepIndex (Fin 1) (Fin (schurWordSize w)) → Prop
  | .inl _ => False
  | .inr (.inl _) => True
  | .inr (.inr (.inl t)) => t ∉ Finset.univ.image (schurWordAngleCell w)
  | .inr (.inr (.inr _)) => True

def PairFreeStep (w : List Bool) : SchurStepIndex (Fin 2) (Fin (schurWordSize w)) → Prop
  | .inl _ => False
  | .inr (.inl h) => h ≠ (1,1)
  | .inr (.inr (.inl t)) => t ∉ Finset.univ.image (schurWordAngleCell w)
  | .inr (.inr (.inr _)) => True

theorem pairHeadOmega_single_eq_zero_iff (h : Fin 2 × Fin 2) :
    pairHeadOmega (Pi.single h (1 : ℝ)) = 0 ↔ h ≠ (1,1) := by
  have hz (r : ℝ) : pairSkew r = 0 ↔ r = 0 := by
    constructor
    · intro he
      have he' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) he
      simpa [pairSkew] using he'
    · intro he
      subst r
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [pairSkew]
  rw [pairHeadOmega_apply,hz]
  simp [Pi.single_apply,eq_comm]

theorem scalar_not_mem_angleCell_step (w : List Bool)
    (c : SchurStepIndex (Fin 1) (Fin (schurWordSize w))) :
    schurCellEquiv 1 (schurWordSize w) c ∉
      Finset.univ.image (schurWordAngleCell (false::w)) ↔ ScalarFreeStep w c := by
  refine (schurWord_not_mem_angleCell_iff (false::w)
    (schurCellEquiv 1 (schurWordSize w) c)).trans ?_
  refine (schurOmegaPhysical_single_eq_zero_iff
    (0 : (Fin 1 × Fin 1 → ℝ) →ₗ[ℝ] Matrix (Fin 1) (Fin 1) ℝ) (schurWordOmega w) c).trans ?_
  rcases c with c | c | c | c
  · exact Iff.rfl
  · constructor
    · intro _; trivial
    · intro _; rfl
  · exact (schurWord_not_mem_angleCell_iff w c).symm
  · exact Iff.rfl

theorem pair_not_mem_angleCell_step (w : List Bool)
    (c : SchurStepIndex (Fin 2) (Fin (schurWordSize w))) :
    schurCellEquiv 2 (schurWordSize w) c ∉
      Finset.univ.image (schurWordAngleCell (true::w)) ↔ PairFreeStep w c := by
  refine (schurWord_not_mem_angleCell_iff (true::w)
    (schurCellEquiv 2 (schurWordSize w) c)).trans ?_
  refine (schurOmegaPhysical_single_eq_zero_iff pairHeadOmega (schurWordOmega w) c).trans ?_
  rcases c with c | c | c | c
  · exact Iff.rfl
  · exact pairHeadOmega_single_eq_zero_iff c
  · exact (schurWord_not_mem_angleCell_iff w c).symm
  · exact Iff.rfl

abbrev ScalarFreeIndex (w : List Bool) :=
  Fin 1 ⊕ ((Fin (schurWordSize w) × Fin 1) ⊕ SchurWordFreeIndex w)
abbrev PairFreeIndex (w : List Bool) :=
  Fin 3 ⊕ ((Fin (schurWordSize w) × Fin 2) ⊕ SchurWordFreeIndex w)

/-- Slots are a,b,c, in the existing raw COLUMN,ROW convention. -/
def pairFreeHeadCell : Fin 3 → Fin 2 × Fin 2 := ![(0,0),(0,1),(1,0)]

theorem pairFreeHeadCell_injective : Function.Injective pairFreeHeadCell := by decide

def scalarFreeCell (w : List Bool) : ScalarFreeIndex w → SchurWordFreeIndex (false::w)
  | .inl j => ⟨schurCellEquiv 1 (schurWordSize w) (.inr (.inl (j,0))),by
      exact (scalar_not_mem_angleCell_step w _).mpr trivial⟩
  | .inr (.inl u) => ⟨schurCellEquiv 1 (schurWordSize w) (.inr (.inr (.inr u))),by
      exact (scalar_not_mem_angleCell_step w _).mpr trivial⟩
  | .inr (.inr t) => ⟨schurCellEquiv 1 (schurWordSize w) (.inr (.inr (.inl t.val))),by
      exact (scalar_not_mem_angleCell_step w _).mpr t.property⟩

def pairFreeCell (w : List Bool) : PairFreeIndex w → SchurWordFreeIndex (true::w)
  | .inl j => ⟨schurCellEquiv 2 (schurWordSize w) (.inr (.inl (pairFreeHeadCell j))),by
      exact (pair_not_mem_angleCell_step w _).mpr (by
        change pairFreeHeadCell j ≠ (1,1)
        fin_cases j <;> decide)⟩
  | .inr (.inl u) => ⟨schurCellEquiv 2 (schurWordSize w) (.inr (.inr (.inr u))),by
      exact (pair_not_mem_angleCell_step w _).mpr trivial⟩
  | .inr (.inr t) => ⟨schurCellEquiv 2 (schurWordSize w) (.inr (.inr (.inl t.val))),by
      exact (pair_not_mem_angleCell_step w _).mpr t.property⟩

theorem scalarFreeCell_bijective (w : List Bool) : Function.Bijective (scalarFreeCell w) := by
  constructor
  · intro i j he
    rcases i with i | i | i <;> rcases j with j | j | j
    all_goals
      have h := congrArg Subtype.val he
      dsimp only [scalarFreeCell] at h
      have h' := (schurCellEquiv 1 (schurWordSize w)).injective h
      simp_all [Subtype.ext_iff]
  · rintro ⟨c,hc⟩
    obtain ⟨p,rfl⟩ := (schurCellEquiv 1 (schurWordSize w)).surjective c
    have hc := (scalar_not_mem_angleCell_step w p).mp hc
    rcases p with p | ⟨j,i⟩ | t | u
    · exact False.elim hc
    · fin_cases j; fin_cases i
      exact ⟨.inl 0,rfl⟩
    · exact ⟨.inr (.inr ⟨t,hc⟩),rfl⟩
    · exact ⟨.inr (.inl u),rfl⟩

theorem pairFreeCell_bijective (w : List Bool) : Function.Bijective (pairFreeCell w) := by
  constructor
  · intro i j he
    rcases i with i | i | i <;> rcases j with j | j | j
    all_goals
      have h := congrArg Subtype.val he
      dsimp only [pairFreeCell] at h
      have h' := (schurCellEquiv 2 (schurWordSize w)).injective h
    · exact congrArg Sum.inl (pairFreeHeadCell_injective (by simpa using h'))
    all_goals simp_all [Subtype.ext_iff]
  · rintro ⟨c,hc⟩
    obtain ⟨p,rfl⟩ := (schurCellEquiv 2 (schurWordSize w)).surjective c
    have hc := (pair_not_mem_angleCell_step w p).mp hc
    rcases p with p | ⟨j,i⟩ | t | u
    · exact False.elim hc
    · fin_cases j <;> fin_cases i
      · exact ⟨.inl 0,rfl⟩
      · exact ⟨.inl 1,rfl⟩
      · exact ⟨.inl 2,rfl⟩
      · exact False.elim (hc rfl)
    · exact ⟨.inr (.inr ⟨t,hc⟩),rfl⟩
    · exact ⟨.inr (.inl u),rfl⟩

/-- Actual finite index permutations, without rescaling or an abstract kernel basis. -/
def scalarFreeIndexEquiv (w : List Bool) : ScalarFreeIndex w ≃ SchurWordFreeIndex (false::w) :=
  Equiv.ofBijective (scalarFreeCell w) (scalarFreeCell_bijective w)
def pairFreeIndexEquiv (w : List Bool) : PairFreeIndex w ≃ SchurWordFreeIndex (true::w) :=
  Equiv.ofBijective (pairFreeCell w) (pairFreeCell_bijective w)

end Paper.Spectral
