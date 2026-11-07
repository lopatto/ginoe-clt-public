/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFreeCoordinateIndex
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix
namespace Paper.Spectral

/-- Pure reindexing followed by two ordinary function-on-sum/product maps. -/
def literalTripleRead {H U T F : Type*} (e : H ⊕ (U ⊕ T) ≃ F) (y : F → ℝ) :
    (H → ℝ) × ((U → ℝ) × (T → ℝ)) :=
  (fun h => y (e (.inl h)), fun u => y (e (.inr (.inl u))),
    fun t => y (e (.inr (.inr t))))

theorem volume_preserving_literalTripleRead {H U T F : Type*}
    [Fintype H] [Fintype U] [Fintype T] [Fintype F]
    (e : H ⊕ (U ⊕ T) ≃ F) :
    MeasurePreserving (literalTripleRead e) volume volume := by
  let r := MeasurableEquiv.piCongrLeft (fun _ : H ⊕ (U ⊕ T) => ℝ) e.symm
  let s := MeasurableEquiv.sumPiEquivProdPi (fun _ : H ⊕ (U ⊕ T) => ℝ)
  let t := MeasurableEquiv.sumPiEquivProdPi (fun _ : U ⊕ T => ℝ)
  have hr := volume_measurePreserving_piCongrLeft (fun _ : H ⊕ (U ⊕ T) => ℝ) e.symm
  have hs := volume_measurePreserving_sumPiEquivProdPi (fun _ : H ⊕ (U ⊕ T) => ℝ)
  have ht := volume_measurePreserving_sumPiEquivProdPi (fun _ : U ⊕ T => ℝ)
  have hp := (MeasurePreserving.id (volume : Measure (H → ℝ))).prod ht
  have he : (Prod.map id t) ∘ s ∘ r = literalTripleRead e := by
    have her (y : F → ℝ) (i : H ⊕ (U ⊕ T)) : r y i = y (e i) := by
      have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
        (β := fun _ : H ⊕ (U ⊕ T) => ℝ) y (e i)
      simpa only [Equiv.symm_apply_apply] using h
    funext y
    apply Prod.ext
    · funext h
      exact her y (.inl h)
    · apply Prod.ext
      · funext u
        exact her y (.inr (.inl u))
      · funext v
        exact her y (.inr (.inr v))
  simpa only [← he] using! hp.comp (hs.comp hr)

def scalarFreeSplit (w : List Bool) := literalTripleRead (scalarFreeIndexEquiv w)
def pairFreeSplit (w : List Bool) := literalTripleRead (pairFreeIndexEquiv w)

theorem volume_preserving_scalarFreeSplit (w : List Bool) :
    MeasurePreserving (scalarFreeSplit w) volume volume :=
  volume_preserving_literalTripleRead (scalarFreeIndexEquiv w)
theorem volume_preserving_pairFreeSplit (w : List Bool) :
    MeasurePreserving (pairFreeSplit w) volume volume :=
  volume_preserving_literalTripleRead (pairFreeIndexEquiv w)

/-- Publish membership in a direction useful for actual zero-filled cell evaluation. -/
theorem scalar_mem_angleCell_step (w : List Bool)
    (c : SchurStepIndex (Fin 1) (Fin (schurWordSize w))) :
    schurCellEquiv 1 (schurWordSize w) c ∈
      Finset.univ.image (schurWordAngleCell (false::w)) ↔ ¬ ScalarFreeStep w c := by
  simpa only [not_not] using not_congr (scalar_not_mem_angleCell_step w c)
theorem pair_mem_angleCell_step (w : List Bool)
    (c : SchurStepIndex (Fin 2) (Fin (schurWordSize w))) :
    schurCellEquiv 2 (schurWordSize w) c ∈
      Finset.univ.image (schurWordAngleCell (true::w)) ↔ ¬ PairFreeStep w c := by
  simpa only [not_not] using not_congr (pair_not_mem_angleCell_step w c)

@[simp] theorem schurStepFreeCells_apply_cell {d n : ℕ}
    (h : Fin d × Fin d → ℝ) (t : Fin n × Fin n → ℝ)
    (U : Matrix (Fin d) (Fin n) ℝ) (c : SchurStepIndex (Fin d) (Fin n)) :
    schurStepFreeCells h t U (schurCellEquiv d n c) = schurStepFreeCoordinates h t U c :=
  congrFun (schurStepFreeCells_coordinates h t U) c

theorem schurWordFreeCells_apply_index (w : List Bool)
    (y : SchurWordFreeIndex w → ℝ) (c : SchurWordFreeIndex w) :
    schurWordFreeCells w y c.val = y c := by
  simp only [schurWordFreeCells,dite_eq_right c.property]

theorem schurWordFreeCells_apply_angle (w : List Bool)
    (y : SchurWordFreeIndex w → ℝ)
    (c : Fin (schurWordSize w) × Fin (schurWordSize w))
    (hc : c ∈ Finset.univ.image (schurWordAngleCell w)) :
    schurWordFreeCells w y c = 0 := by
  simp only [schurWordFreeCells,dite_eq_left hc]

/-- The free permutation reassembles EXACTLY the original scalar constructor.
U is stored in ordinary COLUMN,ROW cells (j,i), so the matrix reads u(j,i). -/
theorem scalarFreeCells_eq_step (w : List Bool) (y : SchurWordFreeIndex (false::w) → ℝ) :
    schurWordFreeCells (false::w) y =
      schurStepFreeCells (fun _ : Fin 1 × Fin 1 => (scalarFreeSplit w y).1 0)
        (schurWordFreeCells w (scalarFreeSplit w y).2.2)
        (fun i j => (scalarFreeSplit w y).2.1 (j,i)) := by
  classical
  funext c
  obtain ⟨c,rfl⟩ := (schurCellEquiv 1 (schurWordSize w)).surjective c
  refine Eq.trans ?_ (schurStepFreeCells_apply_cell _ _ _ c).symm
  rcases c with c | ⟨j,i⟩ | t | u
  · have hc : schurCellEquiv 1 (schurWordSize w) (.inl c) ∈
        Finset.univ.image (schurWordAngleCell (false::w)) := by
      by_contra hn
      exact (scalar_not_mem_angleCell_step w (.inl c)).mp hn
    exact schurWordFreeCells_apply_angle (false::w) y _ hc
  · fin_cases j; fin_cases i
    exact schurWordFreeCells_apply_index (false::w) y (scalarFreeCell w (.inl 0))
  · by_cases ht : t ∈ Finset.univ.image (schurWordAngleCell w)
    · have hc : schurCellEquiv 1 (schurWordSize w) (.inr (.inr (.inl t))) ∈
          Finset.univ.image (schurWordAngleCell (false::w)) := by
        by_contra hn
        exact ((scalar_not_mem_angleCell_step w _).mp hn) ht
      exact (schurWordFreeCells_apply_angle (false::w) y _ hc).trans
        (schurWordFreeCells_apply_angle w (scalarFreeSplit w y).2.2 t ht).symm
    · let c : SchurWordFreeIndex w := ⟨t,ht⟩
      change schurWordFreeCells (false::w) y (scalarFreeCell w (.inr (.inr c))).val =
        schurWordFreeCells w (scalarFreeSplit w y).2.2 c.val
      rw [schurWordFreeCells_apply_index,schurWordFreeCells_apply_index]
      rfl
  · exact schurWordFreeCells_apply_index (false::w) y (scalarFreeCell w (.inr (.inl u)))

theorem pairFreeCells_eq_step (w : List Bool) (y : SchurWordFreeIndex (true::w) → ℝ) :
    schurWordFreeCells (true::w) y =
      schurStepFreeCells
        (pairFreeInput ((pairFreeSplit w y).1 0) ((pairFreeSplit w y).1 1) ((pairFreeSplit w y).1 2))
        (schurWordFreeCells w (pairFreeSplit w y).2.2)
        (fun i j => (pairFreeSplit w y).2.1 (j,i)) := by
  classical
  funext c
  obtain ⟨c,rfl⟩ := (schurCellEquiv 2 (schurWordSize w)).surjective c
  refine Eq.trans ?_ (schurStepFreeCells_apply_cell _ _ _ c).symm
  rcases c with c | ⟨j,i⟩ | t | u
  · have hc : schurCellEquiv 2 (schurWordSize w) (.inl c) ∈
        Finset.univ.image (schurWordAngleCell (true::w)) := by
      by_contra hn
      exact (pair_not_mem_angleCell_step w (.inl c)).mp hn
    exact schurWordFreeCells_apply_angle (true::w) y _ hc
  · fin_cases j <;> fin_cases i
    · exact schurWordFreeCells_apply_index (true::w) y (pairFreeCell w (.inl 0))
    · exact schurWordFreeCells_apply_index (true::w) y (pairFreeCell w (.inl 1))
    · exact schurWordFreeCells_apply_index (true::w) y (pairFreeCell w (.inl 2))
    · have hc : schurCellEquiv 2 (schurWordSize w) (.inr (.inl (1,1))) ∈
          Finset.univ.image (schurWordAngleCell (true::w)) := by
        by_contra hn
        exact ((pair_not_mem_angleCell_step w _).mp hn) rfl
      exact schurWordFreeCells_apply_angle (true::w) y _ hc
  · by_cases ht : t ∈ Finset.univ.image (schurWordAngleCell w)
    · have hc : schurCellEquiv 2 (schurWordSize w) (.inr (.inr (.inl t))) ∈
          Finset.univ.image (schurWordAngleCell (true::w)) := by
        by_contra hn
        exact ((pair_not_mem_angleCell_step w _).mp hn) ht
      exact (schurWordFreeCells_apply_angle (true::w) y _ hc).trans
        (schurWordFreeCells_apply_angle w (pairFreeSplit w y).2.2 t ht).symm
    · let c : SchurWordFreeIndex w := ⟨t,ht⟩
      change schurWordFreeCells (true::w) y (pairFreeCell w (.inr (.inr c))).val =
        schurWordFreeCells w (pairFreeSplit w y).2.2 c.val
      rw [schurWordFreeCells_apply_index,schurWordFreeCells_apply_index]
      rfl
  · exact schurWordFreeCells_apply_index (true::w) y (pairFreeCell w (.inr (.inl u)))

/-- Actual K, not a surrogate matrix, in the new ordinary product coordinates. -/
theorem scalarFreeParameter_eq (w : List Bool) (y : SchurWordFreeIndex (false::w) → ℝ) :
    schurWordParameter (false::w) (schurWordFreeCells (false::w) y) =
      upperBlockMatrix (scalarBlock ((scalarFreeSplit w y).1 0))
        (fun i j => (scalarFreeSplit w y).2.1 (j,i))
        (schurWordParameter w (schurWordFreeCells w (scalarFreeSplit w y).2.2)) := by
  rw [scalarFreeCells_eq_step]
  exact schurParameterPhysical_free scalarHeadParameter (schurWordParameter w) _ _ _

theorem pairFreeParameter_eq (w : List Bool) (y : SchurWordFreeIndex (true::w) → ℝ) :
    schurWordParameter (true::w) (schurWordFreeCells (true::w) y) =
      upperBlockMatrix
        (schurBlock ((pairFreeSplit w y).1 0) ((pairFreeSplit w y).1 1) ((pairFreeSplit w y).1 2))
        (fun i j => (pairFreeSplit w y).2.1 (j,i))
        (schurWordParameter w (schurWordFreeCells w (pairFreeSplit w y).2.2)) := by
  rw [pairFreeCells_eq_step]
  exact schurParameterPhysical_free pairHeadParameter (schurWordParameter w) _ _ _

end Paper.Spectral
