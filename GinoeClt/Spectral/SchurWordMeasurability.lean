/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasRepresentation
public import Mathlib.Data.List.OfFn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace Paper.Spectral

/-- The literal head-cell reader is continuous in the original raw coordinates. -/
theorem continuous_schur_head_cell (d m : ℕ) (j : Fin d × Fin d) :
    Continuous (fun p : Fin (d+m) × Fin (d+m) → ℝ ↦
      schurHeadInput (schurCellCoordinateEquiv ℝ d m p) j) := by
  change Continuous (fun p ↦ schurCellCoordinateEquiv ℝ d m p (.inr (.inl j)))
  exact (continuous_apply _).comp
    (schurCellCoordinateEquiv ℝ d m).toLinearMap.toContinuousLinearMap.continuous

theorem continuous_schur_tail_cells (d m : ℕ) :
    Continuous (fun p : Fin (d+m) × Fin (d+m) → ℝ ↦
      schurTailInput (schurCellCoordinateEquiv ℝ d m p)) :=
  (schurTailInput (R := ℝ) (ι := Fin d) (κ := Fin m)).toContinuousLinearMap.continuous.comp
    (schurCellCoordinateEquiv ℝ d m).toLinearMap.toContinuousLinearMap.continuous

/-- Fixed Fin indexing of the EXISTING head-root list, with no reordering. -/
def schurWordHeadRootAt : (w : List Bool) → SchurWordCells w → Fin w.length → ℂ
  | [], _ => Fin.elim0
  | false::w, p =>
      Fin.cons ((schurHeadInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p) (0,0) : ℝ) : ℂ)
        (schurWordHeadRootAt w (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p)))
  | true::w, p =>
      let h := schurHeadInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p)
      Fin.cons (schurRoot (h (0,0)) (h (0,1)) (h (1,0)))
        (schurWordHeadRootAt w (schurTailInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p)))

theorem schurWordHeadRoots_eq_ofFn (w : List Bool) :
    ∀ p : SchurWordCells w, schurWordHeadRoots w p = List.ofFn (schurWordHeadRootAt w p) := by
  induction w with
  | nil => intro p; simp [schurWordHeadRoots]
  | cons tag w ih =>
    cases tag <;> intro p <;>
      simp only [schurWordHeadRoots, schurWordHeadRootAt, List.ofFn_succ,
        Fin.cons_zero, Fin.cons_succ, ih]

theorem continuous_schurWordHeadRootAt (w : List Bool) :
    ∀ i : Fin w.length, Continuous (fun p : SchurWordCells w ↦ schurWordHeadRootAt w p i) := by
  induction w with
  | nil => intro i; exact Fin.elim0 i
  | cons tag w ih =>
    cases tag <;> intro i
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [schurWordHeadRootAt, Fin.cons_zero, Function.comp_def] using!
          Complex.continuous_ofReal.comp (continuous_schur_head_cell 1 (schurWordSize w) (0,0))
      · simpa only [schurWordHeadRootAt, Fin.cons_succ, Function.comp_def] using!
          (ih j).comp (continuous_schur_tail_cells 1 (schurWordSize w))
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · have h00 := continuous_schur_head_cell 2 (schurWordSize w) (0,0)
        have h01 := continuous_schur_head_cell 2 (schurWordSize w) (0,1)
        have h10 := continuous_schur_head_cell 2 (schurWordSize w) (1,0)
        have hc : Continuous (fun p : SchurWordCells (true::w) ↦
            schurRoot (schurHeadInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p) (0,0))
              (schurHeadInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p) (0,1))
              (schurHeadInput (schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p) (1,0))) := by
          have he (a b c : ℝ) : schurRoot a b c =
              (a : ℂ) + (Real.sqrt (b*c) : ℂ) * Complex.I := by
            apply Complex.ext <;> simp [schurRoot]
          simp_rw [he]
          simpa only [] using!
            (Complex.continuous_ofReal.comp h00).add
              ((Complex.continuous_ofReal.comp
                (Real.continuous_sqrt.comp (h01.mul h10))).mul continuous_const)
        simpa only [schurWordHeadRootAt, Fin.cons_zero] using hc
      · simpa only [schurWordHeadRootAt, Fin.cons_succ, Function.comp_def] using!
          (ih j).comp (continuous_schur_tail_cells 2 (schurWordSize w))

/-- Lexicographic order is a BOREL relation, even where imaginary coordinates tie. -/
theorem measurableSet_schurRootKey_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | schurRootKey (f x) ≤ schurRootKey (g x)} := by
  simp_rw [schurRootKey_le_iff]
  exact (measurableSet_lt (Complex.continuous_im.comp hf).measurable
    (Complex.continuous_im.comp hg).measurable).union
      ((measurableSet_eq_fun (Complex.continuous_im.comp hf).measurable
        (Complex.continuous_im.comp hg).measurable).inter
          (measurableSet_le (Complex.continuous_re.comp hf).measurable
            (Complex.continuous_re.comp hg).measurable))

theorem measurableSet_schurWordPositive (w : List Bool) :
    MeasurableSet {p : SchurWordCells w | SchurWordPositive w p} := by
  induction w with
  | nil => simpa only [SchurWordPositive, Set.ofPred_true] using MeasurableSet.univ
  | cons tag w ih =>
    cases tag
    · simpa only [SchurWordPositive] using!
        ih.preimage (continuous_schur_tail_cells 1 (schurWordSize w)).measurable
    · have h01 := (continuous_schur_head_cell 2 (schurWordSize w) (0,1)).measurable
      have h10 := (continuous_schur_head_cell 2 (schurWordSize w) (1,0)).measurable
      have ht := ih.preimage (continuous_schur_tail_cells 2 (schurWordSize w)).measurable
      simpa only [SchurWordPositive] using!
        (measurableSet_lt (f := fun _ ↦ (0 : ℝ)) measurable_const h10).inter ((measurableSet_le h10 h01).inter ht)

theorem measurableSet_schurWordOrdered (w : List Bool) :
    MeasurableSet {p : SchurWordCells w | SchurWordOrdered w p} := by
  have he : {p : SchurWordCells w | SchurWordOrdered w p} =
      ⋂ i : Fin w.length, ⋂ j : Fin w.length, ⋂ (_h : i < j),
        {p | schurRootKey (schurWordHeadRootAt w p i) ≤ schurRootKey (schurWordHeadRootAt w p j)} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, SchurWordOrdered,
      schurWordHeadRoots_eq_ofFn, List.pairwise_ofFn]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hij
  exact measurableSet_schurRootKey_le _ _
    (continuous_schurWordHeadRootAt w i) (continuous_schurWordHeadRootAt w j)

/-- Per-chart actual source required by finite-family COV, with ORIGINAL definitions. -/
theorem measurableSet_schurAtlasSource (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) : MeasurableSet {p : SchurWordCells w | schurAtlasSource w centers (i,p)} := by
  have ha := (measurableSet_boundedAngularPiece centers i).preimage
    (schurWordAngleMap w).toContinuousLinearMap.continuous.measurable
  simpa only [schurAtlasSource, schurWordRegularSet] using!
    ha.inter ((measurableSet_schurWordPositive w).inter
      ((measurableSet_schurWordOrdered w).inter (isOpen_schurWordRegularSet w).measurableSet))

end Paper.Spectral
