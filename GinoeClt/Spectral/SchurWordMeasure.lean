/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWordJacobian
public import GinoeClt.MeasureTheory.FiniteFiber

/-! Genuine critical-image nullity and regular-domain integration for the full word map. -/
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise ENNReal

namespace Paper.Spectral

/-- The physical word commutator determinant is an ordinary continuous polynomial in the free entries. -/
theorem continuous_det_schurWordDifferential (w : List Bool) :
    Continuous (fun x : SchurWordCells w => LinearMap.det (schurWordDifferential w x)) := by
  have hK : Continuous (schurWordParameter w) := (schurWordParameter w).toContinuousLinearMap.continuous
  have hM : Continuous (fun x : SchurWordCells w => LinearMap.toMatrix' (schurWordDifferential w x)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun x : SchurWordCells w =>
      (schurWordParameter w (Pi.single j 1) +
        schurWordOmega w (Pi.single j 1) * schurWordParameter w x -
          schurWordParameter w x * schurWordOmega w (Pi.single j 1)) i.2 i.1)
    fun_prop
  simpa only [LinearMap.det_toMatrix'] using hM.matrix_det

/-- The actual regular locus, with no spectral or pair-gap hypothesis hidden in it. -/
def schurWordRegularSet (w : List Bool) : Set (SchurWordCells w) :=
  {x | LinearMap.det (schurWordDifferential w x) ≠ 0}

theorem isOpen_schurWordRegularSet (w : List Bool) : IsOpen (schurWordRegularSet w) :=
  isOpen_compl_singleton.preimage (continuous_det_schurWordDifferential w)

theorem schurWordChartCellsDerivative_det_ne_zero (w : List Bool)
    (x : SchurWordCells w) (hx : x ∈ schurWordRegularSet w) :
    LinearMap.det (schurWordChartCellsDerivative w x).toLinearMap ≠ 0 := by
  rw [det_schurWordChartCellsDerivative]
  exact mul_ne_zero hx (det_cayleyAngularEquiv_ne_zero _ _)

/-- The critical IMAGE is null in the full N-squared-dimensional physical space. -/
theorem volume_schurWordChartCells_critical_image (w : List Bool) :
    volume (schurWordChartCells w ''
      {x : SchurWordCells w | LinearMap.det (schurWordDifferential w x) = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (f' := schurWordChartCellsDerivative w) volume
  · intro x _
    exact (hasStrictFDerivAt_schurWordChartCells w x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    change LinearMap.det (schurWordChartCellsDerivative w x).toLinearMap = 0
    rw [det_schurWordChartCellsDerivative, hx, zero_mul]

/-- Every measurable subset of the actual regular locus admits Borel injectivity pieces. -/
theorem exists_schurWord_injective_partition (w : List Bool)
    {s : Set (SchurWordCells w)} (hs : MeasurableSet s)
    (hreg : s ⊆ schurWordRegularSet w) :
    ∃ P : ℕ → Set (SchurWordCells w), (∀ n, MeasurableSet (P n)) ∧
      (Pairwise fun i j => Disjoint (P i) (P j)) ∧
        (⋃ n, P n) = s ∧ ∀ n, InjOn (schurWordChartCells w) (P n) := by
  apply Paper.MeasureTheory.exists_measurable_injective_partition_of_strict_derivative
    (schurWordChartCells w) (schurWordChartCellsDerivative w) hs
  · intro x _
    exact hasStrictFDerivAt_schurWordChartCells w x
  · intro x hx
    exact schurWordChartCellsDerivative_det_ne_zero w x (hreg hx)

/-- Change of variables with LITERAL actual fibers; no constant Schur multiplicity is assumed. -/
theorem lintegral_schurWord_actual_fibers (w : List Bool)
    {s : Set (SchurWordCells w)} (hs : MeasurableSet s)
    (hreg : s ⊆ schurWordRegularSet w)
    (g : SchurWordCells w → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in s,
      ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)|) * g (schurWordChartCells w x)) =
      ∫⁻ y, (({x | x ∈ s ∧ schurWordChartCells w x = y}).encard : ℝ≥0∞) * g y := by
  obtain ⟨P, hP, hd, hU, hi⟩ := exists_schurWord_injective_partition w hs hreg
  have h := Paper.MeasureTheory.lintegral_abs_det_mul_eq_lintegral_fiber_encard volume
    (schurWordChartCells w) (schurWordChartCellsDerivative w) P hP hd hi
    (fun x _ => (hasStrictFDerivAt_schurWordChartCells w x).hasFDerivAt.hasFDerivWithinAt) g hg
  rw [hU] at h
  simpa only [abs_det_schurWordChartCellsDerivative] using h

end Paper.Spectral
