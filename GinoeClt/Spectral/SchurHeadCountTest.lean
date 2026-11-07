/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFullRootsFromHeads
public import GinoeClt.Spectral.SchurOrderingIntegral
public import GinoeClt.Spectral.GaussianSchurPartition
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Classical Matrix
namespace Paper.Spectral

theorem isOpen_scaledCountDomain (A : Set ℂ) (hA : IsOpen A) (n : ℕ) :
    IsOpen (scaledCountDomain n A) := by
  have hs : (Real.sqrt (n+1 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  exact (Homeomorph.mulLeft₀ (Real.sqrt (n+1 : ℝ) : ℂ) hs).isOpenMap A hA

/-- One genuine generating factor per representative, with multiplicity. -/
def schurHeadCountProduct (B : Set ℂ) (t : ℝ≥0) {k : ℕ} (h : Fin k → ℂ) : ℝ≥0∞ :=
  ∏ i, if h i ∈ B then 1+(t : ℝ≥0∞) else 1

theorem measurable_schurHeadCountProduct (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k : ℕ) : Measurable (schurHeadCountProduct B t (k := k)) := by
  unfold schurHeadCountProduct
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.ite (hB.preimage (measurable_pi_apply i)) measurable_const

theorem schurHeadCountProduct_actual (B : Set ℂ) (t : ℝ≥0)
    (w : List Bool) (p : SchurWordCells w) :
    schurHeadCountProduct B t (schurWordHeadRootAt w p) =
      ((schurWordHeadRoots w p).map
        (fun z => if z ∈ B then 1+(t : ℝ≥0∞) else 1)).prod := by
  rw [schurWordHeadRoots_eq_ofFn,List.map_ofFn,List.prod_ofFn]
  rfl

/-- Original list ordering and weak monotonicity are equivalent, retaining ties. -/
theorem schurWordOrdered_iff_headVector_mem (w : List Bool) (p : SchurWordCells w) :
    SchurWordOrdered w p ↔
      schurWordHeadRootAt w p ∈ orderingChamber w.length schurRootKey := by
  simp only [SchurWordOrdered,schurWordHeadRoots_eq_ofFn,List.pairwise_ofFn]
  constructor
  · intro h i j hij
    rcases lt_or_eq_of_le hij with hlt | heq
    · exact h hlt
    · subst j
      exact le_rfl
  · intro h i j hij
    exact h hij.le

theorem measurableSet_schurHeadOrdering (k : ℕ) :
    MeasurableSet (orderingChamber k schurRootKey) :=
  measurableSet_orderingChamber k schurRootKey
    (measurableSet_schurRootKey_le Prod.fst Prod.snd continuous_fst continuous_snd)

/-- The actual count-weighted full Vandermonde test. Ordering is retained as
the original weak representative chamber, rather than silently discarded. -/
def schurHeadCountTest (B : Set ℂ) (t : ℝ≥0) (w : List Bool)
    (h : Fin w.length → ℂ) : ℝ≥0∞ :=
  (orderingChamber w.length schurRootKey).indicator
    (fun v => ENNReal.ofReal (schurHeadVandermondeNorm w v) *
      schurHeadCountProduct B t v) h

theorem measurable_schurHeadCountTest (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (w : List Bool) : Measurable (schurHeadCountTest B t w) :=
  ((continuous_schurHeadVandermondeNorm w).measurable.ennreal_ofReal.mul
    (measurable_schurHeadCountProduct B hB t w.length)).indicator
      (measurableSet_schurHeadOrdering w.length)

theorem schurHeadCountTest_actual (B : Set ℂ) (t : ℝ≥0)
    (w : List Bool) (p : SchurWordCells w) :
    schurHeadCountTest B t w (schurWordHeadRootAt w p) =
      if SchurWordOrdered w p then
        ENNReal.ofReal ‖(Matrix.vandermonde (schurWordFullRootAt w p)).det‖ *
          ((schurWordHeadRoots w p).map
            (fun z => if z ∈ B then 1+(t : ℝ≥0∞) else 1)).prod
      else 0 := by
  unfold schurHeadCountTest
  rw [Set.indicator_apply,← schurWordOrdered_iff_headVector_mem,
    schurHeadVandermondeNorm_actual,schurHeadCountProduct_actual]

theorem schurHeadCountTest_eq_zero_of_not_injective (B : Set ℂ) (t : ℝ≥0)
    (w : List Bool) (h : Fin w.length → ℂ) (hh : ¬ Function.Injective h) :
    schurHeadCountTest B t w h = 0 := by
  unfold schurHeadCountTest
  by_cases ho : h ∈ orderingChamber w.length schurRootKey
  · rw [Set.indicator_of_mem ho,
      schurHeadVandermondeNorm_eq_zero_of_not_injective w h hh,ENNReal.ofReal_zero,zero_mul]
  · exact Set.indicator_of_notMem ho _

end Paper.Spectral
