/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurJacobianVandermonde
public import GinoeClt.Spectral.SchurAngularFactorization
public import Mathlib.Data.List.FinRange
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix
namespace Paper.Spectral

/-- Regularity forces injectivity of the genuine FULL family; no cross-root
factor is cancelled, and no pair-ratio positivity is needed. -/
theorem schurWordFullRootAt_injective_of_regular (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0) :
    Function.Injective (schurWordFullRootAt w p) := by
  have hprod : ‖(Matrix.vandermonde (schurWordFullRootAt w p)).det‖ *
      schurWordPairRatio w p ≠ 0 := by
    rw [← abs_det_schurWordDifferential_eq_vandermonde w p hp]
    exact abs_ne_zero.mpr hd
  have hnorm := (mul_ne_zero_iff.mp hprod).1
  have hdet : (Matrix.vandermonde (schurWordFullRootAt w p)).det ≠ 0 := by
    intro h
    exact hnorm (by rw [h,norm_zero])
  exact Matrix.det_vandermonde_ne_zero_iff.mp hdet

/-- The actual multiplicity multiset is Nodup; it is never replaced by its support. -/
theorem schurWordRoots_nodup_of_regular (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0) :
    (schurWordRoots w p).Nodup := by
  rw [← schurWordFullRootAt_multiset]
  exact Multiset.coe_nodup.mpr (List.nodup_ofFn_ofInjective
    (schurWordFullRootAt_injective_of_regular w p hp hd))

/-- Genuine real characteristic-polynomial separability of every positive regular
parameter matrix, via its full complex multiplicity roots and native splitting. -/
theorem schurWordParameter_charpoly_separable_of_regular (w : List Bool)
    (p : SchurWordCells w) (hp : SchurWordPositive w p)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0) :
    (schurWordParameter w p).charpoly.Separable := by
  have hr : ((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots.Nodup := by
    rw [schurWordParameter_roots w p hp]
    exact schurWordRoots_nodup_of_regular w p hp hd
  have hs : ((schurWordParameter w p).charpoly.map Complex.ofRealHom).Separable :=
    (Polynomial.nodup_roots_iff_of_splits (mapped_charpoly_ne_zero _)
      (IsAlgClosed.splits _)).mp hr
  exact (Polynomial.separable_map Complex.ofRealHom).mp hs

/-- Drop only the regular/simple masks already present in the actual source.
This is POINTWISE, for completely arbitrary ENNReal weights including infinity.
At a nonregular input ofReal|det|=0 and native 0*infinity=0. -/
theorem schurWordFreeSource_indicator_weight (w : List Bool)
    (g : SchurWordCells w → ℝ≥0∞) (y : SchurWordFreeIndex w → ℝ) :
    (schurWordFreeSource w).indicator
      (fun v => ENNReal.ofReal |LinearMap.det
        (schurWordDifferential w (schurWordFreeCells w v))| *
        g (Matrix.vec (schurWordParameter w (schurWordFreeCells w v)))) y =
    {v | SchurWordPositive w (schurWordFreeCells w v) ∧
      SchurWordOrdered w (schurWordFreeCells w v)}.indicator
      (fun v => ENNReal.ofReal |LinearMap.det
        (schurWordDifferential w (schurWordFreeCells w v))| *
        g (Matrix.vec (schurWordParameter w (schurWordFreeCells w v)))) y := by
  classical
  let p := schurWordFreeCells w y
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, schurWordFreeSource]
  change (if SchurWordPositive w p ∧ SchurWordOrdered w p ∧
      LinearMap.det (schurWordDifferential w p) ≠ 0 ∧
        (schurWordParameter w p).charpoly.Separable then
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w p)| *
        g (Matrix.vec (schurWordParameter w p)) else 0) =
    (if SchurWordPositive w p ∧ SchurWordOrdered w p then
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w p)| *
        g (Matrix.vec (schurWordParameter w p)) else 0)
  by_cases hp : SchurWordPositive w p
  · by_cases ho : SchurWordOrdered w p
    · by_cases hd : LinearMap.det (schurWordDifferential w p) ≠ 0
      · have hs := schurWordParameter_charpoly_separable_of_regular w p hp hd
        rw [ite_eq_left ⟨hp,ho,hd,hs⟩,ite_eq_left ⟨hp,ho⟩]
      · have hz : LinearMap.det (schurWordDifferential w p) = 0 := not_ne_iff.mp hd
        simp [hp,ho,hz]
    · simp [hp,ho]
  · simp [hp]

/-- The weighted free integral is EXACTLY over original Pos and Ordered alone.
Measurability of g is unnecessary for this pointwise-mask argument. -/
theorem lintegral_schurWordFreeSource_eq_positive_ordered (w : List Bool)
    (g : SchurWordCells w → ℝ≥0∞) :
    (∫⁻ y in schurWordFreeSource w,
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w y))| *
        g (Matrix.vec (schurWordParameter w (schurWordFreeCells w y)))) =
    ∫⁻ y in {v | SchurWordPositive w (schurWordFreeCells w v) ∧
      SchurWordOrdered w (schurWordFreeCells w v)},
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w y))| *
        g (Matrix.vec (schurWordParameter w (schurWordFreeCells w y))) := by
  have hpo : MeasurableSet {v : SchurWordFreeIndex w → ℝ |
      SchurWordPositive w (schurWordFreeCells w v) ∧
      SchurWordOrdered w (schurWordFreeCells w v)} :=
    ((measurableSet_schurWordPositive w).preimage
      (continuous_schurWordFreeCells w).measurable).inter
      ((measurableSet_schurWordOrdered w).preimage
        (continuous_schurWordFreeCells w).measurable)
  rw [← lintegral_indicator (measurableSet_schurWordFreeSource w),
    ← lintegral_indicator hpo]
  exact lintegral_congr_ae
    (Filter.Eventually.of_forall (schurWordFreeSource_indicator_weight w g))

end Paper.Spectral
