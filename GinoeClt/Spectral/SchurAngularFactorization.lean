/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasIntegration
public import GinoeClt.Spectral.SchurCoordinateVolume
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Matrix
namespace Paper.Spectral

/-- The genuine remaining raw-cell domain, with all physical source conditions.
No angular condition or extra regularity/spectral assumption is implicit. -/
def schurWordFreeSource (w : List Bool) : Set (SchurWordFreeIndex w → ℝ) :=
  {y | SchurWordPositive w (schurWordFreeCells w y) ∧
    SchurWordOrdered w (schurWordFreeCells w y) ∧
    LinearMap.det (schurWordDifferential w (schurWordFreeCells w y)) ≠ 0 ∧
    (schurWordParameter w (schurWordFreeCells w y)).charpoly.Separable}

theorem continuous_schurWordFreeCells (w : List Bool) :
    Continuous (schurWordFreeCells w) := by
  classical
  apply continuous_pi
  intro c
  by_cases hc : c ∈ Finset.univ.image (schurWordAngleCell w)
  · simpa only [schurWordFreeCells, dite_eq_left hc] using
      (continuous_const : Continuous (fun _ : SchurWordFreeIndex w → ℝ => (0 : ℝ)))
  · simpa only [schurWordFreeCells, dite_eq_right hc] using
      (continuous_apply (⟨c,hc⟩ : SchurWordFreeIndex w))

theorem continuous_vec_schurWordFreeParameter (w : List Bool) :
    Continuous (fun y : SchurWordFreeIndex w → ℝ =>
      Matrix.vec (schurWordParameter w (schurWordFreeCells w y))) := by
  apply continuous_pi
  intro ij
  exact (continuous_apply ij.1).comp ((continuous_apply ij.2).comp
    ((schurWordParameter w).toContinuousLinearMap.continuous.comp
      (continuous_schurWordFreeCells w)))

theorem measurableSet_schurWordFreeSource (w : List Bool) :
    MeasurableSet (schurWordFreeSource w) := by
  have hc := (continuous_schurWordFreeCells w).measurable
  have hs : {y : SchurWordFreeIndex w → ℝ |
      (schurWordParameter w (schurWordFreeCells w y)).charpoly.Separable} =
      (fun y => Matrix.vec (schurWordParameter w (schurWordFreeCells w y))) ⁻¹'
        simpleSpectrumCells (schurWordSize w) := by
    ext y
    exact (mem_simpleSpectrumCells_vec_iff _ _).symm
  change MeasurableSet ({y | SchurWordPositive w (schurWordFreeCells w y)} ∩
    ({y | SchurWordOrdered w (schurWordFreeCells w y)} ∩
    ({y | LinearMap.det (schurWordDifferential w (schurWordFreeCells w y)) ≠ 0} ∩
    {y | (schurWordParameter w (schurWordFreeCells w y)).charpoly.Separable})))
  rw [hs]
  exact ((measurableSet_schurWordPositive w).preimage hc).inter
    (((measurableSet_schurWordOrdered w).preimage hc).inter
      (((isOpen_schurWordRegularSet w).measurableSet.preimage hc).inter
        ((measurableSet_simpleSpectrumCells _).preimage
          (continuous_vec_schurWordFreeParameter w).measurable)))

/-- Exact separation of the original explicitly restricted source. -/
theorem schurAtlasSimpleSource_iff_freeSource (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (i : Fin (m+1)) (x : SchurWordCells w) :
    schurAtlasSimpleSource w centers (i,x) ↔
      (schurWordCoordinateSplit w x).1 ∈ boundedAngularPiece centers i ∧
        (schurWordCoordinateSplit w x).2 ∈ schurWordFreeSource w := by
  let y := (schurWordCoordinateSplit w x).2
  have hK : schurWordParameter w x = schurWordParameter w (schurWordFreeCells w y) :=
    schurWordParameter_eq_freeCells w x
  have hsem := schurWord_source_congr_parameter w x (schurWordFreeCells w y) hK
  have hs : schurAtlasCells w centers (i,x) ∈ simpleSpectrumCells (schurWordSize w) ↔
      (schurWordParameter w (schurWordFreeCells w y)).charpoly.Separable := by
    change Matrix.vec (schurAtlasMatrix w centers (i,x)) ∈ _ ↔ _
    rw [mem_simpleSpectrumCells_vec_iff, schurAtlasMatrix_charpoly, hK]
  constructor
  · intro h
    exact ⟨h.1.1, hsem.1.mp h.1.2.1, hsem.2.1.mp h.1.2.2.1,
      hsem.2.2.2.mp h.1.2.2.2, hs.mp h.2⟩
  · rintro ⟨ha,hp,ho,hd,hsp⟩
    exact ⟨⟨ha,hsem.1.mpr hp,hsem.2.1.mpr ho,hsem.2.2.2.mpr hd⟩,hs.mpr hsp⟩

/-- A generic FUNCTIONAL invariance input, subsequently to be proved for each
actual Gaussian/count weight. This is not an ensemble law or external assumption. -/
theorem schurAtlasCells_invariant_weight (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (g : SchurWordCells w → ℝ≥0∞)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
      (M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M))
    (i : Fin (m+1)) (x : SchurWordCells w) :
    g (schurAtlasCells w centers (i,x)) =
      g (Matrix.vec (schurWordParameter w
        (schurWordFreeCells w (schurWordCoordinateSplit w x).2))) := by
  let Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ :=
    ⟨schurAtlasFrame w centers (i,x),schurAtlasFrame_orthogonal w centers (i,x)⟩
  have h := hginv Q (schurWordParameter w x)
  change g (schurAtlasCells w centers (i,x)) = g (Matrix.vec (schurWordParameter w x)) at h
  rw [h,schurWordParameter_eq_freeCells]
  rfl

/-- The literal per-chart angular/free separation, valid also for zero or infinite
free integrals. No injectivity/cover assumption or cancellation is used. -/
theorem schurAtlasSimpleSource_lintegral_factor (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (g : SchurWordCells w → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
      (M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M))
    (i : Fin (m+1)) :
    (∫⁻ x in {x | schurAtlasSimpleSource w centers (i,x)},
      ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)|) * g (schurAtlasCells w centers (i,x))) =
      (∫⁻ a in boundedAngularPiece centers i,
        ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (skewFromCoordinates _ a))) *
      ∫⁻ y in schurWordFreeSource w,
        ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w y))| *
          g (Matrix.vec (schurWordParameter w (schurWordFreeCells w y))) := by
  let A : SchurWordAngles w → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (skewFromCoordinates _ a))
  let B : (SchurWordFreeIndex w → ℝ) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w y))| *
      g (Matrix.vec (schurWordParameter w (schurWordFreeCells w y)))
  have hA : Measurable A :=
    (continuous_cayleyAngularJacobian_coordinates _).measurable.ennreal_ofReal
  have hB : Measurable B :=
    (((continuous_det_schurWordDifferential w).comp
      (continuous_schurWordFreeCells w)).abs.measurable.ennreal_ofReal).mul
        (hg.comp (continuous_vec_schurWordFreeParameter w).measurable)
  have hAB : Measurable (fun z : SchurWordAngles w × (SchurWordFreeIndex w → ℝ) =>
      A z.1 * B z.2) := (hA.comp measurable_fst).mul (hB.comp measurable_snd)
  have he : {x | schurAtlasSimpleSource w centers (i,x)} =
      (schurWordCoordinateSplit w) ⁻¹'
        (boundedAngularPiece centers i ×ˢ schurWordFreeSource w) := by
    ext x
    exact schurAtlasSimpleSource_iff_freeSource w centers i x
  have hw (x : SchurWordCells w) :
      ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)|) * g (schurAtlasCells w centers (i,x)) =
      A (schurWordCoordinateSplit w x).1 * B (schurWordCoordinateSplit w x).2 := by
    have hΩ : skewFromCoordinates (schurWordSize w) (schurWordAngleMap w x) =
        schurWordOmegaSkew w x := by
      apply Subtype.ext
      exact skewFromCoordinates_schurWordAngleMap w x
    have hD := schurWordDifferential_congr_parameter w x
      (schurWordFreeCells w (schurWordCoordinateSplit w x).2)
      (schurWordParameter_eq_freeCells w x)
    rw [schurAtlasCells_invariant_weight w centers g hginv i x,
      ENNReal.ofReal_mul (cayleyAngularJacobian_pos _ _).le]
    change _ = ENNReal.ofReal (cayleyAngularJacobian _
      (skewFromCoordinates _ (schurWordAngleMap w x))) * _
    rw [hΩ,hD]
    exact mul_assoc _ _ _
  rw [he]
  calc
    _ = ∫⁻ x in (schurWordCoordinateSplit w) ⁻¹'
        (boundedAngularPiece centers i ×ˢ schurWordFreeSource w),
        A (schurWordCoordinateSplit w x).1 * B (schurWordCoordinateSplit w x).2 := by
      exact lintegral_congr_ae (Filter.Eventually.of_forall hw)
    _ = ∫⁻ z in boundedAngularPiece centers i ×ˢ schurWordFreeSource w,
        A z.1 * B z.2 :=
      (volume_preserving_schurWordCoordinateSplit w).setLIntegral_comp_preimage
        ((measurableSet_boundedAngularPiece centers i).prod
          (measurableSet_schurWordFreeSource w)) hAB
    _ = _ := by
      rw [Measure.volume_eq_prod,← Measure.prod_restrict]
      exact lintegral_prod_mul hA.aemeasurable hB.aemeasurable

/-- The actual source integral factors through the EXISTING finite positive actual
angular mass. Invariance remains explicit and no mass division is performed. -/
theorem sum_schurAtlasSimpleSource_lintegral_factor (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (g : SchurWordCells w → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
      (M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M)) :
    (∑ i : Fin (m+1), ∫⁻ x in {x | schurAtlasSimpleSource w centers (i,x)},
      ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (schurWordOmegaSkew w x) *
        |LinearMap.det (schurWordDifferential w x)|) * g (schurAtlasCells w centers (i,x))) =
      ENNReal.ofReal (boundedAtlasAngularMass centers) *
        ∫⁻ y in schurWordFreeSource w,
          ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w y))| *
            g (Matrix.vec (schurWordParameter w (schurWordFreeCells w y))) := by
  have hmass (i : Fin (m+1)) :
      (∫⁻ a in boundedAngularPiece centers i,
        ENNReal.ofReal (cayleyAngularJacobian (schurWordSize w) (skewFromCoordinates _ a))) =
      ENNReal.ofReal (∫ a in boundedAngularPiece centers i,
        cayleyAngularJacobian (schurWordSize w) (skewFromCoordinates _ a)) :=
    (ofReal_integral_eq_lintegral_ofReal (integrableOn_boundedAngularPiece centers i)
      (Filter.Eventually.of_forall fun a => (cayleyAngularJacobian_pos _ _).le)).symm
  simp_rw [schurAtlasSimpleSource_lintegral_factor w centers g hg hginv,hmass]
  rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg]
  · rfl
  · intro i _
    exact integral_nonneg fun a => (cayleyAngularJacobian_pos _ _).le

end Paper.Spectral
