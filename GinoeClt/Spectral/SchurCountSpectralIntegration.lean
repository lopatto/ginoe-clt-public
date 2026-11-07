/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurHeadCountTest
public import GinoeClt.Spectral.SchurGaussianSpectralIntegral
public import GinoeClt.Spectral.SchurJacobianVandermonde
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal NNReal Classical
namespace Paper.Spectral

/-- The actual positive ordered free-cell integral, including the physical word
Jacobian, actual matrix Gaussian and one generating factor per head. -/
def schurPositiveOrderedCountIntegral (B : Set ℂ) (t : ℝ≥0) (w : List Bool) : ℝ≥0∞ :=
  ∫⁻ u in {u : SchurWordFreeIndex w → ℝ |
      SchurWordPositive w (schurWordFreeCells w u) ∧
        SchurWordOrdered w (schurWordFreeCells w u)},
    ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w u))| *
      ENNReal.ofReal (schurUpperGaussian (Matrix.vec
        (schurWordParameter w (schurWordFreeCells w u)))) *
        ((schurWordHeadRoots w (schurWordFreeCells w u)).map
          (fun z => if z ∈ B then 1+(t : ℝ≥0∞) else 1)).prod

/-- Original Pos/Order weighted integral equals the COMPLETE actual free
Gaussian/physical-ratio integral with the explicit Vandermonde/count/order test.
This uses the norm-Jacobian identity without dividing by any pair gap. -/
theorem schurFreeSpectralIntegral_headCountTest (B : Set ℂ) (t : ℝ≥0) (w : List Bool) :
    schurFreeSpectralIntegral w (schurHeadCountTest B t w) =
      schurPositiveOrderedCountIntegral B t w := by
  unfold schurFreeSpectralIntegral schurPositiveOrderedCountIntegral
  have hP := measurableSet_schurFreePositiveSet w
  have hO := (measurableSet_schurWordOrdered w).preimage
    (continuous_schurWordFreeCells w).measurable
  have hPO : MeasurableSet {u : SchurWordFreeIndex w → ℝ |
      SchurWordPositive w (schurWordFreeCells w u) ∧
        SchurWordOrdered w (schurWordFreeCells w u)} := hP.inter hO
  rw [← lintegral_indicator hP,← lintegral_indicator hPO]
  apply lintegral_congr
  intro u
  by_cases hp : SchurWordPositive w (schurWordFreeCells w u)
  · have hpos : u ∈ schurFreePositiveSet w := hp
    rw [Set.indicator_of_mem hpos,schurHeadCountTest_actual B t w]
    by_cases ho : SchurWordOrdered w (schurWordFreeCells w u)
    · have hboth : u ∈ {u : SchurWordFreeIndex w → ℝ |
          SchurWordPositive w (schurWordFreeCells w u) ∧
            SchurWordOrdered w (schurWordFreeCells w u)} := ⟨hp,ho⟩
      rw [Set.indicator_of_mem hboth,ite_eq_left ho,
        abs_det_schurWordDifferential_eq_vandermonde w _ hp,
        ENNReal.ofReal_mul (norm_nonneg _)]
      ac_rfl
    · have hboth : u ∉ {u : SchurWordFreeIndex w → ℝ |
          SchurWordPositive w (schurWordFreeCells w u) ∧
            SchurWordOrdered w (schurWordFreeCells w u)} := fun h => ho h.2
      rw [Set.indicator_of_notMem hboth,ite_eq_right ho,mul_zero]
  · have hpos : u ∉ schurFreePositiveSet w := hp
    have hboth : u ∉ {u : SchurWordFreeIndex w → ℝ |
        SchurWordPositive w (schurWordFreeCells w u) ∧
          SchurWordOrdered w (schurWordFreeCells w u)} := fun h => hp h.1
    rw [Set.indicator_of_notMem hpos,Set.indicator_of_notMem hboth]

/-- Actual Gaussian/Jacobian/count integration for every word, with its
original weak positivity and ordering and exact common size-only scalar. -/
theorem schurPositiveOrderedCountIntegral_eq (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (w : List Bool) :
    schurPositiveOrderedCountIntegral B t w =
      ENNReal.ofReal (Real.sqrt (2*Real.pi)^((schurWordSize w).choose 2)) *
        schurSpectralIntegral w (schurHeadCountTest B t w) := by
  rw [← schurFreeSpectralIntegral_headCountTest]
  exact schurFreeSpectralIntegral_eq w _ (measurable_schurHeadCountTest B hB t w)

/-- Noncanonical words have NO original positive ordered source. This is a
source-domain fact, not a simple-spectrum or a.e. replacement. -/
theorem schurPositiveOrderedCountIntegral_eq_zero_of_not_canonical
    (B : Set ℂ) (t : ℝ≥0) (w : List Bool)
    (hw : w ≠ List.replicate (w.count false) false ++ List.replicate (w.count true) true) :
    schurPositiveOrderedCountIntegral B t w = 0 := by
  have hs : {u : SchurWordFreeIndex w → ℝ |
      SchurWordPositive w (schurWordFreeCells w u) ∧
        SchurWordOrdered w (schurWordFreeCells w u)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact hw (ordered_schurWord_eq_canonical w _ hu.1 hu.2)
  unfold schurPositiveOrderedCountIntegral
  rw [hs]
  exact setLIntegral_empty _

theorem schurSpectralIntegral_headCountTest_eq_zero_of_not_canonical
    (B : Set ℂ) (hB : MeasurableSet B) (t : ℝ≥0) (w : List Bool)
    (hw : w ≠ List.replicate (w.count false) false ++ List.replicate (w.count true) true) :
    schurSpectralIntegral w (schurHeadCountTest B t w) = 0 := by
  have h := schurPositiveOrderedCountIntegral_eq_zero_of_not_canonical B t w hw
  rw [schurPositiveOrderedCountIntegral_eq B hB t w] at h
  have hc : ENNReal.ofReal (Real.sqrt (2*Real.pi)^((schurWordSize w).choose 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos (Real.sqrt_pos.mpr (by positivity)) _)).ne'
  exact (mul_eq_zero.mp h).resolve_left hc

/-- A finite nonnegative raw Gaussian density prefactor can be extracted from
the original positive ordered integral, even for zero or infinite residual mass. -/
theorem schurPositiveOrderedCountIntegral_density (c : ℝ) (hc : 0 ≤ c)
    (B : Set ℂ) (t : ℝ≥0) (w : List Bool) :
    (∫⁻ u in {u : SchurWordFreeIndex w → ℝ |
        SchurWordPositive w (schurWordFreeCells w u) ∧
          SchurWordOrdered w (schurWordFreeCells w u)},
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w u))| *
        (ENNReal.ofReal (c*Real.exp (-(∑ i : Fin (schurWordSize w),
          ∑ j : Fin (schurWordSize w),
            schurWordParameter w (schurWordFreeCells w u) i j ^ 2)/2)) *
          ((schurWordHeadRoots w (schurWordFreeCells w u)).map
            (fun z => if z ∈ B then 1+(t : ℝ≥0∞) else 1)).prod)) =
      ENNReal.ofReal c * schurPositiveOrderedCountIntegral B t w := by
  have hS : MeasurableSet {u : SchurWordFreeIndex w → ℝ |
      SchurWordPositive w (schurWordFreeCells w u) ∧
        SchurWordOrdered w (schurWordFreeCells w u)} :=
    ((measurableSet_schurWordPositive w).preimage
      (continuous_schurWordFreeCells w).measurable).inter
        ((measurableSet_schurWordOrdered w).preimage
          (continuous_schurWordFreeCells w).measurable)
  unfold schurPositiveOrderedCountIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun hS
  intro u _
  change ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w u))| *
      (ENNReal.ofReal (c*Real.exp (-(∑ i : Fin (schurWordSize w),
        ∑ j : Fin (schurWordSize w),
          schurWordParameter w (schurWordFreeCells w u) i j ^ 2)/2)) *
        ((schurWordHeadRoots w (schurWordFreeCells w u)).map
          (fun z => if z ∈ B then 1+(t : ℝ≥0∞) else 1)).prod) = _
  have hg : Real.exp (-(∑ i : Fin (schurWordSize w), ∑ j : Fin (schurWordSize w),
        schurWordParameter w (schurWordFreeCells w u) i j ^ 2)/2) =
      schurUpperGaussian (Matrix.vec (schurWordParameter w (schurWordFreeCells w u))) := by
    symm
    unfold schurUpperGaussian
    rw [sum_sq_matrix_vec]
  rw [hg,ENNReal.ofReal_mul hc]
  ac_rfl

end Paper.Spectral
