/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.GaussianCountWeight
public import GinoeClt.Spectral.SchurHeadCount
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Matrix ENNReal BigOperators NNReal Classical
namespace Paper.Spectral

/-- Genuine raw free-coordinate partition for the actual Gaussian/count weight.
The sum is finite and the only domain conditions are original Pos and Order. -/
def gaussianCountFreePartition (A : Set ℂ) (n : ℕ) (t : ℝ≥0) : ℝ≥0∞ :=
  ∑ w : SchurWordsOfSize (n+1),
    (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ *
    ∫⁻ u in {v | SchurWordPositive w.val (schurWordFreeCells w.val v) ∧
        SchurWordOrdered w.val (schurWordFreeCells w.val v)},
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val (schurWordFreeCells w.val u))| *
      gaussianCountWeight A n t (schurCellsCast w.property
        (Matrix.vec (schurWordParameter w.val (schurWordFreeCells w.val u))))

/-- The finite generating integral under the ACTUAL matrix law is the actual
angular mass times the displayed raw free-coordinate partition. -/
theorem countGeneratingIntegral_eq_schurPartition (A : Set ℂ) (hA : IsOpen A) (n : ℕ)
    (t : ℝ≥0) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (n+1)) ℝ)
    (hcover : ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (n+1) (centers i)) :
    (∫⁻ M : SampleSpace n, (1 + (t : ℝ≥0∞)) ^ count A n M ∂matrixLaw n) =
      ENNReal.ofReal (boundedAtlasAngularMass centers) * gaussianCountFreePartition A n t := by
  rw [← lintegral_gaussianCountWeight A hA n t]
  exact lintegral_eq_angularMass_mul_sum_schurPositive centers hcover
    (gaussianCountWeight A n t) (measurable_gaussianCountWeight A hA n t)
    (gaussianCountWeight_orthogonal_conj A n t)

/-- Actual probability normalization determines the raw partition's base value. -/
theorem gaussianCountFreePartition_zero_eq_inv (A : Set ℂ) (hA : IsOpen A) (n : ℕ)
    {m : ℕ} (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (n+1)) ℝ)
    (hcover : ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (n+1) (centers i)) :
    gaussianCountFreePartition A n 0 = (ENNReal.ofReal (boundedAtlasAngularMass centers))⁻¹ := by
  have hnorm : ENNReal.ofReal (boundedAtlasAngularMass centers) *
      gaussianCountFreePartition A n 0 = 1 := by
    simpa using (countGeneratingIntegral_eq_schurPartition A hA n 0 centers hcover).symm
  have h0 : ENNReal.ofReal (boundedAtlasAngularMass centers) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (boundedAtlasAngularMass_pos centers)).ne'
  have ht : ENNReal.ofReal (boundedAtlasAngularMass centers) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ = ((ENNReal.ofReal (boundedAtlasAngularMass centers))⁻¹ *
        ENNReal.ofReal (boundedAtlasAngularMass centers)) * gaussianCountFreePartition A n 0 := by
      rw [ENNReal.inv_mul_cancel h0 ht,one_mul]
    _ = (ENNReal.ofReal (boundedAtlasAngularMass centers))⁻¹ *
        (ENNReal.ofReal (boundedAtlasAngularMass centers) * gaussianCountFreePartition A n 0) :=
      mul_assoc _ _ _
    _ = _ := by rw [hnorm,mul_one]

/-- The common angular factor cancels only AFTER its positivity/finiteness and
the exact probability normalization have been proved. -/
theorem countGeneratingIntegral_eq_schurPartition_ratio (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (t : ℝ≥0) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (n+1)) ℝ)
    (hcover : ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (n+1) (centers i)) :
    (∫⁻ M : SampleSpace n, (1 + (t : ℝ≥0∞)) ^ count A n M ∂matrixLaw n) =
      gaussianCountFreePartition A n t / gaussianCountFreePartition A n 0 := by
  rw [gaussianCountFreePartition_zero_eq_inv A hA n centers hcover,
    div_eq_mul_inv,inv_inv,mul_comm]
  exact countGeneratingIntegral_eq_schurPartition A hA n t centers hcover

theorem gaussianCountFreePartition_zero_ne_zero (A : Set ℂ) (hA : IsOpen A) (n : ℕ)
    {m : ℕ} (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (n+1)) ℝ)
    (hcover : ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (n+1) (centers i)) :
    gaussianCountFreePartition A n 0 ≠ 0 := by
  rw [gaussianCountFreePartition_zero_eq_inv A hA n centers hcover]
  simp

theorem gaussianCountFreePartition_zero_ne_top (A : Set ℂ) (hA : IsOpen A) (n : ℕ)
    {m : ℕ} (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (n+1)) ℝ)
    (hcover : ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (n+1) (centers i)) :
    gaussianCountFreePartition A n 0 ≠ ∞ := by
  rw [gaussianCountFreePartition_zero_eq_inv A hA n centers hcover]
  exact ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr (boundedAtlasAngularMass_pos centers)).ne'

/-- The same genuine free partition, now with no matrix-count function inside
the integrals: its test weight is the explicit product over raw representatives. -/
theorem gaussianCountFreePartition_eq_heads (A : Set ℂ) (n : ℕ)
    (hA : ∀ z ∈ A, 0 < z.im) (t : ℝ≥0) :
    gaussianCountFreePartition A n t =
      ∑ w : SchurWordsOfSize (n+1), (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ *
        ∫⁻ u in {v | SchurWordPositive w.val (schurWordFreeCells w.val v) ∧
            SchurWordOrdered w.val (schurWordFreeCells w.val v)},
          ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val (schurWordFreeCells w.val u))| *
          (ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ ((n+1)^2) *
            Real.exp (-(∑ i : Fin (schurWordSize w.val), ∑ j : Fin (schurWordSize w.val),
              schurWordParameter w.val (schurWordFreeCells w.val u) i j ^ 2) / 2)) *
            ((schurWordHeadRoots w.val (schurWordFreeCells w.val u)).map
              (fun z => if z ∈ scaledCountDomain n A then 1 + (t : ℝ≥0∞) else 1)).prod) := by
  unfold gaussianCountFreePartition
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  apply setLIntegral_congr_fun
    (((measurableSet_schurWordPositive w.val).preimage
        (continuous_schurWordFreeCells w.val).measurable).inter
      ((measurableSet_schurWordOrdered w.val).preimage
        (continuous_schurWordFreeCells w.val).measurable))
  intro u hu
  exact congrArg (fun z : ℝ≥0∞ =>
      ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val (schurWordFreeCells w.val u))| * z)
    (gaussianCountWeight_schurWord_cast A n hA w (schurWordFreeCells w.val u) hu.1 t)

end Paper.Spectral
