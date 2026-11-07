/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurSectorIntegration
public import GinoeClt.Spectral.Count
public import GinoeClt.Spectral.OrthogonalConjugation
public import GinoeClt.Probability.MatrixDensity
public import GinoeClt.Reduction
public import Mathlib.MeasureTheory.Function.Floor
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Matrix NNReal ENNReal BigOperators
namespace Paper.Spectral

/-- Natural-valued measurability of the SAME frozen multiplicity count. -/
theorem measurable_count_nat_of_isOpen (A : Set ℂ) (hA : IsOpen A) (n : ℕ) :
    Measurable (count A n) := by
  have h := (countMeasurable_of_isOpen A hA n).nat_floor
  simpa only [Nat.floor_natCast] using h

theorem continuous_matrixGaussianDensity (n : ℕ) : Continuous (matrixGaussianDensity n) := by
  have he : matrixGaussianDensity n = fun M : SampleSpace n =>
      (Real.sqrt (2 * Real.pi))⁻¹ ^ ((n+1)^2) *
        Real.exp (-(∑ i : Fin (n+1), ∑ j : Fin (n+1), M i j ^ 2) / 2) :=
    funext (matrixGaussianDensity_eq n)
  rw [he]
  fun_prop

theorem matrixGaussianDensity_orthogonal_conj (n : ℕ)
    (Q : Matrix.orthogonalGroup (Fin (n+1)) ℝ) (M : SampleSpace n) :
    matrixGaussianDensity n ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ) =
      matrixGaussianDensity n M := by
  let R : Matrix.orthogonalGroup (Fin (n+1)) ℝ :=
    ⟨(Q : Matrix _ _ ℝ)ᵀ, Matrix.transpose_mem_unitaryGroup_iff.mpr Q.property⟩
  have h := matrixActionIsometry_matrixVector n Q R M
  have hn : ‖matrixVector n ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)‖ =
      ‖matrixVector n M‖ := by
    calc
      _ = ‖matrixActionIsometry n Q R (matrixVector n M)‖ := congrArg norm h.symm
      _ = _ := (matrixActionIsometry n Q R).norm_map _
  unfold matrixGaussianDensity Probability.euclideanGaussianDensity
  rw [hn]

/-- Actual frozen Gaussian density times the generating power of the actual
SCALED multiplicity count. The finite nonnegative parameter is not a moment assumption. -/
def gaussianCountWeight (A : Set ℂ) (n : ℕ) (t : ℝ≥0)
    (y : (Fin (n+1) × Fin (n+1)) → ℝ) : ℝ≥0∞ :=
  let M : SampleSpace n := Matrix.of (fun i j => y (j,i))
  ENNReal.ofReal (matrixGaussianDensity n M) *
    (1 + (t : ℝ≥0∞)) ^ count A n M

@[simp] theorem gaussianCountWeight_vec (A : Set ℂ) (n : ℕ) (t : ℝ≥0) (M : SampleSpace n) :
    gaussianCountWeight A n t (Matrix.vec M) =
      ENNReal.ofReal (matrixGaussianDensity n M) *
        (1 + (t : ℝ≥0∞)) ^ count A n M := rfl

@[simp] theorem gaussianCountWeight_zero (A : Set ℂ) (n : ℕ)
    (y : (Fin (n+1) × Fin (n+1)) → ℝ) :
    gaussianCountWeight A n 0 y =
      ENNReal.ofReal (matrixGaussianDensity n (Matrix.of (fun i j => y (j,i)))) := by
  simp [gaussianCountWeight]

theorem measurable_gaussianCountWeight (A : Set ℂ) (hA : IsOpen A) (n : ℕ) (t : ℝ≥0) :
    Measurable (gaussianCountWeight A n t) := by
  have hM : Measurable (fun y : (Fin (n+1) × Fin (n+1)) → ℝ =>
      (Matrix.of (fun i j => y (j,i)) : SampleSpace n)) := by fun_prop
  exact (((continuous_matrixGaussianDensity n).measurable.comp hM).ennreal_ofReal).mul
    ((measurable_of_countable (fun k : ℕ => (1 + (t : ℝ≥0∞)) ^ k)).comp
      ((measurable_count_nat_of_isOpen A hA n).comp hM))

theorem gaussianCountWeight_orthogonal_conj (A : Set ℂ) (n : ℕ) (t : ℝ≥0)
    (Q : Matrix.orthogonalGroup (Fin (n+1)) ℝ) (M : SampleSpace n) :
    gaussianCountWeight A n t (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) =
      gaussianCountWeight A n t (Matrix.vec M) := by
  rw [gaussianCountWeight_vec, gaussianCountWeight_vec,
    matrixGaussianDensity_orthogonal_conj, count_orthogonal_conj]

/-- Ordinary column-major coordinate volume agrees EXACTLY with the frozen
iterated matrix-entry volume. -/
theorem matrixVec_volumePreserving (n : ℕ) :
    MeasurePreserving (Matrix.vec : SampleSpace n → (Fin (n+1) × Fin (n+1) → ℝ))
      (matrixVolume n) volume := by
  have hu : MeasurePreserving
      (Function.uncurry : SampleSpace n → (Fin (n+1) × Fin (n+1) → ℝ))
      (matrixVolume n) volume := ⟨by fun_prop,matrixVolume_uncurry_map n⟩
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin (n+1) × Fin (n+1) => (volume : Measure ℝ))
      (Equiv.prodComm (Fin (n+1)) (Fin (n+1)))).comp hu

/-- The coordinate integral is the genuine count generating integral under the
original Gaussian matrix law, with exact density normalization. -/
theorem lintegral_gaussianCountWeight (A : Set ℂ) (hA : IsOpen A) (n : ℕ) (t : ℝ≥0) :
    (∫⁻ y, gaussianCountWeight A n t y) =
      ∫⁻ M : SampleSpace n, (1 + (t : ℝ≥0∞)) ^ count A n M ∂matrixLaw n := by
  have hD := (continuous_matrixGaussianDensity n).measurable.ennreal_ofReal
  have hP := (measurable_of_countable (fun k : ℕ => (1 + (t : ℝ≥0∞)) ^ k)).comp
    (measurable_count_nat_of_isOpen A hA n)
  calc
    _ = ∫⁻ M : SampleSpace n, gaussianCountWeight A n t (Matrix.vec M) ∂matrixVolume n :=
      ((matrixVec_volumePreserving n).lintegral_comp
        (measurable_gaussianCountWeight A hA n t)).symm
    _ = ∫⁻ M : SampleSpace n, ENNReal.ofReal (matrixGaussianDensity n M) *
        (1 + (t : ℝ≥0∞)) ^ count A n M ∂matrixVolume n := by
      simp only [gaussianCountWeight_vec]
    _ = _ := by
      rw [matrixLaw_eq_withDensity]
      simpa only [Function.comp_def, Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul (matrixVolume n) hD hP).symm

/-- The actual finite-size generating integral is finite, by the proved pointwise
count bound. No uniform exponential-moment assumption is introduced. -/
theorem lintegral_gaussianCountWeight_le (A : Set ℂ) (hA : IsOpen A) (n : ℕ) (t : ℝ≥0) :
    (∫⁻ y, gaussianCountWeight A n t y) ≤ (1 + (t : ℝ≥0∞)) ^ (n+1) := by
  rw [lintegral_gaussianCountWeight A hA n t]
  calc
    _ ≤ ∫⁻ _M : SampleSpace n, (1 + (t : ℝ≥0∞)) ^ (n+1) ∂matrixLaw n := by
      apply lintegral_mono
      intro M
      exact pow_le_pow_right₀ (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ (t : ℝ≥0∞) from zero_le)) (count_le A n M)
    _ = _ := by simp

theorem lintegral_gaussianCountWeight_ne_top (A : Set ℂ) (hA : IsOpen A) (n : ℕ) (t : ℝ≥0) :
    (∫⁻ y, gaussianCountWeight A n t y) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (lintegral_gaussianCountWeight_le A hA n t)
  simp

/-- Parameter zero recovers total probability ONE exactly. -/
theorem lintegral_gaussianCountWeight_zero (A : Set ℂ) (hA : IsOpen A) (n : ℕ) :
    (∫⁻ y, gaussianCountWeight A n 0 y) = 1 := by
  rw [lintegral_gaussianCountWeight A hA n 0]
  simp

end Paper.Spectral
