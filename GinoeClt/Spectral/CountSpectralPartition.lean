/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurCountSpectralIntegration
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal NNReal Classical
namespace Paper.Spectral

/-- Actual finite-word spectral partition, with original weak ordering encoded
in the explicit head test and the genuine gauge count 2^word.length. -/
def countSpectralPartition (B : Set ℂ) (t : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  ∑ w : SchurWordsOfSize N, (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ *
    schurSpectralIntegral w.val (schurHeadCountTest B t w.val)

/-- The exact size-only scalar from raw standard Gaussian density and the
proved literal free Gaussian integration. -/
def gaussianSchurSpectralFactor (N : ℕ) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹^(N^2) * Real.sqrt (2*Real.pi)^(N.choose 2)

theorem gaussianSchurSpectralFactor_pos (N : ℕ) :
    0 < gaussianSchurSpectralFactor N := by
  unfold gaussianSchurSpectralFactor
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- The genuine original free partition is now expressed as the explicit
spectral test partition, with its exact positive finite density prefactor. -/
theorem gaussianCountFreePartition_eq_spectral (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) (t : ℝ≥0) :
    gaussianCountFreePartition A n t =
      ENNReal.ofReal (gaussianSchurSpectralFactor (n+1)) *
        countSpectralPartition (scaledCountDomain n A) t (n+1) := by
  rw [gaussianCountFreePartition_eq_heads A n hupper t]
  unfold countSpectralPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [schurPositiveOrderedCountIntegral_density _ (by positivity)]
  rw [schurPositiveOrderedCountIntegral_eq _ (isOpen_scaledCountDomain A hA n).measurableSet]
  rw [w.property]
  unfold gaussianSchurSpectralFactor
  rw [ENNReal.ofReal_mul (by positivity)]
  ac_rfl

lemma div_common_finite_pos (c a b : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    (c*a)/(c*b) = a/b := by
  rw [div_eq_mul_inv,div_eq_mul_inv,ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  calc
    _ = (c*c⁻¹)*(a*b⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hct,one_mul]

/-- Exact actual finite-ensemble generating integral in spectral coordinates.
No atlas/conditional-law hypothesis remains: the needed cover exists by proof. -/
theorem countGeneratingIntegral_eq_spectralPartition_ratio (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) (t : ℝ≥0) :
    (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n) =
      countSpectralPartition (scaledCountDomain n A) t (n+1) /
        countSpectralPartition (scaledCountDomain n A) 0 (n+1) := by
  obtain ⟨m,centers,hcover⟩ := exists_finite_bounded_orthogonal_target_atlas (n+1)
  rw [countGeneratingIntegral_eq_schurPartition_ratio A hA n t centers hcover,
    gaussianCountFreePartition_eq_spectral A hA n hupper t,
    gaussianCountFreePartition_eq_spectral A hA n hupper 0]
  exact div_common_finite_pos _ _ _
    (ENNReal.ofReal_pos.mpr (gaussianSchurSpectralFactor_pos _)).ne'
    ENNReal.ofReal_ne_top

theorem countSpectralPartition_zero_ne_zero (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) :
    countSpectralPartition (scaledCountDomain n A) 0 (n+1) ≠ 0 := by
  obtain ⟨m,centers,hcover⟩ := exists_finite_bounded_orthogonal_target_atlas (n+1)
  have h := gaussianCountFreePartition_zero_ne_zero A hA n centers hcover
  rw [gaussianCountFreePartition_eq_spectral A hA n hupper 0] at h
  intro hz
  exact h (by rw [hz,mul_zero])

theorem countSpectralPartition_zero_ne_top (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) :
    countSpectralPartition (scaledCountDomain n A) 0 (n+1) ≠ ∞ := by
  obtain ⟨m,centers,hcover⟩ := exists_finite_bounded_orthogonal_target_atlas (n+1)
  have h := gaussianCountFreePartition_zero_ne_top A hA n centers hcover
  rw [gaussianCountFreePartition_eq_spectral A hA n hupper 0] at h
  intro hz
  have hc : ENNReal.ofReal (gaussianSchurSpectralFactor (n+1)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (gaussianSchurSpectralFactor_pos _)).ne'
  exact h (by rw [hz,ENNReal.mul_top hc])

end Paper.Spectral
