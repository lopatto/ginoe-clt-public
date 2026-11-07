/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurSectorWords
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Classical BigOperators
namespace Paper.Spectral

/-- Relative canonical-sector weights derived from the actual word gauge.
Real and complex ordering are still inside the literal spectral test. -/
def countSectorPartition (B : Set ℂ) (t : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  ∑ l : Fin (N/2+1), (((2^l.val : ℕ) : ℝ≥0∞)) *
    schurSpectralIntegral (sectorSchurWord N l).val
      (schurHeadCountTest B t (sectorSchurWord N l).val)

lemma sectorGaugeFactor (N l : ℕ) (hl : l ≤ N) :
    (((2^(N-l) : ℕ) : ℝ≥0∞))⁻¹ =
      (((2^N : ℕ) : ℝ≥0∞))⁻¹ * ((2^l : ℕ) : ℝ≥0∞) := by
  have hp : ((2^(N-l) : ℕ) : ℝ≥0∞) * ((2^l : ℕ) : ℝ≥0∞) =
      ((2^N : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul,← pow_add,Nat.sub_add_cancel hl]
  have hu : ((2^(N-l) : ℕ) : ℝ≥0∞) *
      ((((2^N : ℕ) : ℝ≥0∞))⁻¹ * ((2^l : ℕ) : ℝ≥0∞)) = 1 := by
    calc
      _ = (((2^(N-l) : ℕ) : ℝ≥0∞) * ((2^l : ℕ) : ℝ≥0∞)) *
        (((2^N : ℕ) : ℝ≥0∞))⁻¹ := by ac_rfl
      _ = _ := by rw [hp,ENNReal.mul_inv_cancel (by positivity) (by simp)]
  calc
    _ = (((2^(N-l) : ℕ) : ℝ≥0∞))⁻¹ * 1 := by rw [mul_one]
    _ = (((2^(N-l) : ℕ) : ℝ≥0∞))⁻¹ *
        (((2^(N-l) : ℕ) : ℝ≥0∞) *
          ((((2^N : ℕ) : ℝ≥0∞))⁻¹ * ((2^l : ℕ) : ℝ≥0∞))) :=
      congrArg (fun q => (((2^(N-l) : ℕ) : ℝ≥0∞))⁻¹*q) hu.symm
    _ = _ := ENNReal.inv_mul_cancel_left (by positivity) (by simp)

/-- The common 2^-N factor and relative 2^l factors follow from the actual
2^word.length gauge count. No sector constants are assumed. -/
theorem countSpectralPartition_eq_gauge_mul_sector (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (N : ℕ) :
    countSpectralPartition B t N =
      (((2^N : ℕ) : ℝ≥0∞))⁻¹ * countSectorPartition B t N := by
  rw [countSpectralPartition_eq_sectors B hB t N]
  unfold countSectorPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hl : l.val ≤ N := by
    have h := l.isLt
    omega
  rw [sectorGaugeFactor N l.val hl]
  exact mul_assoc _ _ _

/-- Exact actual finite-ensemble generating integral in canonical sectors,
including every parity. Real ordering is deliberately retained. -/
theorem countGeneratingIntegral_eq_sectorPartition_ratio (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) (t : ℝ≥0) :
    (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n) =
      countSectorPartition (scaledCountDomain n A) t (n+1) /
        countSectorPartition (scaledCountDomain n A) 0 (n+1) := by
  rw [countGeneratingIntegral_eq_spectralPartition_ratio A hA n hupper t,
    countSpectralPartition_eq_gauge_mul_sector _ (isOpen_scaledCountDomain A hA n).measurableSet,
    countSpectralPartition_eq_gauge_mul_sector _ (isOpen_scaledCountDomain A hA n).measurableSet]
  exact div_common_finite_pos _ _ _ (by simp) (by simp)

theorem countSectorPartition_zero_ne_zero (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) :
    countSectorPartition (scaledCountDomain n A) 0 (n+1) ≠ 0 := by
  have h := countSpectralPartition_zero_ne_zero A hA n hupper
  rw [countSpectralPartition_eq_gauge_mul_sector _
    (isOpen_scaledCountDomain A hA n).measurableSet] at h
  intro hz
  exact h (by rw [hz,mul_zero])

theorem countSectorPartition_zero_ne_top (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ z ∈ A, 0 < z.im) :
    countSectorPartition (scaledCountDomain n A) 0 (n+1) ≠ ∞ := by
  have h := countSpectralPartition_zero_ne_top A hA n hupper
  rw [countSpectralPartition_eq_gauge_mul_sector _
    (isOpen_scaledCountDomain A hA n).measurableSet] at h
  intro hz
  have hc : (((2^(n+1) : ℕ) : ℝ≥0∞))⁻¹ ≠ 0 := by simp
  exact h (by rw [hz,ENNReal.mul_top hc])

end Paper.Spectral
