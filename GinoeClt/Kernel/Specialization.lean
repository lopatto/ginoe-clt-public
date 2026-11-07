/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Bounds
public import GinoeClt.Kernel.Reality

/-! # Actual S_N determinant moments and cyclic traces

The exact manuscript factors N^k and N^m are retained. Reality is proved
from Hermitian symmetry. This file asserts no correlation-law or asymptotic estimate.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ComplexConjugate PowerSeries

namespace Paper.Kernel

def rescaledS (N : ℕ) (z w : ℂ) : ℂ := S N (rescale N z) (rescale N w)

/-- The source T_k, with T_0 explicitly fixed to one. -/
def determinantMoment (A : Set ℂ) (N k : ℕ) : ℂ :=
  if k = 0 then 1 else
    (N : ℂ) ^ k * KernelIntegrals.determinantIntegral (volume.restrict A) (rescaledS N) k

/-- The source positive-order R_m. The internal zero-order extension is zero. -/
def cyclicTrace (A : Set ℂ) (N m : ℕ) : ℂ :=
  (N : ℂ) ^ m * KernelIntegrals.cycleIntegral (volume.restrict A) (rescaledS N) m

def determinantalPseudoCumulant (A : Set ℂ) (N n : ℕ) : ℂ :=
  Cumulants.pseudoCumulant ℂ (determinantMoment A N) n

def maskedScaledS (A : Set ℂ) (N : ℕ) : ℂ → ℂ → ℂ := maskKernel A (scaledS N)

@[simp] theorem determinantMoment_zero (A : Set ℂ) (N : ℕ) :
    determinantMoment A N 0 = 1 := by simp [determinantMoment]

@[simp] theorem cyclicTrace_zero (A : Set ℂ) (N : ℕ) :
    cyclicTrace A N 0 = 0 := by simp [cyclicTrace, KernelIntegrals.cycleIntegral]

theorem determinantMoment_eq_source (A : Set ℂ) (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    determinantMoment A N k =
      (N : ℂ) ^ k * ∫ x : Fin k → ℂ in Set.univ.pi (fun _ => A),
        Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) x)
        ∂Measure.pi (fun _ : Fin k => (volume : Measure ℂ)) := by
  rw [determinantMoment, ite_eq_right (Nat.ne_zero_of_lt hk)]
  rw [Measure.restrict_pi_pi]
  rfl

theorem cyclicTrace_eq_source (A : Set ℂ) (N : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    cyclicTrace A N m =
      (N : ℂ) ^ m * ∫ x : Fin m → ℂ in Set.univ.pi (fun _ => A),
        (∏ i, S N (rescale N (x i)) (rescale N (x (finRotate m i))))
        ∂Measure.pi (fun _ : Fin m => (volume : Measure ℂ)) := by
  rw [cyclicTrace, KernelIntegrals.cycleIntegral, ite_eq_right (Nat.ne_zero_of_lt hm),
    Measure.restrict_pi_pi]
  rfl

theorem determinantMoment_eq_normalized {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    determinantMoment A N k =
      (N : ℂ) ^ k * KernelIntegrals.determinantIntegral (volume.restrict A) (rescaledS N) k := by
  let := isFiniteMeasure_area hA
  by_cases hk : k = 0
  · subst k
    simp
  · exact ite_eq_right hk

theorem determinantMoment_eq_scaledIntegral {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    determinantMoment A N k =
      KernelIntegrals.determinantIntegral (volume.restrict A) (scaledS N) k := by
  rw [determinantMoment_eq_normalized hA]
  exact (determinantIntegral_const_mul (volume.restrict A) (rescaledS N) (N : ℂ) k).symm

theorem cyclicTrace_eq_scaledIntegral (A : Set ℂ) (N m : ℕ) :
    cyclicTrace A N m =
      KernelIntegrals.cycleIntegral (volume.restrict A) (scaledS N) m :=
  (cycleIntegral_const_mul (volume.restrict A) (rescaledS N) (N : ℂ) m).symm

theorem determinantMoment_eq_maskedIntegral {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    determinantMoment A N k =
      KernelIntegrals.determinantIntegral (volume.restrict A) (maskedScaledS A N) k := by
  rw [maskedScaledS, determinantIntegral_mask volume A hA.1.measurableSet]
  exact determinantMoment_eq_scaledIntegral hA N k

theorem cyclicTrace_eq_maskedIntegral {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N m : ℕ) :
    cyclicTrace A N m =
      KernelIntegrals.cycleIntegral (volume.restrict A) (maskedScaledS A N) m := by
  rw [maskedScaledS, cycleIntegral_mask volume A hA.1.measurableSet]
  exact cyclicTrace_eq_scaledIntegral A N m

theorem measurable_maskedScaledS {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    Measurable (Function.uncurry (maskedScaledS A N)) :=
  measurable_maskKernel A hA.1.measurableSet _ (continuous_scaledS N).measurable

theorem exists_maskedScaledS_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z w, ‖maskedScaledS A N z w‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_scaledS_bound hA N
  exact ⟨C, norm_maskKernel_le A _ C
    (fun z hz w hw => hC z (subset_closure hz) w (subset_closure hw))⟩

theorem rescaledS_hermitian (N : ℕ) (z w : ℂ) :
    rescaledS N w z = conj (rescaledS N z w) :=
  S_hermitian N _ _

theorem determinantMoment_conj (A : Set ℂ) (N k : ℕ) :
    conj (determinantMoment A N k) = determinantMoment A N k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [determinantMoment, ite_eq_right hk, map_mul, map_pow, map_natCast,
      conj_determinantIntegral _ _ (rescaledS_hermitian N)]

theorem cyclicTrace_conj {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N m : ℕ) :
    conj (cyclicTrace A N m) = cyclicTrace A N m := by
  let := isFiniteMeasure_area hA
  rw [cyclicTrace, map_mul, map_pow, map_natCast,
    conj_cycleIntegral _ _ (rescaledS_hermitian N)]

theorem determinantMoment_im (A : Set ℂ) (N k : ℕ) : (determinantMoment A N k).im = 0 :=
  im_eq_zero_of_conj_eq (determinantMoment_conj A N k)

theorem cyclicTrace_im {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N m : ℕ) :
    (cyclicTrace A N m).im = 0 :=
  im_eq_zero_of_conj_eq (cyclicTrace_conj hA N m)

/-- Source L35, Stirling form, for the exact S_N kernel and normalization. -/
theorem determinantalPseudoCumulant_cycle_formula {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (N n : ℕ) :
    determinantalPseudoCumulant A N n =
      Cumulants.cycleStirlingTransform ℂ (cyclicTrace A N) n := by
  let := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_maskedScaledS_bound hA N
  have ht : KernelIntegrals.determinantIntegral (volume.restrict A) (maskedScaledS A N) =
      determinantMoment A N := funext fun k => (determinantMoment_eq_maskedIntegral hA N k).symm
  have hr : KernelIntegrals.cycleIntegral (volume.restrict A) (maskedScaledS A N) =
      cyclicTrace A N := funext fun m => (cyclicTrace_eq_maskedIntegral hA N m).symm
  have hh := Cumulants.pseudoCumulant_determinantIntegral (volume.restrict A)
    (maskedScaledS A N) (measurable_maskedScaledS hA N) C hC n
  rw [ht, hr] at hh
  exact hh

theorem determinantMoment_exponential {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    (PowerSeries.exp ℂ).subst
        (Cumulants.cycleLogSeries (Cumulants.signedCycleTrace (cyclicTrace A N))) =
      Cumulants.ordinaryEGF (determinantMoment A N) := by
  let := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_maskedScaledS_bound hA N
  have ht : KernelIntegrals.determinantIntegral (volume.restrict A) (maskedScaledS A N) =
      determinantMoment A N := funext fun k => (determinantMoment_eq_maskedIntegral hA N k).symm
  have hr : KernelIntegrals.cycleIntegral (volume.restrict A) (maskedScaledS A N) =
      cyclicTrace A N := funext fun m => (cyclicTrace_eq_maskedIntegral hA N m).symm
  have hh := Cumulants.determinantIntegral_exponential (volume.restrict A)
    (maskedScaledS A N) (measurable_maskedScaledS hA N) C hC
  rw [ht, hr] at hh
  exact hh

/-- Source L36 for the actual determinantal pseudo-cumulants. -/
theorem determinantalPseudoCumulant_recursion {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    determinantalPseudoCumulant A N n =
      (-1 : ℂ) ^ n * (n - 1).factorial * (cyclicTrace A N 1 - cyclicTrace A N n) +
        ∑ j ∈ Finset.Ico 2 n, -(Cumulants.signedStirling n j : ℂ) *
          determinantalPseudoCumulant A N j := by
  simp_rw [determinantalPseudoCumulant_cycle_formula hA N]
  exact Cumulants.cycleStirlingTransform_recursion ℂ (cyclicTrace A N) hn


/-- H_n commutes with ring homomorphisms; no reality or probability premise is hidden. -/
theorem pseudoCumulant_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (T : ℕ → R) (n : ℕ) :
    f (Cumulants.pseudoCumulant R T n) =
      Cumulants.pseudoCumulant S (fun k => f (T k)) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Cumulants.pseudoCumulant_eq_mobius T (Nat.one_le_iff_ne_zero.mpr hn),
      Cumulants.pseudoCumulant_eq_mobius _ (Nat.one_le_iff_ne_zero.mpr hn)]
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_prod]

theorem cycleStirlingTransform_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (trace : ℕ → R) (n : ℕ) :
    f (Cumulants.cycleStirlingTransform R trace n) =
      Cumulants.cycleStirlingTransform S (fun k => f (trace k)) n := by
  unfold Cumulants.cycleStirlingTransform Cumulants.stirlingSecondTransform
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m = 0
  · subst m
    simp [Cumulants.cycleWeight]
  · simp [Cumulants.cycleWeight, hm]

/-- The genuine real values of T_k; the embedding theorem below proves that
taking the real part changes no value of the source complex integral. -/
def realDeterminantMoment (A : Set ℂ) (N k : ℕ) : ℝ := (determinantMoment A N k).re

def realCyclicTrace (A : Set ℂ) (N m : ℕ) : ℝ := (cyclicTrace A N m).re

def realDeterminantalPseudoCumulant (A : Set ℂ) (N n : ℕ) : ℝ :=
  Cumulants.pseudoCumulant ℝ (realDeterminantMoment A N) n

theorem ofReal_realDeterminantMoment (A : Set ℂ) (N k : ℕ) :
    (realDeterminantMoment A N k : ℂ) = determinantMoment A N k := by
  apply Complex.ext
  · rfl
  · exact (determinantMoment_im A N k).symm

theorem ofReal_realCyclicTrace {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N m : ℕ) :
    (realCyclicTrace A N m : ℂ) = cyclicTrace A N m := by
  apply Complex.ext
  · rfl
  · exact (cyclicTrace_im hA N m).symm

theorem ofReal_realDeterminantalPseudoCumulant (A : Set ℂ) (N n : ℕ) :
    (realDeterminantalPseudoCumulant A N n : ℂ) = determinantalPseudoCumulant A N n := by
  have hh := pseudoCumulant_map (algebraMap ℝ ℂ) (realDeterminantMoment A N) n
  have ht : (fun k => (realDeterminantMoment A N k : ℂ)) = determinantMoment A N :=
    funext fun k => ofReal_realDeterminantMoment A N k
  change (Cumulants.pseudoCumulant ℝ (realDeterminantMoment A N) n : ℂ) =
    Cumulants.pseudoCumulant ℂ (fun k => (realDeterminantMoment A N k : ℂ)) n at hh
  rw [ht] at hh
  exact hh

/-- Source L35 in genuine real scalars, with all traces and moments still tied
to their original integral definitions by the preceding embedding theorems. -/
theorem realDeterminantalPseudoCumulant_cycle_formula {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (N n : ℕ) :
    realDeterminantalPseudoCumulant A N n =
      Cumulants.cycleStirlingTransform ℝ (realCyclicTrace A N) n := by
  have hh := cycleStirlingTransform_map (algebraMap ℝ ℂ) (realCyclicTrace A N) n
  have hr : (fun m => (realCyclicTrace A N m : ℂ)) = cyclicTrace A N :=
    funext fun m => ofReal_realCyclicTrace hA N m
  change (Cumulants.cycleStirlingTransform ℝ (realCyclicTrace A N) n : ℂ) =
    Cumulants.cycleStirlingTransform ℂ (fun m => (realCyclicTrace A N m : ℂ)) n at hh
  rw [hr] at hh
  apply Complex.ofReal_injective
  rw [ofReal_realDeterminantalPseudoCumulant, determinantalPseudoCumulant_cycle_formula hA]
  exact hh.symm

/-- Source L36 in genuine real scalars. -/
theorem realDeterminantalPseudoCumulant_recursion {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    realDeterminantalPseudoCumulant A N n =
      (-1 : ℝ) ^ n * (n - 1).factorial * (realCyclicTrace A N 1 - realCyclicTrace A N n) +
        ∑ j ∈ Finset.Ico 2 n, -(Cumulants.signedStirling n j : ℝ) *
          realDeterminantalPseudoCumulant A N j := by
  simp_rw [realDeterminantalPseudoCumulant_cycle_formula hA N]
  exact Cumulants.cycleStirlingTransform_recursion ℝ (realCyclicTrace A N) hn

end Paper.Kernel
