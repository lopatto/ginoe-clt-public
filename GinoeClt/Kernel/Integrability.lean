/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Specialization

/-! # Integrability of the actual unmasked S_N products and determinants -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal Classical

namespace Paper.Kernel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι]

theorem permutationIntegrand_mask_ae (μ : Measure Ω) [SigmaFinite μ]
    (A : Set Ω) (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) :
    KernelIntegrals.permutationIntegrand (maskKernel A K) σ =ᵐ[
      Measure.pi (fun _ : ι => μ.restrict A)] KernelIntegrals.permutationIntegrand K σ := by
  filter_upwards [ae_coords_mem (ι := ι) μ A hA] with x hx
  unfold KernelIntegrals.permutationIntegrand
  exact Finset.prod_congr rfl fun i _ => maskKernel_eq_of_mem A K (hx i) (hx (σ i))

theorem determinantIntegrand_mask_ae (μ : Measure Ω) [SigmaFinite μ]
    (A : Set Ω) (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (k : ℕ) :
    (fun x : Fin k → Ω => Matrix.det (KernelIntegrals.kernelMatrix (maskKernel A K) x)) =ᵐ[
      Measure.pi (fun _ : Fin k => μ.restrict A)]
        fun x => Matrix.det (KernelIntegrals.kernelMatrix K x) := by
  filter_upwards [ae_coords_mem (ι := Fin k) μ A hA] with x hx
  congr 1
  ext i j
  exact maskKernel_eq_of_mem A K (hx i) (hx j)

theorem integrable_restricted_permutationIntegrand
    (μ : Measure Ω) [SigmaFinite μ] {A : Set Ω} [IsFiniteMeasure (μ.restrict A)]
    (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0) (hbound : ∀ x ∈ A, ∀ y ∈ A, ‖K x y‖ ≤ C) (σ : Equiv.Perm ι) :
    Integrable (KernelIntegrals.permutationIntegrand K σ)
      (Measure.pi (fun _ : ι => μ.restrict A)) :=
  (KernelIntegrals.integrable_permutationIntegrand (μ.restrict A) (maskKernel A K)
    (measurable_maskKernel A hA K hK) C (norm_maskKernel_le A K C hbound) σ).congr
      (permutationIntegrand_mask_ae μ A hA K σ)

theorem integrable_restricted_determinantIntegrand
    (μ : Measure Ω) [SigmaFinite μ] {A : Set Ω} [IsFiniteMeasure (μ.restrict A)]
    (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0) (hbound : ∀ x ∈ A, ∀ y ∈ A, ‖K x y‖ ≤ C) (k : ℕ) :
    Integrable (fun x : Fin k → Ω => Matrix.det (KernelIntegrals.kernelMatrix K x))
      (Measure.pi (fun _ : Fin k => μ.restrict A)) :=
  (KernelIntegrals.integrable_determinantIntegrand (μ.restrict A) (maskKernel A K)
    (measurable_maskKernel A hA K hK) C (norm_maskKernel_le A K C hbound)).congr
      (determinantIntegrand_mask_ae μ A hA K k)

theorem measurable_rescaledS (N : ℕ) : Measurable (Function.uncurry (rescaledS N)) :=
  (continuous_rescaledKernel _ (continuous_S N) N).measurable

theorem integrable_rescaledS_permutation {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N : ℕ) (σ : Equiv.Perm ι) :
    Integrable (KernelIntegrals.permutationIntegrand (rescaledS N) σ)
      (Measure.pi (fun _ : ι => (volume : Measure ℂ).restrict A)) := by
  let := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_S_bound hA N
  exact integrable_restricted_permutationIntegrand volume hA.1.measurableSet _ (measurable_rescaledS N)
    C (fun z hz w hw => hC z (subset_closure hz) w (subset_closure hw)) σ

theorem integrable_rescaledS_determinant {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    Integrable (fun x : Fin k → ℂ => Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) x))
      (Measure.pi (fun _ : Fin k => (volume : Measure ℂ).restrict A)) := by
  let := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_S_bound hA N
  exact integrable_restricted_determinantIntegrand volume hA.1.measurableSet _ (measurable_rescaledS N)
    C (fun z hz w hw => hC z (subset_closure hz) w (subset_closure hw)) k

theorem integrable_scaledS_permutation {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N : ℕ) (σ : Equiv.Perm ι) :
    Integrable (KernelIntegrals.permutationIntegrand (scaledS N) σ)
      (Measure.pi (fun _ : ι => (volume : Measure ℂ).restrict A)) := by
  let := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_scaledS_bound hA N
  exact integrable_restricted_permutationIntegrand volume hA.1.measurableSet _ (continuous_scaledS N).measurable
    C (fun z hz w hw => hC z (subset_closure hz) w (subset_closure hw)) σ

theorem integrable_scaledS_determinant {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    Integrable (fun x : Fin k → ℂ => Matrix.det (KernelIntegrals.kernelMatrix (scaledS N) x))
      (Measure.pi (fun _ : Fin k => (volume : Measure ℂ).restrict A)) := by
  let := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_scaledS_bound hA N
  exact integrable_restricted_determinantIntegrand volume hA.1.measurableSet _ (continuous_scaledS N).measurable
    C (fun z hz w hw => hC z (subset_closure hz) w (subset_closure hw)) k

theorem integrableOn_source_determinant {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    IntegrableOn (fun x : Fin k → ℂ => Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) x))
      (Set.univ.pi (fun _ => A)) (Measure.pi (fun _ : Fin k => (volume : Measure ℂ))) := by
  rw [IntegrableOn, Measure.restrict_pi_pi]
  exact integrable_rescaledS_determinant hA N k

theorem integrableOn_source_cycle {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N m : ℕ) :
    IntegrableOn (fun x : Fin m → ℂ =>
      ∏ i, S N (rescale N (x i)) (rescale N (x (finRotate m i))))
      (Set.univ.pi (fun _ => A)) (Measure.pi (fun _ : Fin m => (volume : Measure ℂ))) := by
  rw [IntegrableOn, Measure.restrict_pi_pi]
  exact integrable_rescaledS_permutation hA N (finRotate m)

end Paper.Kernel
