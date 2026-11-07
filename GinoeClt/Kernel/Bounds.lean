/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Definitions
public import GinoeClt.Geometry.BoundaryLength
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Fixed-N kernel bounds on compact admissible closures

These compactness bounds may depend on N and A. They assert no uniform
asymptotic kernel estimate.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace Paper.Kernel

theorem compact_kernel_bound {A : Set ℂ} (hA : IsCompact A)
    (K : ℂ → ℂ → ℂ) (hK : ContinuousOn (Function.uncurry K) (A ×ˢ A)) :
    ∃ C : ℝ≥0, ∀ z ∈ A, ∀ w ∈ A, ‖K z w‖ ≤ C := by
  obtain ⟨B, hB⟩ := (hA.prod hA).exists_bound_of_continuousOn hK
  refine ⟨⟨max B 0, le_max_right _ _⟩, ?_⟩
  intro z hz w hw
  exact (hB (z, w) ⟨hz, hw⟩).trans (le_max_left _ _)

theorem admissible_closure_isCompact {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    IsCompact (closure A) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure (admissible_isBounded hA).closure

theorem isFiniteMeasure_area {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    IsFiniteMeasure (volume.restrict A) :=
  isFiniteMeasure_restrict.mpr (admissible_isBounded hA).measure_lt_top.ne

theorem continuous_rescaledKernel (K : ℂ → ℂ → ℂ)
    (hK : Continuous (Function.uncurry K)) (N : ℕ) :
    Continuous (Function.uncurry (fun z w => K (rescale N z) (rescale N w))) :=
  hK.comp (((continuous_rescale N).comp continuous_fst).prodMk
    ((continuous_rescale N).comp continuous_snd))

theorem exists_S_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z ∈ closure A, ∀ w ∈ closure A,
      ‖S N (rescale N z) (rescale N w)‖ ≤ C :=
  compact_kernel_bound (admissible_closure_isCompact hA) _
    (continuous_rescaledKernel _ (continuous_S N) N).continuousOn

theorem exists_D_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z ∈ closure A, ∀ w ∈ closure A,
      ‖D N (rescale N z) (rescale N w)‖ ≤ C :=
  compact_kernel_bound (admissible_closure_isCompact hA) _
    (continuous_rescaledKernel _ (continuous_D N) N).continuousOn

theorem exists_I_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z ∈ closure A, ∀ w ∈ closure A,
      ‖I N (rescale N z) (rescale N w)‖ ≤ C :=
  compact_kernel_bound (admissible_closure_isCompact hA) _
    (continuous_rescaledKernel _ (continuous_I N) N).continuousOn

theorem exists_scaledS_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z ∈ closure A, ∀ w ∈ closure A, ‖scaledS N z w‖ ≤ C :=
  compact_kernel_bound (admissible_closure_isCompact hA) _ (continuous_scaledS N).continuousOn

theorem exists_U_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    ∃ C : ℝ≥0, ∀ z ∈ closure A, ∀ w ∈ closure A, ‖U N z w‖ ≤ C := by
  apply compact_kernel_bound (admissible_closure_isCompact hA)
  intro x hx
  exact (continuousAt_U N (hA.2.2.1 hx.1).2 (hA.2.2.1 hx.2).2).continuousWithinAt

end Paper.Kernel
