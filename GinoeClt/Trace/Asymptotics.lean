/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.CrossingAsymptotics
public import GinoeClt.Trace.KernelComparison
public import GinoeClt.Analysis.VarianceKernel

/-! # The original weak cyclic-trace asymptotics -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators

namespace Paper.Trace

/-- Lemma 3.7's higher-order estimate, retaining every delta in (0,1/2). -/
theorem cyclicTrace_area_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) (n : ℕ) :
    (fun m : ℕ => Kernel.cyclicTrace A (m + 1) (n + 1) -
      (((m + 1 : ℕ) : ℂ) * (volume.real A : ℂ) / (Real.pi : ℂ))) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  have hc := (scaled_cycleIntegral_error_bigO hA n).trans
    (Cumulants.sizePower_mono_bigO (by linarith only [hδ.1] : (1 / 2 : ℝ) ≤ 1 / 2 + δ))
  have hh := (cyclicTrace_leading_error_bigO hA hδ n).add hc
  apply hh.congr_left
  intro m
  push_cast
  ring

lemma cyclicTrace_one_eq {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    Kernel.cyclicTrace A N 1 = (N : ℂ) *
      ∫ z in A, Kernel.S N (Kernel.rescale N z) (Kernel.rescale N z) := by
  let : IsFiniteMeasure (volume.restrict A) := Kernel.isFiniteMeasure_area hA
  rw [Kernel.cyclicTrace, KernelIntegrals.cycleIntegral_one]
  simp only [pow_one, Kernel.rescaledS]

/-- The stronger O(1) diagonal assertion in the same source lemma. -/
theorem cyclicTrace_one_area_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    (fun N : ℕ => Kernel.cyclicTrace A N 1 -
      (((N : ℝ) / Real.pi * volume.real A : ℝ) : ℂ)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  apply (Kernel.diagonalKernelError_bigO hA).congr_left
  intro N
  rw [cyclicTrace_one_eq hA]
  rfl

lemma ofReal_realCyclicTrace_area_error {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (N k : ℕ) :
    ((Kernel.realCyclicTrace A N k - (N : ℝ) * volume.real A / Real.pi : ℝ) : ℂ) =
      Kernel.cyclicTrace A N k - (N : ℂ) * (volume.real A : ℂ) / (Real.pi : ℂ) := by
  rw [Complex.ofReal_sub, Kernel.ofReal_realCyclicTrace hA]
  push_cast
  rfl

/-- The real source R_k is unchanged: its reality was proved, not assumed. -/
theorem realCyclicTrace_area_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) (n : ℕ) :
    (fun m : ℕ => Kernel.realCyclicTrace A (m + 1) (n + 1) -
      (m + 1 : ℝ) * volume.real A / Real.pi) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  apply IsBigO.of_norm_left
  apply (cyclicTrace_area_error_bigO hA hδ n).norm_left.congr_left
  intro m
  rw [← ofReal_realCyclicTrace_area_error hA, Complex.norm_real, Real.norm_eq_abs]
  push_cast
  rfl

theorem realCyclicTrace_one_area_error_bigO {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) :
    (fun N : ℕ => Kernel.realCyclicTrace A N 1 -
      (N : ℝ) * volume.real A / Real.pi) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  apply IsBigO.of_norm_left
  apply (cyclicTrace_one_area_error_bigO hA).norm_left.congr_left
  intro N
  have he := ofReal_realCyclicTrace_area_error hA N 1
  have he' : ((Kernel.realCyclicTrace A N 1 - (N : ℝ) * volume.real A / Real.pi : ℝ) : ℂ) =
      Kernel.cyclicTrace A N 1 - (((N : ℝ) / Real.pi * volume.real A : ℝ) : ℂ) := by
    rw [he]
    push_cast
    ring
  rw [← he', Complex.norm_real, Real.norm_eq_abs]

end Paper.Trace
