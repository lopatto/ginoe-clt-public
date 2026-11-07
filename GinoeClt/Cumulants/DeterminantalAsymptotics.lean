/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.Asymptotics

/-! # The manuscript's pseudo-cumulant recursion and weak trace bound -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators

namespace Paper.Kernel

lemma realCyclicTrace_sub_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) {r : ℕ} (hr : 1 ≤ r) :
    (fun m : ℕ => realCyclicTrace A (m + 1) 1 - realCyclicTrace A (m + 1) r) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hh := (Trace.realCyclicTrace_area_error_bigO hA hδ 0).sub
    (Trace.realCyclicTrace_area_error_bigO hA hδ n)
  apply hh.congr_left
  intro m
  ring

/-- The original recursion yields the original weak bound at every fixed order. -/
theorem realDeterminantalPseudoCumulant_bigO {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) {δ : ℝ}
    (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) :
    ∀ r : ℕ, 2 ≤ r →
      (fun m : ℕ => realDeterminantalPseudoCumulant A (m + 1) r) =O[atTop]
        Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  let u : ℕ → ℕ → ℝ := fun r m => realDeterminantalPseudoCumulant A (m + 1) r
  let leading : ℕ → ℕ → ℝ := fun r m =>
    (-1 : ℝ) ^ r * (r - 1).factorial *
      (realCyclicTrace A (m + 1) 1 - realCyclicTrace A (m + 1) r)
  let coeff : ℕ → ℕ → ℝ := fun r j => -(Cumulants.signedStirling r j : ℝ)
  have h2 : u 2 =O[atTop] Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
    apply (realCyclicTrace_sub_bigO hA hδ (by decide : 1 ≤ 2)).congr_left
    intro m
    dsimp only [u]
    rw [realDeterminantalPseudoCumulant_cycle_formula hA,
      Cumulants.cycleStirlingTransform_two]
  have hl : ∀ r, 3 ≤ r → leading r =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
    intro r hr
    exact (realCyclicTrace_sub_bigO hA hδ (by omega : 1 ≤ r)).const_mul_left
      ((-1 : ℝ) ^ r * (r - 1).factorial)
  have hrec : ∀ r, 3 ≤ r → ∀ m,
      u r m = leading r m + ∑ j ∈ Finset.Ico 2 r, coeff r j * u j m := by
    intro r hr m
    exact realDeterminantalPseudoCumulant_recursion hA (m + 1) (by omega : 2 ≤ r)
  exact Cumulants.triangular_recursion_bigO u _ leading coeff h2 hl hrec

/-- The conclusion uses delta=1/8; the cyclic-cancellation refinement is unnecessary. -/
theorem normalized_realDeterminantalPseudoCumulant_tendsto_zero {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun m : ℕ => (((m + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ r *
      realDeterminantalPseudoCumulant A (m + 1) r) atTop (𝓝 0) := by
  apply Cumulants.normalized_fiveEighths_tendsto_zero hr
  have hh := realDeterminantalPseudoCumulant_bigO hA
    (by norm_num : (1 / 8 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2)) r (by omega : 2 ≤ r)
  norm_num at hh
  exact hh

end Paper.Kernel
