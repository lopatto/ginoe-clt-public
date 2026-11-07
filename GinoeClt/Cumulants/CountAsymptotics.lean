/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.CountKernelComparison
public import GinoeClt.Cumulants.DeterminantalAsymptotics

/-! # Count-cumulant asymptotics parameterized by the finite factorial-moment identity

The finite factorial-moment identity is an explicit proof parameter here. It is
proved and supplied in SkewOrthogonal.CountPfaffianIdentity, which exports the
resulting unconditional cumulant limits.
-/

@[expose] public section
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Paper

/-- The weak manuscript bound for actual raw-count cumulants, parameterized by the finite factorial-moment identity. -/
theorem countCumulant_bigO_of_momentIdentity {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A)
    {r : ℕ} (hr : 2 ≤ r) :
    (fun m : ℕ => countCumulant A m r) =O[atTop] Cumulants.sizePower (5 / 8) := by
  obtain ⟨c, hc, hE⟩ := countCumulant_determinantal_exp_close hA hLaw
  have he : (fun m : ℕ => Real.exp (-c * (m + 1 : ℝ))) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    apply (Trace.sizePow_exp_bigO_one hc 0).congr_left
    intro m
    simp only [pow_zero, one_mul]
  have hone : (fun _ : ℕ => (1 : ℝ)) =O[atTop] Cumulants.sizePower (5 / 8) := by
    apply (Cumulants.sizePower_mono_bigO (by norm_num : (0 : ℝ) ≤ 5 / 8)).congr_left
    intro m
    simp only [Cumulants.sizePower, Real.rpow_zero]
  have hp := Kernel.realDeterminantalPseudoCumulant_bigO hA
    (by norm_num : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 2)) r hr
  have hp' : (fun m : ℕ => Kernel.realDeterminantalPseudoCumulant A (m + 1) r) =O[atTop]
      Cumulants.sizePower (5 / 8) := by
    norm_num at hp
    exact hp
  have hh := (((hE r (by omega : 1 ≤ r)).trans he).trans hone).add hp'
  apply hh.congr_left
  intro m
  ring

theorem normalized_countCumulant_tendsto_zero_of_momentIdentity {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A)
    {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun m : ℕ => (((m + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ r * countCumulant A m r)
      atTop (𝓝 0) :=
  Cumulants.normalized_fiveEighths_tendsto_zero hr
    (countCumulant_bigO_of_momentIdentity hA hLaw (by omega : 2 ≤ r))

/-- Exact centering/scaling is the reviewed analytic-cgf normalization. -/
theorem cumulant_tendsto_zero_of_momentIdentity {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A)
    {r : ℕ} (hr : 3 ≤ r) :
    Tendsto (fun m : ℕ => cumulant A m r) atTop (𝓝 0) := by
  have he : (fun m : ℕ => cumulant A m r) =
      (fun m : ℕ => (((m + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ r * countCumulant A m r) :=
    funext fun m => cumulant_eq_countCumulant (countMeasurable_of_isOpen A hA.1) m r
      (by omega : 2 ≤ r)
  rw [he]
  exact normalized_countCumulant_tendsto_zero_of_momentIdentity hA hLaw hr

end Paper
