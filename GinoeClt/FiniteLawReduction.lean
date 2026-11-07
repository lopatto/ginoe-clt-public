/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.CLT
public import GinoeClt.Cumulants.CountAsymptotics
public import GinoeClt.Analysis.PseudoVariance

/-! # The remaining finite-law reduction

These conditional reductions isolate the finite factorial-moment identity.
It is proved and supplied in SkewOrthogonal.CountPfaffianIdentity, which gives
the unconditional main theorem. No external mathematical result is assumed.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace Paper

lemma varianceOfLength_coe (ell : ℝ≥0) :
    (varianceOfLength ell : ℝ) = (ell : ℝ) / (2 * Real.pi ^ (3 / 2 : ℝ)) := by
  simp only [varianceOfLength, NNReal.coe_div]
  rw [Real.coe_toNNReal _ (by positivity)]

/-- All analytic asymptotic work is reduced to the explicitly open finite law. -/
theorem cumulantLimits_of_momentIdentity {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A)
    (ell : ℝ≥0) (hell : (ell : ℝ≥0∞) = boundaryMeasure A) : CumulantLimits A ell := by
  have hlen : (boundaryMeasure A).toReal = (ell : ℝ) := by rw [← hell]; simp
  intro r hr
  by_cases hr2 : r = 2
  · subst r
    have hh := cumulant_two_tendsto_of_finiteLaw hA hLaw
    change Tendsto (fun n : ℕ => cumulant A n 2) atTop (𝓝 (varianceOfLength ell : ℝ))
    rw [varianceOfLength_coe, ← hlen]
    exact hh
  · by_cases hr1 : r = 1
    · subst r
      have he : (fun n : ℕ => cumulant A n 1) = fun _ => (0 : ℝ) :=
        funext fun n => cumulant_one (countMeasurable_of_isOpen A hA.1) n
      rw [he]
      simpa only [pairCumulant, ite_eq_right (by decide : (1 : ℕ) ≠ 2)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [pairCumulant, ite_eq_right hr2] using
        cumulant_tendsto_zero_of_momentIdentity hA hLaw (by omega : 3 ≤ r)

/-- CLT reduction parameterized by the finite factorial-moment identity. -/
theorem mainTheorem_of_momentIdentity (A : Set ℂ)
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    MainConclusion A := by
  apply mainTheorem_of_cumulantLimits A hA
  intro ell hell _hpos
  exact cumulantLimits_of_momentIdentity hA hLaw ell hell

end Paper
