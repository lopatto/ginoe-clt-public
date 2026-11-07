/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.CountFactorialMoments
public import GinoeClt.Cumulants.ExponentialComparison
public import GinoeClt.Kernel.PfaffianApproximation
public import GinoeClt.Spectral.Count

/-! # Conditional count-to-kernel reduction

The finite GinOE correlation identity is not proved here. The named input below
is the genuine factorial-moment consequence of the manuscript's correlation
identity and Pfaffian formula, including its area Jacobian. Its eventual,
fixed-order scope suffices for this asymptotic reduction; it does not replace
the full correlation-function theorem. No external result is assumed globally.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Paper

/-- Open finite-ensemble input: the actual real factorial moment, embedded in
ℂ, equals the literal complex Pfaffian integral. This is the fixed-order
eventual consequence of manuscript (corrdef), (pfcorr), and the scaling
Jacobian. It is an explicit proof parameter, not an approved assumption. -/
def CountPfaffianMomentIdentity (A : Set ℂ) : Prop :=
  ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
    (countFactorialMoment A n k : ℂ) = Kernel.pfaffianKernelMoment A (n + 1) k

theorem countFactorialMoment_nonneg (A : Set ℂ) (n k : ℕ) :
    0 ≤ countFactorialMoment A n k :=
  integral_nonneg fun _ => Nat.cast_nonneg _

theorem countFactorialMoment_le {A : Set ℂ} (h : CountMeasurable A) (n k : ℕ) :
    countFactorialMoment A n k ≤ (n + 1 : ℝ) ^ k := by
  have hh : ∀ M : SampleSpace n, ((count A n M).descFactorial k : ℝ) ≤
      (n + 1 : ℝ) ^ k := by
    intro M
    exact_mod_cast (Nat.descFactorial_le_pow (count A n M) k).trans
      (Nat.pow_le_pow_left (count_le A n M) k)
  calc
    countFactorialMoment A n k ≤ ∫ _ : SampleSpace n, (n + 1 : ℝ) ^ k ∂matrixLaw n :=
      integral_mono (count_descFactorial_integrable h n k) (integrable_const _) hh
    _ = (n + 1 : ℝ) ^ k := by simp

theorem countFactorialMoment_powerBound {A : Set ℂ} (h : CountMeasurable A) (k : ℕ) :
    ExponentialErrors.PowerBound (fun n => countFactorialMoment A n k) := by
  refine ⟨k, IsBigO.of_norm_le fun n => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (countFactorialMoment_nonneg A n k)]
  simpa only [Cumulants.sizePower, Real.rpow_natCast] using countFactorialMoment_le h n k

/-- Dropping exponential decay gives a polynomial growth bound, without
spending any part of its rate. -/
theorem expPowerBound_powerBound {c : ℝ} (hc : 0 < c) {f : ℕ → ℝ}
    (h : ExponentialErrors.ExpPowerBound c f) : ExponentialErrors.PowerBound f := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ha.trans (IsBigO.of_norm_le fun n => ?_)⟩
  have he : Real.exp (-c * (n + 1 : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hn : 0 ≤ (n + 1 : ℝ) := by positivity
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hc.le hn)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hp : 0 ≤ Cumulants.sizePower a n := by
    unfold Cumulants.sizePower
    positivity
  rw [abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left he hp).trans_eq (mul_one _)

/-- Conditional on the actual finite-ensemble identity, the real determinant
moments approximate the actual factorial moments at the unchanged common
exponential rate. The Pfaffian moments are not projected to real parts. -/
theorem realDeterminantMoment_count_expPowerBound {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ExponentialErrors.ExpPowerBound c
      (fun n => Kernel.realDeterminantMoment A (n + 1) k - countFactorialMoment A n k) := by
  obtain ⟨c, hc, hE⟩ := Kernel.pfaffianKernelMoment_det_expPowerBound hA
  refine ⟨c, hc, fun k => ?_⟩
  obtain ⟨a, ha⟩ := hE k
  refine ⟨a, (IsBigO.of_bound' ?_).trans ha⟩
  filter_upwards [hLaw k] with n hn
  have hz : ((Kernel.realDeterminantMoment A (n + 1) k -
      countFactorialMoment A n k : ℝ) : ℂ) =
      Kernel.determinantMoment A (n + 1) k - Kernel.pfaffianKernelMoment A (n + 1) k := by
    rw [Complex.ofReal_sub, Kernel.ofReal_realDeterminantMoment, hn]
  rw [norm_norm, ← Complex.norm_real, hz, norm_sub_rev]

theorem realDeterminantMoment_powerBound {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) (k : ℕ) :
    ExponentialErrors.PowerBound (fun n => Kernel.realDeterminantMoment A (n + 1) k) := by
  obtain ⟨c, hc, hE⟩ := realDeterminantMoment_count_expPowerBound hA hLaw
  have hJ := countFactorialMoment_powerBound (countMeasurable_of_isOpen A hA.1) k
  have hD := expPowerBound_powerBound hc (hE k)
  have hh := hJ.add hD
  convert hh using 1
  funext n
  ring

/-- The source L33 comparison, conditional only on the explicitly displayed
open finite-ensemble identity. Polynomial propagation spends the rate once,
after H_r is evaluated; the resulting rate is independent of fixed r. -/
theorem countCumulant_determinantal_exp_close {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r →
      (fun n => countCumulant A n r -
        Kernel.realDeterminantalPseudoCumulant A (n + 1) r) =O[atTop]
          fun n => Real.exp (-c * (n + 1 : ℝ)) := by
  obtain ⟨c, hc, hE⟩ := realDeterminantMoment_count_expPowerBound hA hLaw
  have hMeas := countMeasurable_of_isOpen A hA.1
  refine ⟨c / 2, by positivity, fun r hr => ?_⟩
  have hh := Cumulants.pseudoCumulant_exp_close hc
    (fun k n => Kernel.realDeterminantMoment A (n + 1) k)
    (fun k n => countFactorialMoment A n k)
    (realDeterminantMoment_powerBound hA hLaw)
    (countFactorialMoment_powerBound hMeas) hE r
  have hn := hh.neg_left
  convert hn using 1
  funext n
  rw [countCumulant_eq_pseudoCumulant hMeas n r hr]
  unfold Kernel.realDeterminantalPseudoCumulant
  ring

end Paper
