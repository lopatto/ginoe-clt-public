/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.AnalyticCumulants
public import GinoeClt.Cumulants.AnalyticMobius
public import GinoeClt.Cumulants.PseudoCumulants
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Topology.Algebra.Polynomial

/-! # Actual factorial moments of the finite multiplicity count -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace Paper

/-- Falling-factorial moment of the actual count, before a correlation-density
or determinant approximation is used. The empty factorial moment is one. -/
def countFactorialMoment (A : Set ℂ) (n k : ℕ) : ℝ :=
  ∫ M : SampleSpace n, ((count A n M).descFactorial k : ℝ) ∂matrixLaw n

theorem count_descFactorial_measurable {A : Set ℂ} (h : CountMeasurable A) (n k : ℕ) :
    Measurable (fun M : SampleSpace n => ((count A n M).descFactorial k : ℝ)) := by
  have hh := (descPochhammer ℝ k).continuous.measurable.comp (h n)
  simpa only [Function.comp_def, descPochhammer_eval_eq_descFactorial] using hh

theorem count_descFactorial_integrable {A : Set ℂ} (h : CountMeasurable A) (n k : ℕ) :
    Integrable (fun M : SampleSpace n => ((count A n M).descFactorial k : ℝ))
      (matrixLaw n) := by
  apply (integrable_const ((n + 1 : ℝ) ^ k)).mono'
    (count_descFactorial_measurable h n k).aestronglyMeasurable
  apply ae_of_all
  intro M
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.descFactorial_le_pow (count A n M) k).trans
    (Nat.pow_le_pow_left (count_le A n M) k)

@[simp] theorem countFactorialMoment_zero (A : Set ℂ) (n : ℕ) :
    countFactorialMoment A n 0 = 1 := by
  simp [countFactorialMoment]

theorem count_moment_eq_stirling {A : Set ℂ} (h : CountMeasurable A) (n j : ℕ) :
    (∫ M : SampleSpace n, (count A n M : ℝ) ^ j ∂matrixLaw n) =
      ∑ k ∈ Finset.range (j + 1), (Nat.stirlingSecond j k : ℝ) *
        countFactorialMoment A n k := by
  have hfun : (fun M : SampleSpace n => (count A n M : ℝ) ^ j) =
      fun M => ∑ k ∈ Finset.range (j + 1), (Nat.stirlingSecond j k : ℝ) *
        ((count A n M).descFactorial k : ℝ) := by
    funext M
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (count A n M) j
  rw [hfun, integral_finsetSum _ (fun k _ =>
    (count_descFactorial_integrable h n k).const_mul _)]
  simp only [integral_const_mul, countFactorialMoment]

theorem count_moment_eq_stirling_pos {A : Set ℂ} (h : CountMeasurable A)
    (n j : ℕ) (hj : 1 ≤ j) :
    (∫ M : SampleSpace n, (count A n M : ℝ) ^ j ∂matrixLaw n) =
      ∑ k ∈ Finset.Icc 1 j, (Nat.stirlingSecond j k : ℝ) *
        countFactorialMoment A n k := by
  rw [count_moment_eq_stirling h n j]
  symm
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
  · intro k hk hnot
    have hk0 : k = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    subst k
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
    simp

/-- The source H_n evaluated at the genuine finite-count factorial moments
equals the genuine analytic raw-count cumulant. No ensemble law is assumed. -/
theorem countCumulant_eq_pseudoCumulant {A : Set ℂ} (h : CountMeasurable A)
    (n r : ℕ) (hr : 1 ≤ r) :
    countCumulant A n r =
      Cumulants.pseudoCumulant ℝ (countFactorialMoment A n) r := by
  rw [countCumulant,
    Cumulants.cumulant_eq_mobius _ _ (count_mem_interior_integrableExpSet h n 0) hr,
    Cumulants.pseudoCumulant_eq_mobius _ hr]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  exact count_moment_eq_stirling_pos h n B.card
    (Finset.one_le_card.mpr (P.nonempty_of_mem_parts hB))

end Paper
