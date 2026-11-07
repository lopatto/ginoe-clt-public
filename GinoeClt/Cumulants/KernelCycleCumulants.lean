/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.SupportCycleFactorization
public import GinoeClt.Cumulants.CycleIndexEGF
public import GinoeClt.Cumulants.StirlingRecursion

/-! # Pseudo-cumulants of actual determinant integrals

This joins the literal H_n polynomial to the signed cycle-index identity.
All determinant and trace sequences are the actual product integrals of the kernel.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries NNReal Classical

namespace Paper.Cumulants
variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem pseudoCumulant_eq_formalFactorialLog (T : ℕ → R) (h0 : T 0 = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    pseudoCumulant R T n =
      (n.factorial : R) * PowerSeries.coeff n
        (PowerSeries.logOf ((ordinaryEGF T).subst (expMinusOne (R := R)))) := by
  rw [ordinaryEGF_subst_expMinusOne, formal_log_coeff _ (by simp [h0]) hn,
    pseudoCumulant_eq_mobius T hn]
  apply Finset.sum_congr rfl
  intro P _
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
  · intro k hk hnot
    have hk0 : k = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range] at *
      omega
    subst k
    have hB0 : B.card ≠ 0 := Finset.card_ne_zero.mpr (P.nonempty_of_mem_parts hB)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hB0
    simp [hj]

theorem logOf_subst (F G : PowerSeries R) (hF : PowerSeries.constantCoeff F = 1)
    (hG : PowerSeries.HasSubst G) :
    PowerSeries.logOf (F.subst G) = (PowerSeries.logOf F).subst G := by
  have hs : PowerSeries.HasSubst (F - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hF])
  have hone : (1 : PowerSeries R).subst G = 1 := by
    rw [← PowerSeries.coe_substAlgHom (R := R) hG]
    exact map_one (PowerSeries.substAlgHom (R := R) hG)
  rw [PowerSeries.logOf_eq, PowerSeries.logOf_eq,
    PowerSeries.subst_comp_subst_apply hs hG (PowerSeries.log R),
    PowerSeries.subst_sub hG, hone]


theorem factorial_coeff_cycleLog_subst (trace : ℕ → R) (n : ℕ) :
    (n.factorial : R) * PowerSeries.coeff n
        ((cycleLogSeries (signedCycleTrace trace)).subst (expMinusOne (R := R))) =
      cycleStirlingTransform R trace n := by
  have he : PowerSeries.HasSubst (expMinusOne (R := R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_expMinusOne
  rw [PowerSeries.coeff_subst' he]
  simp only [smul_eq_mul]
  have hs :
      Function.support (fun m => PowerSeries.coeff m (cycleLogSeries (signedCycleTrace trace)) *
        PowerSeries.coeff n ((expMinusOne (R := R)) ^ m)) ⊆
          (Finset.range (n + 1) : Set ℕ) := by
    intro m hm
    by_contra hmn
    have hnm : n < m := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hmn
      omega
    have hz := Nat.stirlingSecond_eq_zero_of_lt hnm
    rw [Function.mem_support, coeff_expMinusOne_pow, hz,
      Nat.cast_zero, mul_zero, mul_zero] at hm
    exact hm rfl
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.mul_sum, cycleStirlingTransform, stirlingSecondTransform]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m = 0
  · subst m
    simp [cycleLogSeries, cycleWeight]
  · rw [cycleLogSeries, PowerSeries.coeff_mk, ite_eq_right hm,
      coeff_expMinusOne_pow, cycleWeight, ite_eq_right hm,
      signedCycleTrace_eq trace (Nat.one_le_iff_ne_zero.mpr hm)]
    have hq : (n.factorial : ℚ) * (m : ℚ)⁻¹ *
        ((m.factorial : ℚ) / (n.factorial : ℚ)) = ((m - 1).factorial : ℚ) := by
      rw [← Nat.mul_factorial_pred hm, Nat.cast_mul]
      field_simp
    have hR := congrArg (algebraMap ℚ R) hq
    simp only [map_mul, map_natCast] at hR
    calc
      _ = ((n.factorial : R) * algebraMap ℚ R ((m : ℚ)⁻¹) *
          algebraMap ℚ R ((m.factorial : ℚ) / (n.factorial : ℚ))) *
          ((Nat.stirlingSecond n m : R) * (-1 : R) ^ (m - 1) * trace m) := by ring
      _ = _ := by rw [hR]; ring

theorem pseudoCumulant_determinantCycleSequence (trace : ℕ → R) (n : ℕ) :
    pseudoCumulant R (determinantCycleSequence trace) n =
      cycleStirlingTransform R trace n := by
  by_cases hn : n = 0
  · subst n
    simp only [pseudoCumulant_zero, cycleStirlingTransform_zero]
  · have h0 : determinantCycleSequence trace 0 = 1 := by
      have hh := congrArg PowerSeries.constantCoeff
        (ordinaryEGF_determinantCycleSequence trace)
      simpa only [constantCoeff_ordinaryEGF,
        permutationCycleSeries_eq_cyclePartitionSeries,
        constantCoeff_cyclePartitionSeries] using hh
    rw [pseudoCumulant_eq_formalFactorialLog _ h0 (Nat.one_le_iff_ne_zero.mpr hn)]
    rw [logOf_subst _ _ (by rw [constantCoeff_ordinaryEGF, h0])
      (PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_expMinusOne),
      logOf_determinantCycleSequence, factorial_coeff_cycleLog_subst]


open MeasureTheory

section ActualIntegrals
variable {Ω : Type*} [MeasurableSpace Ω]

theorem determinantIntegral_eq_determinantCycleSequence
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ)
    (hK : Measurable (Function.uncurry K)) (C : ℝ≥0)
    (hbound : ∀ x y, ‖K x y‖ ≤ C) :
    KernelIntegrals.determinantIntegral μ K =
      determinantCycleSequence (KernelIntegrals.cycleIntegral μ K) := by
  funext k
  exact KernelIntegrals.determinantIntegral_eq_cycleType_sum μ K hK C hbound k

/-- The source's exponential determinant/cycle identity for the actual kernel
product integrals, as a formal power series. -/
theorem determinantIntegral_exponential
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ)
    (hK : Measurable (Function.uncurry K)) (C : ℝ≥0)
    (hbound : ∀ x y, ‖K x y‖ ≤ C) :
    (PowerSeries.exp ℂ).subst
        (cycleLogSeries (signedCycleTrace (KernelIntegrals.cycleIntegral μ K))) =
      ordinaryEGF (KernelIntegrals.determinantIntegral μ K) := by
  rw [determinantIntegral_eq_determinantCycleSequence μ K hK C hbound]
  exact determinantCycleSequence_exponential _

/-- The literal H_n of actual determinant integrals equals the Stirling sum of
the actual cyclic trace integrals. No auxiliary point process is presumed. -/
theorem pseudoCumulant_determinantIntegral
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ)
    (hK : Measurable (Function.uncurry K)) (C : ℝ≥0)
    (hbound : ∀ x y, ‖K x y‖ ≤ C) (n : ℕ) :
    pseudoCumulant ℂ (KernelIntegrals.determinantIntegral μ K) n =
      cycleStirlingTransform ℂ (KernelIntegrals.cycleIntegral μ K) n := by
  rw [determinantIntegral_eq_determinantCycleSequence μ K hK C hbound,
    pseudoCumulant_determinantCycleSequence]

/-- The source signed-Stirling recursion, now applied to actual determinant
pseudo-cumulants and actual cycle integrals. -/
theorem pseudoCumulant_determinantIntegral_recursion
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ)
    (hK : Measurable (Function.uncurry K)) (C : ℝ≥0)
    (hbound : ∀ x y, ‖K x y‖ ≤ C) {n : ℕ} (hn : 2 ≤ n) :
    pseudoCumulant ℂ (KernelIntegrals.determinantIntegral μ K) n =
      (-1 : ℂ) ^ n * (n - 1).factorial *
          (KernelIntegrals.cycleIntegral μ K 1 - KernelIntegrals.cycleIntegral μ K n) +
        ∑ j ∈ Finset.Ico 2 n, -(signedStirling n j : ℂ) *
          pseudoCumulant ℂ (KernelIntegrals.determinantIntegral μ K) j := by
  simp_rw [pseudoCumulant_determinantIntegral μ K hK C hbound]
  exact cycleStirlingTransform_recursion ℂ (KernelIntegrals.cycleIntegral μ K) hn

end ActualIntegrals

end Paper.Cumulants
