/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.AnalyticPartition
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! # Actual analytic cumulants as the finite Möbius polynomial of moments -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical

namespace Paper.Cumulants

theorem iteratedDeriv_log_one {n : ℕ} (hn : 1 ≤ n) :
    iteratedDeriv n Real.log 1 = (-1 : ℝ) ^ (n - 1) * (n - 1).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp

/-- Local exponential integrability suffices; the cumulant is the derivative
of the actual real log MGF, not a new algebraic definition. -/
theorem cumulant_eq_mobius {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) {n : ℕ} (hn : 1 ≤ n) :
    iteratedDeriv n (cgf X μ) 0 =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        ((-1 : ℝ) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial) *
          ∏ B ∈ P.parts, ∫ ω, X ω ^ B.card ∂μ := by
  have hm : ContDiffAt ℝ n (mgf X μ) 0 := (analyticAt_mgf h).contDiffAt
  have hl : ContDiffAt ℝ n Real.log (mgf X μ 0) :=
    Real.contDiffAt_log.mpr (by simp)
  change iteratedDeriv n (Real.log ∘ mgf X μ) 0 = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hl hm (i := n) le_rfl]
  calc
    _ = ∑ c : OrderedFinpartition n,
        ((-1 : ℝ) ^ (c.length - 1) * (c.length - 1).factorial) *
          ∏ i : Fin c.length, ∫ ω, X ω ^ c.partSize i ∂μ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [mgf_zero, iteratedDeriv_log_one (c.length_pos hn)]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact iteratedDeriv_mgf_zero h (c.partSize i)
    _ = _ := by
      rw [← (Paper.PartitionBridge.equiv n).sum_comp]
      apply Finset.sum_congr rfl
      intro c _
      have hcard : ((Paper.PartitionBridge.equiv n) c).parts.card = c.length :=
        Paper.PartitionBridge.card_toFinpartition_parts c
      rw [hcard, ← Paper.PartitionBridge.prod_partSize_eq c (fun k => ∫ ω, X ω ^ k ∂μ)]

end Paper.Cumulants
