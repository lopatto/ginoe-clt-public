/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Definitions
public import GinoeClt.Combinatorics.PartitionBridge
public import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# The analytic moment--cumulant identity

Local exponential integrability justifies differentiating the actual MGF and CGF.
The native all-order chain rule and canonical partition bridge then identify the
ordinary finite moment polynomial, including its empty-partition case.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators Classical
namespace Paper.Cumulants

theorem moment_eq_partition_cumulants {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : 0 ∈ interior (integrableExpSet X μ)) (r : ℕ) :
    (∫ ω, X ω ^ r ∂μ) =
      momentPolynomial r (fun k => iteratedDeriv k (cgf X μ) 0) := by
  have heq : mgf X μ =ᶠ[𝓝 0] Real.exp ∘ cgf X μ := by
    filter_upwards [isOpen_interior.eventually_mem h] with t ht
    exact (exp_cgf (X := X) (μ := μ) (t := t)
      (interior_subset (s := integrableExpSet X μ) ht)).symm
  have hc : ContDiffAt ℝ r (cgf X μ) 0 :=
    (analyticAt_cgf h).contDiffAt
  have he : ContDiffAt ℝ r Real.exp (cgf X μ 0) :=
    Real.contDiff_exp.contDiffAt
  have hexp (k : ℕ) : iteratedDeriv k Real.exp (cgf X μ 0) = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, cgf_zero, Real.exp_zero]
  calc
    (∫ ω, X ω ^ r ∂μ) = iteratedDeriv r (mgf X μ) 0 :=
      (iteratedDeriv_mgf_zero h r).symm
    _ = iteratedDeriv r (Real.exp ∘ cgf X μ) 0 := heq.iteratedDeriv_eq r
    _ = ∑ c : OrderedFinpartition r,
        ∏ i : Fin c.length, iteratedDeriv (c.partSize i) (cgf X μ) 0 := by
      simpa only [hexp, one_mul] using
        (iteratedDeriv_comp_eq_sum_orderedFinpartition he hc (i := r) le_rfl)
    _ = momentPolynomial r (fun k => iteratedDeriv k (cgf X μ) 0) := by
      simpa only [momentPolynomial] using
        (PartitionBridge.sum_prod_partSize_eq (n := r) (fun k => iteratedDeriv k (cgf X μ) 0))

end Paper.Cumulants
