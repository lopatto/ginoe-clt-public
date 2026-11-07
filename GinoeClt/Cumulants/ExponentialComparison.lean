/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.ExponentialErrors
public import GinoeClt.Cumulants.PseudoCumulants

/-! # Fixed-order pseudo-cumulant error propagation

The factorial-moment versus determinant-integral estimates are explicit inputs
to this lemma. Their GinOE instances are proved in CountKernelComparison under
the finite factorial-moment identity supplied by SkewOrthogonal.CountPfaffianIdentity.
This module proves finite polynomial error propagation, keeping one exponential
rate for every fixed order.
-/

@[expose] public section
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Paper.Cumulants

theorem pseudoCumulant_exp_close {c : ℝ} (hc : 0 < c)
    (T J : ℕ → ℕ → ℝ)
    (hT : ∀ k, ExponentialErrors.PowerBound (T k))
    (hJ : ∀ k, ExponentialErrors.PowerBound (J k))
    (hTJ : ∀ k, ExponentialErrors.ExpPowerBound c (fun n => T k n - J k n))
    (r : ℕ) :
    (fun n => pseudoCumulant ℝ (fun k => T k n) r -
      pseudoCumulant ℝ (fun k => J k n) r) =O[atTop]
        fun n => Real.exp (-(c / 2) * (n + 1 : ℝ)) := by
  exact ExponentialErrors.polynomial_exp_close hc
    (factorialCumulantPolynomial ℝ r) T J hT hJ hTJ

end Paper.Cumulants
