/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.Bijection
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! # The genuine analytic complex principal Lambert branch

The global inverse is constructed from the proved complex bijection.
Outside the slit plane the total function uses Function.invFunOn's arbitrary default;
no assertion outside the slit plane is part of the branch contract.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology Real ComplexConjugate

namespace Paper.Lambert

def W : ℂ → ℂ := Function.invFunOn expMul principalDomain

theorem W_mem {z : ℂ} (hz : z ∈ slitPlane) : W z ∈ principalDomain :=
  Function.invFunOn_mem (expMul_bijOn.surjOn hz)

theorem expMul_W {z : ℂ} (hz : z ∈ slitPlane) : expMul (W z) = z :=
  Function.invFunOn_eq (expMul_bijOn.surjOn hz)

theorem W_expMul {w : ℂ} (hw : w ∈ principalDomain) : W (expMul w) = w :=
  expMul_bijOn.injOn.leftInvOn_invFunOn hw

@[simp] theorem W_zero : W 0 = 0 := by
  have hh := W_expMul zero_mem_principalDomain
  simpa only [expMul, Complex.exp_zero, zero_mul] using hh

theorem W_mul_exp {z : ℂ} (hz : z ∈ slitPlane) : W z * Complex.exp (W z) = z :=
  expMul_W hz

theorem analyticAt_W {z : ℂ} (hz : z ∈ slitPlane) : AnalyticAt ℂ W z := by
  let w := W z
  have hw : w ∈ principalDomain := W_mem hz
  have ha : AnalyticAt ℂ expMul w := analyticAt_expMul w
  have hn : deriv expMul w ≠ 0 := by
    rw [(hasDerivAt_expMul w).deriv]
    exact expMul_deriv_ne_zero hw
  let g : ℂ → ℂ := ha.hasStrictDerivAt.localInverse expMul (deriv expMul w) w hn
  have hg : AnalyticAt ℂ g (expMul w) := ha.analyticAt_localInverse hn
  have hg0 : g (expMul w) = w :=
    (ha.hasStrictDerivAt.eventually_left_inverse hn).self_of_nhds
  have hgv : ∀ᶠ v in 𝓝 (expMul w), g v ∈ principalDomain := by
    have hh : principalDomain ∈ 𝓝 (g (expMul w)) := by
      rw [hg0]
      exact isOpen_principalDomain.mem_nhds hw
    exact hg.continuousAt.eventually hh
  have hright : ∀ᶠ v in 𝓝 (expMul w), expMul (g v) = v :=
    ha.hasStrictDerivAt.eventually_right_inverse hn
  have heq : g =ᶠ[𝓝 (expMul w)] W := by
    filter_upwards [hgv, hright] with v hv hfv
    have hvs : v ∈ slitPlane := hfv ▸ expMul_mapsTo_slitPlane hv
    apply expMul_bijOn.injOn hv (W_mem hvs)
    exact hfv.trans (expMul_W hvs).symm
  have hh := hg.congr heq
  have hwz : expMul w = z := expMul_W hz
  rwa [hwz] at hh

theorem analyticOnNhd_W : AnalyticOnNhd ℂ W slitPlane := fun _ hz => analyticAt_W hz

theorem hasDerivAt_W {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt W (Complex.exp (W z) * (1 + W z))⁻¹ z := by
  have ha := analyticAt_expMul (W z)
  have hn : deriv expMul (W z) ≠ 0 := by
    rw [(hasDerivAt_expMul (W z)).deriv]
    exact expMul_deriv_ne_zero (W_mem hz)
  have hv : ∀ᶠ w in 𝓝 (W z), w ∈ principalDomain :=
    isOpen_principalDomain.mem_nhds (W_mem hz)
  have hleft : ∀ᶠ w in 𝓝 (W z), W (expMul w) = w :=
    hv.mono fun _ hw => W_expMul hw
  have hh := ha.hasStrictDerivAt.to_local_left_inverse hn hleft
  rw [(hasDerivAt_expMul (W z)).deriv, expMul_W hz] at hh
  exact hh.hasDerivAt

theorem slitPlane_conj {z : ℂ} (hz : z ∈ slitPlane) : conj z ∈ slitPlane := by
  simpa only [slitPlane, Set.mem_ofPred_eq, Complex.conj_im, Complex.conj_re, neg_eq_zero] using hz

theorem W_conj {z : ℂ} (hz : z ∈ slitPlane) : W (conj z) = conj (W z) := by
  apply expMul_bijOn.injOn (W_mem (slitPlane_conj hz)) (principalDomain_conj (W_mem hz))
  rw [expMul_W (slitPlane_conj hz), expMul_conj, expMul_W hz]

/-- Complete proved branch contract: complex analyticity on the exact slit,
normalization at zero, and the Lambert equation at every point of that slit. -/
theorem principal_W :
    AnalyticOnNhd ℂ W slitPlane ∧ W 0 = 0 ∧
      ∀ z ∈ slitPlane, W z * Complex.exp (W z) = z :=
  ⟨analyticOnNhd_W, W_zero, fun _ hz => W_mul_exp hz⟩

end Paper.Lambert
