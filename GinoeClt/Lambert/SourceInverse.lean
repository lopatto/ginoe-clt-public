/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.PrincipalW
public import GinoeClt.Lambert.UnitDisk

/-! # The literal inverse functions used in the Lambert appendix

The unit-disk inverse follows from the proved global principal range. This
replaces the source's local-inverse/identity-theorem glue without changing its
functions or the radial inverse paths.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology Real

namespace Paper.Lambert

def phi (q : ℂ) : ℂ := q * Complex.exp (1 - q)

def sourceScale (v : ℂ) : ℂ := -v / (Real.exp 1 : ℂ)

def psi (v : ℂ) : ℂ := -W (sourceScale v)

def sourceSlitPlane : Set ℂ := {v | ¬(v.im = 0 ∧ 1 ≤ v.re)}

theorem sourceScale_mem_iff (v : ℂ) :
    sourceScale v ∈ slitPlane ↔ v ∈ sourceSlitPlane := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hcut : -Real.exp (-1) = (-1 : ℝ) / Real.exp 1 := by
    rw [Real.exp_neg]
    ring
  simp only [sourceScale, slitPlane, sourceSlitPlane, Set.mem_ofPred_eq,
    Complex.div_ofReal_im, Complex.div_ofReal_re, Complex.neg_im, Complex.neg_re,
    div_eq_zero_iff, he.ne', or_false, neg_eq_zero, hcut,
    div_le_div_iff_of_pos_right he, neg_le_neg_iff]

theorem sourceScale_injective : Function.Injective sourceScale := by
  intro v w h
  have he : (Real.exp 1 : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  apply neg_injective
  exact (div_left_inj' he).mp h

theorem sourceScale_phi (q : ℂ) : sourceScale (phi q) = expMul (-q) := by
  have he : (Real.exp 1 : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  simp only [sourceScale, phi, expMul, Complex.exp_sub, Complex.exp_neg,
    Complex.ofReal_exp, Complex.ofReal_one]
  field_simp

@[simp] theorem phi_zero : phi 0 = 0 := by simp [phi]
@[simp] theorem phi_one : phi 1 = 1 := by simp [phi]
@[simp] theorem psi_zero : psi 0 = 0 := by simp [psi, sourceScale]

theorem psi_phi {q : ℂ} (hq : -q ∈ principalDomain) : psi (phi q) = q := by
  simp only [psi, sourceScale_phi, W_expMul hq, neg_neg]

theorem phi_psi {v : ℂ} (hv : v ∈ sourceSlitPlane) : phi (psi v) = v := by
  apply sourceScale_injective
  rw [sourceScale_phi]
  simpa only [psi, neg_neg] using expMul_W ((sourceScale_mem_iff v).mpr hv)

theorem phi_mem_sourceSlitPlane {q : ℂ} (hq : ‖q‖ < 1) :
    phi q ∈ sourceSlitPlane := by
  apply (sourceScale_mem_iff _).mp
  rw [sourceScale_phi]
  apply expMul_mapsTo_slitPlane
  apply mem_principalDomain_of_norm_lt_one
  simpa only [norm_neg] using hq

theorem psi_phi_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) : psi (phi q) = q :=
  psi_phi (mem_principalDomain_of_norm_lt_one (by simpa only [norm_neg] using hq))

theorem psi_ne_one {v : ℂ} (hv : v ∈ sourceSlitPlane) : psi v ≠ 1 := by
  intro hh
  have hv1 : v = 1 := by simpa only [hh, phi_one] using (phi_psi hv).symm
  subst v
  exact hv ⟨by norm_num, by norm_num⟩

theorem isOpen_sourceSlitPlane : IsOpen sourceSlitPlane := by
  have hh : sourceSlitPlane = sourceScale ⁻¹' slitPlane := by
    ext v
    exact (sourceScale_mem_iff v).symm
  rw [hh]
  apply isOpen_slitPlane.preimage
  unfold sourceScale
  fun_prop

theorem analyticAt_sourceScale (v : ℂ) : AnalyticAt ℂ sourceScale v := by
  unfold sourceScale
  fun_prop

theorem analyticAt_phi (q : ℂ) : AnalyticAt ℂ phi q := by
  unfold phi
  fun_prop

theorem analyticAt_psi {v : ℂ} (hv : v ∈ sourceSlitPlane) : AnalyticAt ℂ psi v := by
  have hh := (analyticAt_W ((sourceScale_mem_iff v).mpr hv)).comp
    (analyticAt_sourceScale v)
  exact hh.neg

theorem analyticOnNhd_psi : AnalyticOnNhd ℂ psi sourceSlitPlane :=
  fun _ hv => analyticAt_psi hv

theorem sourceSlitPlane_smul {v : ℂ} (hv : v ∈ sourceSlitPlane)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (s : ℂ) * v ∈ sourceSlitPlane := by
  by_cases hs : s = 0
  · subst s
    simp [sourceSlitPlane]
  intro hh
  have hvi : v.im = 0 := by
    have hi : s * v.im = 0 := by simpa only [Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add] using hh.1
    exact (mul_eq_zero.mp hi).resolve_left hs
  have hvr : v.re < 1 := lt_of_not_ge (fun h => hv ⟨hvi, h⟩)
  have hsr : s * v.re < 1 := by
    by_cases hr : 0 ≤ v.re
    · exact (mul_le_mul_of_nonneg_right hs1 hr).trans_lt (by simpa using hvr)
    · have := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_not_ge hr)
      linarith
  have hh' : 1 ≤ s * v.re := by simpa only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hh.2
  exact (not_le_of_gt hsr) hh'

theorem hasDerivAt_phi (q : ℂ) :
    HasDerivAt phi (Complex.exp (1 - q) * (1 - q)) q := by
  have hh := (hasDerivAt_id q).mul
    ((Complex.hasDerivAt_exp (1 - q)).comp q
      ((hasDerivAt_const q (1 : ℂ)).sub (hasDerivAt_id q)))
  have hd : 1 * Complex.exp (1 - q) + q * (Complex.exp (1 - q) * (0 - 1)) =
      Complex.exp (1 - q) * (1 - q) := by ring
  simp only [Function.comp_apply, id_eq] at hh
  rw [hd] at hh
  unfold phi
  simpa only [Function.comp_def, Pi.mul_def, Pi.sub_def, id_eq] using hh

theorem hasDerivAt_psi {v : ℂ} (hv : v ∈ sourceSlitPlane) :
    HasDerivAt psi (deriv psi v) v :=
  (analyticAt_psi hv).differentiableAt.hasDerivAt

theorem phi_deriv_mul_psi_deriv {v : ℂ} (hv : v ∈ sourceSlitPlane) :
    Complex.exp (1 - psi v) * (1 - psi v) * deriv psi v = 1 := by
  have hh := (hasDerivAt_phi (psi v)).comp v (hasDerivAt_psi hv)
  have he : (fun z => phi (psi z)) =ᶠ[𝓝 v] id := by
    have hn : ∀ᶠ z in 𝓝 v, z ∈ sourceSlitPlane := isOpen_sourceSlitPlane.mem_nhds hv
    exact hn.mono fun z hz => phi_psi hz
  calc
    _ = deriv (phi ∘ psi) v := hh.deriv.symm
    _ = deriv id v := by simpa only [Function.comp_def] using he.deriv_eq
    _ = 1 := (hasDerivAt_id v).deriv

theorem deriv_psi {v : ℂ} (hv : v ∈ sourceSlitPlane) :
    deriv psi v = (Complex.exp (1 - psi v) * (1 - psi v))⁻¹ := by
  have hn : Complex.exp (1 - psi v) * (1 - psi v) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (sub_ne_zero.mpr (Ne.symm (psi_ne_one hv)))
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact phi_deriv_mul_psi_deriv hv

end Paper.Lambert
