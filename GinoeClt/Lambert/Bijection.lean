/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.PolarConverse
public import GinoeClt.Lambert.RealAxis

/-! # Global complex bijection for the principal Lambert branch -/

@[expose] public section
noncomputable section
open Set
open scoped Real ComplexConjugate

namespace Paper.Lambert

theorem arg_mem_Ioo_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.arg z ∈ Ioo (0 : ℝ) Real.pi := by
  have h0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr hz.le
  have hn : Complex.arg z ≠ 0 := by
    intro hh
    have he := Complex.norm_mul_sin_arg z
    rw [hh, Real.sin_zero, mul_zero] at he
    linarith
  exact ⟨lt_of_le_of_ne h0 hn.symm, Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')⟩

theorem rayPoint_arg_norm (z : ℂ) : rayPoint (Complex.arg z) ‖z‖ = z :=
  Complex.ext (Complex.norm_mul_cos_arg z) (Complex.norm_mul_sin_arg z)

theorem exists_expMul_upper {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, w ∈ principalDomain ∧ expMul w = z := by
  have hθ := arg_mem_Ioo_of_im_pos hz
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simp [h] at hz)
  obtain ⟨v, ⟨hv, hvr⟩, _⟩ := existsUnique_polarRadius hθ hr
  refine ⟨polarPoint (Complex.arg z) v, polarPoint_mem_principalDomain hθ hv, ?_⟩
  rw [expMul_polarPoint _ _ (sin_polar_positive hθ hv).ne', hvr, rayPoint_arg_norm]

theorem expMul_upper_injective {w₁ w₂ : ℂ}
    (h₁ : w₁ ∈ principalDomain) (h₂ : w₂ ∈ principalDomain)
    (he : expMul w₁ = expMul w₂) (hp : 0 < (expMul w₁).im) : w₁ = w₂ := by
  have hp₂ : 0 < (expMul w₂).im := he ▸ hp
  obtain ⟨hθ₁, hv₁, hw₁, hr₁⟩ := upper_polar_coordinates h₁ hp
  obtain ⟨hθ₂, hv₂, hw₂, hr₂⟩ := upper_polar_coordinates h₂ hp₂
  rw [he] at hθ₁ hv₁ hw₁ hr₁
  have hv : w₁.im = w₂.im :=
    (strictMonoOn_polarRadius hθ₂).injOn hv₁ hv₂ (hr₁.trans hr₂.symm)
  calc
    w₁ = polarPoint (Complex.arg (expMul w₂)) w₁.im := hw₁
    _ = polarPoint (Complex.arg (expMul w₂)) w₂.im := congrArg _ hv
    _ = w₂ := hw₂.symm

theorem existsUnique_expMul_upper {z : ℂ} (hz : 0 < z.im) :
    ∃! w : ℂ, w ∈ principalDomain ∧ expMul w = z := by
  obtain ⟨w, hw, hfw⟩ := exists_expMul_upper hz
  refine ⟨w, ⟨hw, hfw⟩, ?_⟩
  rintro v ⟨hv, hfv⟩
  exact expMul_upper_injective hv hw (hfv.trans hfw.symm) (by rw [hfv]; exact hz)

/-- Complete global preimage existence and uniqueness on the complex slit plane. -/
theorem existsUnique_expMul {z : ℂ} (hz : z ∈ slitPlane) :
    ∃! w : ℂ, w ∈ principalDomain ∧ expMul w = z := by
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hp : 0 < (conj z).im := by simpa only [Complex.conj_im, neg_pos] using hneg
    obtain ⟨u, ⟨hu, hfu⟩, huniq⟩ := existsUnique_expMul_upper hp
    refine ⟨conj u, ⟨principalDomain_conj hu, ?_⟩, ?_⟩
    · rw [expMul_conj, hfu, Complex.conj_conj]
    · rintro w ⟨hw, hfw⟩
      have he : expMul (conj w) = conj z := by rw [expMul_conj, hfw]
      have hwc : conj w = u := huniq _ ⟨principalDomain_conj hw, he⟩
      have hh := congrArg (conj : ℂ → ℂ) hwc
      simpa only [Complex.conj_conj] using hh
  · have hr : -Real.exp (-1) < z.re := by
      apply lt_of_not_ge
      exact fun hle => hz ⟨hzero, hle⟩
    have hez : z = (z.re : ℂ) := Complex.ext rfl hzero
    simpa only [← hez] using existsUnique_expMul_real hr
  · exact existsUnique_expMul_upper hpos

theorem expMul_bijOn : Set.BijOn expMul principalDomain slitPlane := by
  refine ⟨expMul_mapsTo_slitPlane, ?_, ?_⟩
  · intro w₁ h₁ w₂ h₂ he
    obtain ⟨u, hu, huniq⟩ := existsUnique_expMul (expMul_mapsTo_slitPlane h₁)
    exact (huniq w₁ ⟨h₁, rfl⟩).trans (huniq w₂ ⟨h₂, he.symm⟩).symm
  · intro z hz
    exact (existsUnique_expMul hz).exists

end Paper.Lambert
