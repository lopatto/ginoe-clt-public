/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.SourceInverse
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The compact radial inverse paths in the Lambert appendix -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology Real

namespace Paper.Lambert

def radialArgument (q : ℂ) (t : ℝ) : ℂ := ((1 - t : ℝ) : ℂ) * phi q

def appendixPath (q : ℂ) (t : ℝ) : ℂ := psi (radialArgument q t)

def pathFactor (q : ℂ) (t : ℝ) : ℂ := (1 - appendixPath q t)⁻¹

def pathFactorDerivative (q : ℂ) (t : ℝ) : ℂ :=
  -phi q * deriv psi (radialArgument q t) / (1 - appendixPath q t) ^ 2

def pathParameters (r : ℝ) : Set (ℂ × ℝ) := closedBall 0 r ×ˢ Icc 0 1

def radialImage (r : ℝ) : Set ℂ :=
  (fun p : ℂ × ℝ => radialArgument p.1 p.2) '' pathParameters r

theorem continuous_phi : Continuous phi :=
  continuous_iff_continuousAt.mpr fun q => (analyticAt_phi q).continuousAt

theorem continuous_radialArgument :
    Continuous (fun p : ℂ × ℝ => radialArgument p.1 p.2) := by
  unfold radialArgument
  exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_snd)).mul
    (continuous_phi.comp continuous_fst)

theorem isCompact_pathParameters (r : ℝ) : IsCompact (pathParameters r) :=
  (isCompact_closedBall (0 : ℂ) r).prod isCompact_Icc

theorem isCompact_radialImage (r : ℝ) : IsCompact (radialImage r) :=
  (isCompact_pathParameters r).image continuous_radialArgument

theorem radialArgument_mem {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ} (ht : t ∈ Icc 0 1) :
    radialArgument q t ∈ sourceSlitPlane :=
  sourceSlitPlane_smul (phi_mem_sourceSlitPlane hq) (by linarith [ht.2]) (by linarith [ht.1])

theorem radialArgument_mem_of_parameters {r : ℝ} (hr : r < 1) {p : ℂ × ℝ}
    (hp : p ∈ pathParameters r) : radialArgument p.1 p.2 ∈ sourceSlitPlane := by
  have hq : ‖p.1‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hp.1
  exact radialArgument_mem (hq.trans_lt hr) hp.2

theorem radialImage_subset {r : ℝ} (hr : r < 1) : radialImage r ⊆ sourceSlitPlane := by
  rintro v ⟨p, hp, rfl⟩
  exact radialArgument_mem_of_parameters hr hp

@[simp] theorem appendixPath_one (q : ℂ) : appendixPath q 1 = 0 := by
  simp [appendixPath, radialArgument]

theorem appendixPath_zero {q : ℂ} (hq : ‖q‖ < 1) : appendixPath q 0 = q := by
  simpa only [appendixPath, radialArgument, sub_zero, Complex.ofReal_one, one_mul] using
    psi_phi_of_norm_lt_one hq

theorem pathFactor_zero {q : ℂ} (hq : ‖q‖ < 1) :
    pathFactor q 0 = (1 - q)⁻¹ := by
  rw [pathFactor, appendixPath_zero hq]

theorem hasDerivAt_radialArgument (q : ℂ) (t : ℝ) :
    HasDerivAt (radialArgument q) (-phi q) t := by
  have hh := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).ofReal_comp).mul_const
    (phi q)
  unfold radialArgument
  simpa only [Pi.mul_def, Pi.sub_def, Function.comp_def, id_eq, zero_sub,
    Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul] using hh

theorem hasDerivAt_appendixPath {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    HasDerivAt (appendixPath q)
      (-phi q * deriv psi (radialArgument q t)) t := by
  have hh := (hasDerivAt_psi (radialArgument_mem hq ht)).scomp t
    (hasDerivAt_radialArgument q t)
  unfold appendixPath
  simpa only [Function.comp_def, smul_eq_mul] using hh

theorem hasDerivAt_pathFactor {q : ℂ} (hq : ‖q‖ < 1) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    HasDerivAt (pathFactor q) (pathFactorDerivative q t) t := by
  have hn : 1 - appendixPath q t ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (psi_ne_one (radialArgument_mem hq ht)))
  have hh := ((hasDerivAt_const t (1 : ℂ)).sub
    (hasDerivAt_appendixPath hq ht)).inv hn
  unfold pathFactor pathFactorDerivative
  simpa only [Pi.inv_def, Pi.sub_def, zero_sub, neg_neg] using hh

theorem continuousOn_pathFactor {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun p : ℂ × ℝ => pathFactor p.1 p.2) (pathParameters r) := by
  have hp : ContinuousOn (fun p : ℂ × ℝ => appendixPath p.1 p.2) (pathParameters r) :=
    analyticOnNhd_psi.continuousOn.comp continuous_radialArgument.continuousOn
      (fun _ hp => radialArgument_mem_of_parameters hr hp)
  exact (continuousOn_const.sub hp).inv₀ fun p hp =>
    sub_ne_zero.mpr (Ne.symm (psi_ne_one (radialArgument_mem_of_parameters hr hp)))

theorem continuousOn_pathFactorDerivative {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun p : ℂ × ℝ => pathFactorDerivative p.1 p.2) (pathParameters r) := by
  have hd : ContinuousOn (fun p : ℂ × ℝ => deriv psi (radialArgument p.1 p.2))
      (pathParameters r) :=
    analyticOnNhd_psi.deriv.continuousOn.comp continuous_radialArgument.continuousOn
      (fun _ hp => radialArgument_mem_of_parameters hr hp)
  have hp : ContinuousOn (fun p : ℂ × ℝ => appendixPath p.1 p.2) (pathParameters r) :=
    analyticOnNhd_psi.continuousOn.comp continuous_radialArgument.continuousOn
      (fun _ hp => radialArgument_mem_of_parameters hr hp)
  exact ((continuous_phi.comp continuous_fst).continuousOn.neg.mul hd).div
    ((continuousOn_const.sub hp).pow 2) fun p hp =>
      pow_ne_zero 2 (sub_ne_zero.mpr
        (Ne.symm (psi_ne_one (radialArgument_mem_of_parameters hr hp))))

theorem exists_uniform_pathFactorDerivative_bound {r : ℝ} (hr : r < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℂ, ‖q‖ ≤ r → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pathFactorDerivative q t‖ ≤ M := by
  obtain ⟨B, hB⟩ := (isCompact_pathParameters r).exists_bound_of_continuousOn
    (continuousOn_pathFactorDerivative hr)
  refine ⟨max B 0, le_max_right _ _, fun q hq t ht => ?_⟩
  apply (hB (q, t) ?_).trans (le_max_left _ _)
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hq, ht⟩

theorem norm_pathFactor_sub_zero_le {r M : ℝ} (hr : r < 1)
    (hM : ∀ q : ℂ, ‖q‖ ≤ r → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pathFactorDerivative q t‖ ≤ M)
    {q : ℂ} (hq : ‖q‖ ≤ r) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖pathFactor q t - (1 - q)⁻¹‖ ≤ M * t := by
  have hq1 : ‖q‖ < 1 := hq.trans_lt hr
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (hasDerivAt_pathFactor hq1 hu).hasDerivWithinAt)
    (fun u hu => hM q hq u (Ico_subset_Icc_self hu)) t ht
  simpa only [pathFactor_zero hq1, sub_zero] using hh

theorem integral_one_sub_pow (m : ℕ) :
    (∫ t : ℝ in 0..1, (1 - t) ^ m) = (m + 1 : ℝ)⁻¹ := by
  have hh := intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ m)
    (a := 0) (b := 1) 1
  calc
    _ = ∫ t : ℝ in 0..1, t ^ m := by simpa only [sub_self, sub_zero] using hh
    _ = _ := by simp

theorem integral_mul_one_sub_pow (m : ℕ) :
    (∫ t : ℝ in 0..1, t * (1 - t) ^ m) =
      1 / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  have he (t : ℝ) : t * (1 - t) ^ m = (1 - t) ^ m - (1 - t) ^ (m + 1) := by
    rw [pow_succ]
    ring
  simp_rw [he]
  have hc0 : Continuous (fun t : ℝ => (1 - t) ^ m) := by fun_prop
  have hc1 : Continuous (fun t : ℝ => (1 - t) ^ (m + 1)) := by fun_prop
  rw [intervalIntegral.integral_sub
    (hc0.intervalIntegrable 0 1) (hc1.intervalIntegrable 0 1),
    integral_one_sub_pow, integral_one_sub_pow]
  push_cast
  field_simp
  ring

theorem weighted_pathFactor_remainder {r M : ℝ} (hr : r < 1)
    (hM : ∀ q : ℂ, ‖q‖ ≤ r → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pathFactorDerivative q t‖ ≤ M) {q : ℂ} (hq : ‖q‖ ≤ r) (m : ℕ) :
    ‖(∫ t : ℝ in 0..1, ((1 - t) ^ m : ℝ) • pathFactor q t) -
        (m + 1 : ℝ)⁻¹ • (1 - q)⁻¹‖ ≤
      M / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  have hq1 : ‖q‖ < 1 := hq.trans_lt hr
  have hfc : ContinuousOn (pathFactor q) (Icc (0 : ℝ) 1) :=
    fun t ht => (hasDerivAt_pathFactor hq1 ht).continuousAt.continuousWithinAt
  have hw : Continuous (fun t : ℝ => (1 - t) ^ m) :=
    (continuous_const.sub continuous_id).pow m
  have hf : IntervalIntegrable (fun t : ℝ => (1 - t) ^ m • pathFactor q t) volume 0 1 :=
    (hw.continuousOn.smul hfc).intervalIntegrable_of_Icc zero_le_one
  have hc : IntervalIntegrable (fun t : ℝ => (1 - t) ^ m • (1 - q)⁻¹) volume 0 1 :=
    (hw.smul continuous_const).intervalIntegrable 0 1
  have he :
      (∫ t : ℝ in 0..1, ((1 - t) ^ m : ℝ) • pathFactor q t) -
          (m + 1 : ℝ)⁻¹ • (1 - q)⁻¹ =
        ∫ t : ℝ in 0..1, ((1 - t) ^ m : ℝ) •
          (pathFactor q t - (1 - q)⁻¹) := by
    rw [← integral_one_sub_pow m, ← intervalIntegral.integral_smul_const,
      ← intervalIntegral.integral_sub hf hc]
    congr 1
    funext t
    exact (smul_sub _ _ _).symm
  rw [he]
  calc
    _ ≤ ∫ t : ℝ in 0..1, M * (t * (1 - t) ^ m) := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · filter_upwards with t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have hw0 : 0 ≤ (1 - t) ^ m := pow_nonneg (by linarith [ht'.2]) _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0]
        exact (mul_le_mul_of_nonneg_left
          (norm_pathFactor_sub_zero_le hr hM hq ht') hw0).trans_eq (by ring)
      · exact (continuous_const.mul (continuous_id.mul hw)).intervalIntegrable 0 1
    _ = M / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
      rw [intervalIntegral.integral_const_mul, integral_mul_one_sub_pow]
      ring

theorem exists_weighted_pathFactor_remainder_bound {r : ℝ} (hr : r < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ℂ, ‖q‖ ≤ r → ∀ m : ℕ,
      ‖(∫ t : ℝ in 0..1, ((1 - t) ^ m : ℝ) • pathFactor q t) -
          (m + 1 : ℝ)⁻¹ • (1 - q)⁻¹‖ ≤
        M / ((m + 1 : ℝ) * (m + 2 : ℝ)) := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_pathFactorDerivative_bound hr
  exact ⟨M, hM0, fun _ hq m => weighted_pathFactor_remainder hr hM hq m⟩

/-- The manuscript's exact N-indexed weighted error; no division by q occurs. -/
theorem weighted_pathFactor_remainder_N {r M : ℝ} (hr : r < 1)
    (hM : ∀ q : ℂ, ‖q‖ ≤ r → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖pathFactorDerivative q t‖ ≤ M) {q : ℂ} (hq : ‖q‖ ≤ r)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖(∫ t : ℝ in 0..1, (1 - (t : ℂ)) ^ (N - 1) * pathFactor q t) -
        1 / ((N : ℂ) * (1 - q))‖ ≤ M / ((N : ℝ) * (N + 1 : ℝ)) := by
  have hh := weighted_pathFactor_remainder hr hM hq (N - 1)
  have h0 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  have h1 : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by linarith
  rw [h0, h1] at hh
  simpa only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast, one_div,
    mul_inv_rev, mul_comm] using hh

end Paper.Lambert
