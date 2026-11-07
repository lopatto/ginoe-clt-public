/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Estimates
public import GinoeClt.Analysis.GaussianIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Purely analytic kernel estimates for the variance calculation

No ensemble correlation or count-variance identity is assumed or asserted here.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace Paper.Kernel

lemma integrable_S_diagonal {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    IntegrableOn (fun z => S N (rescale N z) (rescale N z)) A := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_area hA
  obtain ⟨C, hC⟩ := exists_S_bound hA N
  have hc : Continuous (fun z => S N (rescale N z) (rescale N z)) :=
    (continuous_rescaledKernel _ (continuous_S N) N).comp (continuous_id.prodMk continuous_id)
  refine (integrable_const (C : ℝ)).mono' hc.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hA.1.measurableSet] with z hz
  exact hC z (subset_closure hz) z (subset_closure hz)

def diagonalKernelError (A : Set ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * (∫ z in A, S N (rescale N z) (rescale N z)) -
    (((N : ℝ) / Real.pi * volume.real A : ℝ) : ℂ)

lemma diagonalKernelError_eq {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    diagonalKernelError A N = (N : ℂ) *
      (∫ z in A, S N (rescale N z) (rescale N z) - ((1 / Real.pi : ℝ) : ℂ)) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_area hA
  rw [integral_sub (integrable_S_diagonal hA N) (integrable_const _), integral_const]
  simp only [diagonalKernelError, Measure.real, Measure.restrict_apply_univ, Complex.real_smul]
  push_cast
  ring

lemma nat_pow_mul_exp_tendsto_zero {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ k * Real.exp (-c * (N : ℝ))) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  convert! hh using 1
  ext N
  change (N : ℝ) ^ k * Real.exp (-c * (N : ℝ)) = (N : ℝ) ^ (k : ℝ) * Real.exp (-c * (N : ℝ))
  rw [Real.rpow_natCast]

/-- Equation (11)'s diagonal integral estimate, without any correlation-law input. -/
theorem diagonalKernelError_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    diagonalKernelError A =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_area hA
  obtain ⟨C, c, hC, hc, hK⟩ := kernel_estimates hA
  have hdec : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-c * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [pow_one] using nat_pow_mul_exp_tendsto_zero hc 1
  have hexp : ∀ᶠ N : ℕ in atTop, (N : ℝ) * Real.exp (-c * (N : ℝ)) < 1 :=
    (tendsto_order.1 hdec).2 1 (by norm_num)
  apply IsBigO.of_bound (2 * C * volume.real A)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hexp] with N hN hE
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpoint : ∀ᵐ z ∂volume.restrict A,
      ‖S N (rescale N z) (rescale N z) - ((1 / Real.pi : ℝ) : ℂ)‖ ≤
        C / (N : ℝ) + C * Real.exp (-c * (N : ℝ)) := by
    filter_upwards [ae_restrict_mem hA.1.measurableSet] with z hz
    have hzcl := subset_closure hz
    have hzim : 0 < z.im := (hA.2.2.1 hzcl).2
    have hh := (hK N hN z hzcl z hzcl).2.2.2
    rw [U_diag N hzim, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, Real.exp_zero, mul_one] at hh
    exact hh
  have hInt := norm_integral_le_of_norm_le_const hpoint
  rw [diagonalKernelError_eq hA N, norm_mul, Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left hInt hN0.le
  have hmass : (volume.restrict A).real univ = volume.real A := by
    simp only [Measure.real, Measure.restrict_apply_univ]
  rw [hmass] at hh
  have hArea : 0 ≤ volume.real A := ENNReal.toReal_nonneg
  have hNC : (N : ℝ) * (C / (N : ℝ)) = C := by field_simp
  simp only [norm_one, mul_one]
  have hmul := mul_le_mul_of_nonneg_right hE.le (mul_nonneg hC.le hArea)
  calc (N : ℝ) * ‖∫ z in A, S N (rescale N z) (rescale N z) - ((1 / Real.pi : ℝ) : ℂ)‖ ≤
      (N : ℝ) * ((C / (N : ℝ) + C * Real.exp (-c * (N : ℝ))) * volume.real A) := hh
    _ = ((N : ℝ) * (C / (N : ℝ))) * volume.real A +
        ((N : ℝ) * Real.exp (-c * (N : ℝ))) * (C * volume.real A) := by ring
    _ ≤ 2 * C * volume.real A := by rw [hNC]; nlinarith

lemma integrable_doubleKernel_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) {K : ℂ → ℂ → E} (hKm : StronglyMeasurable (Function.uncurry K))
    {B : ℝ} (hB : ∀ z ∈ A, ∀ w ∈ A, ‖K z w‖ ≤ B) :
    Integrable (Function.uncurry K) ((volume.restrict A).prod (volume.restrict A)) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hmem : ∀ᵐ p : ℂ × ℂ ∂(volume.restrict A).prod (volume.restrict A), p ∈ A ×ˢ A := by
    apply (Measure.ae_prod_iff_ae_ae (hA.prod hA)).2
    filter_upwards [ae_restrict_mem hA] with z hz
    filter_upwards [ae_restrict_mem hA] with w hw
    exact ⟨hz, hw⟩
  refine (integrable_const B).mono' hKm.aestronglyMeasurable ?_
  filter_upwards [hmem] with p hp
  exact hB p.1 hp.1 p.2 hp.2

lemma norm_doubleIntegral_le_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) {K : ℂ → ℂ → E} (hKm : StronglyMeasurable (Function.uncurry K))
    {B : ℝ} (hB : ∀ z ∈ A, ∀ w ∈ A, ‖K z w‖ ≤ B) :
    ‖∫ z in A, ∫ w in A, K z w‖ ≤ B * volume.real A ^ 2 := by
  let μ := (volume : Measure ℂ).restrict A
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hInt := integrable_doubleKernel_of_bound hA hb hKm hB
  have hbound : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, ‖K p.1 p.2‖ ≤ B := by
    have hmem : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, p ∈ A ×ˢ A := by
      apply (Measure.ae_prod_iff_ae_ae (hA.prod hA)).2
      filter_upwards [ae_restrict_mem hA] with z hz
      filter_upwards [ae_restrict_mem hA] with w hw
      exact ⟨hz, hw⟩
    filter_upwards [hmem] with p hp
    exact hB p.1 hp.1 p.2 hp.2
  have heq : (∫ z in A, ∫ w in A, K z w) = ∫ p : ℂ × ℂ, K p.1 p.2 ∂μ.prod μ := by
    symm
    convert! integral_prod (Function.uncurry K) hInt using 1
  rw [heq]
  have hh := norm_integral_le_of_norm_le_const hbound
  have hmass : (μ.prod μ).real univ = volume.real A ^ 2 := by
    rw [← Set.univ_prod_univ, measureReal_prod_prod]
    simp only [μ, Measure.real, Measure.restrict_apply_univ, pow_two]
  rw [hmass] at hh
  exact hh

lemma integrable_doubleKernel_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {K : ℂ → ℂ → E} (hK : Continuous (Function.uncurry K)) :
    Integrable (Function.uncurry K) ((volume.restrict A).prod (volume.restrict A)) := by
  obtain ⟨B, hB⟩ := ((admissible_closure_isCompact hA).prod
    (admissible_closure_isCompact hA)).exists_bound_of_continuousOn hK.continuousOn
  apply integrable_doubleKernel_of_bound hA.1.measurableSet (admissible_isBounded hA) hK.stronglyMeasurable
  intro z hz w hw
  exact hB (z, w) ⟨subset_closure hz, subset_closure hw⟩

def diKernelTerm (A : Set ℂ) (N : ℕ) : ℂ := (N : ℂ) ^ 2 *
  (∫ z in A, ∫ w in A, D N (rescale N z) (rescale N w) * I N (rescale N z) (rescale N w))

/-- The D-I variance kernel contribution tends to zero exponentially up to its
fixed polynomial prefactor. This is purely an analytic statement. -/
theorem diKernelTerm_tendsto_zero {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    Tendsto (diKernelTerm A) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hc, hK⟩ := kernel_estimates hA
  have hbound : ∀ᶠ N : ℕ in atTop, ‖diKernelTerm A N‖ ≤
      (N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ)) * (C ^ 2 * volume.real A ^ 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hE0 : 0 ≤ Real.exp (-c * (N : ℝ)) := (Real.exp_pos _).le
    have hE1 : Real.exp (-c * (N : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hn)
    have hpoint : ∀ z ∈ A, ∀ w ∈ A,
        ‖D N (rescale N z) (rescale N w) * I N (rescale N z) (rescale N w)‖ ≤
          C ^ 2 * Real.exp (-c * (N : ℝ)) := by
      intro z hz w hw
      have hh := (hK N hN z (subset_closure hz) w (subset_closure hw)).1
      have hD : ‖D N (rescale N z) (rescale N w)‖ ≤ C * Real.exp (-c * (N : ℝ)) := by
        linarith [norm_nonneg (I N (rescale N z) (rescale N w))]
      have hI : ‖I N (rescale N z) (rescale N w)‖ ≤ C * Real.exp (-c * (N : ℝ)) := by
        linarith [norm_nonneg (D N (rescale N z) (rescale N w))]
      rw [norm_mul]
      have hp := mul_le_mul hD hI (norm_nonneg _) (mul_nonneg hC.le hE0)
      have he := mul_le_mul_of_nonneg_left hE1 hE0
      nlinarith [sq_nonneg C]
    have hcont : Continuous (Function.uncurry (fun z w =>
        D N (rescale N z) (rescale N w) * I N (rescale N z) (rescale N w))) :=
      (continuous_rescaledKernel _ (continuous_D N) N).mul
        (continuous_rescaledKernel _ (continuous_I N) N)
    have hh := norm_doubleIntegral_le_of_bound hA.1.measurableSet (admissible_isBounded hA)
      hcont.stronglyMeasurable hpoint
    rw [diKernelTerm, norm_mul, norm_pow, Complex.norm_natCast]
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (N : ℝ))
    nlinarith
  apply squeeze_zero_norm' hbound
  simpa only [zero_mul] using (nat_pow_mul_exp_tendsto_zero hc 2).mul_const (C ^ 2 * volume.real A ^ 2)

theorem diKernelTerm_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    diKernelTerm A =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  (diKernelTerm_tendsto_zero hA).isBigO_one ℝ

lemma gaussian_doubleIntegral_le {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {a : ℝ} (ha : 0 < a) :
    (∫ z in A, ∫ w in A, Real.exp (-a * ‖z - w‖ ^ 2)) ≤ volume.real A * (Real.pi / a) := by
  let μ := (volume : Measure ℂ).restrict A
  let : IsFiniteMeasure μ := isFiniteMeasure_area hA
  have hcont : Continuous (fun p : ℂ × ℂ => Real.exp (-a * ‖p.1 - p.2‖ ^ 2)) := by fun_prop
  have hprod := integrable_doubleKernel_of_continuous hA
    (K := fun z w : ℂ => Real.exp (-a * ‖z - w‖ ^ 2)) (by convert! hcont using 1)
  have hpoint : ∀ z : ℂ, (∫ w in A, Real.exp (-a * ‖z - w‖ ^ 2)) ≤ Real.pi / a := by
    intro z
    have hi := (Paper.GaussianIntegrals.integrable_gaussian ha).comp_sub_left z
    have hh := setIntegral_le_integral (s := A) hi (ae_of_all _ (fun w => (Real.exp_pos _).le))
    have heq : (∫ w : ℂ, Real.exp (-a * ‖z - w‖ ^ 2)) = Real.pi / a := by
      convert! (integral_sub_left_eq_self (μ := (volume : Measure ℂ))
        (fun u : ℂ => Real.exp (-a * ‖u‖ ^ 2)) z).trans (Paper.GaussianIntegrals.gaussian_mass ha) using 1
    exact hh.trans_eq heq
  have hh := integral_mono_ae hprod.integral_prod_left (integrable_const (Real.pi / a))
    (ae_of_all μ hpoint)
  simpa only [Function.uncurry_apply_pair, integral_const, μ, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using hh

lemma gaussian_secondMoment_doubleIntegral_le {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {a : ℝ} (ha : 0 < a) :
    (∫ z in A, ∫ w in A, ‖z - w‖ ^ 2 * Real.exp (-a * ‖z - w‖ ^ 2)) ≤
      volume.real A * (Real.pi / a ^ 2) := by
  let μ := (volume : Measure ℂ).restrict A
  let : IsFiniteMeasure μ := isFiniteMeasure_area hA
  have hcont : Continuous (fun p : ℂ × ℂ => ‖p.1 - p.2‖ ^ 2 * Real.exp (-a * ‖p.1 - p.2‖ ^ 2)) := by fun_prop
  have hprod := integrable_doubleKernel_of_continuous hA
    (K := fun z w : ℂ => ‖z - w‖ ^ 2 * Real.exp (-a * ‖z - w‖ ^ 2)) (by convert! hcont using 1)
  have hpoint : ∀ z : ℂ, (∫ w in A, ‖z - w‖ ^ 2 * Real.exp (-a * ‖z - w‖ ^ 2)) ≤ Real.pi / a ^ 2 := by
    intro z
    have hi := (Paper.GaussianIntegrals.integrable_gaussian_second_moment ha).comp_sub_left z
    have hh := setIntegral_le_integral (s := A) hi
      (ae_of_all _ (fun w => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
    have heq : (∫ w : ℂ, ‖z - w‖ ^ 2 * Real.exp (-a * ‖z - w‖ ^ 2)) = Real.pi / a ^ 2 := by
      convert! (integral_sub_left_eq_self (μ := (volume : Measure ℂ))
        (fun u : ℂ => ‖u‖ ^ 2 * Real.exp (-a * ‖u‖ ^ 2)) z).trans
          (Paper.GaussianIntegrals.gaussian_second_moment ha) using 1
    exact hh.trans_eq heq
  have hh := integral_mono_ae hprod.integral_prod_left (integrable_const (Real.pi / a ^ 2))
    (ae_of_all μ hpoint)
  simpa only [Function.uncurry_apply_pair, integral_const, μ, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using hh

end Paper.Kernel
