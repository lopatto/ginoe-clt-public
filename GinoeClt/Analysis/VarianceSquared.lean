/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.VarianceKernel

/-! # Squared-S Gaussian approximation and its integrated error -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace Paper.Kernel

lemma abs_norm_sq_sub_le (s u : ℂ) :
    |‖s‖ ^ 2 - ‖u‖ ^ 2| ≤ ‖s - u‖ * (‖s‖ + ‖u‖) := by
  rw [show ‖s‖ ^ 2 - ‖u‖ ^ 2 = (‖s‖ - ‖u‖) * (‖s‖ + ‖u‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le s u) (add_nonneg (norm_nonneg _) (norm_nonneg _))

lemma scalar_squared_error {t g e : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1) :
    (t * g + e) * (2 * g + t * g + e) ≤ 3 * t * g ^ 2 + 5 * e := by
  have htt : t * t ≤ t := mul_le_of_le_one_left ht ht1
  have htg : t * g ≤ 1 := (mul_le_of_le_one_left hg ht1).trans hg1
  have hge : g * e ≤ e := mul_le_of_le_one_left he hg1
  have htge : t * g * e ≤ e := mul_le_of_le_one_left he htg
  have hee : e * e ≤ e := mul_le_of_le_one_left he he1
  have httg := mul_le_mul_of_nonneg_right htt (sq_nonneg g)
  nlinarith

lemma squared_norm_error_of_gaussian_bound {C t g e : ℝ} (hC : 0 ≤ C)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hg : 0 ≤ g) (hg1 : g ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1)
    {s u : ℂ} (hu : ‖u‖ ≤ C * g) (hδ : ‖s - u‖ ≤ C * t * g + C * e) :
    |‖s‖ ^ 2 - ‖u‖ ^ 2| ≤ 3 * C ^ 2 * t * g ^ 2 + 5 * C ^ 2 * e := by
  have hs : ‖s‖ ≤ ‖s - u‖ + ‖u‖ := by
    simpa only [sub_add_cancel] using norm_add_le (s - u) u
  have hsum : ‖s‖ + ‖u‖ ≤ 2 * C * g + (C * t * g + C * e) := by linarith
  calc |‖s‖ ^ 2 - ‖u‖ ^ 2| ≤ ‖s - u‖ * (‖s‖ + ‖u‖) := abs_norm_sq_sub_le s u
    _ ≤ (C * t * g + C * e) * (2 * C * g + (C * t * g + C * e)) :=
      mul_le_mul hδ hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = C ^ 2 * ((t * g + e) * (2 * g + t * g + e)) := by ring
    _ ≤ C ^ 2 * (3 * t * g ^ 2 + 5 * e) :=
      mul_le_mul_of_nonneg_left (scalar_squared_error ht ht1 hg hg1 he he1) (sq_nonneg C)
    _ = _ := by ring

lemma norm_U_sq_gaussian_error_le {d : ℝ} (hd : 0 < d) {N : ℕ} {z w : ℂ}
    (hz : d ≤ z.im) (hw : d ≤ w.im) :
    |‖U N z w‖ ^ 2 - (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)| ≤
      (1 / (4 * Real.pi ^ 2 * d ^ 2)) * ‖z - w‖ ^ 2 * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) := by
  have hz0 := hd.trans_le hz
  have hw0 := hd.trans_le hw
  have hprod : d ^ 2 ≤ z.im * w.im := by
    have hh := mul_le_mul hz hw hd.le hz0.le
    nlinarith
  have hratio : ‖z - w‖ ^ 2 / (4 * z.im * w.im) ≤ ‖z - w‖ ^ 2 / (4 * d ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  rw [norm_U_sq hz0 hw0]
  have hid : (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) *
      (1 + ‖z - w‖ ^ 2 / (4 * z.im * w.im)) -
      (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) =
      (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) * (‖z - w‖ ^ 2 / (4 * z.im * w.im)) := by ring
  rw [hid, abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hratio
    (by positivity : 0 ≤ (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2))
  convert! hh using 1; ring

/-- The manuscript's pointwise squared-kernel estimate, with the full Gaussian
exponent preserved. All constants precede N and the two points. -/
theorem squared_S_gaussian_error {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 2 ≤ N → ∀ z ∈ closure A, ∀ w ∈ closure A,
      |‖S N (rescale N z) (rescale N w)‖ ^ 2 -
        (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)| ≤
        C * ((‖z - w‖ ^ 2 + (N : ℝ)⁻¹) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) +
          Real.exp (-c * (N : ℝ))) := by
  obtain ⟨C, c, hC, hc, hK⟩ := kernel_estimates hA
  let B : ℝ := 1 / (4 * Real.pi ^ 2 * bulkDistance A ^ 2)
  let K : ℝ := 8 * C ^ 2 + B + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK0 : 0 < K := by dsimp [K]; positivity
  refine ⟨K, c, hK0, hc, fun N hN z hz w hw => ?_⟩
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  let g : ℝ := Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2)
  let e : ℝ := Real.exp (-c * (N : ℝ))
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hg1 : g ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hn]) (sq_nonneg _))
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have ht0 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hn.le
  have ht1 : (N : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hn).mpr hn1
  have hgg : g ^ 2 = Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) := by
    change Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) ^ 2 = _
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpair := hK N hN z hz w hw
  have herr : ‖S N (rescale N z) (rescale N w) - U N z w‖ ≤ C * (N : ℝ)⁻¹ * g + C * e := by
    convert! hpair.2.2.2 using 1
  have hSU := squared_norm_error_of_gaussian_bound hC.le ht0 ht1 hg0 hg1 he0 he1 hpair.2.2.1 herr
  rw [hgg] at hSU
  have hU := norm_U_sq_gaussian_error_le (bulkDistance_pos hA)
    (bulkDistance_le_im hA hz) (bulkDistance_le_im hA hw) (N := N)
  change |‖U N z w‖ ^ 2 - (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)| ≤
    B * ‖z - w‖ ^ 2 * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) at hU
  have h3 : 3 * C ^ 2 ≤ K := by dsimp [K]; nlinarith [sq_nonneg C]
  have h5 : 5 * C ^ 2 ≤ K := by dsimp [K]; nlinarith [sq_nonneg C]
  have hBK : B ≤ K := by dsimp [K]; nlinarith [sq_nonneg C]
  have hsum := (abs_add_le
    (‖S N (rescale N z) (rescale N w)‖ ^ 2 - ‖U N z w‖ ^ 2)
    (‖U N z w‖ ^ 2 - (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)))
  have h1 := mul_le_mul_of_nonneg_right h3 (mul_nonneg ht0 (Real.exp_pos (-(N : ℝ) * ‖z - w‖ ^ 2)).le)
  have h2 := mul_le_mul_of_nonneg_right h5 he0
  have h3' := mul_le_mul_of_nonneg_right hBK (mul_nonneg (sq_nonneg ‖z - w‖) (Real.exp_pos (-(N : ℝ) * ‖z - w‖ ^ 2)).le)
  have hid : (‖S N (rescale N z) (rescale N w)‖ ^ 2 - ‖U N z w‖ ^ 2) +
      (‖U N z w‖ ^ 2 - (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) =
      ‖S N (rescale N z) (rescale N w)‖ ^ 2 -
        (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2) := by ring
  rw [hid] at hsum
  dsimp only [e] at hSU h2
  nlinarith

def squaredKernelError (A : Set ℂ) (N : ℕ) : ℝ := (N : ℝ) ^ 2 *
  (∫ z in A, ∫ w in A, ‖S N (rescale N z) (rescale N w)‖ ^ 2 -
    (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2))

/-- The integrated squared-S error is O(1), as required by the variance
calculation. This is an estimate for the actual kernels only. -/
theorem squaredKernelError_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    squaredKernelError A =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  let μ := (volume : Measure ℂ).restrict A
  let : IsFiniteMeasure μ := isFiniteMeasure_area hA
  obtain ⟨C, c, hC, hc, hK⟩ := squared_S_gaussian_error hA
  have hdec := nat_pow_mul_exp_tendsto_zero hc 2
  have hexp : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ)) < 1 :=
    (tendsto_order.1 hdec).2 1 (by norm_num)
  apply IsBigO.of_bound (C * (2 * volume.real A * Real.pi + volume.real A ^ 2))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hexp] with N hN hExp
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let g : ℂ × ℂ → ℝ := fun p => Real.exp (-(N : ℝ) * ‖p.1 - p.2‖ ^ 2)
  let m : ℂ × ℂ → ℝ := fun p => ‖p.1 - p.2‖ ^ 2 * g p
  let E : ℂ × ℂ → ℝ := fun p => ‖S N (rescale N p.1) (rescale N p.2)‖ ^ 2 - (1 / Real.pi ^ 2) * g p
  let M : ℂ × ℂ → ℝ := fun p => C * ((‖p.1 - p.2‖ ^ 2 + (N : ℝ)⁻¹) * g p + Real.exp (-c * (N : ℝ)))
  have hgc : Continuous g := by dsimp only [g]; fun_prop
  have hmc : Continuous m := by dsimp only [m]; fun_prop
  have hEc : Continuous E := ((continuous_rescaledKernel _ (continuous_S N) N).norm.pow 2).sub (hgc.const_mul _)
  have hMc : Continuous M := by dsimp only [M]; fun_prop
  have hgi : Integrable g (μ.prod μ) := by
    convert! integrable_doubleKernel_of_continuous hA (K := fun z w => g (z, w)) (by convert! hgc using 1) using 1
  have hmi : Integrable m (μ.prod μ) := by
    convert! integrable_doubleKernel_of_continuous hA (K := fun z w => m (z, w)) (by convert! hmc using 1) using 1
  have hEi : Integrable E (μ.prod μ) := by
    convert! integrable_doubleKernel_of_continuous hA (K := fun z w => E (z, w)) (by convert! hEc using 1) using 1
  have hMi : Integrable M (μ.prod μ) := by
    convert! integrable_doubleKernel_of_continuous hA (K := fun z w => M (z, w)) (by convert! hMc using 1) using 1
  have hmem : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, p ∈ A ×ˢ A := by
    apply (Measure.ae_prod_iff_ae_ae (hA.1.measurableSet.prod hA.1.measurableSet)).2
    filter_upwards [ae_restrict_mem hA.1.measurableSet] with z hz
    filter_upwards [ae_restrict_mem hA.1.measurableSet] with w hw
    exact ⟨hz, hw⟩
  have hpoint : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, ‖E p‖ ≤ M p := by
    filter_upwards [hmem] with p hp
    simpa only [E, M, g, Real.norm_eq_abs] using hK N hN p.1 (subset_closure hp.1) p.2 (subset_closure hp.2)
  have herr := norm_integral_le_of_norm_le hMi hpoint
  have hMajBody : M = fun p => C * ((m p + (N : ℝ)⁻¹ * g p) + Real.exp (-c * (N : ℝ))) := by
    funext p
    dsimp only [M, m]
    ring
  have hsum : Integrable (fun p => m p + (N : ℝ)⁻¹ * g p) (μ.prod μ) := by
    convert! hmi.add (hgi.const_mul (N : ℝ)⁻¹) using 1
  have hMajEq : (∫ p, M p ∂μ.prod μ) = C * ((∫ p, m p ∂μ.prod μ) +
      (N : ℝ)⁻¹ * (∫ p, g p ∂μ.prod μ) + Real.exp (-c * (N : ℝ)) * volume.real A ^ 2) := by
    rw [hMajBody, integral_const_mul,
      integral_add hsum (integrable_const (Real.exp (-c * (N : ℝ)))),
      integral_add hmi (hgi.const_mul (N : ℝ)⁻¹), integral_const_mul, integral_const]
    have hmass : (μ.prod μ).real univ = volume.real A ^ 2 := by
      rw [← Set.univ_prod_univ, measureReal_prod_prod]
      simp only [μ, Measure.real, Measure.restrict_apply_univ, pow_two]
    rw [hmass]
    simp only [smul_eq_mul, mul_comm]
  have hgBound : (∫ p, g p ∂μ.prod μ) ≤ volume.real A * (Real.pi / (N : ℝ)) := by
    rw [integral_prod g hgi]
    convert! gaussian_doubleIntegral_le hA hn using 1
  have hmBound : (∫ p, m p ∂μ.prod μ) ≤ volume.real A * (Real.pi / (N : ℝ) ^ 2) := by
    rw [integral_prod m hmi]
    convert! gaussian_secondMoment_doubleIntegral_le hA hn using 1
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hn.le
  have hGmul := mul_le_mul_of_nonneg_left hgBound hNinv
  have hUpper : C * ((∫ p, m p ∂μ.prod μ) + (N : ℝ)⁻¹ * (∫ p, g p ∂μ.prod μ) +
      Real.exp (-c * (N : ℝ)) * volume.real A ^ 2) ≤
      C * (volume.real A * (Real.pi / (N : ℝ) ^ 2) + (N : ℝ)⁻¹ *
        (volume.real A * (Real.pi / (N : ℝ))) + Real.exp (-c * (N : ℝ)) * volume.real A ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith
  rw [hMajEq] at herr
  have herr' := herr.trans hUpper
  rw [integral_prod E hEi] at herr'
  have hS : |squaredKernelError A N| = (N : ℝ) ^ 2 * ‖∫ z in A, ∫ w in A, E (z, w)‖ := by
    change |(N : ℝ) ^ 2 * (∫ z in A, ∫ w in A, E (z, w))| = _
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
  simp only [Real.norm_eq_abs, norm_one, mul_one]
  rw [hS]
  have hMul := mul_le_mul_of_nonneg_left herr' (sq_nonneg (N : ℝ))
  have hRat1 : (N : ℝ) ^ 2 * (Real.pi / (N : ℝ) ^ 2) = Real.pi := by field_simp
  have hRat2 : (N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (Real.pi / (N : ℝ))) = Real.pi := by field_simp
  have hArea : 0 ≤ volume.real A ^ 2 := sq_nonneg _
  have hExpMul := mul_le_mul_of_nonneg_right hExp.le hArea
  change (N : ℝ) ^ 2 * ‖∫ z in A, ∫ w in A, E (z, w)‖ ≤
    (N : ℝ) ^ 2 * (C * (volume.real A * (Real.pi / (N : ℝ) ^ 2) + (N : ℝ)⁻¹ *
      (volume.real A * (Real.pi / (N : ℝ))) + Real.exp (-c * (N : ℝ)) * volume.real A ^ 2)) at hMul
  have hAlg : (N : ℝ) ^ 2 * (C * (volume.real A * (Real.pi / (N : ℝ) ^ 2) + (N : ℝ)⁻¹ *
      (volume.real A * (Real.pi / (N : ℝ))) + Real.exp (-c * (N : ℝ)) * volume.real A ^ 2)) =
      C * (2 * volume.real A * Real.pi + ((N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ))) * volume.real A ^ 2) := by
    calc _ = C * (volume.real A * ((N : ℝ) ^ 2 * (Real.pi / (N : ℝ) ^ 2)) +
        volume.real A * ((N : ℝ) ^ 2 * ((N : ℝ)⁻¹ * (Real.pi / (N : ℝ)))) +
        ((N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ))) * volume.real A ^ 2) := by ring
      _ = _ := by rw [hRat1, hRat2]; ring
  rw [hAlg] at hMul
  exact hMul.trans (mul_le_mul_of_nonneg_left (by linarith [hExpMul]) hC.le)

lemma squaredKernelError_eq {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    squaredKernelError A N = (N : ℝ) ^ 2 *
      (∫ z in A, ∫ w in A, ‖S N (rescale N z) (rescale N w)‖ ^ 2) -
      ((N : ℝ) ^ 2 / Real.pi ^ 2) *
        (∫ z in A, ∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) := by
  let μ := (volume : Measure ℂ).restrict A
  have hSc : Continuous (Function.uncurry (fun z w => ‖S N (rescale N z) (rescale N w)‖ ^ 2)) :=
    (continuous_rescaledKernel _ (continuous_S N) N).norm.pow 2
  have hGc : Continuous (Function.uncurry (fun z w : ℂ => Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2))) := by fun_prop
  have hSi := integrable_doubleKernel_of_continuous hA hSc
  have hGi := integrable_doubleKernel_of_continuous hA hGc
  have hh := integral_integral_sub hSi (hGi.const_mul (1 / Real.pi ^ 2))
  have hsub : (∫ z in A, ∫ w in A, ‖S N (rescale N z) (rescale N w)‖ ^ 2 -
      (1 / Real.pi ^ 2) * Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) =
      (∫ z in A, ∫ w in A, ‖S N (rescale N z) (rescale N w)‖ ^ 2) -
        (1 / Real.pi ^ 2) * (∫ z in A, ∫ w in A, Real.exp (-(N : ℝ) * ‖z - w‖ ^ 2)) := by
    simp only [integral_const_mul] at hh
    convert! hh using 1
  rw [squaredKernelError, hsub]
  ring

end Paper.Kernel
