/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Estimates
public import GinoeClt.Trace.GaussianBounds
public import GinoeClt.Kernel.Integrability
public import GinoeClt.Trace.AmplitudeIntegral
public import GinoeClt.Analysis.ExponentialErrors

/-! # Ordinary finite-product propagation of mixed Gaussian and exponential errors -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Real BigOperators

namespace Paper.Trace

theorem mixed_product_scalar_bound {g p e : ℝ}
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (2 * g + e) * (p + e) ≤ 6 * (g * p + e) := by
  have hge : g * e ≤ e := by nlinarith only [hg1, he0]
  have hep : e * p ≤ e := by nlinarith only [hp1, he0]
  have hee : e * e ≤ e := by nlinarith only [he0, he1]
  have hgp : 0 ≤ g * p := mul_nonneg hg0 hp0
  nlinarith only [hge, hep, hee, hgp]

theorem mixed_difference_scalar_bound {g p e δ : ℝ}
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (δ * g + e) * (p + e) + g * (δ * p + e) ≤ 6 * (δ * g * p + e) := by
  have hdg : δ * g ≤ 1 := (mul_le_mul hδ1 hg1 hg0 zero_le_one).trans_eq (by ring)
  have hδge : δ * g * e ≤ e := by nlinarith only [hdg, he0]
  have hge : g * e ≤ e := by nlinarith only [hg1, he0]
  have hep : e * p ≤ e := by nlinarith only [hp1, he0]
  have hee : e * e ≤ e := by nlinarith only [he0, he1]
  have hδgp : 0 ≤ δ * g * p := mul_nonneg (mul_nonneg hδ0 hg0) hp0
  nlinarith only [hδge, hge, hep, hee, hδgp]

/-- Ordinary finite-product expansion, keeping the common exponential rate
separate from the Gaussian product. No cyclic structure or cancellation is used. -/
theorem mixed_product_bounds {n : ℕ} {L δ e : ℝ} (hL : 1 ≤ L)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (a b : Fin n → ℂ) (g : Fin n → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1)
    (hb : ∀ i, ‖b i‖ ≤ L * g i)
    (herr : ∀ i, ‖a i - b i‖ ≤ L * (δ * g i + e)) :
    ‖∏ i, a i‖ ≤ (6 * L) ^ n * ((∏ i, g i) + e) ∧
      ‖(∏ i, a i) - ∏ i, b i‖ ≤ (6 * L) ^ n * (δ * (∏ i, g i) + e) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  induction n with
  | zero =>
      simpa using (show (1 : ℝ) ≤ 1 + e ∧ 0 ≤ δ + e from
        ⟨by linarith only [he0], add_nonneg hδ0 he0⟩)
  | succ n ih =>
      have ht := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => g i.succ)
        (fun i => hg0 i.succ) (fun i => hg1 i.succ)
        (fun i => hb i.succ) (fun i => herr i.succ)
      let p : ℝ := ∏ i : Fin n, g i.succ
      let H : ℝ := (6 * L) ^ n
      have hp0 : 0 ≤ p := Finset.prod_nonneg fun i _ => hg0 i.succ
      have hp1 : p ≤ 1 := Finset.prod_le_one₀ (fun i _ => hg0 i.succ) (fun i _ => hg1 i.succ)
      have hH0 : 0 ≤ H := by dsimp [H]; positivity
      have hgδ : δ * g 0 ≤ g 0 := by nlinarith only [hδ1, hg0 0]
      have hhead : ‖a 0‖ ≤ L * (2 * g 0 + e) := by
        have hh : ‖a 0‖ ≤ ‖b 0‖ + ‖a 0 - b 0‖ := by
          calc
            _ = ‖b 0 + (a 0 - b 0)‖ := congrArg norm (by ring)
            _ ≤ _ := norm_add_le _ _
        have hs := mul_le_mul_of_nonneg_left hgδ hL0
        nlinarith only [hh, hb 0, herr 0, hs]
      have hcoeff : 0 ≤ L * H := mul_nonneg hL0 hH0
      constructor
      · rw [Fin.prod_univ_succ, Fin.prod_univ_succ, norm_mul]
        calc
          _ ≤ (L * (2 * g 0 + e)) * (H * (p + e)) :=
            mul_le_mul hhead ht.1 (norm_nonneg _)
              (mul_nonneg hL0 (add_nonneg (mul_nonneg (by norm_num) (hg0 0)) he0))
          _ = (L * H) * ((2 * g 0 + e) * (p + e)) := by ring
          _ ≤ (L * H) * (6 * (g 0 * p + e)) :=
            mul_le_mul_of_nonneg_left
              (mixed_product_scalar_bound (hg0 0) (hg1 0) hp0 hp1 he0 he1) hcoeff
          _ = _ := by dsimp [H, p]; rw [pow_succ]; ring
      · have hx : (∏ i, a i) - ∏ i, b i =
            (a 0 - b 0) * (∏ i : Fin n, a i.succ) +
              b 0 * ((∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ) := by
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
          ring
        rw [hx, Fin.prod_univ_succ]
        calc
          _ ≤ ‖a 0 - b 0‖ * ‖∏ i : Fin n, a i.succ‖ +
              ‖b 0‖ * ‖(∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ‖ := by
            exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
          _ ≤ (L * (δ * g 0 + e)) * (H * (p + e)) +
              (L * g 0) * (H * (δ * p + e)) :=
            add_le_add
              (mul_le_mul (herr 0) ht.1 (norm_nonneg _)
                (mul_nonneg hL0 (add_nonneg (mul_nonneg hδ0 (hg0 0)) he0)))
              (mul_le_mul (hb 0) ht.2 (norm_nonneg _) (mul_nonneg hL0 (hg0 0)))
          _ = (L * H) * ((δ * g 0 + e) * (p + e) + g 0 * (δ * p + e)) := by ring
          _ ≤ (L * H) * (6 * (δ * g 0 * p + e)) :=
            mul_le_mul_of_nonneg_left
              (mixed_difference_scalar_bound (hg0 0) (hg1 0) hp0 hp1 he0 he1 hδ0 hδ1) hcoeff
          _ = _ := by dsimp [H, p]; rw [pow_succ]; ring

theorem prod_cycleGaussians (N : ℕ) {k : ℕ} (z : Fin k → ℂ) :
    (∏ i, Real.exp (-(N : ℝ) / 2 * ‖z i - z (finRotate k i)‖ ^ 2)) =
      Real.exp (-(N : ℝ) / 2 * cycleEnergy z) := by
  rw [← Real.exp_sum, ← Finset.mul_sum]
  rfl

/-- One rate is chosen before the cycle order; only the prefactor varies with k. -/
theorem cyclic_product_kernel_error_bulk {d : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ z : Fin k → ℂ, (∀ i, d ≤ (z i).im) → (∀ i, ‖z i‖ ≤ 1 - d) →
      ‖(∏ i, Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate k i)))) -
          ∏ i, Kernel.U N (z i) (z (finRotate k i))‖ ≤
        C / (N : ℝ) * Real.exp (-(N : ℝ) / 2 * cycleEnergy z) +
          C * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨K, c, hK, hc, hKernel⟩ := Kernel.kernel_estimates_bulk hd hdh
  let L : ℝ := max 1 K
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hKL : K ≤ L := le_max_right _ _
  refine ⟨c, hc, fun k => ⟨(6 * L) ^ k, by positivity, fun N hN z hzy hz => ?_⟩⟩
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hnp : 0 < (N : ℝ) := by linarith only [hn]
  let g : Fin k → ℝ := fun i => Real.exp (-(N : ℝ) / 2 * ‖z i - z (finRotate k i)‖ ^ 2)
  let a : Fin k → ℂ := fun i =>
    Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate k i)))
  let b : Fin k → ℂ := fun i => Kernel.U N (z i) (z (finRotate k i))
  have hg0 (i : Fin k) : 0 ≤ g i := (Real.exp_pos _).le
  have hg1 (i : Fin k) : g i ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hn]) (sq_nonneg _)
  have he0 : 0 ≤ Real.exp (-c * (N : ℝ)) := (Real.exp_pos _).le
  have he1 : Real.exp (-c * (N : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hnp.le
  have hδ0 : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hnp.le
  have hδ1 : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
  have hb (i : Fin k) : ‖b i‖ ≤ L * g i :=
    ((hKernel N hN (z i) (z (finRotate k i)) (hzy i) (hzy (finRotate k i))
      (hz i) (hz (finRotate k i))).2.2.1).trans (mul_le_mul_of_nonneg_right hKL (hg0 i))
  have herr (i : Fin k) : ‖a i - b i‖ ≤
      L * ((N : ℝ)⁻¹ * g i + Real.exp (-c * (N : ℝ))) := by
    have hh := (hKernel N hN (z i) (z (finRotate k i)) (hzy i) (hzy (finRotate k i))
      (hz i) (hz (finRotate k i))).2.2.2
    calc
      _ ≤ K / (N : ℝ) * g i + K * Real.exp (-c * (N : ℝ)) := hh
      _ = K * ((N : ℝ)⁻¹ * g i + Real.exp (-c * (N : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKL
        (add_nonneg (mul_nonneg hδ0 (hg0 i)) he0)
  have hh := (mixed_product_bounds hL hδ0 hδ1 he0 he1 a b g hg0 hg1 hb herr).2
  apply hh.trans_eq
  have hgp : (∏ i, g i) = Real.exp (-(N : ℝ) / 2 * cycleEnergy z) := prod_cycleGaussians N z
  rw [hgp]
  ring

theorem cyclic_product_kernel_error {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ z ∈ Set.univ.pi (fun _ : Fin k => closure A),
      ‖(∏ i, Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate k i)))) -
          ∏ i, Kernel.U N (z i) (z (finRotate k i))‖ ≤
        C / (N : ℝ) * Real.exp (-(N : ℝ) / 2 * cycleEnergy z) +
          C * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨c, hc, hh⟩ := cyclic_product_kernel_error_bulk
    (Kernel.bulkDistance_pos hA) (Kernel.bulkDistance_le_half hA)
  refine ⟨c, hc, fun k => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hh k
  exact ⟨C, hC, fun N hN z hz => hbound N hN z
    (fun i => Kernel.bulkDistance_le_im hA (hz i (Set.mem_univ i)))
    (fun i => Kernel.norm_le_one_sub_bulkDistance hA (hz i (Set.mem_univ i)))⟩

def scaledKernelIntegralError (A : Set ℂ) (N k : ℕ) : ℂ :=
  (N : ℂ) ^ k *
    ((∫ z in Set.univ.pi (fun _ : Fin k => A),
      ∏ i, Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate k i)))) -
      (∫ z in Set.univ.pi (fun _ : Fin k => A),
        ∏ i, Kernel.U N (z i) (z (finRotate k i))))

theorem scaled_kernel_integral_error_bound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ N : ℕ, 2 ≤ N → ‖scaledKernelIntegralError A N (n + 1)‖ ≤
        C₁ + C₂ * ((N : ℝ) ^ (n + 1) * Real.exp (-c * (N : ℝ))) := by
  obtain ⟨c, hc, hPoint⟩ := cyclic_product_kernel_error hA
  have hAfin : volume A ≠ ⊤ := (admissible_isBounded hA).measure_lt_top.ne
  have hAbound : ∀ z ∈ A, ‖z‖ ≤ 1 := fun z hz => (hA.2.2.1 (subset_closure hz)).1.le
  have hAim : ∀ z ∈ A, Kernel.bulkDistance A ≤ z.im :=
    fun z hz => Kernel.bulkDistance_le_im hA (subset_closure hz)
  refine ⟨c, hc, fun n => ?_⟩
  obtain ⟨K, hK, hbound⟩ := hPoint (n + 1)
  let B := Set.univ.pi (fun _ : Fin (n + 1) => A)
  have hB : MeasurableSet B := MeasurableSet.pi Set.countable_univ (fun _ _ => hA.1.measurableSet)
  have hvol : volume B = volume A ^ (n + 1) := by
    change Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℂ)) B = _
    rw [Measure.pi_pi]
    simp
  have hBfin : volume B ≠ ⊤ := by rw [hvol]; exact ENNReal.pow_ne_top hAfin
  have hBreal : volume.real B = volume.real A ^ (n + 1) := by
    simp only [measureReal_def, hvol, ENNReal.toReal_pow]
  refine ⟨K * volume.real A * (2 * Real.pi) ^ n,
    K * volume.real A ^ (n + 1), by positivity, by positivity, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hS := Kernel.integrableOn_source_cycle hA N (n + 1)
  have hU := (U_cycle_integral_difference (Kernel.bulkDistance_pos hA) n hA.1.measurableSet
    hAfin hAbound hAim hN1).1
  change IntegrableOn (fun z : Fin (n + 1) → ℂ =>
    ∏ i, Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate (n + 1) i)))) B at hS
  change IntegrableOn (fun z : Fin (n + 1) → ℂ =>
    ∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i))) B at hU
  have hGauss : IntegrableOn (fun z : Fin (n + 1) → ℂ =>
      Real.exp (-(N : ℝ) / 2 * cycleEnergy z)) B := by
    simpa only [neg_div] using
      (cycleGaussian_integral_split (by positivity : 0 < (N : ℝ) / 2) n A hAfin).1
  have hMass : (∫ z in B, Real.exp (-(N : ℝ) / 2 * cycleEnergy z)) ≤
      volume.real A * (Real.pi / ((N : ℝ) / 2)) ^ n := by
    simpa only [neg_div] using
      cycleGaussian_bound (by positivity : 0 < (N : ℝ) / 2) n A hAfin
  have hConst : IntegrableOn (fun _ : Fin (n + 1) → ℂ => K * Real.exp (-c * (N : ℝ))) B :=
    integrableOn_const hBfin
  have hDom := (hGauss.const_mul (K / (N : ℝ))).add hConst
  have hmem : ∀ᵐ z ∂volume.restrict B, z ∈ B := ae_restrict_mem hB
  have hAE : ∀ᵐ z ∂volume.restrict B,
      ‖(∏ i, Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate (n + 1) i)))) -
          ∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i))‖ ≤
        K / (N : ℝ) * Real.exp (-(N : ℝ) / 2 * cycleEnergy z) + K * Real.exp (-c * (N : ℝ)) := by
    filter_upwards [hmem] with z hz
    exact hbound N hN z (fun i hi => subset_closure (hz i hi))
  have hInt :
      ‖(∫ z in B, ∏ i, Kernel.S N (Kernel.rescale N (z i)) (Kernel.rescale N (z (finRotate (n + 1) i)))) -
          (∫ z in B, ∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i)))‖ ≤
        K / (N : ℝ) * (volume.real A * (Real.pi / ((N : ℝ) / 2)) ^ n) +
          volume.real B * (K * Real.exp (-c * (N : ℝ))) := by
    rw [← integral_sub hS hU]
    have hh := norm_integral_le_of_norm_le hDom hAE
    simp only [Pi.add_apply] at hh
    rw [integral_add (hGauss.const_mul (K / (N : ℝ))) hConst,
      integral_const_mul, setIntegral_const, smul_eq_mul] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hMass (by positivity)) le_rfl)
  unfold scaledKernelIntegralError
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hInt (pow_nonneg hn.le (n + 1))).trans_eq
  rw [hBreal]
  have hq : Real.pi / ((N : ℝ) / 2) = (2 * Real.pi) / (N : ℝ) := by field_simp
  rw [hq, div_pow, pow_succ]
  field_simp

theorem sizePow_exp_bigO_one {c : ℝ} (hc : 0 < c) (k : ℕ) :
    (fun m : ℕ => (m + 1 : ℝ) ^ k * Real.exp (-c * (m + 1 : ℝ))) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  have hInput : ExponentialErrors.ExpPowerBound c
      (fun m : ℕ => (m + 1 : ℝ) ^ k * Real.exp (-c * (m + 1 : ℝ))) := by
    refine ⟨(k : ℝ), ?_⟩
    simpa only [Cumulants.sizePower, Real.rpow_natCast] using
      isBigO_refl (fun m : ℕ => (m + 1 : ℝ) ^ k * Real.exp (-c * (m + 1 : ℝ))) atTop
  have hExp : (fun m : ℕ => Real.exp (-(c / 2) * (m + 1 : ℝ))) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    apply Eventually.isBigO
    apply Filter.Eventually.of_forall
    intro m
    change |Real.exp (-(c / 2) * (m + 1 : ℝ))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  exact (hInput.exp_close hc).trans hExp

/-- Source Q28, with actual integrals and one final fixed-polynomial absorption. -/
theorem scaledKernelIntegralError_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (n : ℕ) :
    (fun m : ℕ => scaledKernelIntegralError A (m + 1) (n + 1)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ := scaled_kernel_integral_error_bound hA
  obtain ⟨C₁, C₂, hC₁, hC₂, hB⟩ := hbound n
  let g : ℕ → ℝ := fun m => C₁ +
    C₂ * ((m + 1 : ℝ) ^ (n + 1) * Real.exp (-c * (m + 1 : ℝ)))
  have hf : (fun m : ℕ => scaledKernelIntegralError A (m + 1) (n + 1)) =O[atTop] g := by
    apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hh := hB (m + 1) (by omega)
    simpa only [g, Nat.cast_add, Nat.cast_one] using hh
  have hg : g =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    have hh := (isBigO_const_one ℝ C₁ (atTop : Filter ℕ)).add
      ((sizePow_exp_bigO_one hc (n + 1)).const_mul_left C₂)
    dsimp only [g]
    simpa only [Pi.add_def] using hh
  exact hf.trans hg

theorem cyclicTrace_U_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (n : ℕ) :
    (fun m : ℕ => Kernel.cyclicTrace A (m + 1) (n + 1) -
      ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
        (∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
          ∏ i, Kernel.U (m + 1) (z i) (z (finRotate (n + 1) i)))) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  apply (scaledKernelIntegralError_bigO hA n).congr_left
  intro m
  unfold scaledKernelIntegralError
  rw [Kernel.cyclicTrace_eq_source A (m + 1) (by omega : 1 ≤ n + 1)]
  have hvol : Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℂ)) = volume := volume_pi.symm
  rw [hvol]
  ring

/-- The original source leading-cycle reduction for the actual trace R_k. -/
theorem cyclicTrace_leading_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) (n : ℕ) :
    (fun m : ℕ => Kernel.cyclicTrace A (m + 1) (n + 1) -
      (Real.pi : ℂ)⁻¹ ^ (n + 1) * ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
        (∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
          Complex.exp (cycleExponent (m + 1) z))) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  have hPow : (fun _ : ℕ => (1 : ℝ)) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
    have hab : (0 : ℝ) ≤ (1 / 2 : ℝ) + δ := by linarith only [hδ.1]
    have hb := Cumulants.sizePower_mono_bigO hab
    unfold Cumulants.sizePower at hb ⊢
    simpa only [Real.rpow_zero] using hb
  have hKernel := (cyclicTrace_U_error_bigO hA n).trans hPow
  have hAfin : volume A ≠ ⊤ := (admissible_isBounded hA).measure_lt_top.ne
  have hAmp := U_cycle_leading_error_bigO (Kernel.bulkDistance_pos hA) hδ n
    hA.1.measurableSet hAfin
    (fun z hz => (hA.2.2.1 (subset_closure hz)).1.le)
    (fun z hz => Kernel.bulkDistance_le_im hA (subset_closure hz))
  apply (hKernel.add hAmp).congr_left
  intro m
  ring

end Paper.Trace
