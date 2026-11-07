/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.UniformBounds

/-! # The four uniform estimates of manuscript Lemma 2.3 -/

@[expose] public section
noncomputable section
open Set
open scoped Real ComplexConjugate

namespace Paper.Kernel

theorem norm_approximation_le (x g t : ℂ) (hg : ‖1 + g‖ ≤ 1) :
    ‖x * (1 + g) * (1 - t) - x‖ ≤ ‖x‖ * ‖g‖ + ‖x * t‖ := by
  have he : x * (1 + g) * (1 - t) - x = x * g - (x * t) * (1 + g) := by ring
  rw [he]
  calc
    _ ≤ ‖x * g‖ + ‖(x * t) * (1 + g)‖ := norm_sub_le _ _
    _ = ‖x‖ * ‖g‖ + ‖x * t‖ * ‖1 + g‖ := by rw [norm_mul, norm_mul]
    _ ≤ _ := by nlinarith [norm_nonneg (x * t)]

theorem norm_approximation_base_le (x g t : ℂ) (hg : ‖1 + g‖ ≤ 1) :
    ‖x * (1 + g) * (1 - t)‖ ≤ ‖x‖ + ‖x * t‖ := by
  have he : x * (1 + g) * (1 - t) = x * (1 + g) - (x * t) * (1 + g) := by ring
  rw [he]
  calc
    _ ≤ ‖x * (1 + g)‖ + ‖(x * t) * (1 + g)‖ := norm_sub_le _ _
    _ = ‖x‖ * ‖1 + g‖ + ‖x * t‖ * ‖1 + g‖ := by rw [norm_mul, norm_mul]
    _ ≤ _ := by nlinarith [norm_nonneg x, norm_nonneg (x * t)]

/-- Uniform in all points of the d-separated bulk, so both constants depend
only on d. The proved bounds already hold for every N ≥ 2. -/
theorem kernel_estimates_bulk {d : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 2 ≤ N → ∀ z w : ℂ,
      d ≤ z.im → d ≤ w.im → ‖z‖ ≤ 1 - d → ‖w‖ ≤ 1 - d →
      ‖D N (rescale N z) (rescale N w)‖ + ‖I N (rescale N z) (rescale N w)‖ ≤
          C * Real.exp (-c * (N : ℝ)) ∧
      ‖S N (rescale N z) (rescale N w)‖ ≤ C ∧
      ‖U N z w‖ ≤ C * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) ∧
      ‖S N (rescale N z) (rescale N w) - U N z w‖ ≤
        C / (N : ℝ) * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) +
          C * Real.exp (-c * (N : ℝ)) := by
  have hr0 : 0 < (1 - d) ^ 2 := by nlinarith
  have hr1 : (1 - d) ^ 2 < 1 := by nlinarith
  obtain ⟨R, hR0, hR⟩ := Lambert.corrected_truncation hr0 hr1
  let P : ℝ := 1 / (Real.pi * d)
  let B : ℝ := (1 + R) / (d ^ 2 * Real.sqrt (2 * Real.pi) * (1 - (1 - d) ^ 2))
  let T : ℝ := P * B
  let G : ℝ := 1 / (2 * d ^ 2)
  let K : ℝ := 2 * (P + T) + P * G + 1
  let c : ℝ := min (entropy ((1 - d) ^ 2)) (2 * d ^ 2)
  have hP : 0 < P := by dsimp [P]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := mul_pos hP hB
  have hG : 0 < G := by dsimp [G]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hH : 0 < entropy ((1 - d) ^ 2) := entropy_pos hr0 hr1
  have hc : 0 < c := lt_min hH (by positivity)
  have hPK : P ≤ K := by dsimp [K]; nlinarith
  have hTK : T ≤ K := by dsimp [K]; nlinarith
  have hPGK : P * G ≤ K := by dsimp [K]; nlinarith
  have hPTK : P + T ≤ K := by dsimp [K]; nlinarith
  have h2PTK : 2 * (P + T) ≤ K := by dsimp [K]; nlinarith only [hP, hG, mul_pos hP hG]
  refine ⟨K, c, hK, hc, fun N hN z w hzy hwy hz hw => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hz0 := hd.trans_le hzy
  have hw0 := hd.trans_le hwy
  obtain ⟨_, _, hqD0, hqD1, hqS0, hqS1⟩ := bulk_pair_norm_bounds hd hdh hzy hwy hz hw
  have hAmp := norm_one_add_gaussianAmplitudeError_le_one hN1 hz0 hw0
  have hS : S N (rescale N z) (rescale N w) =
      U N z w * (1 + (gaussianAmplitudeError N z w : ℂ)) *
        (1 - truncationTail N (z * conj w)) := by
    rw [S_rescale_eq_U hN1 hz0 hw0, truncatedExponential_eq_one_sub_tail hN (hqS1.trans_lt hr1)]
  have hD : D N (rescale N z) (rescale N w) =
      leadingD N z w * (1 + (gaussianAmplitudeError N z w : ℂ)) *
        (1 - truncationTail N (z * w)) := by
    rw [D_rescale_eq_leadingD hN1 hz0 hw0, truncatedExponential_eq_one_sub_tail hN (hqD1.trans_lt hr1)]
  have hU := norm_U_bulk_le hd hzy hwy hz hw (N := N)
  have hV := norm_leadingD_bulk_le hd hzy hwy hz hw (N := N)
  have hSt := norm_U_mul_tail_bulk_le hd hdh hR0.le hN1 hzy hwy hz hw
    ((hR N hN (z * conj w) hqS1).2)
  have hDt := norm_leadingD_mul_tail_bulk_le hd hdh hR0.le hN1 hzy hwy hz hw
    ((hR N hN (z * w) hqD1).2)
  change ‖U N z w * truncationTail N (z * conj w)‖ ≤
    T * Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) at hSt
  change ‖leadingD N z w * truncationTail N (z * w)‖ ≤
    T * Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) at hDt
  have hExH : Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) ≤
      Real.exp (-c * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh : c ≤ entropy ((1 - d) ^ 2) := min_le_left _ _
    exact mul_le_mul_of_nonneg_right (neg_le_neg hh) hn.le
  have hExD : Real.exp (-(2 * d ^ 2) * (N : ℝ)) ≤ Real.exp (-c * (N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh : c ≤ 2 * d ^ 2 := min_le_right _ _
    exact mul_le_mul_of_nonneg_right (neg_le_neg hh) hn.le
  have hGauss1 : Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hn]) (sq_nonneg _)
  have hExpH1 : Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hH.le) hn.le
  have hDb : ‖D N (rescale N z) (rescale N w)‖ ≤ (P + T) * Real.exp (-c * (N : ℝ)) := by
    rw [hD]
    calc
      _ ≤ ‖leadingD N z w‖ + ‖leadingD N z w * truncationTail N (z * w)‖ :=
        norm_approximation_base_le _ _ _ hAmp
      _ ≤ P * Real.exp (-(2 * d ^ 2) * (N : ℝ)) +
          T * Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := add_le_add hV hDt
      _ ≤ P * Real.exp (-c * (N : ℝ)) + T * Real.exp (-c * (N : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hExD hP.le) (mul_le_mul_of_nonneg_left hExH hT.le)
      _ = _ := by ring
  have hSb : ‖S N (rescale N z) (rescale N w)‖ ≤ P + T := by
    rw [hS]
    calc
      _ ≤ ‖U N z w‖ + ‖U N z w * truncationTail N (z * conj w)‖ :=
        norm_approximation_base_le _ _ _ hAmp
      _ ≤ P * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) +
          T * Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := add_le_add hU hSt
      _ ≤ _ := by
        simpa only [mul_one] using add_le_add
          (mul_le_mul_of_nonneg_left hGauss1 hP.le)
          (mul_le_mul_of_nonneg_left hExpH1 hT.le)
  have hGamma : ‖(gaussianAmplitudeError N z w : ℂ)‖ ≤ G / (N : ℝ) := by
    have hh := gaussianAmplitudeError_bound hd hN1 hzy hwy
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply hh.trans_eq
    dsimp [G]
    ring
  have hDiff : ‖S N (rescale N z) (rescale N w) - U N z w‖ ≤
      (P * G) / (N : ℝ) * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) +
        T * Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) := by
    rw [hS]
    calc
      _ ≤ ‖U N z w‖ * ‖(gaussianAmplitudeError N z w : ℂ)‖ +
          ‖U N z w * truncationTail N (z * conj w)‖ :=
        norm_approximation_le _ _ _ hAmp
      _ ≤ (P * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2)) * (G / (N : ℝ)) +
          T * Real.exp (-entropy ((1 - d) ^ 2) * (N : ℝ)) :=
        add_le_add (mul_le_mul hU hGamma (norm_nonneg _) (by positivity)) hSt
      _ = _ := by ring
  refine ⟨?_, hSb.trans hPTK, ?_, ?_⟩
  · rw [I_eq_neg_conj_D, norm_neg, Complex.norm_conj]
    calc
      _ ≤ 2 * ((P + T) * Real.exp (-c * (N : ℝ))) := by linarith only [hDb]
      _ = (2 * (P + T)) * Real.exp (-c * (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2PTK (Real.exp_pos _).le
  · exact hU.trans (mul_le_mul_of_nonneg_right hPK (Real.exp_pos _).le)
  · exact hDiff.trans (add_le_add
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hPGK hn.le) (Real.exp_pos _).le)
      (mul_le_mul hTK hExH (Real.exp_pos _).le hK.le))

/-- Lemma 2.3 on the full closure of every admissible Lipschitz domain.
The generic bulk theorem places its witnesses before all points and N. -/
theorem kernel_estimates {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ z ∈ closure A, ∀ w ∈ closure A,
      ‖D N (rescale N z) (rescale N w)‖ + ‖I N (rescale N z) (rescale N w)‖ ≤
          C * Real.exp (-c * (N : ℝ)) ∧
      ‖S N (rescale N z) (rescale N w)‖ ≤ C ∧
      ‖U N z w‖ ≤ C * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) ∧
      ‖S N (rescale N z) (rescale N w) - U N z w‖ ≤
        C / (N : ℝ) * Real.exp (-(N : ℝ) / 2 * ‖z - w‖ ^ 2) +
          C * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨C, c, hC, hc, hh⟩ := kernel_estimates_bulk (bulkDistance_pos hA) (bulkDistance_le_half hA)
  exact ⟨C, c, hC, hc, fun N hN z hz w hw => hh N hN z w
    (bulkDistance_le_im hA hz) (bulkDistance_le_im hA hw)
    (norm_le_one_sub_bulkDistance hA hz) (norm_le_one_sub_bulkDistance hA hw)⟩

end Paper.Kernel
