/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Algebra.Pfaffian
public import GinoeClt.Kernel.Estimates
public import GinoeClt.Kernel.Integrability
public import GinoeClt.Trace.AmplitudeError
public import GinoeClt.Analysis.ExponentialErrors
import Mathlib.Tactic.FinCases

/-! # Deterministic exponentially accurate Pfaffian-to-determinant approximation

These are literal kernel matrices and their integrals. No GinOE correlation
law or point-process existence is assumed.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Asymptotics Equiv
open scoped Real Topology BigOperators

namespace Paper.Kernel

def pfaffianKernelMatrix (N : ℕ) {k : ℕ} (z : Fin k → ℂ) :
    Matrix (PairedIndex k) (PairedIndex k) ℂ :=
  fun p q => if p.2 = 0 then
    if q.2 = 0 then D N (rescale N (z p.1)) (rescale N (z q.1))
    else S N (rescale N (z p.1)) (rescale N (z q.1))
  else if q.2 = 0 then -S N (rescale N (z q.1)) (rescale N (z p.1))
    else I N (rescale N (z p.1)) (rescale N (z q.1))

theorem norm_permutationSign {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Perm ι) :
    ‖permutationSign σ‖ = 1 := by
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [permutationSign, h]

theorem pfaffian_difference_bound {k : ℕ}
    (M Q : Matrix (PairedIndex k) (PairedIndex k) ℂ) {L ε : ℝ}
    (hL : 1 ≤ L)
    (hM : ∀ p q, ‖M p q‖ ≤ L) (hQ : ∀ p q, ‖Q p q‖ ≤ L)
    (herr : ∀ p q, ‖M p q - Q p q‖ ≤ ε) :
    ‖pfaffian M - pfaffian Q‖ ≤
      (‖((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹‖ *
        (Fintype.card (Perm (PairedIndex k)) : ℝ) * L ^ k * (k : ℝ)) * ε := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hterm (σ : Perm (PairedIndex k)) :
      ‖(∏ i : Fin k, M (σ (i, 0)) (σ (i, 1))) -
        ∏ i : Fin k, Q (σ (i, 0)) (σ (i, 1))‖ ≤ L ^ k * ((k : ℝ) * ε) := by
    have hh := Trace.norm_prod_difference_le
      (fun i : Fin k => M (σ (i, 0)) (σ (i, 1)))
      (fun i : Fin k => Q (σ (i, 0)) (σ (i, 1))) hL
      (fun i => hM _ _) (fun i => hQ _ _)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL0 k)
    calc
      _ ≤ ∑ _i : Fin k, ε := Finset.sum_le_sum fun i _ => herr _ _
      _ = _ := by simp
  have he : pfaffian M - pfaffian Q =
      ((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹ *
        ∑ σ : Perm (PairedIndex k), permutationSign σ *
          ((∏ i : Fin k, M (σ (i, 0)) (σ (i, 1))) -
            ∏ i : Fin k, Q (σ (i, 0)) (σ (i, 1))) := by
    unfold pfaffian
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  rw [he, norm_mul]
  calc
    _ ≤ ‖((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹‖ *
        ∑ σ : Perm (PairedIndex k),
          ‖permutationSign σ *
            ((∏ i : Fin k, M (σ (i, 0)) (σ (i, 1))) -
              ∏ i : Fin k, Q (σ (i, 0)) (σ (i, 1)))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹‖ *
        ∑ _σ : Perm (PairedIndex k), L ^ k * ((k : ℝ) * ε) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_mul, norm_permutationSign, one_mul]
      exact hterm σ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The exponential rate is selected before every fixed Pfaffian order. -/
theorem pfaffian_det_error_bulk {d : ℝ} (hd : 0 < d) (hdh : d ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ z : Fin k → ℂ, (∀ i, d ≤ (z i).im) → (∀ i, ‖z i‖ ≤ 1 - d) →
      ‖pfaffian (pfaffianKernelMatrix N z) -
        Matrix.det (fun i j : Fin k => S N (rescale N (z i)) (rescale N (z j)))‖ ≤
          C * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨K, c, hK, hc, hKernel⟩ := kernel_estimates_bulk hd hdh
  let L : ℝ := max 1 K
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hKL : K ≤ L := le_max_right _ _
  refine ⟨c, hc, fun k => ?_⟩
  let A : ℝ := ‖((2 : ℂ) ^ k * (k.factorial : ℂ))⁻¹‖ *
    (Fintype.card (Perm (PairedIndex k)) : ℝ) * L ^ k * (k : ℝ)
  refine ⟨A * K + 1, by dsimp [A]; positivity, fun N hN z hzy hz => ?_⟩
  let Q : Matrix (Fin k) (Fin k) ℂ := fun i j => S N (rescale N (z i)) (rescale N (z j))
  let M₀ := interlacedMatrix Q
  have hExp : Real.exp (-c * (N : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Nat.cast_nonneg N)
  have hKe : K * Real.exp (-c * (N : ℝ)) ≤ K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp hK.le
  have hS (i j : Fin k) : ‖S N (rescale N (z i)) (rescale N (z j))‖ ≤ L :=
    ((hKernel N hN (z i) (z j) (hzy i) (hzy j) (hz i) (hz j)).2.1).trans hKL
  have hDexp (i j : Fin k) : ‖D N (rescale N (z i)) (rescale N (z j))‖ ≤
      K * Real.exp (-c * (N : ℝ)) :=
    (le_add_of_nonneg_right (norm_nonneg (I N (rescale N (z i)) (rescale N (z j))))).trans
      (hKernel N hN (z i) (z j) (hzy i) (hzy j) (hz i) (hz j)).1
  have hIexp (i j : Fin k) : ‖I N (rescale N (z i)) (rescale N (z j))‖ ≤
      K * Real.exp (-c * (N : ℝ)) :=
    (le_add_of_nonneg_left (norm_nonneg (D N (rescale N (z i)) (rescale N (z j))))).trans
      (hKernel N hN (z i) (z j) (hzy i) (hzy j) (hz i) (hz j)).1
  have hM : ∀ p q, ‖pfaffianKernelMatrix N z p q‖ ≤ L := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b
    · simpa [pfaffianKernelMatrix] using ((hDexp i j).trans hKe).trans hKL
    · simpa [pfaffianKernelMatrix] using hS i j
    · simpa [pfaffianKernelMatrix] using hS j i
    · simpa [pfaffianKernelMatrix] using ((hIexp i j).trans hKe).trans hKL
  have hM₀ : ∀ p q, ‖M₀ p q‖ ≤ L := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b
    · simpa [M₀, interlacedMatrix] using hLp.le
    · simpa [M₀, interlacedMatrix, Q] using hS i j
    · simpa [M₀, interlacedMatrix, Q] using hS j i
    · simpa [M₀, interlacedMatrix] using hLp.le
  have herr : ∀ p q, ‖pfaffianKernelMatrix N z p q - M₀ p q‖ ≤
      K * Real.exp (-c * (N : ℝ)) := by
    rintro ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b
    · simpa [pfaffianKernelMatrix, M₀, interlacedMatrix] using hDexp i j
    · simp [pfaffianKernelMatrix, M₀, interlacedMatrix, Q]
      positivity
    · simp [pfaffianKernelMatrix, M₀, interlacedMatrix, Q]
      positivity
    · simpa [pfaffianKernelMatrix, M₀, interlacedMatrix] using hIexp i j
  have hh := pfaffian_difference_bound (pfaffianKernelMatrix N z) M₀ hL hM hM₀ herr
  dsimp only [M₀] at hh
  rw [pfaffian_interlacedMatrix_det] at hh
  have hh' : ‖pfaffian (pfaffianKernelMatrix N z) - Q.det‖ ≤
      (A * K) * Real.exp (-c * (N : ℝ)) := hh.trans_eq (by dsimp [A]; ring)
  exact hh'.trans (mul_le_mul_of_nonneg_right (by linarith : A * K ≤ A * K + 1)
    (Real.exp_pos _).le)

theorem pfaffian_det_error {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ z ∈ Set.univ.pi (fun _ : Fin k => closure A),
      ‖pfaffian (pfaffianKernelMatrix N z) -
        Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) z)‖ ≤
          C * Real.exp (-c * (N : ℝ)) := by
  obtain ⟨c, hc, hh⟩ := pfaffian_det_error_bulk (bulkDistance_pos hA) (bulkDistance_le_half hA)
  refine ⟨c, hc, fun k => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hh k
  exact ⟨C, hC, fun N hN z hz => hbound N hN z
    (fun i => bulkDistance_le_im hA (hz i (Set.mem_univ i)))
    (fun i => norm_le_one_sub_bulkDistance hA (hz i (Set.mem_univ i)))⟩

theorem continuous_pfaffianKernel (N k : ℕ) :
    Continuous (fun z : Fin k → ℂ => pfaffian (pfaffianKernelMatrix N z)) := by
  have hcoord (i : Fin k) : Continuous (fun z : Fin k → ℂ => rescale N (z i)) :=
    (continuous_rescale N).comp (continuous_apply i)
  unfold pfaffian
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ hσ
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i hi
  unfold pfaffianKernelMatrix
  split_ifs
  · exact (continuous_D N).comp ((hcoord _).prodMk (hcoord _))
  · exact (continuous_S N).comp ((hcoord _).prodMk (hcoord _))
  · exact ((continuous_S N).comp ((hcoord _).prodMk (hcoord _))).neg
  · exact (continuous_I N).comp ((hcoord _).prodMk (hcoord _))

/-- A complex kernel integral, not an ensemble factorial moment. The source
order-zero convention is explicit. Identification with actual counts is proved in SkewOrthogonal.CountPfaffianIdentity. -/
def pfaffianKernelMoment (A : Set ℂ) (N k : ℕ) : ℂ :=
  if k = 0 then 1 else (N : ℂ) ^ k *
    ∫ z in Set.univ.pi (fun _ : Fin k => A), pfaffian (pfaffianKernelMatrix N z)

@[simp] theorem pfaffianKernelMoment_zero (A : Set ℂ) (N : ℕ) :
    pfaffianKernelMoment A N 0 = 1 := by simp [pfaffianKernelMoment]

/-- The unabsorbed N^k factor is retained, with one rate selected before k. -/
theorem pfaffianKernelMoment_det_error {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      IntegrableOn (fun z : Fin k → ℂ => pfaffian (pfaffianKernelMatrix N z))
        (Set.univ.pi (fun _ : Fin k => A)) ∧
      ‖pfaffianKernelMoment A N k - determinantMoment A N k‖ ≤
        C * ((N : ℝ) ^ k * Real.exp (-c * (N : ℝ))) := by
  obtain ⟨c, hc, hPoint⟩ := pfaffian_det_error hA
  have hAfin : volume A ≠ ⊤ := (admissible_isBounded hA).measure_lt_top.ne
  refine ⟨c, hc, fun k => ?_⟩
  obtain ⟨K, hK, hbound⟩ := hPoint k
  let B := Set.univ.pi (fun _ : Fin k => A)
  have hB : MeasurableSet B := MeasurableSet.pi Set.countable_univ (fun _ _ => hA.1.measurableSet)
  have hvol : volume B = volume A ^ k := by
    change Measure.pi (fun _ : Fin k => (volume : Measure ℂ)) B = _
    rw [Measure.pi_pi]
    simp
  have hBfin : volume B ≠ ⊤ := by rw [hvol]; exact ENNReal.pow_ne_top hAfin
  have hBreal : volume.real B = volume.real A ^ k := by
    simp only [measureReal_def, hvol, ENNReal.toReal_pow]
  refine ⟨K * volume.real A ^ k + 1, by positivity, fun N hN => ?_⟩
  have hDet := integrableOn_source_determinant hA N k
  change IntegrableOn (fun z : Fin k → ℂ =>
    Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) z)) B at hDet
  have hmem : ∀ᵐ z ∂volume.restrict B, z ∈ B := ae_restrict_mem hB
  have hAE : ∀ᵐ z ∂volume.restrict B,
      ‖pfaffian (pfaffianKernelMatrix N z) -
        Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) z)‖ ≤ K * Real.exp (-c * (N : ℝ)) := by
    filter_upwards [hmem] with z hz
    exact hbound N hN z (fun i hi => subset_closure (hz i hi))
  have hConst : IntegrableOn (fun _ : Fin k → ℂ => K * Real.exp (-c * (N : ℝ))) B :=
    integrableOn_const hBfin
  have hDiff : IntegrableOn (fun z : Fin k → ℂ =>
      pfaffian (pfaffianKernelMatrix N z) -
        Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) z)) B :=
    hConst.mono' ((continuous_pfaffianKernel N k).aestronglyMeasurable.sub
      hDet.aestronglyMeasurable) hAE
  have hPf : IntegrableOn (fun z : Fin k → ℂ => pfaffian (pfaffianKernelMatrix N z)) B := by
    apply (hDiff.add hDet).congr
    exact Filter.Eventually.of_forall fun z => by simp only [Pi.add_apply, sub_add_cancel]
  refine ⟨hPf, ?_⟩
  have hInt :
      ‖(∫ z in B, pfaffian (pfaffianKernelMatrix N z)) -
        (∫ z in B, Matrix.det (KernelIntegrals.kernelMatrix (rescaledS N) z))‖ ≤
          volume.real B * (K * Real.exp (-c * (N : ℝ))) := by
    rw [← integral_sub hPf hDet]
    have hh := norm_integral_le_of_norm_le hConst hAE
    simpa only [setIntegral_const, smul_eq_mul] using hh
  by_cases hk : k = 0
  · subst k
    simp only [pfaffianKernelMoment_zero, determinantMoment_zero, sub_self, norm_zero, pow_zero, one_mul]
    positivity
  · have hk1 : 1 ≤ k := by omega
    rw [pfaffianKernelMoment, ite_eq_right hk, determinantMoment_eq_source A N hk1]
    have hπ : Measure.pi (fun _ : Fin k => (volume : Measure ℂ)) = volume := volume_pi.symm
    rw [hπ, ← mul_sub, norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (N : ℝ) ^ k * (volume.real B * (K * Real.exp (-c * (N : ℝ)))) :=
        mul_le_mul_of_nonneg_left hInt (pow_nonneg (Nat.cast_nonneg N) k)
      _ = (K * volume.real A ^ k) * ((N : ℝ) ^ k * Real.exp (-c * (N : ℝ))) := by
        rw [hBreal]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : K * volume.real A ^ k ≤ K * volume.real A ^ k + 1)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg N) k) (Real.exp_pos _).le)

/-- Intended input for polynomial Hn propagation: the N^k factor is still
present in ExpPowerBound, and the rate has not been absorbed or decreased. -/
theorem pfaffianKernelMoment_det_expPowerBound {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ExponentialErrors.ExpPowerBound c
      (fun m : ℕ => ‖pfaffianKernelMoment A (m + 1) k - determinantMoment A (m + 1) k‖) := by
  obtain ⟨c, hc, hbound⟩ := pfaffianKernelMoment_det_error hA
  refine ⟨c, hc, fun k => ?_⟩
  obtain ⟨C, hC, hB⟩ := hbound k
  refine ⟨(k : ℝ), IsBigO.of_bound C ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hh := (hB (m + 1) (by omega)).2
  change |‖pfaffianKernelMoment A (m + 1) k - determinantMoment A (m + 1) k‖| ≤
    C * |Cumulants.sizePower (k : ℝ) m * Real.exp (-c * (m + 1 : ℝ))|
  rw [abs_of_nonneg (norm_nonneg _)]
  have hg : 0 ≤ Cumulants.sizePower (k : ℝ) m * Real.exp (-c * (m + 1 : ℝ)) := by
    unfold Cumulants.sizePower
    positivity
  rw [abs_of_nonneg hg]
  unfold Cumulants.sizePower
  rw [Real.rpow_natCast]
  simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- Optional once-absorbed corollary. Polynomial Hn propagation should use the
previous unabsorbed ExpPowerBound theorem. -/
theorem pfaffianKernelMoment_det_exp_close {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ,
      (fun m : ℕ => ‖pfaffianKernelMoment A (m + 1) k - determinantMoment A (m + 1) k‖) =O[atTop]
        (fun m : ℕ => Real.exp (-c * (m + 1 : ℝ))) := by
  obtain ⟨c, hc, hbound⟩ := pfaffianKernelMoment_det_expPowerBound hA
  exact ⟨c / 2, by positivity, fun k => (hbound k).exp_close hc⟩

end Paper.Kernel
