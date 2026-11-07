/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.Amplitude
public import GinoeClt.Kernel.UniformBounds

/-! # First-order cyclic amplitude error, without a cancellation refinement -/

@[expose] public section
noncomputable section
open Set
open scoped Real BigOperators ComplexConjugate

namespace Paper.Trace

theorem norm_prod_difference_le {n : ℕ} (a b : Fin n → ℂ) {L : ℝ}
    (hL : 1 ≤ L) (ha : ∀ i, ‖a i‖ ≤ L) (hb : ∀ i, ‖b i‖ ≤ L) :
    ‖(∏ i, a i) - ∏ i, b i‖ ≤ L ^ n * ∑ i, ‖a i - b i‖ := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  induction n with
  | zero => simp
  | succ n ih =>
    have htail := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ)
    have hprod : ‖∏ i : Fin n, a i.succ‖ ≤ L ^ n := by
      calc
        _ ≤ ∏ i : Fin n, ‖a i.succ‖ := Finset.norm_prod_le _ _
        _ ≤ ∏ _i : Fin n, L := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => ha i.succ)
        _ = _ := by simp
    have hp : L ^ n ≤ L ^ (n + 1) := by
      rw [pow_succ]
      calc
        L ^ n = L ^ n * 1 := by ring
        _ ≤ L ^ n * L := mul_le_mul_of_nonneg_left hL (pow_nonneg hL0 n)
    have he : (∏ i, a i) - ∏ i, b i =
        (a 0 - b 0) * (∏ i : Fin n, a i.succ) +
          b 0 * ((∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ) := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      ring
    rw [he, Fin.sum_univ_succ]
    calc
      _ ≤ ‖a 0 - b 0‖ * ‖∏ i : Fin n, a i.succ‖ +
          ‖b 0‖ * ‖(∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ ‖a 0 - b 0‖ * L ^ n +
          L * (L ^ n * ∑ i : Fin n, ‖a i.succ - b i.succ‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
          (mul_le_mul (hb 0) htail (norm_nonneg _) hL0)
      _ ≤ L ^ (n + 1) * (‖a 0 - b 0‖ + ∑ i : Fin n, ‖a i.succ - b i.succ‖) := by
        have hh := mul_le_mul_of_nonneg_left hp (norm_nonneg (a 0 - b 0))
        calc
          _ ≤ ‖a 0 - b 0‖ * L ^ (n + 1) +
              L * (L ^ n * ∑ i : Fin n, ‖a i.succ - b i.succ‖) :=
            add_le_add hh le_rfl
          _ = _ := by rw [pow_succ]; ring

def amplitudeFactor (z w : ℂ) : ℂ :=
  Complex.I * (conj w - z) / ((2 * Real.pi * z.im : ℝ) : ℂ)

def baseAmplitudeFactor (z w : ℂ) : ℂ :=
  ((w.im : ℝ) : ℂ) / ((Real.pi * z.im : ℝ) : ℂ)

theorem amplitudeFactor_sub_base (z w : ℂ) :
    amplitudeFactor z w - baseAmplitudeFactor z w =
      Complex.I * (w - z) / ((2 * Real.pi * z.im : ℝ) : ℂ) := by
  have he : Complex.I * (conj w - z) - ((2 * w.im : ℝ) : ℂ) =
      Complex.I * (w - z) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  unfold amplitudeFactor baseAmplitudeFactor
  push_cast at he ⊢
  linear_combination he / (2 * (Real.pi : ℂ) * (z.im : ℂ))

theorem prod_baseAmplitudeFactor {k : ℕ} (z : Fin k → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (∏ i, baseAmplitudeFactor (z i) (z (finRotate k i))) = (Real.pi : ℂ)⁻¹ ^ k := by
  have hr : (∏ i, ((z (finRotate k i)).im : ℂ)) = ∏ i, ((z i).im : ℂ) :=
    Equiv.prod_comp (finRotate k) (fun i => ((z i).im : ℂ))
  have hp : (∏ i, ((z i).im : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => by exact_mod_cast (hz i).ne')
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold baseAmplitudeFactor
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hr]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hpi]
  rw [← mul_pow, one_div, mul_inv_cancel₀ hpi, one_pow]

theorem norm_amplitudeFactor_le {d : ℝ} (hd : 0 < d) {z w : ℂ}
    (hzy : d ≤ z.im) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖amplitudeFactor z w‖ ≤ 1 / (Real.pi * d) := by
  have hy : 0 < z.im := hd.trans_le hzy
  have hp : ‖conj w - z‖ ≤ 2 :=
    Kernel.norm_sub_le_two (d := 0) le_rfl (by simpa only [sub_zero] using hz)
      (by simpa only [sub_zero, Complex.norm_conj] using hw)
  have hh := Kernel.prefactor_quotient_le hd hzy hzy hp
  rw [← pow_two, Real.sqrt_sq hy.le] at hh
  unfold amplitudeFactor
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi * z.im)]
  exact hh

theorem norm_baseAmplitudeFactor_le {d : ℝ} (hd : 0 < d) {z w : ℂ}
    (hzy : d ≤ z.im) (hwy : 0 < w.im) (hw : ‖w‖ ≤ 1) :
    ‖baseAmplitudeFactor z w‖ ≤ 1 / (Real.pi * d) := by
  have hy : 0 < z.im := hd.trans_le hzy
  have hw1 : w.im ≤ 1 := ((le_abs_self _).trans (Complex.abs_im_le_norm w)).trans hw
  have hden : Real.pi * d ≤ Real.pi * z.im := mul_le_mul_of_nonneg_left hzy Real.pi_pos.le
  have hd0 : 0 < Real.pi * d := by positivity
  unfold baseAmplitudeFactor
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hwy, abs_of_pos (mul_pos Real.pi_pos hy)]
  exact (div_le_div_of_nonneg_left hwy.le hd0 hden).trans
    (div_le_div_of_nonneg_right hw1 hd0.le)

theorem norm_amplitudeFactor_sub_base_le {d : ℝ} (hd : 0 < d) {z w : ℂ}
    (hzy : d ≤ z.im) :
    ‖amplitudeFactor z w - baseAmplitudeFactor z w‖ ≤
      (1 / (2 * Real.pi * d)) * ‖z - w‖ := by
  have hy : 0 < z.im := hd.trans_le hzy
  have hden : 2 * Real.pi * d ≤ 2 * Real.pi * z.im :=
    mul_le_mul_of_nonneg_left hzy (by positivity)
  have hd0 : 0 < 2 * Real.pi * d := by positivity
  rw [amplitudeFactor_sub_base, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi * z.im),
    norm_sub_rev]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hd0 hden).trans_eq (by ring)

/-- Source Q29: the original first-order amplitude error, with no cancellation refinement. -/
theorem cycleAmplitude_error {d : ℝ} (hd : 0 < d) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Fin k → ℂ,
      (∀ i, d ≤ (z i).im) → (∀ i, ‖z i‖ ≤ 1) →
      ‖cycleAmplitude z - (Real.pi : ℂ)⁻¹ ^ k‖ ≤
        C * ∑ i, ‖z i - z (finRotate k i)‖ := by
  let L : ℝ := max 1 (1 / (Real.pi * d))
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨L ^ k / (2 * Real.pi * d), by positivity, fun z hzy hz => ?_⟩
  have hpos : ∀ i, 0 < (z i).im := fun i => hd.trans_le (hzy i)
  have ha : ∀ i, ‖amplitudeFactor (z i) (z (finRotate k i))‖ ≤ L := fun i =>
    (norm_amplitudeFactor_le hd (hzy i) (hz i) (hz (finRotate k i))).trans (le_max_right _ _)
  have hb : ∀ i, ‖baseAmplitudeFactor (z i) (z (finRotate k i))‖ ≤ L := fun i =>
    (norm_baseAmplitudeFactor_le hd (hzy i) (hpos (finRotate k i))
      (hz (finRotate k i))).trans (le_max_right _ _)
  have hh := norm_prod_difference_le
    (fun i => amplitudeFactor (z i) (z (finRotate k i)))
    (fun i => baseAmplitudeFactor (z i) (z (finRotate k i))) hL ha hb
  have hs :
      (∑ i, ‖amplitudeFactor (z i) (z (finRotate k i)) -
        baseAmplitudeFactor (z i) (z (finRotate k i))‖) ≤
      (1 / (2 * Real.pi * d)) * ∑ i, ‖z i - z (finRotate k i)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => norm_amplitudeFactor_sub_base_le hd (hzy i)
  rw [prod_baseAmplitudeFactor z hpos] at hh
  change ‖cycleAmplitude z - (Real.pi : ℂ)⁻¹ ^ k‖ ≤ _ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hs (pow_nonneg hL0.le k)).trans_eq (by ring))

end Paper.Trace
