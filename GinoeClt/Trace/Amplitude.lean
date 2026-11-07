/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.CycleExponent
public import GinoeClt.Kernel.Leading

/-! # The literal cyclic amplitude in the source trace proof -/

@[expose] public section
noncomputable section
open Set
open scoped Real BigOperators ComplexConjugate

namespace Paper.Trace

def cycleAmplitude {k : ℕ} (z : Fin k → ℂ) : ℂ :=
  ∏ i, Complex.I * (conj (z (finRotate k i)) - z i) /
    ((2 * Real.pi * (z i).im : ℝ) : ℂ)

theorem leadingSExponent_im (N : ℕ) (z w : ℂ) :
    (Kernel.leadingSExponent N z w).im =
      (N : ℝ) * (z * conj w).im +
        (N : ℝ) * (w.re * w.im - z.re * z.im) := by
  simp [Kernel.leadingSExponent, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem sum_leadingSExponent (N : ℕ) {k : ℕ} (z : Fin k → ℂ) :
    (∑ i, Kernel.leadingSExponent N (z i) (z (finRotate k i))) =
      cycleExponent (N : ℝ) z := by
  apply Complex.ext
  · have hr : (∑ i, Kernel.leadingSExponent N (z i) (z (finRotate k i))).re =
        ∑ i, (Kernel.leadingSExponent N (z i) (z (finRotate k i))).re :=
      map_sum Complex.reCLM _ _
    rw [hr]
    simp_rw [Kernel.leadingSExponent_re]
    rw [← Finset.mul_sum]
    simpa only [cycleEnergy, neg_div] using (cycleExponent_re (N : ℝ) z).symm
  · have hi : (∑ i, Kernel.leadingSExponent N (z i) (z (finRotate k i))).im =
        ∑ i, (Kernel.leadingSExponent N (z i) (z (finRotate k i))).im :=
      map_sum Complex.imCLM _ _
    have ht : (∑ i, (z (finRotate k i)).re * (z (finRotate k i)).im) =
        ∑ i, (z i).re * (z i).im := Equiv.sum_comp (finRotate k) (fun i => (z i).re * (z i).im)
    have hp : (cyclePairing z).im = ∑ i, (z i * conj (z (finRotate k i))).im :=
      map_sum Complex.imCLM _ _
    rw [hi]
    simp_rw [leadingSExponent_im]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ht, sub_self, mul_zero, add_zero]
    simp only [cycleExponent, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add]
    rw [hp]
    simp only [Complex.mul_im]

theorem prod_sqrt_cycle_im {k : ℕ} (z : Fin k → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (∏ i, Real.sqrt ((z i).im * (z (finRotate k i)).im)) = ∏ i, (z i).im := by
  have hr : (∏ i, Real.sqrt (z (finRotate k i)).im) = ∏ i, Real.sqrt (z i).im :=
    Equiv.prod_comp (finRotate k) (fun i => Real.sqrt (z i).im)
  calc
    _ = (∏ i, Real.sqrt (z i).im) * (∏ i, Real.sqrt (z (finRotate k i)).im) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      exact Real.sqrt_mul (hz i).le _
    _ = (∏ i, Real.sqrt (z i).im) ^ 2 := by rw [hr]; ring
    _ = _ := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i hi
      exact Real.sq_sqrt (hz i).le

theorem prod_U_eq_exp_cycleExponent_mul_amplitude (N : ℕ) {k : ℕ}
    (z : Fin k → ℂ) (hz : ∀ i, 0 < (z i).im) :
    (∏ i, Kernel.U N (z i) (z (finRotate k i))) =
      Complex.exp (cycleExponent (N : ℝ) z) * cycleAmplitude z := by
  have hden : (∏ i, ((2 * Real.pi * Real.sqrt
      ((z i).im * (z (finRotate k i)).im) : ℝ) : ℂ)) =
      ∏ i, ((2 * Real.pi * (z i).im : ℝ) : ℂ) := by
    have hr : (∏ i, 2 * Real.pi * Real.sqrt ((z i).im * (z (finRotate k i)).im)) =
        ∏ i, 2 * Real.pi * (z i).im := by
      simp only [Finset.prod_mul_distrib, prod_sqrt_cycle_im z hz]
    exact_mod_cast hr
  have he (i : Fin k) : Kernel.U N (z i) (z (finRotate k i)) =
      (Complex.I * (conj (z (finRotate k i)) - z i) /
        ((2 * Real.pi * Real.sqrt ((z i).im * (z (finRotate k i)).im) : ℝ) : ℂ)) *
          Complex.exp (Kernel.leadingSExponent N (z i) (z (finRotate k i))) := rfl
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, sum_leadingSExponent,
    Finset.prod_div_distrib, hden]
  unfold cycleAmplitude
  rw [Finset.prod_div_distrib]
  ring

end Paper.Trace
