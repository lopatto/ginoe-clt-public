/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Kernel.ErfcCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Global Gaussian domination of the exact complementary tail. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
namespace Paper.Kernel

theorem gaussian_tail_translate (x : ℝ) :
    (∫ t in Ioi x, Real.exp (-(t ^ 2))) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-((s + x) ^ 2)) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  change (∫ t in Ioi x, g t) = ∫ s in Ioi (0 : ℝ), g (s + x)
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self (fun t : ℝ => (Ioi x).indicator g t) x]
  congr 1
  funext s
  have hm : x < s + x ↔ (0 : ℝ) < s := by
    constructor <;> intro h <;> linarith
  simp only [Set.indicator, Set.mem_Ioi, hm]

theorem erfc_le_gaussian {x : ℝ} (hx : 0 ≤ x) :
    erfc x ≤ Real.exp (-(x ^ 2)) := by
  have hint :
      (∫ s in Ioi (0 : ℝ), Real.exp (-((s + x) ^ 2))) ≤
        Real.exp (-(x ^ 2)) * ∫ s in Ioi (0 : ℝ), Real.exp (-(s ^ 2)) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (integrable_gaussian.comp_add_right x).integrableOn
      (integrable_gaussian.const_mul (Real.exp (-(x ^ 2)))).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs0 : 0 ≤ s := le_of_lt hs
    nlinarith [mul_nonneg hx hs0]
  calc
    erfc x = (2 / Real.sqrt Real.pi) *
        ∫ s in Ioi (0 : ℝ), Real.exp (-((s + x) ^ 2)) := by
      rw [erfc, gaussian_tail_translate]
    _ ≤ (2 / Real.sqrt Real.pi) *
        (Real.exp (-(x ^ 2)) * ∫ s in Ioi (0 : ℝ), Real.exp (-(s ^ 2))) :=
      mul_le_mul_of_nonneg_left hint (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = Real.exp (-(x ^ 2)) * erfc 0 := by
      rw [erfc]
      ring
    _ = Real.exp (-(x ^ 2)) := by rw [erfc_zero, mul_one]

end Paper.Kernel
