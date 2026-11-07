/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.CrossingPath
public import GinoeClt.Trace.FirstExit
public import GinoeClt.Geometry.PerimeterGaussian

/-! # The original first-exit Gaussian crossing asymptotics -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators

namespace Paper.Trace

lemma gaussianCrossing_half_eq (A : Set ℂ) (N : ℕ) :
    gaussianCrossing ((N : ℝ) / 2) A = Geometry.gaussianCrossing A (1 / 2) N := by
  unfold gaussianCrossing Geometry.gaussianCrossing
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  change Real.exp (-(↑N / 2) * ‖w - z‖ ^ 2) =
    Real.exp (-(1 / 2) * ↑N * ‖z - w‖ ^ 2)
  rw [norm_sub_rev w z]
  congr 1
  ring

lemma scaled_firstExit_norm_le {A : Set ℂ} (hA : volume A ≠ ⊤)
    (n : ℕ) (j : Fin (n + 1)) (m : ℕ) :
    ‖((m + 1 : ℕ) : ℂ) ^ (n + 2) *
      (∫ x in firstExitDomain A (n + 1) j,
        Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x))‖ ≤
      (2 * Real.pi) ^ n * ((m + 1 : ℝ) ^ 2 *
        Geometry.gaussianCrossing A (1 / 2) (m + 1)) := by
  have hN : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hh := norm_firstExit_cycleIntegral_le hN n A hA j
  rw [gaussianCrossing_half_eq] at hh
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hh (pow_nonneg hN.le (n + 2))).trans_eq
  push_cast
  rw [div_pow, pow_add]
  field_simp

/-- Each scaled source first-exit term is O(sqrt N); no cyclic cancellation is used. -/
theorem scaled_firstExit_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    (n : ℕ) (j : Fin (n + 1)) :
    (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (n + 2) *
      (∫ x in firstExitDomain A (n + 1) j,
        Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x))) =O[atTop]
      Cumulants.sizePower (1 / 2) := by
  have hc : (fun m : ℕ => Geometry.gaussianCrossing A (1 / 2) (m + 1)) =O[atTop]
      Cumulants.sizePower (-3 / 2) := by
    have hh := (Geometry.half_gaussian_crossing_bigO hA).comp_tendsto
      (tendsto_add_atTop_nat 1)
    change (fun m : ℕ => Geometry.gaussianCrossing A (1 / 2) (m + 1)) =O[atTop]
      (fun m : ℕ => (((m + 1 : ℕ) : ℝ)) ^ (-3 / 2 : ℝ)) at hh
    change (fun m : ℕ => Geometry.gaussianCrossing A (1 / 2) (m + 1)) =O[atTop]
      (fun m : ℕ => (m + 1 : ℝ) ^ (-3 / 2 : ℝ))
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hp : (fun m : ℕ => (m + 1 : ℝ) ^ 2) =O[atTop] Cumulants.sizePower 2 := by
    change (fun m : ℕ => (m + 1 : ℝ) ^ 2) =O[atTop]
      (fun m : ℕ => (m + 1 : ℝ) ^ (2 : ℝ))
    simpa only [Real.rpow_two] using
      (isBigO_refl (fun m : ℕ => (m + 1 : ℝ) ^ 2) atTop)
  have he (m : ℕ) : Cumulants.sizePower 2 m * Cumulants.sizePower (-3 / 2) m =
      Cumulants.sizePower (1 / 2) m := by rw [Cumulants.sizePower_mul]; norm_num
  have hg := ((hp.mul hc).congr_right he).const_mul_left ((2 * Real.pi) ^ n)
  have hf : (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (n + 2) *
      (∫ x in firstExitDomain A (n + 1) j,
        Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x))) =O[atTop]
      (fun m : ℕ => (2 * Real.pi) ^ n * ((m + 1 : ℝ) ^ 2 *
        Geometry.gaussianCrossing A (1 / 2) (m + 1))) := by
    apply Eventually.isBigO
    exact Filter.Eventually.of_forall (scaled_firstExit_norm_le
      (admissible_isBounded hA).measure_lt_top.ne n j)
  exact hf.trans hg

lemma scaled_cycleIntegral_error_eq {A : Set ℂ} (hA : MeasurableSet A)
    (hfin : volume A ≠ ⊤) (n m : ℕ) :
    (Real.pi : ℂ)⁻¹ ^ (n + 1) * ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
        (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A),
          Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x)) -
      (((m + 1 : ℕ) : ℂ) * (volume.real A : ℂ) / (Real.pi : ℂ)) =
      -((Real.pi : ℂ)⁻¹ ^ (n + 1)) *
        (∑ j : Fin n, ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
          (∫ x in firstExitDomain A n j,
            Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x))) := by
  rw [cycleIntegral_eq_anchor_sub_firstExit (by positivity) n A hA hfin]
  push_cast
  rw [← Finset.mul_sum]
  have hN : (m : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (m : ℝ) + 1 ≠ 0 by positivity)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [inv_pow, div_pow, pow_succ]
  field_simp
  ring

theorem scaled_cycleIntegral_error_bigO {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (n : ℕ) :
    (fun m : ℕ => (Real.pi : ℂ)⁻¹ ^ (n + 1) * ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
        (∫ x in Set.univ.pi (fun _ : Fin (n + 1) => A),
          Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x)) -
      (((m + 1 : ℕ) : ℂ) * (volume.real A : ℂ) / (Real.pi : ℂ))) =O[atTop]
      Cumulants.sizePower (1 / 2) := by
  have hs : (fun m : ℕ => ∑ j : Fin n, ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
      (∫ x in firstExitDomain A n j,
        Complex.exp (cycleExponent (((m + 1 : ℕ) : ℝ)) x))) =O[atTop]
      Cumulants.sizePower (1 / 2) := by
    cases n with
    | zero =>
      apply Eventually.isBigO
      apply Filter.Eventually.of_forall
      intro m
      simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
      exact Real.rpow_nonneg (by positivity) _
    | succ n =>
      have hh := IsBigO.sum (s := Finset.univ) (fun j _ => scaled_firstExit_bigO hA n j)
      apply hh.congr_left
      intro m
      simp only [Finset.sum_apply]

  have hh := hs.const_mul_left (-((Real.pi : ℂ)⁻¹ ^ (n + 1)))
  apply hh.congr_left
  intro m
  exact (scaled_cycleIntegral_error_eq hA.1.measurableSet
    (admissible_isBounded hA).measure_lt_top.ne n m).symm

end Paper.Trace
