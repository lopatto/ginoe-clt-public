/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Asymptotics.Arith
public import Mathlib.Analysis.Asymptotics.Ring

/-! # Fixed-order recursion bounds and CLT power normalization

These estimates provide the asymptotic normalization. Kernel, variance and
comparison estimates enter as explicit hypotheses here. Their GinOE instances
are proved in downstream modules and assembled in SkewOrthogonal.CountPfaffianIdentity.
-/

@[expose] public section
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

namespace Paper.Cumulants

def sizePower (a : ℝ) (n : ℕ) : ℝ := (n + 1 : ℝ) ^ a

theorem tendsto_matrixSize : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨k, hk⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop k] with n hn
  have hn' : (k : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem sizePower_mul (a b : ℝ) (n : ℕ) :
    sizePower a n * sizePower b n = sizePower (a + b) n := by
  exact (Real.rpow_add (by positivity : 0 < (n + 1 : ℝ)) a b).symm

theorem sizePower_mono_bigO {a b : ℝ} (hab : a ≤ b) :
    sizePower a =O[atTop] sizePower b := by
  apply Eventually.isBigO
  apply Filter.Eventually.of_forall
  intro n
  change |(n + 1 : ℝ) ^ a| ≤ (n + 1 : ℝ) ^ b
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_exponent_le
    (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]) hab

theorem sizePower_tendsto_zero {a : ℝ} (ha : a < 0) :
    Tendsto (sizePower a) atTop (𝓝 0) := by
  convert (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp tendsto_matrixSize using 1
  funext n
  simp [sizePower]

theorem normalized_tendsto_zero {f : ℕ → ℝ} {a b : ℝ}
    (hf : f =O[atTop] sizePower a) (hab : a < b) :
    Tendsto (fun n => sizePower (-b) n * f n) atTop (𝓝 0) := by
  have hh := (isBigO_refl (sizePower (-b)) atTop).mul hf
  have he (n : ℕ) : sizePower (-b) n * sizePower a n = sizePower (a - b) n := by
    rw [sizePower_mul]
    congr 1
    ring
  exact (hh.congr_right he).trans_tendsto (sizePower_tendsto_zero (sub_neg.mpr hab))

/-- A finite triangular recursion only uses lower orders at the same size.
The common majorant is arbitrary and is not required to be nonzero. -/
theorem triangular_recursion_bigO (u : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (leading : ℕ → ℕ → ℝ) (coeff : ℕ → ℕ → ℝ)
    (h2 : u 2 =O[atTop] g)
    (hleading : ∀ r, 3 ≤ r → leading r =O[atTop] g)
    (hrec : ∀ r, 3 ≤ r → ∀ n,
      u r n = leading r n + ∑ j ∈ Finset.Ico 2 r, coeff r j * u j n) :
    ∀ r, 2 ≤ r → u r =O[atTop] g := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_cases hr2 : r = 2
    · simpa only [hr2] using h2
    have hr3 : 3 ≤ r := by omega
    have hs : (fun n => ∑ j ∈ Finset.Ico 2 r, coeff r j * u j n) =O[atTop] g := by
      have hs' := IsBigO.sum (s := Finset.Ico 2 r) (g := g) (l := atTop)
        (fun j hj => (ih j (Finset.mem_Ico.mp hj).2 (Finset.mem_Ico.mp hj).1).const_mul_left
          (coeff r j))
      exact hs'.congr_left (fun n => by simp)
    exact ((hleading r hr3).add hs).congr_left (fun n => (hrec r hr3 n).symm)


/-- Recover a raw power bound from a convergent normalized sequence. -/
theorem isBigO_of_normalized_tendsto {f : ℕ → ℝ} {a v : ℝ}
    (h : Tendsto (fun n => sizePower (-a) n * f n) atTop (𝓝 v)) :
    f =O[atTop] sizePower a := by
  have h1 : (fun n => sizePower (-a) n * f n) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := h.isBigO_one (F := ℝ)
  have hh := h1.mul (isBigO_refl (sizePower a) atTop)
  apply hh.congr
  · intro n
    calc
      _ = (sizePower (-a) n * sizePower a n) * f n := by ring
      _ = f n := by rw [sizePower_mul]; simp [sizePower]
  · intro n
    exact one_mul _

/-- Exact coefficient in the frozen N^(-1/4) cumulant normalization. -/
theorem normalizationCoeff_eq_sizePower (n r : ℕ) :
    (((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ r = sizePower (-(r : ℝ) / 4) n := by
  calc
    _ = ((n + 1 : ℝ) ^ (-(1 / 4 : ℝ))) ^ r := by
      rw [Real.rpow_neg (by positivity)]
    _ = (n + 1 : ℝ) ^ ((-(1 / 4 : ℝ)) * (r : ℝ)) := by
      rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ = _ := by
      unfold sizePower
      congr 1
      ring

theorem normalized_fiveEighths_tendsto_zero {f : ℕ → ℝ} {r : ℕ} (hr : 3 ≤ r)
    (hf : f =O[atTop] sizePower (5 / 8)) :
    Tendsto (fun n : ℕ => (((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ r * f n) atTop (𝓝 0) := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hdec : (5 / 8 : ℝ) < (r : ℝ) / 4 := by linarith
  convert normalized_tendsto_zero hf hdec using 1
  funext n
  rw [normalizationCoeff_eq_sizePower]
  congr 1
  congr 1
  ring

end Paper.Cumulants
