/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.GaussianIntegrals
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Positive path and anchored-cycle quadratic bounds -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Paper.Trace

def pathEnergy {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i : Fin n, ‖z i.succ - z i.castSucc‖ ^ 2

def cycleEnergy {k : ℕ} (z : Fin k → ℂ) : ℝ :=
  ∑ i : Fin k, ‖z i - z (finRotate k i)‖ ^ 2

theorem pathEnergy_nonneg {n : ℕ} (z : Fin (n + 1) → ℂ) : 0 ≤ pathEnergy z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cycleEnergy_nonneg {k : ℕ} (z : Fin k → ℂ) : 0 ≤ cycleEnergy z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sq_norm_sum_le_card_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hn := norm_sum_le s f
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := by simpa only [mul_comm] using hcs

theorem anchored_sq_le_pathEnergy {n : ℕ} (z : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) : ‖z i - z 0‖ ^ 2 ≤ (n : ℝ) * pathEnergy z := by
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa using mul_nonneg (Nat.cast_nonneg n) (pathEnergy_nonneg z)
  · have hc : ((Finset.Iic a).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show (Finset.Iic a).card ≤ n by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.subset_univ (Finset.Iic a)))
    have hs : (∑ j ∈ Finset.Iic a, ‖z j.succ - z j.castSucc‖ ^ 2) ≤ pathEnergy z := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    calc
      ‖z a.succ - z 0‖ ^ 2 = ‖∑ j ∈ Finset.Iic a, (z j.succ - z j.castSucc)‖ ^ 2 := by
        rw [Fin.sum_Iic_sub]
      _ ≤ ((Finset.Iic a).card : ℝ) *
          ∑ j ∈ Finset.Iic a, ‖z j.succ - z j.castSucc‖ ^ 2 :=
        sq_norm_sum_le_card_sum_sq _ _
      _ ≤ (n : ℝ) * pathEnergy z :=
        mul_le_mul hc hs (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg n)

theorem cycleEnergy_eq_pathEnergy {n : ℕ} (z : Fin (n + 1) → ℂ) :
    cycleEnergy z = pathEnergy z + ‖z (Fin.last n) - z 0‖ ^ 2 := by
  rw [cycleEnergy, Fin.sum_univ_castSucc, finRotate_last]
  congr 1
  unfold pathEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [show finRotate (n + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt, norm_sub_rev]

theorem pathEnergy_le_cycleEnergy {n : ℕ} (z : Fin (n + 1) → ℂ) :
    pathEnergy z ≤ cycleEnergy z := by
  rw [cycleEnergy_eq_pathEnergy]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem anchored_sum_sq_le_cycleEnergy {n : ℕ} (z : Fin (n + 1) → ℂ) :
    (∑ i : Fin (n + 1), ‖z i - z 0‖ ^ 2) ≤
      ((n + 1 : ℕ) : ℝ) * (n : ℝ) * cycleEnergy z := by
  calc
    (∑ i : Fin (n + 1), ‖z i - z 0‖ ^ 2) ≤
        ∑ _i : Fin (n + 1), (n : ℝ) * pathEnergy z :=
      Finset.sum_le_sum fun i _ => anchored_sq_le_pathEnergy z i
    _ = ((n + 1 : ℕ) : ℝ) * (n : ℝ) * pathEnergy z := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pathEnergy_le_cycleEnergy z) (by positivity)

end Paper.Trace
