/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.CycleExponent
public import Mathlib.Analysis.Complex.Basic

/-! # Translation invariance of the literal Gaussian cycle exponent -/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Paper.Trace

theorem ofReal_squareMass {k : ℕ} (z : Fin k → ℂ) :
    ((squareMass z : ℝ) : ℂ) = ∑ i, z i * conj (z i) := by
  unfold squareMass
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  exact (Complex.mul_conj' (z i)).symm

theorem cycleExponent_eq_edge_sum (a : ℝ) {k : ℕ} (z : Fin k → ℂ) :
    cycleExponent a z = (a : ℂ) * ∑ i, z i * conj (z (finRotate k i) - z i) := by
  unfold cycleExponent
  rw [Complex.ofReal_mul, Complex.ofReal_neg, ofReal_squareMass]
  simp_rw [map_sub, mul_sub, Finset.sum_sub_distrib]
  unfold cyclePairing
  ring

theorem cycleExponent_add_const (a : ℝ) {k : ℕ} (z : Fin k → ℂ) (c : ℂ) :
    cycleExponent a (fun i => z i + c) = cycleExponent a z := by
  rw [cycleExponent_eq_edge_sum, cycleExponent_eq_edge_sum]
  congr 1
  have hr : (∑ i : Fin k, z (finRotate k i)) = ∑ i : Fin k, z i :=
    Equiv.sum_comp (finRotate k) z
  have hz : (∑ i : Fin k, conj (z (finRotate k i) - z i)) = 0 := by
    calc
      (∑ i : Fin k, conj (z (finRotate k i) - z i)) =
          conj (∑ i : Fin k, (z (finRotate k i) - z i)) := (map_sum (starRingEnd ℂ) _ _).symm
      _ = 0 := by rw [Finset.sum_sub_distrib, hr, sub_self, map_zero]
  simp only [add_sub_add_right_eq_sub, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hz, mul_zero, add_zero]

theorem cycleExponent_anchor (a : ℝ) {n : ℕ} (z : ℂ) (u : Fin n → ℂ) :
    cycleExponent a (Fin.cons z u) =
      cycleExponent a (Fin.cons 0 (fun i => u i - z)) := by
  have he : (fun i : Fin (n + 1) => ((Fin.cons (0 : ℂ) (fun j : Fin n => u j - z) : Fin (n + 1) → ℂ) i) + z) =
      (Fin.cons z u : Fin (n + 1) → ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← he, cycleExponent_add_const]

theorem exp_cycleExponent_anchor (a : ℝ) {n : ℕ} (z : ℂ) (u : Fin n → ℂ) :
    Complex.exp (cycleExponent a (Fin.cons z u)) =
      openChainGaussian a n (fun i => u i - z) := by
  rw [cycleExponent_anchor, openChainGaussian_eq_exp_cycleExponent]

end Paper.Trace
