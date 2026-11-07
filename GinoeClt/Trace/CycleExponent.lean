/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.Energy
public import Mathlib.Analysis.Complex.Norm

/-! # Literal Gaussian cycle exponent and the anchored open chain -/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Paper.Trace

def squareMass {k : ℕ} (z : Fin k → ℂ) : ℝ := ∑ i, ‖z i‖ ^ 2

def cyclePairing {k : ℕ} (z : Fin k → ℂ) : ℂ := ∑ i, z i * conj (z (finRotate k i))

def cycleExponent (a : ℝ) {k : ℕ} (z : Fin k → ℂ) : ℂ :=
  (((-a * squareMass z) : ℝ) : ℂ) + (a : ℂ) * cyclePairing z

def chainHead : (n : ℕ) → (Fin n → ℂ) → ℂ
  | 0, _ => 0
  | _ + 1, u => u 0

def chainInteraction : (n : ℕ) → (Fin n → ℂ) → ℂ
  | 0, _ => 0
  | n + 1, u => ∑ i : Fin n, u i.castSucc * conj (u i.succ)

def openChainGaussian (a : ℝ) (n : ℕ) (u : Fin n → ℂ) : ℂ :=
  Complex.exp (((-a * squareMass u : ℝ) : ℂ) + (a : ℂ) * chainInteraction n u)

theorem norm_sub_sq_complex (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 - 2 * (z * conj w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem squareMass_nonneg {k : ℕ} (z : Fin k → ℂ) : 0 ≤ squareMass z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cycleEnergy_eq_squareMass_pairing {k : ℕ} (z : Fin k → ℂ) :
    cycleEnergy z = 2 * squareMass z - 2 * (cyclePairing z).re := by
  have hr : (∑ i : Fin k, ‖z (finRotate k i)‖ ^ 2) = squareMass z :=
    Equiv.sum_comp (finRotate k) (fun i => ‖z i‖ ^ 2)
  have hre : (cyclePairing z).re = ∑ i, (z i * conj (z (finRotate k i))).re :=
    map_sum Complex.reCLM _ _
  unfold cycleEnergy
  simp_rw [norm_sub_sq_complex]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hr, ← Finset.mul_sum, ← hre]
  change squareMass z + squareMass z - 2 * (cyclePairing z).re = _
  ring

theorem cycleExponent_re (a : ℝ) {k : ℕ} (z : Fin k → ℂ) :
    (cycleExponent a z).re = -(a / 2) * cycleEnergy z := by
  simp only [cycleExponent, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [cycleEnergy_eq_squareMass_pairing]
  ring

theorem norm_exp_cycleExponent (a : ℝ) {k : ℕ} (z : Fin k → ℂ) :
    ‖Complex.exp (cycleExponent a z)‖ = Real.exp (-(a / 2) * cycleEnergy z) := by
  rw [Complex.norm_exp, cycleExponent_re]

theorem squareMass_cons {n : ℕ} (w : ℂ) (u : Fin n → ℂ) :
    squareMass (Fin.cons w u) = ‖w‖ ^ 2 + squareMass u := by
  simp [squareMass, Fin.sum_univ_succ]

theorem chainInteraction_cons {n : ℕ} (w : ℂ) (u : Fin n → ℂ) :
    chainInteraction (n + 1) (Fin.cons w u) =
      w * conj (chainHead n u) + chainInteraction n u := by
  cases n with
  | zero => simp [chainInteraction, chainHead]
  | succ n => simp [chainInteraction, chainHead, Fin.sum_univ_succ]

theorem cyclePairing_cons_zero (n : ℕ) (u : Fin n → ℂ) :
    cyclePairing (Fin.cons 0 u) = chainInteraction n u := by
  have hrot (i : Fin (n + 1)) :
      (Fin.cons (0 : ℂ) u : Fin (n + 1) → ℂ) (finRotate (n + 1) i) =
        (Fin.snoc u (0 : ℂ) : Fin (n + 1) → ℂ) i :=
    congrFun (Fin.snoc_eq_cons_rotate u 0).symm i
  unfold cyclePairing
  simp_rw [hrot]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, zero_mul, Fin.cons_succ, zero_add]
  cases n with
  | zero => simp [chainInteraction]
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have hl : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hl, Fin.snoc_last, map_zero, mul_zero, add_zero]
    change (∑ i : Fin n, u i.castSucc * conj ((Fin.snoc u (0 : ℂ) : Fin (n + 1 + 1) → ℂ) i.castSucc.succ)) =
      ∑ i : Fin n, u i.castSucc * conj (u i.succ)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]

theorem openChainGaussian_eq_exp_cycleExponent (a : ℝ) (n : ℕ) (u : Fin n → ℂ) :
    openChainGaussian a n u = Complex.exp (cycleExponent a (Fin.cons 0 u)) := by
  simp [openChainGaussian, cycleExponent, squareMass_cons, cyclePairing_cons_zero]

theorem norm_openChainGaussian (a : ℝ) (n : ℕ) (u : Fin n → ℂ) :
    ‖openChainGaussian a n u‖ = Real.exp (-(a / 2) * cycleEnergy (Fin.cons 0 u)) := by
  rw [openChainGaussian_eq_exp_cycleExponent, norm_exp_cycleExponent]

theorem squareMass_le_anchored_cycleEnergy (n : ℕ) (u : Fin n → ℂ) :
    squareMass u ≤ ((n + 1 : ℕ) : ℝ) * (n : ℝ) * cycleEnergy (Fin.cons 0 u) := by
  have h := anchored_sum_sq_le_cycleEnergy (Fin.cons (0 : ℂ) u)
  simpa [squareMass, Fin.sum_univ_succ] using h

end Paper.Trace
