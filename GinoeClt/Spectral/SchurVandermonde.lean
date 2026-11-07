/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFullRoots
public import Mathlib.LinearAlgebra.Vandermonde
@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Paper.Spectral

theorem det_vandermonde_finCast {m n : ℕ} (h : m = n) (v : Fin n → ℂ) :
    (Matrix.vandermonde (fun i : Fin m ↦ v (Fin.cast h i))).det = (Matrix.vandermonde v).det := by
  subst n
  rfl

theorem det_vandermonde_cons {n : ℕ} (a : ℂ) (v : Fin n → ℂ) :
    (Matrix.vandermonde (Fin.cons a v)).det =
      (∏ i : Fin n, (v i-a)) * (Matrix.vandermonde v).det := by
  simp only [Matrix.det_vandermonde, Fin.prod_univ_succ,
    Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Fin.cons_zero, Fin.cons_succ]

theorem norm_det_vandermonde_cons {n : ℕ} (a : ℂ) (v : Fin n → ℂ) :
    ‖(Matrix.vandermonde (Fin.cons a v)).det‖ =
      (∏ i : Fin n, ‖v i-a‖) * ‖(Matrix.vandermonde v).det‖ := by
  rw [det_vandermonde_cons, norm_mul, norm_prod]

theorem norm_det_vandermonde_cons_two {n : ℕ} (a b : ℂ) (v : Fin n → ℂ) :
    ‖(Matrix.vandermonde (Fin.cons a (Fin.cons b v))).det‖ =
      ‖b-a‖ * (∏ i : Fin n, ‖v i-a‖ * ‖v i-b‖) * ‖(Matrix.vandermonde v).det‖ := by
  simp only [norm_det_vandermonde_cons, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.prod_mul_distrib]
  ring

theorem norm_conj_sub_real (z : ℂ) (a : ℝ) : ‖conj z-(a : ℂ)‖ = ‖z-(a : ℂ)‖ := by
  simpa only [map_sub, Complex.conj_ofReal] using Complex.norm_conj (z-(a : ℂ))

theorem norm_real_sub_conj (a : ℝ) (z : ℂ) : ‖(a : ℂ)-conj z‖ = ‖(a : ℂ)-z‖ := by
  rw [norm_sub_rev, norm_conj_sub_real, norm_sub_rev]

theorem norm_conj_sub_conj (z v : ℂ) : ‖conj z-conj v‖ = ‖z-v‖ := by
  rw [← map_sub, Complex.norm_conj]

theorem norm_conj_sub (z v : ℂ) : ‖conj z-v‖ = ‖z-conj v‖ := by
  simpa only [map_sub, starRingEnd_self_apply] using Complex.norm_conj (z-conj v)

/-- The actual within-pair factor in the FULL Vandermonde. No gap/noncollision assumption. -/
theorem norm_schurRoot_conj_sub (a b c : ℝ) :
    ‖conj (schurRoot a b c)-schurRoot a b c‖ = 2 * Real.sqrt (b*c) := by
  have he : conj (schurRoot a b c)-schurRoot a b c =
      ((-2 * Real.sqrt (b*c) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [schurRoot, Complex.mul_re, Complex.mul_im]; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  norm_num

end Paper.Spectral
