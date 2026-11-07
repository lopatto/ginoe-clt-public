/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Definitions
public import GinoeClt.Lambert.PathEstimates

/-! # The exact entire primitive of the truncated exponential -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Real BigOperators

namespace Paper.Lambert

theorem truncatedExponential_succ (m : ℕ) (u : ℂ) :
    Kernel.truncatedExponential (m + 1) u = Kernel.truncatedExponential m u +
      Complex.exp (-u) * u ^ m / (m.factorial : ℂ) := by
  unfold Kernel.truncatedExponential
  rw [Finset.sum_range_succ]
  ring

theorem hasDerivAt_exp_neg (u : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-z)) (-Complex.exp (-u)) u := by
  simpa only [Function.comp_def, mul_neg_one] using
    (Complex.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)

theorem hasDerivAt_truncatedExponential_succ (n : ℕ) (u : ℂ) :
    HasDerivAt (Kernel.truncatedExponential (n + 1))
      (-Complex.exp (-u) * u ^ n / (n.factorial : ℂ)) u := by
  induction n with
  | zero =>
      unfold Kernel.truncatedExponential
      simpa only [Nat.zero_add, Finset.sum_range_one, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, mul_one] using hasDerivAt_exp_neg u
  | succ n ih =>
      have hh := ih.add ((hasDerivAt_exp_neg u).mul
        ((hasDerivAt_pow (n + 1) u).div_const ((n + 1).factorial : ℂ)))
      have hc : (-Complex.exp (-u) * u ^ n / (n.factorial : ℂ)) +
          ((-Complex.exp (-u)) * (u ^ (n + 1) / ((n + 1).factorial : ℂ)) +
          Complex.exp (-u) * (((n + 1 : ℕ) : ℂ) * u ^ ((n + 1) - 1) /
            ((n + 1).factorial : ℂ))) =
          -Complex.exp (-u) * u ^ (n + 1) / ((n + 1).factorial : ℂ) := by
        have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hs : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      have hh' := hh.congr_deriv hc
      apply hh'.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, Pi.mul_apply]
        simpa only [mul_div_assoc] using truncatedExponential_succ (n + 1) z

@[simp] theorem truncatedExponential_zero_arg {N : ℕ} (hN : 1 ≤ N) :
    Kernel.truncatedExponential N 0 = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
  simp [Kernel.truncatedExponential, Finset.sum_range_succ']

/-- The exact exponential algebra behind the source's Lambert change of variables. -/
theorem primitive_kernel_eq (n : ℕ) (z : ℂ) :
    z ^ n * Complex.exp (-((n + 1 : ℂ) * z)) *
        (Complex.exp (1 - z))⁻¹ =
      Complex.exp (-(n + 1 : ℂ)) * (phi z) ^ n := by
  have he : -((n + 1 : ℂ) * z) - (1 - z) =
      -(n + 1 : ℂ) + (n : ℂ) * (1 - z) := by ring
  have hx : Complex.exp (-((n + 1 : ℂ) * z)) *
      (Complex.exp (1 - z))⁻¹ =
      Complex.exp (-((n + 1 : ℂ) * z) - (1 - z)) := by
    simpa only [div_eq_mul_inv] using
      (Complex.exp_sub (-((n + 1 : ℂ) * z)) (1 - z)).symm
  calc
    _ = z ^ n * (Complex.exp (-((n + 1 : ℂ) * z)) *
        (Complex.exp (1 - z))⁻¹) := by ring
    _ = z ^ n * Complex.exp (-((n + 1 : ℂ) * z) - (1 - z)) := by rw [hx]
    _ = z ^ n * (Complex.exp (-(n + 1 : ℂ)) *
        Complex.exp ((n : ℂ) * (1 - z))) := by rw [he, Complex.exp_add]
    _ = _ := by rw [Complex.exp_nat_mul, phi, mul_pow]; ring

def pathCoefficient (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (n + 1) * Complex.exp (-(n + 1 : ℂ)) / (n.factorial : ℂ)

def pathPrimitive (n : ℕ) (q : ℂ) (t : ℝ) : ℂ :=
  Kernel.truncatedExponential (n + 1) ((n + 1 : ℂ) * appendixPath q t)

theorem hasDerivAt_pathPrimitive (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    HasDerivAt (pathPrimitive n q)
      (pathCoefficient n * (phi q) ^ (n + 1) *
        (1 - (t : ℂ)) ^ n * pathFactor q t) t := by
  have hv := radialArgument_mem hq ht
  have hp := (hasDerivAt_appendixPath hq ht).const_mul (n + 1 : ℂ)
  have hh := (hasDerivAt_truncatedExponential_succ n
    ((n + 1 : ℂ) * appendixPath q t)).scomp t hp
  have hphi : phi (appendixPath q t) = radialArgument q t := phi_psi hv
  have hpow : (phi (appendixPath q t)) ^ n =
      (1 - (t : ℂ)) ^ n * (phi q) ^ n := by
    rw [hphi]
    simp only [radialArgument, Complex.ofReal_sub, Complex.ofReal_one, mul_pow]
  have hd :
      ((n + 1 : ℂ) * (-phi q * deriv psi (radialArgument q t))) *
          (-Complex.exp (-((n + 1 : ℂ) * appendixPath q t)) *
            ((n + 1 : ℂ) * appendixPath q t) ^ n / (n.factorial : ℂ)) =
        pathCoefficient n * (phi q) ^ (n + 1) *
          (1 - (t : ℂ)) ^ n * pathFactor q t := by
    rw [deriv_psi hv]
    change ((n + 1 : ℂ) * (-phi q *
        (Complex.exp (1 - appendixPath q t) * (1 - appendixPath q t))⁻¹)) *
      (-Complex.exp (-((n + 1 : ℂ) * appendixPath q t)) *
        ((n + 1 : ℂ) * appendixPath q t) ^ n / (n.factorial : ℂ)) = _
    calc
      _ = ((n + 1 : ℂ) ^ (n + 1) * phi q / (n.factorial : ℂ)) *
          ((appendixPath q t) ^ n * Complex.exp (-((n + 1 : ℂ) * appendixPath q t)) *
            (Complex.exp (1 - appendixPath q t))⁻¹) *
          (1 - appendixPath q t)⁻¹ := by
        rw [mul_inv_rev, mul_pow, pow_succ]
        ring
      _ = ((n + 1 : ℂ) ^ (n + 1) * phi q / (n.factorial : ℂ)) *
          (Complex.exp (-(n + 1 : ℂ)) *
            ((1 - (t : ℂ)) ^ n * (phi q) ^ n)) *
          (1 - appendixPath q t)⁻¹ := by
        rw [primitive_kernel_eq, hpow]
      _ = _ := by
        unfold pathCoefficient pathFactor
        rw [pow_succ]
        ring
  have hh' := hh.congr_deriv hd
  unfold pathPrimitive
  simpa only [Function.comp_def, Pi.mul_def, smul_eq_mul] using hh'

/-- Exact evaluation along the manuscript's radial inverse path, including q=0.
The entire primitive is the actual finite truncated-exponential sum. -/
theorem truncatedExponential_lambert_integral (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Kernel.truncatedExponential (n + 1) ((n + 1 : ℂ) * q) =
      1 - pathCoefficient n * (phi q) ^ (n + 1) *
        ∫ t : ℝ in 0..1, (1 - (t : ℂ)) ^ n * pathFactor q t := by
  have hfc : ContinuousOn (pathFactor q) (Icc (0 : ℝ) 1) :=
    fun t ht => (hasDerivAt_pathFactor hq ht).continuousAt.continuousWithinAt
  have hc : Continuous (fun t : ℝ => pathCoefficient n * (phi q) ^ (n + 1) *
      (1 - (t : ℂ)) ^ n) := by fun_prop
  have hi : IntervalIntegrable (fun t : ℝ =>
      pathCoefficient n * (phi q) ^ (n + 1) *
        (1 - (t : ℂ)) ^ n * pathFactor q t) volume 0 1 :=
    (hc.continuousOn.mul hfc).intervalIntegrable_of_Icc zero_le_one
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_pathPrimitive n hq
      (by simpa only [uIcc_of_le zero_le_one] using ht)) hi
  have he :
      (∫ t : ℝ in 0..1, pathCoefficient n * (phi q) ^ (n + 1) *
        (1 - (t : ℂ)) ^ n * pathFactor q t) =
      pathCoefficient n * (phi q) ^ (n + 1) *
        ∫ t : ℝ in 0..1, (1 - (t : ℂ)) ^ n * pathFactor q t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  have h0 : pathPrimitive n q 0 =
      Kernel.truncatedExponential (n + 1) ((n + 1 : ℂ) * q) := by
    rw [pathPrimitive, appendixPath_zero hq]
  have h1 : pathPrimitive n q 1 = 1 := by
    rw [pathPrimitive, appendixPath_one, mul_zero]
    exact truncatedExponential_zero_arg (by omega)
  rw [he, h0, h1] at hh
  linear_combination hh

end Paper.Lambert
