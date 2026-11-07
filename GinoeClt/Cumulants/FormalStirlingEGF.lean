/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.FormalHn

/-! # The formal exponential generating function of Stirling numbers

All coefficient calculations are formal and hold in arbitrary rational
algebras. They use the recurrence, not an unproved enumeration of partitions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries
namespace Paper.Cumulants

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def expMinusOne : PowerSeries R := PowerSeries.exp R - 1

@[simp] theorem constantCoeff_expMinusOne :
    PowerSeries.constantCoeff (expMinusOne (R := R)) = 0 := by
  simp [expMinusOne]

theorem derivative_expMinusOne :
    d⁄dX (expMinusOne (R := R)) = expMinusOne + 1 := by
  simp [expMinusOne, map_sub, PowerSeries.derivative_exp]

omit [Algebra ℚ R] in
theorem iterateDerivative_zero (n : ℕ) :
    d⁄dX^[n] (0 : PowerSeries R) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_zero]

omit [Algebra ℚ R] in
theorem iterateDerivative_add (F G : PowerSeries R) (n : ℕ) :
    d⁄dX^[n] (F + G) = d⁄dX^[n] F + d⁄dX^[n] G := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

omit [Algebra ℚ R] in
theorem iterateDerivative_nsmul (F : PowerSeries R) (k n : ℕ) :
    d⁄dX^[n] (k • F) = k • (d⁄dX^[n] F) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_nsmul]

theorem derivative_expMinusOne_pow_succ (m : ℕ) :
    d⁄dX ((expMinusOne (R := R)) ^ (m + 1)) =
      (m + 1) • (expMinusOne ^ (m + 1) + expMinusOne ^ m) := by
  rw [PowerSeries.derivative_pow, derivative_expMinusOne]
  simp only [Nat.add_one_sub_one, nsmul_eq_mul]
  rw [pow_succ]
  ring

theorem constantCoeff_iterDerivative_expMinusOne_pow (n m : ℕ) :
    PowerSeries.constantCoeff (d⁄dX^[n] ((expMinusOne (R := R)) ^ m)) =
      (m.factorial : R) * (Nat.stirlingSecond n m : R) := by
  induction n generalizing m with
  | zero => cases m <;> simp
  | succ n ih =>
      cases m with
      | zero =>
          rw [pow_zero, Function.iterate_succ_apply, PowerSeries.derivative_one,
            iterateDerivative_zero]
          simp
      | succ m =>
          rw [Function.iterate_succ_apply, derivative_expMinusOne_pow_succ,
            iterateDerivative_nsmul, iterateDerivative_add, map_nsmul, map_add, ih, ih,
            Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
          simp only [nsmul_eq_mul]
          push_cast
          ring

theorem factorial_mul_coeff_expMinusOne_pow (n m : ℕ) :
    (n.factorial : R) * PowerSeries.coeff n ((expMinusOne (R := R)) ^ m) =
      (m.factorial : R) * (Nat.stirlingSecond n m : R) := by
  rw [← PowerSeries.constantCoeff_iterate_derivative]
  exact constantCoeff_iterDerivative_expMinusOne_pow n m

private theorem inverseFactorial_mul_factorial (n : ℕ) :
    algebraMap ℚ R (1 / (n.factorial : ℚ)) * (n.factorial : R) = 1 := by
  have hq : (1 / (n.factorial : ℚ)) * (n.factorial : ℚ) = 1 :=
    one_div_mul_cancel (by exact_mod_cast Nat.factorial_ne_zero n)
  have h := congrArg (algebraMap ℚ R) hq
  simpa only [map_mul, map_natCast, map_one] using h

theorem coeff_expMinusOne_pow (n m : ℕ) :
    PowerSeries.coeff n ((expMinusOne (R := R)) ^ m) =
      algebraMap ℚ R ((m.factorial : ℚ) / (n.factorial : ℚ)) *
        (Nat.stirlingSecond n m : R) := by
  calc
    PowerSeries.coeff n ((expMinusOne (R := R)) ^ m) =
        (algebraMap ℚ R (1 / (n.factorial : ℚ)) * (n.factorial : R)) *
          PowerSeries.coeff n ((expMinusOne (R := R)) ^ m) := by
      rw [inverseFactorial_mul_factorial, one_mul]
    _ = algebraMap ℚ R (1 / (n.factorial : ℚ)) *
        ((m.factorial : R) * (Nat.stirlingSecond n m : R)) := by
      rw [mul_assoc, factorial_mul_coeff_expMinusOne_pow]
    _ = _ := by
      rw [← mul_assoc, ← map_natCast (algebraMap ℚ R) m.factorial, ← map_mul]
      congr 2
      ring

theorem ordinaryEGF_subst_expMinusOne (u : ℕ → R) :
    (ordinaryEGF u).subst (expMinusOne (R := R)) =
      ordinaryEGF (fun n => ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R) * u k) := by
  ext n
  have he : PowerSeries.HasSubst (expMinusOne (R := R)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_expMinusOne
  rw [PowerSeries.coeff_subst' he]
  simp only [ordinaryEGF, PowerSeries.coeff_mk, smul_eq_mul]
  have hs :
      Function.support (fun k => (algebraMap ℚ R (1 / (k.factorial : ℚ)) * u k) *
        PowerSeries.coeff n ((expMinusOne (R := R)) ^ k)) ⊆
          (Finset.range (n + 1) : Set ℕ) := by
    intro k hk
    by_contra hkn
    have hnk : n < k := by
      simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hkn
      omega
    have hz := Nat.stirlingSecond_eq_zero_of_lt hnk
    rw [Function.mem_support, coeff_expMinusOne_pow, hz, Nat.cast_zero, mul_zero, mul_zero] at hk
    exact hk rfl
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_expMinusOne_pow]
  have hq :
      (1 / (k.factorial : ℚ)) * ((k.factorial : ℚ) / (n.factorial : ℚ)) =
        1 / (n.factorial : ℚ) := by
    field_simp
  have hR := congrArg (algebraMap ℚ R) hq
  simp only [map_mul] at hR
  calc
    (algebraMap ℚ R (1 / (k.factorial : ℚ)) * u k) *
        (algebraMap ℚ R ((k.factorial : ℚ) / (n.factorial : ℚ)) * (Nat.stirlingSecond n k : R)) =
      (algebraMap ℚ R (1 / (k.factorial : ℚ)) *
        algebraMap ℚ R ((k.factorial : ℚ) / (n.factorial : ℚ))) *
          ((Nat.stirlingSecond n k : R) * u k) := by ring
    _ = _ := by rw [hR]

/-- The source's factorial generating series in independent variables,
with u_0 fixed to one and every positive u_k an independent indeterminate. -/
def factorialVariableEGF (R : Type*) [CommRing R] [Algebra ℚ R] :
    PowerSeries (MvPolynomial ℕ R) :=
  ordinaryEGF (fun k => if k = 0 then 1 else MvPolynomial.X k)

@[simp] theorem constantCoeff_factorialVariableEGF :
    PowerSeries.constantCoeff (factorialVariableEGF R) = 1 := by
  simp [factorialVariableEGF]

theorem factorialMomentEGF_eq_factorialVariableEGF_subst :
    ordinaryEGF (fun j => factorialMomentPolynomial R j) =
      (factorialVariableEGF R).subst (expMinusOne (R := MvPolynomial ℕ R)) := by
  unfold factorialVariableEGF
  rw [ordinaryEGF_subst_expMinusOne]
  congr 1
  funext j
  by_cases hj : j = 0
  · subst j
    simp
  · rw [factorialMomentPolynomial, ite_eq_right hj]
    calc
      (∑ k ∈ Finset.Icc 1 j,
          MvPolynomial.C (Nat.stirlingSecond j k : R) * MvPolynomial.X k) =
        ∑ k ∈ Finset.Icc 1 j,
          (Nat.stirlingSecond j k : MvPolynomial ℕ R) *
            (if k = 0 then 1 else MvPolynomial.X k) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [ite_eq_right (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hk).1), map_natCast]
      _ = ∑ k ∈ Finset.range (j + 1),
          (Nat.stirlingSecond j k : MvPolynomial ℕ R) *
            (if k = 0 then 1 else MvPolynomial.X k) := by
        apply Finset.sum_subset
        · intro k hk
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
        · intro k hk hnot
          have hk0 : k = 0 := by
            simp only [Finset.mem_Icc, Finset.mem_range] at *
            omega
          subst k
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
          simp

/-- The full source coefficient identity: H_n is obtained from the formal
logarithm after substituting exp(t)-1 into the factorial generating series.
The equality is in independent multivariate-polynomial variables. -/
theorem factorialCumulantPolynomial_eq_factorialEGFLog (n : ℕ) (hn : 1 ≤ n) :
    factorialCumulantPolynomial R n =
      (n.factorial : MvPolynomial ℕ R) *
        PowerSeries.coeff n (PowerSeries.logOf
          ((factorialVariableEGF R).subst (expMinusOne (R := MvPolynomial ℕ R)))) := by
  rw [← factorialMomentEGF_eq_factorialVariableEGF_subst]
  exact factorialCumulantPolynomial_eq_formalLog n hn


end Paper.Cumulants
