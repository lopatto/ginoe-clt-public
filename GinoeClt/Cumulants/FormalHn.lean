/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.FormalFaa
public import GinoeClt.Cumulants.PseudoCumulants

/-!
# Formal logarithmic coefficients of the universal cumulant polynomial

All input coefficients are arbitrary ring elements. In particular the result
applies with a multivariate polynomial coefficient ring, so it is an identity in
independent variables rather than only an identity evaluated at random moments.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries
namespace Paper.Cumulants

variable {R : Type*} [CommRing R] [Algebra ℚ R]

def ordinaryEGF (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => algebraMap ℚ R (1 / (n.factorial : ℚ)) * a n

@[simp] theorem constantCoeff_ordinaryEGF (a : ℕ → R) :
    PowerSeries.constantCoeff (ordinaryEGF a) = a 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [ordinaryEGF]

theorem constantCoeff_iterDerivative_ordinaryEGF (a : ℕ → R) (n : ℕ) :
    PowerSeries.constantCoeff (d⁄dX^[n] (ordinaryEGF a)) = a n := by
  rw [PowerSeries.constantCoeff_iterate_derivative]
  simp only [ordinaryEGF, PowerSeries.coeff_mk]
  have hq : (n.factorial : ℚ) * (1 / (n.factorial : ℚ)) = 1 := by
    exact mul_one_div_cancel (by exact_mod_cast Nat.factorial_ne_zero n)
  have hR := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_natCast, map_one] at hR
  rw [← mul_assoc, hR, one_mul]

theorem constantCoeff_iterDerivative_log {n : ℕ} (hn : 1 ≤ n) :
    PowerSeries.constantCoeff (d⁄dX^[n] (PowerSeries.log R)) =
      (-1 : R) ^ (n - 1) * (n - 1).factorial := by
  have hne : n ≠ 0 := Nat.ne_zero_of_lt hn
  rw [PowerSeries.constantCoeff_iterate_derivative, PowerSeries.coeff_log, ite_eq_right hne]
  have hp : (-1 : ℚ) ^ (n + 1) = (-1 : ℚ) ^ (n - 1) := by
    calc
      (-1 : ℚ) ^ (n + 1) = (-1 : ℚ) ^ ((n - 1) + 2) := by congr 1; omega
      _ = (-1 : ℚ) ^ (n - 1) := by rw [pow_add]; norm_num
  have hq :
      (n.factorial : ℚ) * ((-1 : ℚ) ^ (n + 1) / (n : ℚ)) =
        (-1 : ℚ) ^ (n - 1) * (n - 1).factorial := by
    rw [hp, ← Nat.mul_factorial_pred hne, Nat.cast_mul]
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hne
    field_simp
  have hR := congrArg (algebraMap ℚ R) hq
  simpa only [map_mul, map_pow, map_neg, map_one, map_natCast] using hR

theorem constantCoeff_iterDerivative_ordinaryEGF_sub_one (a : ℕ → R) {j : ℕ} (hj : 1 ≤ j) :
    PowerSeries.constantCoeff (d⁄dX^[j] (ordinaryEGF a - 1)) = a j := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
  simpa only [Function.iterate_succ_apply, map_sub, PowerSeries.derivative_one, sub_zero] using
    constantCoeff_iterDerivative_ordinaryEGF a (j + 1)

omit [Algebra ℚ R] in
private theorem sum_length_prod_eq {n : ℕ} (w a : ℕ → R) :
    (∑ c : OrderedFinpartition n, a c.length * ∏ i : Fin c.length, w (c.partSize i)) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)), a P.parts.card * ∏ B ∈ P.parts, w B.card := by
  rw [← (PartitionBridge.equiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  have hc : ((PartitionBridge.equiv n) c).parts.card = c.length :=
    PartitionBridge.card_toFinpartition_parts c
  rw [hc, ← PartitionBridge.prod_partSize_eq c w]

/-- The logarithmic coefficient formula for arbitrary prescribed ordinary
moments, before any factorial-moment or determinant substitution. -/
theorem formal_log_coeff (a : ℕ → R) (ha : a 0 = 1) {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : R) * PowerSeries.coeff n (PowerSeries.logOf (ordinaryEGF a)) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        ((-1 : R) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial) *
          ∏ B ∈ P.parts, a B.card := by
  let G : PowerSeries R := ordinaryEGF a - 1
  have hG : G.constantCoeff = 0 := by simp [G, ha]
  have hg : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero' hG
  have hcc (F : PowerSeries R) :
      PowerSeries.constantCoeff (F.subst G) = PowerSeries.constantCoeff F := by
    simpa [← PowerSeries.constantCoeff_eq] using
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hG F
  have h := congrArg PowerSeries.constantCoeff (formalFaa (PowerSeries.log R) G hg n)
  rw [PowerSeries.constantCoeff_iterate_derivative] at h
  calc
    (n.factorial : R) * PowerSeries.coeff n (PowerSeries.logOf (ordinaryEGF a)) =
        ∑ c : OrderedFinpartition n,
          PowerSeries.constantCoeff (((d⁄dX^[c.length] (PowerSeries.log R)).subst G)) *
            ∏ i : Fin c.length, PowerSeries.constantCoeff (d⁄dX^[c.partSize i] G) := by
      simpa only [PowerSeries.logOf_eq, G, map_sum, formalFaaTerm, map_mul, map_prod] using h
    _ = ∑ c : OrderedFinpartition n,
        ((-1 : R) ^ (c.length - 1) * (c.length - 1).factorial) *
          ∏ i : Fin c.length, a (c.partSize i) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hcc, constantCoeff_iterDerivative_log (c.length_pos hn)]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact constantCoeff_iterDerivative_ordinaryEGF_sub_one a (c.partSize_pos i)
    _ = _ := sum_length_prod_eq a (fun m => (-1 : R) ^ (m - 1) * (m - 1).factorial)

/-- The already-defined universal H_n polynomial is exactly the corresponding
formal logarithmic coefficient in its independent polynomial variables. -/
theorem factorialCumulantPolynomial_eq_formalLog (n : ℕ) (hn : 1 ≤ n) :
    factorialCumulantPolynomial R n =
      (n.factorial : MvPolynomial ℕ R) *
        PowerSeries.coeff n (PowerSeries.logOf
          (ordinaryEGF (fun j => factorialMomentPolynomial R j))) := by
  rw [formal_log_coeff (fun j => factorialMomentPolynomial R j)
    (factorialMomentPolynomial_zero (R := R)) hn]
  rw [factorialCumulantPolynomial, ite_eq_right (Nat.ne_zero_of_lt hn)]
  apply Finset.sum_congr rfl
  intro P _
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

end Paper.Cumulants
