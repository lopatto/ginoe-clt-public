/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Signed Stirling inversion and the cycle-cumulant recursion

The signed first-kind coefficients are defined as the actual coefficients of
the falling-factorial polynomial. Thus their meaning is the manuscript's
characterization, rather than a new sequence with unproved identification.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Paper.Cumulants

def signedStirling (n j : ℕ) : ℤ :=
  (descPochhammer ℤ n).coeff j

theorem descPochhammer_eq_sum_signedStirling (n : ℕ) :
    descPochhammer ℤ n =
      ∑ j ∈ Finset.range (n + 1), Polynomial.C (signedStirling n j) * Polynomial.X ^ j := by
  simpa only [descPochhammer_natDegree, signedStirling] using
    (descPochhammer ℤ n).as_sum_range_C_mul_X_pow

@[simp] theorem signedStirling_zero (j : ℕ) :
    signedStirling 0 j = if j = 0 then 1 else 0 := by
  simp [signedStirling, Polynomial.coeff_one]

@[simp] theorem signedStirling_succ_zero (n : ℕ) :
    signedStirling (n + 1) 0 = 0 := by
  unfold signedStirling
  rw [descPochhammer_succ_left, Polynomial.coeff_X_mul_zero]

theorem signedStirling_succ_succ (n j : ℕ) :
    signedStirling (n + 1) (j + 1) =
      signedStirling n j - (n : ℤ) * signedStirling n (j + 1) := by
  unfold signedStirling
  rw [descPochhammer_succ_right, mul_sub, Polynomial.coeff_sub,
    Polynomial.coeff_mul_X, Polynomial.coeff_mul_natCast]
  ring

theorem signedStirling_eq_zero_of_lt {n j : ℕ} (h : n < j) : signedStirling n j = 0 := by
  unfold signedStirling
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simpa only [descPochhammer_natDegree] using h

@[simp] theorem signedStirling_self (n : ℕ) : signedStirling n n = 1 := by
  unfold signedStirling
  simpa only [descPochhammer_natDegree] using (monic_descPochhammer ℤ n).coeff_natDegree

theorem signedStirling_one_right (n : ℕ) :
    signedStirling (n + 1) 1 = (-1 : ℤ) ^ n * n.factorial := by
  induction n with
  | zero => simp [signedStirling]
  | succ n ih =>
      rw [signedStirling_succ_succ, signedStirling_succ_zero, ih, pow_succ, Nat.factorial_succ]
      push_cast
      ring

def signedStirlingTransform (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), signedStirling n j * f j

theorem signedStirlingTransform_succ (f : ℕ → ℤ) (n : ℕ) :
    signedStirlingTransform f (n + 1) =
      signedStirlingTransform (fun j => f (j + 1)) n -
        (n : ℤ) * signedStirlingTransform f n := by
  have hshift :
      (∑ j ∈ Finset.range (n + 1), signedStirling n (j + 1) * f (j + 1)) =
        signedStirlingTransform f n - signedStirling n 0 * f 0 := by
    have h := Finset.sum_range_succ' (fun j => signedStirling n j * f j) (n + 1)
    rw [Finset.sum_range_succ,
      signedStirling_eq_zero_of_lt (Nat.lt_succ_self n), zero_mul, add_zero] at h
    unfold signedStirlingTransform
    linarith
  have hz : (n : ℤ) * signedStirling n 0 * f 0 = 0 := by
    cases n <;> simp
  unfold signedStirlingTransform
  rw [Finset.sum_range_succ']
  simp only [signedStirling_succ_zero, zero_mul, add_zero]
  simp_rw [signedStirling_succ_succ, sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  calc
    (∑ j ∈ Finset.range (n + 1), (n : ℤ) * signedStirling n (j + 1) * f (j + 1)) =
        (n : ℤ) * ∑ j ∈ Finset.range (n + 1), signedStirling n (j + 1) * f (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (n : ℤ) * (signedStirlingTransform f n - signedStirling n 0 * f 0) := by rw [hshift]
    _ = (n : ℤ) * signedStirlingTransform f n := by
      rw [mul_sub]
      rw [← mul_assoc, hz, sub_zero]

theorem signedStirlingTransform_add (f g : ℕ → ℤ) (n : ℕ) :
    signedStirlingTransform (fun j => f j + g j) n =
      signedStirlingTransform f n + signedStirlingTransform g n := by
  unfold signedStirlingTransform
  simp only [mul_add, Finset.sum_add_distrib]

theorem signedStirlingTransform_const_mul (c : ℤ) (f : ℕ → ℤ) (n : ℕ) :
    signedStirlingTransform (fun j => c * f j) n = c * signedStirlingTransform f n := by
  unfold signedStirlingTransform
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The signed first-kind and second-kind coefficient matrices are inverse.
This is proved from the falling-factorial recurrence, without a new assumption. -/
theorem signedStirling_second_orthogonal (n k : ℕ) :
    signedStirlingTransform (fun j => (Nat.stirlingSecond j k : ℤ)) n =
      if n = k then 1 else 0 := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [signedStirlingTransform]
  | succ n ih =>
      cases k with
      | zero =>
          simp only [Nat.succ_ne_zero]
          unfold signedStirlingTransform
          apply Finset.sum_eq_zero
          intro j _
          cases j <;> simp
      | succ k =>
          rw [signedStirlingTransform_succ]
          have hf :
              (fun j => (Nat.stirlingSecond (j + 1) (k + 1) : ℤ)) =
                fun j => (k + 1 : ℤ) * (Nat.stirlingSecond j (k + 1) : ℤ) +
                  (Nat.stirlingSecond j k : ℤ) := by
            funext j
            rw [Nat.stirlingSecond_succ_succ]
            push_cast
            ring
          rw [hf, signedStirlingTransform_add, signedStirlingTransform_const_mul,
            ih (k + 1), ih k]
          by_cases hnk : n = k
          · subst n
            simp
          · by_cases hnk1 : n = k + 1
            · subst n
              simp
            · simp [hnk, hnk1]


variable (R : Type*) [CommRing R]

theorem signedStirling_second_orthogonal_cast (n k : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (signedStirling n j : R) * (Nat.stirlingSecond j k : R)) =
      if n = k then 1 else 0 := by
  have h := congrArg (Int.castRingHom R) (signedStirling_second_orthogonal n k)
  simpa [signedStirlingTransform] using h

def stirlingSecondTransform (f : ℕ → R) (n : ℕ) : R :=
  ∑ m ∈ Finset.range (n + 1), (Nat.stirlingSecond n m : R) * f m

/-- Finite triangular basis inversion. No probability or determinant premise. -/
theorem stirlingSecondTransform_inverse (f : ℕ → R) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (signedStirling n j : R) * stirlingSecondTransform R f j) =
      f n := by
  have hext (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      stirlingSecondTransform R f j =
        ∑ m ∈ Finset.range (n + 1), (Nat.stirlingSecond j m : R) * f m := by
    unfold stirlingSecondTransform
    apply Finset.sum_subset
    · apply Finset.range_mono
      exact Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    · intro m hm hnot
      have hjm : j < m := by
        simp only [Finset.mem_range, not_lt] at hnot
        omega
      simp [Nat.stirlingSecond_eq_zero_of_lt hjm]
  calc
    (∑ j ∈ Finset.range (n + 1), (signedStirling n j : R) * stirlingSecondTransform R f j) =
        ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
          (signedStirling n j : R) * (Nat.stirlingSecond j m : R) * f m := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hext j hj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ m ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1), (signedStirling n j : R) *
          (Nat.stirlingSecond j m : R)) * f m := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_mul]
    _ = f n := by
      simp_rw [signedStirling_second_orthogonal_cast]
      simp

/-- Signed cycle contribution, with a zero extension at order zero. -/
def cycleWeight (m : ℕ) : R :=
  if m = 0 then 0 else (-1 : R) ^ (m - 1) * (m - 1).factorial

/-- The Stirling cycle expression from the determinantal cycle formula.
Its equality to H_n(T) for actual determinant integrals is a separate result. -/
def cycleStirlingTransform (trace : ℕ → R) (n : ℕ) : R :=
  stirlingSecondTransform R (fun m => cycleWeight R m * trace m) n

@[simp] theorem cycleStirlingTransform_zero (trace : ℕ → R) :
    cycleStirlingTransform R trace 0 = 0 := by
  simp [cycleStirlingTransform, stirlingSecondTransform, cycleWeight]

@[simp] theorem cycleStirlingTransform_one (trace : ℕ → R) :
    cycleStirlingTransform R trace 1 = trace 1 := by
  simp [cycleStirlingTransform, stirlingSecondTransform, cycleWeight,
    Finset.sum_range_succ, Nat.stirlingSecond_self]

private theorem sum_range_split_ends (f : ℕ → R) {n : ℕ} (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n + 1), f j) =
      f 0 + f 1 + (∑ j ∈ Finset.Ico 2 n, f j) + f n := by
  rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico f hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The manuscript's signed-Stirling cycle recursion. Its finite sum is empty
at order two; all coefficients are independent of the trace sequence. -/
theorem cycleStirlingTransform_recursion (trace : ℕ → R) {n : ℕ} (hn : 2 ≤ n) :
    cycleStirlingTransform R trace n =
      (-1 : R) ^ n * (n - 1).factorial * (trace 1 - trace n) +
        ∑ j ∈ Finset.Ico 2 n, -(signedStirling n j : R) *
          cycleStirlingTransform R trace j := by
  have h1 : 1 ≤ n := le_trans (by decide) hn
  have hne : n ≠ 0 := Nat.ne_zero_of_lt h1
  have hsInt : signedStirling n 1 = (-1 : ℤ) ^ (n - 1) * (n - 1).factorial := by
    simpa only [Nat.sub_add_cancel h1] using signedStirling_one_right (n - 1)
  have hsR : (signedStirling n 1 : R) = (-1 : R) ^ (n - 1) * (n - 1).factorial := by
    have h := congrArg (Int.castRingHom R) hsInt
    simpa using h
  have hInv := stirlingSecondTransform_inverse R
    (fun m => cycleWeight R m * trace m) n
  change (∑ j ∈ Finset.range (n + 1), (signedStirling n j : R) *
    cycleStirlingTransform R trace j) = cycleWeight R n * trace n at hInv
  rw [sum_range_split_ends R _ hn] at hInv
  simp only [cycleStirlingTransform_zero, cycleStirlingTransform_one, mul_zero, zero_add,
    signedStirling_self, Int.cast_one, one_mul] at hInv
  rw [hsR, cycleWeight, ite_eq_right hne] at hInv
  have hp : (-1 : R) ^ n = -((-1 : R) ^ (n - 1)) := by
    calc
      (-1 : R) ^ n = (-1 : R) ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = -((-1 : R) ^ (n - 1)) := by rw [pow_succ, mul_neg_one]
  have hsNeg :
      (∑ j ∈ Finset.Ico 2 n, -(signedStirling n j : R) * cycleStirlingTransform R trace j) =
        -(∑ j ∈ Finset.Ico 2 n, (signedStirling n j : R) * cycleStirlingTransform R trace j) := by
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [hp, hsNeg]
  calc
    cycleStirlingTransform R trace n =
        ((-1 : R) ^ (n - 1) * (n - 1).factorial) * trace n -
          (((-1 : R) ^ (n - 1) * (n - 1).factorial) * trace 1 +
            ∑ j ∈ Finset.Ico 2 n, (signedStirling n j : R) * cycleStirlingTransform R trace j) := by
      apply eq_sub_of_add_eq
      simpa only [add_assoc, add_comm, add_left_comm] using hInv
    _ = _ := by ring

theorem cycleStirlingTransform_two (trace : ℕ → R) :
    cycleStirlingTransform R trace 2 = trace 1 - trace 2 := by
  simpa using cycleStirlingTransform_recursion R trace (n := 2) (by decide)


end Paper.Cumulants
