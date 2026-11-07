/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

Adapted from hkjtsgmc79-boop/colombo-odd-lean, OddPfaffianSquare.lean,
revision 250ff20a0c2edae8f37e5733b439bf9128a877bd (Apache-2.0),
the algebraic prefix through recursivePf_congruence. The original finite
proof is retained and generalized from real scalars to characteristic-zero fields.
-/
module

public import GinoeClt.Algebra.PfaffianMinorSummation
import Mathlib.Tactic.Ring

/-!
# Congruence covariance of the recursive Pfaffian

This finite algebraic prefix proves congruence covariance over characteristic-zero
fields. The proof is derived from the already proved arbitrary-size anti-diagonal minor-summation
theorem, rather than postulated as a new Pfaffian API.
-/

@[expose] public section

namespace Paper.PfaffianMinor

variable {R : Type*}

open scoped BigOperators

noncomputable section

section Ring
variable [CommRing R]

/-- Simultaneously apply a matrix to the row vectors of a family of paired
columns. -/
def pfRowTransform {n : Nat} {I : Type*}
    (P : Matrix (Fin n) (Fin n) R)
    (Z : I → Fin n → Fin 2 → R) : I → Fin n → Fin 2 → R :=
  fun t i side ↦ ∑ k, P i k * Z t k side

theorem selectedPairMatrix_pfRowTransform {m : Nat} {I : Type*}
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (Z : I → Fin (2 * m) → Fin 2 → R) (pairs : List.Vector I m) :
    selectedPairMatrix (pfRowTransform P Z) pairs =
      P * selectedPairMatrix Z pairs := by
  ext i j
  simp [selectedPairMatrix, pfRowTransform, Matrix.mul_apply]

theorem selectedPairDetFinset_pfRowTransform {m : Nat} {I : Type*}
    [LinearOrder I]
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (Z : I → Fin (2 * m) → Fin 2 → R) (S : Finset I) :
    selectedPairDetFinset (pfRowTransform P Z) S =
      P.det * selectedPairDetFinset Z S := by
  rw [selectedPairDetFinset, selectedPairDetFinset]
  split_ifs with h
  · rw [selectedPairDet, selectedPairDet,
      selectedPairMatrix_pfRowTransform, Matrix.det_mul]
  · simp

theorem finsetADMSRhs_pfRowTransform {m : Nat} {I : Type*}
    [LinearOrder I]
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (Z : I → Fin (2 * m) → Fin 2 → R) (w : I → R) (U : Finset I) :
    finsetADMSRhs m (pfRowTransform P Z) w U =
      P.det * finsetADMSRhs m Z w U := by
  simp only [finsetADMSRhs, selectedPairDetFinset_pfRowTransform]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem pairWedge_pfRowTransform {n : Nat} {I : Type*}
    (P : Matrix (Fin n) (Fin n) R)
    (Z : I → Fin n → Fin 2 → R) (t : I) (i j : Fin n) :
    pairWedge (pfRowTransform P Z) t i j =
      ∑ a, ∑ b, P i a * P j b * pairWedge Z t a b := by
  simp only [pairWedge, pfRowTransform]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ a, ∑ b, P i a * Z t a 0 * (P j b * Z t b 1)) -
        ∑ a, ∑ b, P i a * Z t a 1 * (P j b * Z t b 0) =
        ∑ a, ((∑ b, P i a * Z t a 0 * (P j b * Z t b 1)) -
          ∑ b, P i a * Z t a 1 * (P j b * Z t b 0)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ a, ∑ b,
        (P i a * Z t a 0 * (P j b * Z t b 1) -
          P i a * Z t a 1 * (P j b * Z t b 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

end Ring

section Field
variable [Field R] [CharZero R]

/-- Coordinate two-columns indexed by all ordered pairs.  The redundant
ordered-pair presentation is intentional: division by two makes every skew matrix a literal `pullbackFinset`, with no choice of an ordering on
unordered pairs. -/
def coordinatePair (n : Nat) : Fin (n * n) → Fin n → Fin 2 → R :=
  fun t i side ↦
    let q := (finProdFinEquiv (m := n) (n := n)).symm t
    if side = 0 then (if i = q.1 then 1 else 0)
    else (if i = q.2 then 1 else 0)

def coordinateWeight {n : Nat} (A : Matrix (Fin n) (Fin n) R) :
    Fin (n * n) → R :=
  fun t ↦
    let q := (finProdFinEquiv (m := n) (n := n)).symm t
    A q.1 q.2 / 2

theorem pullbackFinset_coordinatePair {m : Nat}
    (A : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (hA : ∀ i j, A j i = -A i j) :
    pullbackFinset (coordinatePair (2 * m)) (coordinateWeight A) Finset.univ = A := by
  ext i j
  simp only [pullbackFinset, coordinateWeight]
  rw [← (finProdFinEquiv (m := 2 * m) (n := 2 * m)).sum_comp]
  simp only [pairWedge, coordinatePair]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, one_ne_zero, ite_false]
  simp_rw [mul_ite, ite_mul, mul_one, mul_zero]
  ring_nf
  simp only [ite_true]
  simp_rw [mul_ite, ite_mul, mul_one, mul_zero]
  simp_rw [Finset.sum_add_distrib]
  simp [eq_comm]
  rw [hA]
  ring

omit [CharZero R] in
@[simp]
theorem pfRowTransform_coordinatePair_apply {n : Nat}
    (P : Matrix (Fin n) (Fin n) R) (t : Fin (n * n))
    (i : Fin n) (side : Fin 2) :
    pfRowTransform P (coordinatePair n) t i side =
      let q := (finProdFinEquiv (m := n) (n := n)).symm t
      if side = 0 then P i q.1 else P i q.2 := by
  simp [pfRowTransform, coordinatePair]

theorem pullbackFinset_pfRowTransform_coordinatePair {m : Nat}
    (A P : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (hA : ∀ i j, A j i = -A i j) :
    pullbackFinset (pfRowTransform P (coordinatePair (2 * m)))
        (coordinateWeight A) Finset.univ =
      P * A * P.transpose := by
  ext i j
  simp only [pullbackFinset, coordinateWeight]
  rw [← (finProdFinEquiv (m := 2 * m) (n := 2 * m)).sum_comp]
  simp only [pairWedge, pfRowTransform_coordinatePair_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, one_ne_zero, ite_false, ite_true]
  have hswap :
      (∑ x, ∑ y, A x y * P i y * P j x) =
        -(∑ x, ∑ y, A x y * P i x * P j y) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hA]
    ring
  have hrhs :
      (∑ x, ∑ y, A y x * P i y * P j x) =
        -(∑ x, ∑ y, A x y * P i y * P j x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hA]
    ring
  rw [show (∑ x, (∑ y, P i y * A y x) * P j x) =
      ∑ x, ∑ y, A y x * P i y * P j x by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        ring]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  have hleft :
      (∑ x, ∑ y, A x y * P i x * P j y * (1 / 2)) =
        (1 / 2) * (∑ x, ∑ y, A x y * P i x * P j y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hright :
      (∑ x, ∑ y, A x y * P i y * P j x * (-1 / 2)) =
        (-1 / 2) * (∑ x, ∑ y, A x y * P i y * P j x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  rw [hleft, hright]
  have hrhs2 : (∑ x, ∑ y, P j x * A y x * P i y) =
      -(∑ x, ∑ y, A x y * P i y * P j x) := by
    calc
      _ = ∑ x, ∑ y, A y x * P i y * P j x := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := hrhs
  rw [hrhs2, hswap]
  ring

/-- Congruence covariance of the project's recursive Pfaffian.  The proof is
an application of `recursivePf_pullbackFinset` to the ordered-coordinate
two-form decomposition. -/
theorem recursivePf_congruence {m : Nat}
    (A P : Matrix (Fin (2 * m)) (Fin (2 * m)) R)
    (hA : ∀ i j, A j i = -A i j) :
    recursivePf m (P * A * P.transpose) = P.det * recursivePf m A := by
  let Z := coordinatePair (R := R) (2 * m)
  let w := coordinateWeight A
  have hrepr : pullbackFinset Z w Finset.univ = A :=
    pullbackFinset_coordinatePair A hA
  calc
    recursivePf m (P * A * P.transpose) =
        recursivePf m (pullbackFinset (pfRowTransform P Z) w Finset.univ) := by
      rw [pullbackFinset_pfRowTransform_coordinatePair A P hA]
    _ = finsetADMSRhs m (pfRowTransform P Z) w Finset.univ :=
      recursivePf_pullbackFinset m _ _ _
    _ = P.det * finsetADMSRhs m Z w Finset.univ :=
      finsetADMSRhs_pfRowTransform P Z w Finset.univ
    _ = P.det * recursivePf m A := by
      rw [← recursivePf_pullbackFinset m Z w Finset.univ, hrepr]


end Field
end
end Paper.PfaffianMinor
