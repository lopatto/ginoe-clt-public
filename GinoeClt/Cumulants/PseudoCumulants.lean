/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Universal determinantal pseudo-cumulant polynomials

The variables are factorial moments. For positive order, this is the literal
set-partition Möbius polynomial: first convert factorial moments to ordinary
moments using Stirling numbers of the second kind, then take the ordinary
cumulant polynomial. The internal order-zero extension is zero; the order-zero
factorial-to-ordinary moment polynomial is one. These extensions do not add a
hypothesis on an input sequence.

All algebra works over an arbitrary commutative ring, including complex scalars
before reality of the determinant and cyclic integrals is proved. No point
process, determinant/cycle identity, or external result is assumed here.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Classical Pointwise
namespace Paper.Cumulants

variable (R : Type*) [CommRing R]

/-- The polynomial M_j converting factorial moments to ordinary moments. -/
def factorialMomentPolynomial (j : ℕ) : MvPolynomial ℕ R :=
  if j = 0 then 1 else
    ∑ k ∈ Finset.Icc 1 j, MvPolynomial.C (Nat.stirlingSecond j k : R) * MvPolynomial.X k

/-- The universal H_n polynomial in independent factorial-moment variables.
The value at order zero is only an explicit internal extension. -/
def factorialCumulantPolynomial (n : ℕ) : MvPolynomial ℕ R :=
  if n = 0 then 0 else
    ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
      MvPolynomial.C ((-1 : R) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial) *
        ∏ B ∈ P.parts, factorialMomentPolynomial R B.card

/-- The algebraic surrogate H_n(T), independent of any auxiliary process. -/
def pseudoCumulant (T : ℕ → R) (n : ℕ) : R :=
  MvPolynomial.eval₂Hom (RingHom.id R) T (factorialCumulantPolynomial R n)

variable {R}

@[simp] theorem factorialMomentPolynomial_zero :
    factorialMomentPolynomial R 0 = 1 := by
  simp [factorialMomentPolynomial]

@[simp] theorem factorialMomentPolynomial_one :
    factorialMomentPolynomial R 1 = MvPolynomial.X 1 := by
  simp [factorialMomentPolynomial, Nat.stirlingSecond_self]

@[simp] theorem factorialCumulantPolynomial_zero :
    factorialCumulantPolynomial R 0 = 0 := by
  simp [factorialCumulantPolynomial]

private theorem parts_fin_one (P : Finpartition (Finset.univ : Finset (Fin 1))) :
    P.parts = {Finset.univ} := by
  have hB (B : Finset (Fin 1)) (hB : B ∈ P.parts) : B = Finset.univ := by
    obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
    ext j
    simp only [Finset.mem_univ, iff_true]
    exact (Subsingleton.elim i j) ▸ hi
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · obtain ⟨B, hmem⟩ := P.parts_nonempty (by simp)
    simpa only [hB B hmem] using hmem
  · exact hB

@[simp] theorem factorialCumulantPolynomial_one :
    factorialCumulantPolynomial R 1 = MvPolynomial.X 1 := by
  let : Subsingleton (Finpartition (Finset.univ : Finset (Fin 1))) :=
    ⟨fun P Q => Finpartition.ext (by rw [parts_fin_one P, parts_fin_one Q])⟩
  let P : Finpartition (Finset.univ : Finset (Fin 1)) := Finpartition.indiscrete (by simp)
  rw [factorialCumulantPolynomial, ite_eq_right (by decide), Fintype.sum_subsingleton _ P]
  simp [parts_fin_one P]

@[simp] theorem pseudoCumulant_zero (T : ℕ → R) : pseudoCumulant R T 0 = 0 := by
  simp [pseudoCumulant]

@[simp] theorem pseudoCumulant_one (T : ℕ → R) : pseudoCumulant R T 1 = T 1 := by
  simp [pseudoCumulant]

theorem eval_factorialMomentPolynomial (T : ℕ → R) {j : ℕ} (hj : 1 ≤ j) :
    MvPolynomial.eval₂Hom (RingHom.id R) T (factorialMomentPolynomial R j) =
      ∑ k ∈ Finset.Icc 1 j, (Nat.stirlingSecond j k : R) * T k := by
  simp [factorialMomentPolynomial, Nat.ne_zero_of_lt hj]

/-- The exact positive-order set-partition formula defining H_n(T). -/
theorem pseudoCumulant_eq_mobius (T : ℕ → R) {n : ℕ} (hn : 1 ≤ n) :
    pseudoCumulant R T n =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        ((-1 : R) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial) *
          ∏ B ∈ P.parts, ∑ k ∈ Finset.Icc 1 B.card,
            (Nat.stirlingSecond B.card k : R) * T k := by
  unfold pseudoCumulant factorialCumulantPolynomial
  rw [ite_eq_right (Nat.ne_zero_of_lt hn), map_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [map_mul, MvPolynomial.eval₂Hom_C, map_prod]
  simp only [RingHom.id_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro B hB
  exact eval_factorialMomentPolynomial T
    (Finset.one_le_card.mpr (P.nonempty_of_mem_parts hB))

private theorem weightedDegree_C_le (c : R) :
    MvPolynomial.weightedTotalDegree (id : ℕ → ℕ) (MvPolynomial.C c) ≤ 0 := by
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  change d ∈ (MvPolynomial.monomial 0 c).support at hd
  have h : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

private theorem weightedDegree_X_le (k : ℕ) :
    MvPolynomial.weightedTotalDegree (id : ℕ → ℕ) (MvPolynomial.X k : MvPolynomial ℕ R) ≤ k := by
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  change d ∈ (MvPolynomial.monomial (Finsupp.single k 1) (1 : R)).support at hd
  have h : d = Finsupp.single k 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp [Finsupp.weight_single]

private theorem weightedDegree_sum_le {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ℕ R) (n : ℕ)
    (h : ∀ i ∈ s, MvPolynomial.weightedTotalDegree id (f i) ≤ n) :
    MvPolynomial.weightedTotalDegree id (∑ i ∈ s, f i) ≤ n := by
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  obtain ⟨i, hi, hd⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  exact (MvPolynomial.le_weightedTotalDegree id hd).trans (h i hi)

private theorem weightedDegree_mul_le (p q : MvPolynomial ℕ R) :
    MvPolynomial.weightedTotalDegree id (p * q) ≤
      MvPolynomial.weightedTotalDegree id p + MvPolynomial.weightedTotalDegree id q := by
  unfold MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [map_add]
  exact add_le_add (Finset.le_sup ha) (Finset.le_sup hb)

private theorem weightedDegree_prod_le {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial ℕ R) (d : ι → ℕ)
    (h : ∀ i ∈ s, MvPolynomial.weightedTotalDegree id (f i) ≤ d i) :
    MvPolynomial.weightedTotalDegree id (∏ i ∈ s, f i) ≤ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (weightedDegree_C_le (1 : R))
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (weightedDegree_mul_le _ _).trans
        (add_le_add (h i (Finset.mem_insert_self _ _))
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

theorem factorialMomentPolynomial_weightedDegree_le (j : ℕ) :
    MvPolynomial.weightedTotalDegree id (factorialMomentPolynomial R j) ≤ j := by
  by_cases hj : j = 0
  · subst j
    simpa using (weightedDegree_C_le (1 : R))
  · rw [factorialMomentPolynomial, ite_eq_right hj]
    apply weightedDegree_sum_le
    intro k hk
    exact (weightedDegree_mul_le _ _).trans
      (by simpa using (add_le_add (weightedDegree_C_le (Nat.stirlingSecond j k : R))
        ((weightedDegree_X_le (R := R) k).trans (Finset.mem_Icc.mp hk).2)))

/-- Each independent variable u_k has weight k. Every monomial in H_n has
weighted degree at most n, including the internal zero-order extension. -/
theorem factorialCumulantPolynomial_weightedDegree_le (n : ℕ) :
    MvPolynomial.weightedTotalDegree id (factorialCumulantPolynomial R n) ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp [MvPolynomial.weightedTotalDegree_zero]
  · rw [factorialCumulantPolynomial, ite_eq_right hn]
    apply weightedDegree_sum_le
    intro P _
    apply (weightedDegree_mul_le _ _).trans
    have hprod := weightedDegree_prod_le P.parts
      (fun B => factorialMomentPolynomial R B.card) Finset.card
      (fun B _ => factorialMomentPolynomial_weightedDegree_le B.card)
    have hsum : ∑ B ∈ P.parts, B.card = n := by simpa using P.sum_card_parts
    rw [hsum] at hprod
    simpa using add_le_add
      (weightedDegree_C_le ((-1 : R) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial)) hprod

end Paper.Cumulants
