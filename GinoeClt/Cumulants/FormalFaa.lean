/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Combinatorics.PartitionBridge
public import Mathlib.RingTheory.PowerSeries.Log

/-!
# A finite chain rule for formal power series

This is the purely formal counterpart of Mathlib's ordered-partition chain
rule. The proof uses the same canonical extension equivalence, with the formal
derivative and formal substitution in place of analytic differentiation.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries
namespace Paper.Cumulants

variable {R : Type*} [CommRing R]

theorem formalDerivative_mul (F G : PowerSeries R) :
    d⁄dX (F * G) = d⁄dX F * G + F * d⁄dX G := by
  rw [Derivation.leibniz]
  change F * d⁄dX G + G * d⁄dX F = _
  ring

/-- The finite product rule; proof follows the elementary multiset induction
used by Mathlib's Polynomial.derivative_prod. -/
theorem formalDerivative_multisetProd {ι : Type*} [DecidableEq ι]
    (s : Multiset ι) (f : ι → PowerSeries R) :
    d⁄dX (Multiset.map f s).prod =
      (Multiset.map (fun i => (Multiset.map f (s.erase i)).prod * d⁄dX (f i)) s).sum := by
  refine Multiset.induction_on s (by simp) fun i s h => ?_
  rw [Multiset.map_cons, Multiset.prod_cons, formalDerivative_mul, Multiset.map_cons _ i s,
    Multiset.sum_cons, Multiset.erase_cons_head, mul_comm (d⁄dX (f i))]
  congr 1
  rw [h, ← AddMonoidHom.coe_mulLeft, (AddMonoidHom.mulLeft (f i)).map_multiset_sum _,
    AddMonoidHom.coe_mulLeft]
  simp only [Function.comp_apply, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun j hj => ?_)
  rw [← mul_assoc, ← Multiset.prod_cons, ← Multiset.map_cons]
  by_cases hij : i = j
  · simp [hij, Multiset.cons_erase hj]
  · simp [hij]

theorem formalDerivative_finsetProd {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → PowerSeries R) :
    d⁄dX (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d⁄dX (f i) := by
  simpa only [← Finset.erase_val] using! formalDerivative_multisetProd s.val f

def formalFaaTerm (F G : PowerSeries R) {n : ℕ} (c : OrderedFinpartition n) : PowerSeries R :=
  ((d⁄dX^[c.length] F).subst G) * ∏ i : Fin c.length, d⁄dX^[c.partSize i] G

theorem formalFaaTerm_extend_none (F G : PowerSeries R) {n : ℕ} (c : OrderedFinpartition n) :
    formalFaaTerm F G (c.extend none) =
      ((d⁄dX^[c.length + 1] F).subst G) * d⁄dX G *
        ∏ i : Fin c.length, d⁄dX^[c.partSize i] G := by
  dsimp only [formalFaaTerm, OrderedFinpartition.extend, OrderedFinpartition.extendLeft]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Function.iterate_one]
  exact (mul_assoc _ _ _).symm

theorem formalFaaTerm_extend_some (F G : PowerSeries R) {n : ℕ}
    (c : OrderedFinpartition n) (i : Fin c.length) :
    formalFaaTerm F G (c.extend (some i)) =
      ((d⁄dX^[c.length] F).subst G) * (d⁄dX^[c.partSize i + 1] G) *
        ∏ j ∈ (Finset.univ : Finset (Fin c.length)).erase i, d⁄dX^[c.partSize j] G := by
  change ((d⁄dX^[c.length] F).subst G) *
    (∏ j : Fin c.length, d⁄dX^[Function.update c.partSize i (c.partSize i + 1) j] G) = _
  have hf :
      (fun j => d⁄dX^[Function.update c.partSize i (c.partSize i + 1) j] G) =
        Function.update (fun j => d⁄dX^[c.partSize j] G) i (d⁄dX^[c.partSize i + 1] G) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  exact (mul_assoc _ _ _).symm

theorem formalFaaTerm_derivative (F G : PowerSeries R) (hg : PowerSeries.HasSubst G)
    {n : ℕ} (c : OrderedFinpartition n) :
    d⁄dX (formalFaaTerm F G c) =
      ∑ o : Option (Fin c.length), formalFaaTerm F G (c.extend o) := by
  change d⁄dX (((d⁄dX^[c.length] F).subst G) *
    ∏ i : Fin c.length, d⁄dX^[c.partSize i] G) = _
  rw [formalDerivative_mul, PowerSeries.derivative_subst hg, formalDerivative_finsetProd,
    Fintype.sum_option]
  simp_rw [formalFaaTerm_extend_none, formalFaaTerm_extend_some]
  simp only [Function.iterate_succ_apply']
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Formal Faà di Bruno, valid over every commutative ring. Substitution is
genuine formal substitution with its explicit well-definedness hypothesis. -/
theorem formalFaa (F G : PowerSeries R) (hg : PowerSeries.HasSubst G) (n : ℕ) :
    d⁄dX^[n] (F.subst G) = ∑ c : OrderedFinpartition n, formalFaaTerm F G c := by
  induction n with
  | zero =>
      rw [Fintype.sum_unique]
      simp [formalFaaTerm, OrderedFinpartition.default_eq]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_sum]
      simp_rw [formalFaaTerm_derivative F G hg]
      rw [Finset.sum_sigma']
      exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv n) _ _ (fun p => rfl)

end Paper.Cumulants
