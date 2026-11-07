/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Algebra.PfaffianAgreement

/-! # The checked finite minor-summation theorem at the frozen paired Pfaffian

No new minor-summation theorem is assumed. This is the explicit coordinate
bridge required twice in the finite atomic generating-Pfaffian expansion.
-/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace Paper.SkewOrthogonal

/-- Literal finite sums of pair wedges, at the frozen full-permutation Pfaffian. -/
theorem pfaffian_finite_wedges {ι : Type*} [LinearOrder ι] (m : ℕ)
    (Z : ι → PairedIndex m → Fin 2 → ℂ) (c : ι → ℂ) (s : Finset ι) :
    pfaffian (fun p q ↦ ∑ x ∈ s,
      c x * (Z x p 0 * Z x q 1 - Z x p 1 * Z x q 0)) =
      PfaffianMinor.finsetADMSRhs m
        (fun x i a ↦ Z x ((PfaffianMinor.pairColumnEquiv m).symm i) a) c s := by
  let M : Matrix (PairedIndex m) (PairedIndex m) ℂ := fun p q ↦ ∑ x ∈ s,
    c x * (Z x p 0 * Z x q 1 - Z x p 1 * Z x q 0)
  have hM : ∀ p q, M q p = -M p q := by
    intro p q
    simp only [M, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  change pfaffian M = _
  rw [pfaffian_eq_recursivePf M hM]
  change PfaffianMinor.recursivePf m
    (PfaffianMinor.pullbackFinset
      (fun x i a ↦ Z x ((PfaffianMinor.pairColumnEquiv m).symm i) a) c s) = _
  exact PfaffianMinor.recursivePf_pullbackFinset m _ c s

end Paper.SkewOrthogonal
