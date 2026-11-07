/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.RealSignPfaffian
@[expose] public section
noncomputable section
open Equiv
open scoped BigOperators Matrix
namespace Paper.Spectral
open Paper.PfaffianBridge

/-- The EVEN full signed numerator, for the actual real sign kernel. -/
theorem sum_finTerm_realSignMatrix (r : ℕ) (x : Fin (2*r) → ℝ)
    (hx : StrictMono x) :
    (∑ σ : Perm (Fin (2*r)), finTerm (realSignMatrix x) σ) =
      (2 : ℂ)^r * (r.factorial : ℂ) := by
  rw [realSignMatrix_eq_upper_of_strictMono x hx,
    sum_finTerm_eq_normalizer_recursivePf r _ (upperSignMatrix_skew _),
    recursivePf_upperSignMatrix,mul_one]

/-- Expanded EVEN pairing signs, in the frozen interlaced pair order. -/
theorem even_real_sign_antisymmetrization (r : ℕ) (x : Fin (2*r) → ℝ)
    (hx : StrictMono x) :
    (∑ σ : Perm (Fin (2*r)), permutationSign σ * ∏ a : Fin r,
      (SignType.sign (x (σ (PfaffianMinor.pairColumnEquiv r (a,1))) -
        x (σ (PfaffianMinor.pairColumnEquiv r (a,0)))) : ℂ)) =
      (2 : ℂ)^r * (r.factorial : ℂ) := by
  exact sum_finTerm_realSignMatrix r x hx

/-- ODD pairing signs leave coordinate ZERO unpaired; all paired coordinates
are the successors of the original even interlaced positions. -/
def oddRealSignTerm {r : ℕ} (x : Fin (2*r+1) → ℝ)
    (σ : Perm (Fin (2*r+1))) : ℂ :=
  permutationSign σ * ∏ a : Fin r,
    (SignType.sign (x (σ ((PfaffianMinor.pairColumnEquiv r (a,1)).succ)) -
      x (σ ((PfaffianMinor.pairColumnEquiv r (a,0)).succ))) : ℂ)

/-- First-image extraction has the exact cofactor sign (-1)^j, including r=0. -/
theorem oddRealSignTerm_firstPerm (r : ℕ) (x : Fin (2*r+1) → ℝ)
    (j : Fin (2*r+1)) (σ : Perm (Fin (2*r))) :
    oddRealSignTerm x ((firstPermEquiv (2*r)).symm (j,σ)) =
      (-1 : ℂ)^j.val * finTerm (realSignMatrix (x ∘ j.succAbove)) σ := by
  simp only [oddRealSignTerm,permutationSign_firstPermEquiv_symm,
    firstPermEquiv_symm_succ,finTerm,realSignMatrix,Function.comp_def,PfaffianMinor.pairCol,
    mul_assoc]

/-- The exact ODD sign antisymmetrization with FIRST coordinate unpaired. -/
theorem odd_real_sign_antisymmetrization (r : ℕ) (x : Fin (2*r+1) → ℝ)
    (hx : StrictMono x) :
    (∑ σ : Perm (Fin (2*r+1)), oddRealSignTerm x σ) =
      (2 : ℂ)^r * (r.factorial : ℂ) := by
  calc
    _ = ∑ d : Fin (2*r+1) × Perm (Fin (2*r)),
        oddRealSignTerm x ((firstPermEquiv (2*r)).symm d) :=
      ((firstPermEquiv (2*r)).symm.sum_comp _).symm
    _ = ∑ j : Fin (2*r+1), (-1 : ℂ)^j.val *
        ∑ σ : Perm (Fin (2*r)), finTerm (realSignMatrix (x ∘ j.succAbove)) σ := by
      rw [Fintype.sum_prod_type]
      simp_rw [oddRealSignTerm_firstPerm,Finset.mul_sum]
    _ = ∑ j : Fin (2*r+1), (-1 : ℂ)^j.val * ((2 : ℂ)^r * (r.factorial : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sum_finTerm_realSignMatrix r (x ∘ j.succAbove) (hx.comp (Fin.strictMono_succAbove j))]
    _ = _ := by
      rw [← Finset.sum_mul,Fin.sum_neg_one_pow]
      have ho : Odd (2*r+1) := ⟨r,by omega⟩
      rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho),one_mul]

/-- Fully expanded ODD sum, recording the unpaired-first convention explicitly. -/
theorem odd_real_sign_antisymmetrization_expanded (r : ℕ) (x : Fin (2*r+1) → ℝ)
    (hx : StrictMono x) :
    (∑ σ : Perm (Fin (2*r+1)), permutationSign σ * ∏ a : Fin r,
      (SignType.sign (x (σ ((PfaffianMinor.pairColumnEquiv r (a,1)).succ)) -
        x (σ ((PfaffianMinor.pairColumnEquiv r (a,0)).succ))) : ℂ)) =
      (2 : ℂ)^r * (r.factorial : ℂ) :=
  odd_real_sign_antisymmetrization r x hx

end Paper.Spectral
