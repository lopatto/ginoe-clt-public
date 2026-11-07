/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurCanonicalProductIntegral
public import GinoeClt.Spectral.SchurHeadCountTest
public import GinoeClt.Spectral.SchurVandermonde
public import Mathlib.Data.List.Perm.Basic
@[expose] public section
noncomputable section
open Set
open scoped Matrix ComplexConjugate ENNReal NNReal BigOperators Classical
namespace Paper.Spectral

/-- List form used only for a multiplicity-preserving permutation proof. -/
def listVandermondeNorm (s : List ℂ) : ℝ := ‖(Matrix.vandermonde s.get).det‖

theorem listVandermondeNorm_cons (a : ℂ) (s : List ℂ) :
    listVandermondeNorm (a::s) =
      (s.map (fun z => ‖z-a‖)).prod * listVandermondeNorm s := by
  have hg : (a::s).get = Fin.cons a s.get := by
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  have hp : (∏ i : Fin s.length, ‖s.get i-a‖) = (s.map (fun z => ‖z-a‖)).prod := by
    have he : List.ofFn (fun i : Fin s.length => ‖s.get i-a‖) = s.map (fun z => ‖z-a‖) := by
      rw [List.ofFn_comp' s.get (fun z => ‖z-a‖),List.ofFn_get]
    simpa only [List.prod_ofFn] using congrArg List.prod he
  rw [listVandermondeNorm,hg,norm_det_vandermonde_cons,hp]
  rfl

/-- FULL Vandermonde magnitude is symmetric as a LIST function, including repeated
roots. Adjacent swap uses norm_sub_rev; no distinct-root cancellation is used. -/
theorem listVandermondeNorm_perm {s t : List ℂ} (hp : s.Perm t) :
    listVandermondeNorm s = listVandermondeNorm t := by
  induction hp with
  | nil => rfl
  | cons a hp ih =>
    rw [listVandermondeNorm_cons,listVandermondeNorm_cons,ih,
      (hp.map (fun z => ‖z-a‖)).prod_eq]
  | swap a b s =>
    rw [listVandermondeNorm_cons,listVandermondeNorm_cons,
      listVandermondeNorm_cons,listVandermondeNorm_cons]
    simp only [List.map_cons,List.prod_cons]
    rw [norm_sub_rev a b]
    ring
  | trans hp hq ihp ihq => exact ihp.trans ihq

theorem listVandermondeNorm_ofFn {n : ℕ} (v : Fin n → ℂ) :
    listVandermondeNorm (List.ofFn v) = ‖(Matrix.vandermonde v).det‖ := by
  have he : (List.ofFn v).get = fun i => v (Fin.cast (by simp) i) := by
    funext i
    exact List.get_ofFn v i
  rw [listVandermondeNorm,he,det_vandermonde_finCast]

theorem fullRoots_replicate_true_list (l : ℕ) (z : Fin l → ℂ) :
    List.ofFn (schurFullRootsFromHeads (List.replicate l true) (schurComplexHeads l z)) =
      (List.ofFn z).flatMap (fun a => [a,conj a]) := by
  induction l with
  | zero => simp [schurWordSize]
  | succ l ih =>
    obtain ⟨a,v,rfl⟩ : ∃ a : ℂ, ∃ v : Fin l → ℂ, Fin.cons a v = z :=
      ⟨z 0,Fin.tail z,Fin.cons_self_tail z⟩
    rw [schurComplexHeads_cons]
    have he := ofFn_schurFullRootsFromHeads_true (List.replicate l true)
      (Fin.cons a (schurComplexHeads l v))
    simpa only [List.replicate_succ,Fin.cons_zero,Fin.tail_cons,ih,List.ofFn_cons,List.flatMap_cons,
      List.cons_append,List.nil_append] using! he

theorem fullRoots_canonical_list (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    List.ofFn (schurFullRootsFromHeads (schurCanonicalWord k l) (schurCanonicalHeads k l x z)) =
      (List.ofFn x).map Complex.ofReal ++ (List.ofFn z).flatMap (fun a => [a,conj a]) := by
  induction k with
  | zero => simpa only [schurCanonicalHeads_zero,schurCanonicalWord,List.replicate_zero,
      List.nil_append,List.ofFn_zero,List.map_nil] using! fullRoots_replicate_true_list l z
  | succ k ih =>
    obtain ⟨a,v,rfl⟩ : ∃ a : ℝ, ∃ v : Fin k → ℝ, Fin.cons a v = x :=
      ⟨x 0,Fin.tail x,Fin.cons_self_tail x⟩
    rw [schurCanonicalHeads_cons]
    have he := ofFn_schurFullRootsFromHeads_false (schurCanonicalWord k l)
      (Fin.cons (a : ℂ) (schurCanonicalHeads k l v z))
    simpa only [schurCanonicalWord,List.replicate_succ,List.cons_append,Fin.cons_zero,Fin.tail_cons,
      ih,List.ofFn_cons,List.map_cons] using! he

theorem canonical_fullRoots_perm (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ)
    (σ : Equiv.Perm (Fin l)) :
    (List.ofFn (schurFullRootsFromHeads (schurCanonicalWord k l)
      (schurCanonicalHeads k l x (z ∘ σ)))).Perm
    (List.ofFn (schurFullRootsFromHeads (schurCanonicalWord k l)
      (schurCanonicalHeads k l x z))) := by
  rw [fullRoots_canonical_list,fullRoots_canonical_list]
  exact List.Perm.append_left _ ((σ.ofFn_comp_perm z).flatMap_right (fun a => [a,conj a]))

/-- Actual FULL norm, invariant only under COMPLEX coordinates with real x fixed. -/
theorem canonical_headVandermondeNorm_perm (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ)
    (σ : Equiv.Perm (Fin l)) :
    schurHeadVandermondeNorm (schurCanonicalWord k l) (schurCanonicalHeads k l x (z ∘ σ)) =
      schurHeadVandermondeNorm (schurCanonicalWord k l) (schurCanonicalHeads k l x z) := by
  exact (listVandermondeNorm_ofFn _).symm.trans
    ((listVandermondeNorm_perm (canonical_fullRoots_perm k l x z σ)).trans (listVandermondeNorm_ofFn _))

/-- Weak monotonicity is the exact existing Pairwise order on the finite list. -/
theorem monotone_key_iff_pairwise_ofFn {α β : Type*} [Preorder β] {n : ℕ}
    (key : α → β) (h : Fin n → α) :
    Monotone (key ∘ h) ↔ (List.ofFn h).Pairwise (fun a b => key a ≤ key b) := by
  rw [List.pairwise_ofFn]
  constructor
  · intro hm i j hij
    exact hm hij.le
  · intro hm i j hij
    rcases lt_or_eq_of_le hij with hlt | he
    · exact hm hlt
    · subst j
      exact le_rfl

/-- The ORIGINAL whole chamber decomposes into real and complex chambers because
real representatives precede all genuinely upper representatives in the key. -/
theorem canonical_heads_ordering_iff (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    Monotone (schurRootKey ∘ schurCanonicalHeads k l x z) ↔
      Monotone x ∧ Monotone (schurRootKey ∘ z) := by
  rw [monotone_key_iff_pairwise_ofFn,ofFn_schurCanonicalHeads,List.pairwise_append]
  have hr : ((List.ofFn x).map Complex.ofReal).Pairwise
      (fun a b => schurRootKey a ≤ schurRootKey b) ↔ Monotone x := by
    simpa [List.pairwise_map,schurRootKey_le_iff] using!
      (monotone_key_iff_pairwise_ofFn id x).symm
  have hc : ∀ a ∈ (List.ofFn x).map Complex.ofReal, ∀ b ∈ List.ofFn z,
      schurRootKey a ≤ schurRootKey b := by
    intro a ha b hb
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    exact (schurRootKey_le_iff _ _).mpr (Or.inl (by simpa using hz i))
  rw [hr,← monotone_key_iff_pairwise_ofFn]
  exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hc⟩⟩

theorem schurHeadCountProduct_eq_list (B : Set ℂ) (t : ℝ≥0) {n : ℕ} (h : Fin n → ℂ) :
    schurHeadCountProduct B t h =
      ((List.ofFn h).map (fun a => if a ∈ B then 1+(t : ℝ≥0∞) else 1)).prod := by
  rw [List.map_ofFn,List.prod_ofFn]
  rfl

theorem canonical_headCountProduct_perm (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) (σ : Equiv.Perm (Fin l)) :
    schurHeadCountProduct B t (schurCanonicalHeads k l x (z ∘ σ)) =
      schurHeadCountProduct B t (schurCanonicalHeads k l x z) := by
  rw [schurHeadCountProduct_eq_list,schurHeadCountProduct_eq_list]
  have hp : (List.ofFn (schurCanonicalHeads k l x (z ∘ σ))).Perm
      (List.ofFn (schurCanonicalHeads k l x z)) := by
    rw [ofFn_schurCanonicalHeads,ofFn_schurCanonicalHeads]
    exact List.Perm.append_left _ (σ.ofFn_comp_perm z)
  exact (hp.map (fun a => if a ∈ B then 1+(t : ℝ≥0∞) else 1)).prod_eq

theorem complexWeight_product_perm {l : ℕ} (z : Fin l → ℂ) (σ : Equiv.Perm (Fin l)) :
    (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight ((z ∘ σ) i))) =
      ∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i)) :=
  Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem injective_complex_of_canonicalHeads {k l : ℕ} (x : Fin k → ℝ) (z : Fin l → ℂ)
    (hh : Function.Injective (schurCanonicalHeads k l x z)) : Function.Injective z := by
  have hl := List.nodup_ofFn_ofInjective hh
  rw [ofFn_schurCanonicalHeads] at hl
  exact List.nodup_ofFn.mp hl.of_append_right

theorem canonical_headVandermondeNorm_eq_zero {k l : ℕ} (x : Fin k → ℝ) (z : Fin l → ℂ)
    (hz : ¬ Function.Injective z) :
    schurHeadVandermondeNorm (schurCanonicalWord k l) (schurCanonicalHeads k l x z) = 0 :=
  schurHeadVandermondeNorm_eq_zero_of_not_injective _ _
    (fun hh => hz (injective_complex_of_canonicalHeads x z hh))

theorem canonical_headCountTest_eq_zero (B : Set ℂ) (t : ℝ≥0) {k l : ℕ}
    (x : Fin k → ℝ) (z : Fin l → ℂ) (hz : ¬ Function.Injective z) :
    schurHeadCountTest B t (schurCanonicalWord k l) (schurCanonicalHeads k l x z) = 0 :=
  schurHeadCountTest_eq_zero_of_not_injective B t _ _
    (fun hh => hz (injective_complex_of_canonicalHeads x z hh))

/-- Keep the REAL order inside the actual test and expose only the complex
chamber. No symmetry is asserted for the ordered test itself. -/
theorem canonical_headCountTest_ordering (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) (hz : ∀ i, 0 < (z i).im) :
    schurHeadCountTest B t (schurCanonicalWord k l) (schurCanonicalHeads k l x z) =
      if Monotone x then
        (orderingChamber l schurRootKey).indicator
          (fun v => ENNReal.ofReal (schurHeadVandermondeNorm (schurCanonicalWord k l)
            (schurCanonicalHeads k l x v)) * schurHeadCountProduct B t (schurCanonicalHeads k l x v)) z
      else 0 := by
  unfold schurHeadCountTest
  rw [Set.indicator_apply]
  have ho : schurCanonicalHeads k l x z ∈ orderingChamber (schurCanonicalWord k l).length schurRootKey ↔
      Monotone x ∧ Monotone (schurRootKey ∘ z) := canonical_heads_ordering_iff k l x z hz
  rw [ho]
  by_cases hx : Monotone x <;> by_cases hzo : Monotone (schurRootKey ∘ z) <;>
    simp [orderingChamber,hx,hzo]

end Paper.Spectral
