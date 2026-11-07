/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFullRoots
public import GinoeClt.Spectral.SchurWordMeasurability
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.List.FinRange
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate
namespace Paper.Spectral

/-- Reconstruct EVERY full root from one representative per original word block,
in EXACT physical block order, retaining the inserted conjugates and multiplicities. -/
def schurFullRootsFromHeads : (w : List Bool) → (Fin w.length → ℂ) → Fin (schurWordSize w) → ℂ
  | [], _ => Fin.elim0
  | false::w, h =>
      let v : Fin (schurWordSize w + 1) → ℂ :=
        Fin.cons (h 0) (schurFullRootsFromHeads w (Fin.tail h))
      fun i => v (Fin.cast (Nat.one_add _) i)
  | true::w, h =>
      let v : Fin (schurWordSize w + 2) → ℂ :=
        Fin.cons (h 0) (Fin.cons (conj (h 0)) (schurFullRootsFromHeads w (Fin.tail h)))
      fun i => v (Fin.cast (Nat.add_comm 2 _) i)

/-- Agreement with the EXISTING full root family for EVERY actual raw parameter,
without positivity, distinctness, regularity or angle assumptions. -/
theorem schurFullRootsFromHeads_actual (w : List Bool) :
    ∀ p : SchurWordCells w,
      schurFullRootsFromHeads w (schurWordHeadRootAt w p) = schurWordFullRootAt w p := by
  induction w with
  | nil => intro p; rfl
  | cons tag w ih =>
    cases tag <;> intro p <;>
      simp only [schurFullRootsFromHeads,schurWordHeadRootAt,Fin.cons_zero,Fin.tail_cons,
        schurWordFullRootAt,ih]

theorem ofFn_schurFullRootsFromHeads_false (w : List Bool) (h : Fin (false::w).length → ℂ) :
    List.ofFn (schurFullRootsFromHeads (false::w) h) =
      h 0 :: List.ofFn (schurFullRootsFromHeads w (Fin.tail h)) :=
  (list_ofFn_finCast (Nat.one_add (schurWordSize w))
    (Fin.cons (h 0) (schurFullRootsFromHeads w (Fin.tail h)))).trans (List.ofFn_cons _ _)

theorem ofFn_schurFullRootsFromHeads_true (w : List Bool) (h : Fin (true::w).length → ℂ) :
    List.ofFn (schurFullRootsFromHeads (true::w) h) =
      h 0 :: conj (h 0) :: List.ofFn (schurFullRootsFromHeads w (Fin.tail h)) := by
  have he := list_ofFn_finCast (Nat.add_comm 2 (schurWordSize w))
    (Fin.cons (h 0) (Fin.cons (conj (h 0)) (schurFullRootsFromHeads w (Fin.tail h))))
  simpa only [List.ofFn_cons] using! he

/-- The representative LIST is a sublist of the full LIST, with exact multiplicities.
This supplies a shorter genuine duplicate witness than a new index-embedding registry. -/
theorem heads_sublist_schurFullRootsFromHeads (w : List Bool) :
    ∀ h : Fin w.length → ℂ, (List.ofFn h).Sublist (List.ofFn (schurFullRootsFromHeads w h)) := by
  induction w with
  | nil => intro h; simp [schurFullRootsFromHeads]
  | cons tag w ih =>
    cases tag <;> intro h
    · rw [ofFn_schurFullRootsFromHeads_false,List.ofFn_succ]
      exact List.Sublist.cons_cons _ (ih (Fin.tail h))
    · rw [ofFn_schurFullRootsFromHeads_true,List.ofFn_succ]
      exact List.Sublist.cons_cons _ (List.Sublist.cons _ (ih (Fin.tail h)))

theorem injective_heads_of_schurFullRootsFromHeads (w : List Bool) (h : Fin w.length → ℂ)
    (hf : Function.Injective (schurFullRootsFromHeads w h)) : Function.Injective h :=
  List.nodup_ofFn.mp (List.Nodup.sublist (heads_sublist_schurFullRootsFromHeads w h)
    (List.nodup_ofFn_ofInjective hf))

theorem continuous_schurFullRootsFromHeads (w : List Bool) :
    Continuous (schurFullRootsFromHeads w) := by
  induction w with
  | nil => exact continuous_pi fun i => Fin.elim0 i
  | cons tag w ih =>
    cases tag
    · have ht : Continuous (fun h : Fin (false::w).length → ℂ =>
          schurFullRootsFromHeads w (Fin.tail h)) :=
        ih.comp (continuous_pi fun j => continuous_apply j.succ)
      have h0 : Continuous (fun h : Fin (false::w).length → ℂ => h 0) := continuous_apply 0
      have hv : Continuous (fun h : Fin (false::w).length → ℂ =>
          (Fin.cons (h 0) (schurFullRootsFromHeads w (Fin.tail h)) :
            Fin (schurWordSize w + 1) → ℂ)) :=
        h0.finCons ht
      apply continuous_pi
      intro i
      exact (continuous_apply (Fin.cast (Nat.one_add _) i)).comp hv
    · have ht : Continuous (fun h : Fin (true::w).length → ℂ =>
          schurFullRootsFromHeads w (Fin.tail h)) :=
        ih.comp (continuous_pi fun j => continuous_apply j.succ)
      have hc : Continuous (fun h : Fin (true::w).length → ℂ => conj (h 0)) := by fun_prop
      have hv' : Continuous (fun h : Fin (true::w).length → ℂ =>
          (Fin.cons (conj (h 0)) (schurFullRootsFromHeads w (Fin.tail h)) :
            Fin (schurWordSize w + 1) → ℂ)) := hc.finCons ht
      have h0 : Continuous (fun h : Fin (true::w).length → ℂ => h 0) := continuous_apply 0
      have hv : Continuous (fun h : Fin (true::w).length → ℂ =>
          (Fin.cons (h 0) (Fin.cons (conj (h 0)) (schurFullRootsFromHeads w (Fin.tail h))) :
            Fin (schurWordSize w + 2) → ℂ)) :=
        h0.finCons hv'
      apply continuous_pi
      intro i
      exact (continuous_apply (Fin.cast (Nat.add_comm 2 _) i)).comp hv

theorem measurable_schurFullRootsFromHeads (w : List Bool) :
    Measurable (schurFullRootsFromHeads w) :=
  (continuous_schurFullRootsFromHeads w).measurable

/-- Literal magnitude of the FULL Vandermonde, built from representatives. -/
def schurHeadVandermondeNorm (w : List Bool) (h : Fin w.length → ℂ) : ℝ :=
  ‖(Matrix.vandermonde (schurFullRootsFromHeads w h)).det‖

theorem schurHeadVandermondeNorm_actual (w : List Bool) (p : SchurWordCells w) :
    schurHeadVandermondeNorm w (schurWordHeadRootAt w p) =
      ‖(Matrix.vandermonde (schurWordFullRootAt w p)).det‖ := by
  rw [schurHeadVandermondeNorm,schurFullRootsFromHeads_actual]

theorem continuous_schurHeadVandermondeNorm (w : List Bool) :
    Continuous (schurHeadVandermondeNorm w) := by
  have hM : Continuous (fun h : Fin w.length → ℂ =>
      Matrix.vandermonde (schurFullRootsFromHeads w h)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun h : Fin w.length → ℂ => (schurFullRootsFromHeads w h i) ^ j.val)
    exact ((continuous_apply i).comp (continuous_schurFullRootsFromHeads w)).pow _
  exact hM.matrix_det.norm

theorem measurable_schurHeadVandermondeNorm (w : List Bool) :
    Measurable (schurHeadVandermondeNorm w) :=
  (continuous_schurHeadVandermondeNorm w).measurable

/-- Duplicate REPRESENTATIVES force duplicate FULL roots, hence the actual
Vandermonde vanishes. No positivity/half-plane condition or support-set shortcut. -/
theorem schurHeadVandermondeNorm_eq_zero_of_not_injective (w : List Bool)
    (h : Fin w.length → ℂ) (hh : ¬ Function.Injective h) : schurHeadVandermondeNorm w h = 0 := by
  have hz : (Matrix.vandermonde (schurFullRootsFromHeads w h)).det = 0 := by
    by_contra hn
    exact hh (injective_heads_of_schurFullRootsFromHeads w h
      (Matrix.det_vandermonde_ne_zero_iff.mp hn))
  rw [schurHeadVandermondeNorm,hz,norm_zero]

/-- Generic FULL-root permutation invariance. This does not silently assert
invariance under head permutations that exchange scalar and pair tags. -/
theorem norm_det_vandermonde_comp_perm {n : ℕ} (v : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    ‖(Matrix.vandermonde (v ∘ σ)).det‖ = ‖(Matrix.vandermonde v).det‖ := by
  have he : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := rfl
  rw [he,Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end Paper.Spectral
