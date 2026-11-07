/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurWordRoots
public import Mathlib.Data.List.OfFn
@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Paper.Spectral

/-- FULL block-order family, including BOTH conjugate roots and every multiplicity.
The casts only identify equal natural-number sizes; they do not permute roots. -/
def schurWordFullRootAt : (w : List Bool) → SchurWordCells w → Fin (schurWordSize w) → ℂ
  | [], _ => Fin.elim0
  | false::w, p =>
      let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let v : Fin (schurWordSize w + 1) → ℂ :=
        Fin.cons ((schurHeadInput x (0,0) : ℝ) : ℂ) (schurWordFullRootAt w (schurTailInput x))
      fun i ↦ v (Fin.cast (Nat.one_add _) i)
  | true::w, p =>
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let z : ℂ := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
      let v : Fin (schurWordSize w + 2) → ℂ :=
        Fin.cons z (Fin.cons (conj z) (schurWordFullRootAt w (schurTailInput x)))
      fun i ↦ v (Fin.cast (Nat.add_comm 2 _) i)

theorem list_ofFn_finCast {α : Type*} {m n : ℕ} (h : m = n) (v : Fin n → α) :
    List.ofFn (fun i : Fin m ↦ v (Fin.cast h i)) = List.ofFn v := by
  subst n
  rfl

/-- This is the actual existing full-root MULTISET, not its support or a deduplicated list. -/
theorem schurWordFullRootAt_multiset (w : List Bool) :
    ∀ p : SchurWordCells w,
      (List.ofFn (schurWordFullRootAt w p) : Multiset ℂ) = schurWordRoots w p := by
  induction w with
  | nil => intro p; simp [schurWordRoots, schurWordSize, schurWordFullRootAt]
  | cons tag w ih =>
    cases tag <;> intro p
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let a : ℂ := (schurHeadInput x (0,0) : ℝ)
      let t := schurTailInput x
      have he : List.ofFn (schurWordFullRootAt (false::w) p) =
          a :: List.ofFn (schurWordFullRootAt w t) := by
        exact (list_ofFn_finCast (Nat.one_add (schurWordSize w))
          (Fin.cons a (schurWordFullRootAt w t))).trans (List.ofFn_cons a _)
      rw [he]
      change a ::ₘ (List.ofFn (schurWordFullRootAt w t) : Multiset ℂ) =
        a ::ₘ schurWordRoots w t
      rw [ih]
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let z := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
      let t := schurTailInput x
      have he : List.ofFn (schurWordFullRootAt (true::w) p) =
          z :: conj z :: List.ofFn (schurWordFullRootAt w t) := by
        have h := list_ofFn_finCast (Nat.add_comm 2 (schurWordSize w))
          (Fin.cons z (Fin.cons (conj z) (schurWordFullRootAt w t)))
        simpa only [List.ofFn_cons] using! h
      rw [he]
      change z ::ₘ conj z ::ₘ (List.ofFn (schurWordFullRootAt w t) : Multiset ℂ) =
        z ::ₘ conj z ::ₘ schurWordRoots w t
      rw [ih]

theorem prod_schurWordFullRootAt (w : List Bool) (p : SchurWordCells w) (f : ℂ → ℝ) :
    (∏ i : Fin (schurWordSize w), f (schurWordFullRootAt w p i)) =
      ((schurWordRoots w p).map f).prod := by
  rw [← schurWordFullRootAt_multiset]
  simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn, Function.comp_def]

/-- The exact within-pair correction forced by the physical head Jacobian.
Its denominator is positive under ORIGINAL positivity 0<c≤b. -/
def schurWordPairRatio : (w : List Bool) → SchurWordCells w → ℝ
  | [], _ => 1
  | false::w, p =>
      schurWordPairRatio w (schurTailInput (schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p))
  | true::w, p =>
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      (h (0,1)-h (1,0)) / Real.sqrt (h (0,1)*h (1,0)) *
        schurWordPairRatio w (schurTailInput x)

end Paper.Spectral
