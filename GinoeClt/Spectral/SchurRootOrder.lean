/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.PrescribedSchurBlock
public import GinoeClt.Spectral.SchurWordCoverage
public import Mathlib.Order.Prod.Lex.Basic

/-! Ordering the actual scalar/upper root representatives by (imaginary, real) part. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate

namespace Paper.Spectral

/-- A standard lexicographic key, putting real representatives before upper ones. -/
def schurRootKey (z : ℂ) : Lex (ℝ × ℝ) := toLex (z.im, z.re)

theorem schurRootKey_injective : Function.Injective schurRootKey := by
  intro z w h
  have h' : (z.im, z.re) = (w.im, w.re) := h
  exact Complex.ext (congrArg Prod.snd h') (congrArg Prod.fst h')

theorem schurRootKey_le_iff (z w : ℂ) :
    schurRootKey z ≤ schurRootKey w ↔ z.im < w.im ∨ z.im = w.im ∧ z.re ≤ w.re :=
  Prod.Lex.toLex_le_toLex

/-- One actual representative per block: the real root or the upper pair root. -/
def schurWordHeadRoots : (w : List Bool) → SchurWordCells w → List ℂ
  | [], _ => []
  | false :: w, p =>
      let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      ((schurHeadInput x (0,0) : ℝ) : ℂ) :: schurWordHeadRoots w (schurTailInput x)
  | true :: w, p =>
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      schurRoot (h (0,0)) (h (0,1)) (h (1,0)) :: schurWordHeadRoots w (schurTailInput x)

theorem length_schurWordHeadRoots (w : List Bool) :
    ∀ p : SchurWordCells w, (schurWordHeadRoots w p).length = w.length := by
  induction w with
  | nil => intro p; rfl
  | cons b w ih => cases b <;> intro p <;> simp [schurWordHeadRoots, ih]

/-- Representatives are exactly the actual nonnegative-imaginary roots,
with multiplicity, not a chosen set of distinct eigenvalues. -/
theorem schurWordHeadRoots_eq_filter (w : List Bool) :
    ∀ p : SchurWordCells w, SchurWordPositive w p →
      (schurWordHeadRoots w p : Multiset ℂ) =
        (schurWordRoots w p).filter (fun z : ℂ => 0 ≤ z.im) := by
  classical
  induction w with
  | nil => intro p _; rfl
  | cons b w ih =>
    cases b <;> intro p hp
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      have ht := ih (schurTailInput x) hp
      simpa [schurWordHeadRoots, schurWordRoots, x] using
        congrArg (Multiset.cons ((schurHeadInput x (0,0) : ℝ) : ℂ)) ht
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let z := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧
        SchurWordPositive w (schurTailInput x) at hp
      obtain ⟨hc, hcb, ht⟩ := hp
      have hz : 0 < z.im := Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hc hcb) hc)
      have hcz : ¬ 0 ≤ (conj z).im := by rw [Complex.conj_im]; linarith
      change z ::ₘ (schurWordHeadRoots w (schurTailInput x) : Multiset ℂ) =
        (z ::ₘ conj z ::ₘ schurWordRoots w (schurTailInput x)).filter (fun u : ℂ => 0 ≤ u.im)
      rw [Multiset.filter_cons_of_pos (p := fun u : ℂ => 0 ≤ u.im) _ hz.le,
        Multiset.filter_cons_of_neg (p := fun u : ℂ => 0 ≤ u.im) _ hcz, ih _ ht]

/-- Every representative is an actual root, in the closed upper half-plane. -/
theorem mem_schurWordHeadRoots (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p) (z : ℂ) :
    z ∈ schurWordHeadRoots w p ↔
      z ∈ ((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots ∧ 0 ≤ z.im := by
  have h := schurWordHeadRoots_eq_filter w p hp
  rw [← schurWordParameter_roots w p hp] at h
  simpa only [Multiset.mem_coe, Multiset.mem_filter] using
    (show z ∈ (schurWordHeadRoots w p : Multiset ℂ) ↔ _ from by rw [h]; simp only [Multiset.mem_filter])

/-- Orthogonal word coverage transfers its literal multiplicity roots to the input matrix. -/
theorem roots_eq_schurWordRoots_of_conjugation (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p)
    (A : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hQ : (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ * A *
      (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordParameter w p) :
    (A.charpoly.map Complex.ofRealHom).roots = schurWordRoots w p := by
  have h := congrArg (fun M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ =>
    (M.charpoly.map Complex.ofRealHom).roots) hQ
  rw [charpoly_orthogonal_similarity] at h
  exact h.trans (schurWordParameter_roots w p hp)

/-- A positive-size real matrix has a real or upper characteristic root. -/
theorem exists_nonneg_root (N : ℕ) (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ z : ℂ, z ∈ (A.charpoly.map Complex.ofRealHom).roots ∧ 0 ≤ z.im := by
  classical
  obtain ⟨w, hsize, p, hp, hΩ, Q, hQ⟩ := exists_normalized_schur_word N A
  subst N
  have hQ' : (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ * A *
      (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordParameter w p := by
    simpa [Matrix.reindex_apply] using hQ
  have hr := roots_eq_schurWordRoots_of_conjugation w p hp A Q hQ'
  have hl : schurWordHeadRoots w p ≠ [] := by
    intro hempty
    have hlen := length_schurWordHeadRoots w p
    rw [hempty] at hlen
    have hw : w = [] := List.length_eq_zero_iff.mp hlen.symm
    simp [hw, schurWordSize] at hN
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hl
  have hm : z ∈ (schurWordHeadRoots w p : Multiset ℂ) := hz
  rw [schurWordHeadRoots_eq_filter w p hp, ← hr] at hm
  exact ⟨z, Multiset.mem_filter.mp hm⟩

/-- A least actual representative exists; finiteness is used only to choose the next block. -/
theorem exists_least_nonneg_root (N : ℕ) (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ μ : ℂ, μ ∈ (A.charpoly.map Complex.ofRealHom).roots ∧ 0 ≤ μ.im ∧
      ∀ z : ℂ, z ∈ (A.charpoly.map Complex.ofRealHom).roots → 0 ≤ z.im →
        schurRootKey μ ≤ schurRootKey z := by
  classical
  let s := (((A.charpoly.map Complex.ofRealHom).roots).filter
    (fun z : ℂ => 0 ≤ z.im)).toFinset.image schurRootKey
  have hs : s.Nonempty := by
    obtain ⟨z, hz, him⟩ := exists_nonneg_root N hN A
    exact ⟨schurRootKey z, Finset.mem_image.mpr ⟨z, by simp [hz, him], rfl⟩⟩
  obtain ⟨μ, hμ, heq⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
  have hμ' : μ ∈ (A.charpoly.map Complex.ofRealHom).roots ∧ 0 ≤ μ.im := by
    simpa only [Multiset.mem_toFinset, Multiset.mem_filter] using hμ
  refine ⟨μ, hμ'.1, hμ'.2, ?_⟩
  intro z hz him
  rw [heq]
  exact Finset.min'_le s _ (Finset.mem_image.mpr ⟨z, by simp [hz, him], rfl⟩)

end Paper.Spectral
