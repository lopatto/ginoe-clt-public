/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.OrderedSchurCoverage
public import GinoeClt.Spectral.SchurSylvesterRecursion

/-! Literal Sylvester separation from the actual normalized word roots. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate

namespace Paper.Spectral

/-- Actual physical scalar-word Sylvester recursion, with an arbitrary comparison block. -/
theorem det_sylvester_word_scalar {d : ℕ} (w : List Bool)
    (p : SchurWordCells (false::w)) (B : Matrix (Fin d) (Fin d) ℝ) :
    let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
    (sylvesterMatrix (schurWordParameter (false::w) p) B).det =
      (sylvesterMatrix (scalarBlock (schurHeadInput x (0,0))) B).det *
        (sylvesterMatrix (schurWordParameter w (schurTailInput x)) B).det := by
  let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
  have hK := schurParameterPhysical_eq scalarHeadParameter (schurWordParameter w) p
  have h := congrArg (fun M : Matrix (Fin (1+schurWordSize w))
    (Fin (1+schurWordSize w)) ℝ => (sylvesterMatrix M B).det) hK
  refine h.trans ?_
  exact det_sylvester_reindexed_fromBlocks B _ _ _

theorem det_sylvester_word_pair {d : ℕ} (w : List Bool)
    (p : SchurWordCells (true::w)) (B : Matrix (Fin d) (Fin d) ℝ) :
    let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
    let h := schurHeadInput x
    (sylvesterMatrix (schurWordParameter (true::w) p) B).det =
      (sylvesterMatrix (schurBlock (h (0,0)) (h (0,1)) (h (1,0))) B).det *
        (sylvesterMatrix (schurWordParameter w (schurTailInput x)) B).det := by
  let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
  have hK := schurParameterPhysical_eq pairHeadParameter (schurWordParameter w) p
  have h := congrArg (fun M : Matrix (Fin (2+schurWordSize w))
    (Fin (2+schurWordSize w)) ℝ => (sylvesterMatrix M B).det) hK
  refine h.trans ?_
  exact det_sylvester_reindexed_fromBlocks B _ _ _

/-- A scalar not among the actual word roots is genuinely Sylvester-separated. -/
theorem det_sylvester_word_scalar_ne_zero (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p → ∀ a : ℝ,
      (a : ℂ) ∉ schurWordRoots w p →
        (sylvesterMatrix (schurWordParameter w p) (scalarBlock a)).det ≠ 0 := by
  classical
  induction w with
  | nil =>
    intro p hp a ha
    change (sylvesterMatrix (0 : Matrix (Fin 0) (Fin 0) ℝ) (scalarBlock a)).det ≠ 0
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  | cons b w ih =>
    cases b <;> intro p hp a ha
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      have htail : (a : ℂ) ∉ schurWordRoots w t := by
        intro hm
        exact ha (Multiset.mem_cons_of_mem hm)
      have hneq : a ≠ h (0,0) := by
        intro heq
        apply ha
        change (a : ℂ) ∈ ((h (0,0) : ℝ) : ℂ) ::ₘ schurWordRoots w t
        rw [heq]
        exact Multiset.mem_cons_self _ _
      rw [det_sylvester_word_scalar]
      apply mul_ne_zero _ (ih t hp a htail)
      rw [det_sylvester_scalar_scalar]
      exact sub_ne_zero.mpr hneq
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      obtain ⟨hc, hcb, ht⟩ := hp
      have htail : (a : ℂ) ∉ schurWordRoots w t := by
        intro hm
        exact ha (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hm))
      rw [det_sylvester_word_pair]
      apply mul_ne_zero _ (ih t ht a htail)
      rw [det_sylvester_block_scalar]
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (lt_of_lt_of_le hc hcb) hc))

/-- An upper pair root not among the word roots gives the literal pair Sylvester separation. -/
theorem det_sylvester_word_pair_ne_zero (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p → ∀ a b c : ℝ,
      0 < c → c ≤ b → schurRoot a b c ∉ schurWordRoots w p →
        (sylvesterMatrix (schurWordParameter w p) (schurBlock a b c)).det ≠ 0 := by
  classical
  induction w with
  | nil =>
    intro p hp a b c hc hcb ha
    change (sylvesterMatrix (0 : Matrix (Fin 0) (Fin 0) ℝ) (schurBlock a b c)).det ≠ 0
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  | cons tag w ih =>
    cases tag <;> intro p hp a b c hc hcb ha
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let t := schurTailInput x
      have htail : schurRoot a b c ∉ schurWordRoots w t := by
        intro hm
        exact ha (Multiset.mem_cons_of_mem hm)
      rw [det_sylvester_word_scalar]
      apply mul_ne_zero _ (ih t hp a b c hc hcb htail)
      rw [det_sylvester_scalar_block]
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (lt_of_lt_of_le hc hcb) hc))
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      let z := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
      let μ := schurRoot a b c
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      obtain ⟨hd, hde, ht⟩ := hp
      have htail : μ ∉ schurWordRoots w t := by
        intro hm
        exact ha (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hm))
      have hneq : z ≠ μ := by
        intro he
        apply ha
        change μ ∈ z ::ₘ conj z ::ₘ schurWordRoots w t
        rw [← he]
        exact Multiset.mem_cons_self _ _
      have hz : 0 < z.im := Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hd hde) hd)
      have hμ : 0 < μ.im := Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hc hcb) hc)
      have hneqconj : z ≠ conj μ := by
        intro he
        have hi := congrArg Complex.im he
        rw [Complex.conj_im] at hi
        linarith
      rw [det_sylvester_word_pair]
      apply mul_ne_zero _ (ih t ht a b c hc hcb htail)
      exact det_sylvester_block_block_ne_zero _ _ _ _ _ _
        (mul_nonneg (hd.le.trans hde) hd.le) (mul_nonneg (hc.le.trans hcb) hc.le) hneq hneqconj

/-- Separation is a consequence of literal characteristic-root nonmembership. -/
theorem sylvester_word_scalar_separated (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p) (a : ℝ)
    (ha : (a : ℂ) ∉ ((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots) :
    (sylvesterMatrix (schurWordParameter w p) (scalarBlock a)).det ≠ 0 := by
  rw [schurWordParameter_roots w p hp] at ha
  exact det_sylvester_word_scalar_ne_zero w p hp a ha

theorem sylvester_word_pair_separated (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p) (a b c : ℝ) (hc : 0 < c) (hcb : c ≤ b)
    (ha : schurRoot a b c ∉ ((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots) :
    (sylvesterMatrix (schurWordParameter w p) (schurBlock a b c)).det ≠ 0 := by
  rw [schurWordParameter_roots w p hp] at ha
  exact det_sylvester_word_pair_ne_zero w p hp a b c hc hcb ha

end Paper.Spectral
