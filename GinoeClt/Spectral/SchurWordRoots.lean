/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurWordParameters
public import GinoeClt.Spectral.SchurRootFactors

/-! Literal algebraic-multiplicity roots of normalized scalar/pair word matrices. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate

namespace Paper.Spectral

/-- Actual roots in block order, retaining all algebraic multiplicities. -/
def schurWordRoots : (w : List Bool) → SchurWordCells w → Multiset ℂ
  | [], _ => 0
  | false :: w, p =>
      let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      ((schurHeadInput x (0, 0) : ℝ) : ℂ) ::ₘ schurWordRoots w (schurTailInput x)
  | true :: w, p =>
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let z := schurRoot (h (0, 0)) (h (0, 1)) (h (1, 0))
      z ::ₘ conj z ::ₘ schurWordRoots w (schurTailInput x)

theorem mapped_charpoly_ne_zero {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    M.charpoly.map Complex.ofRealHom ≠ 0 := (Matrix.charpoly_monic M).map Complex.ofRealHom |>.ne_zero

theorem scalarBlock_charpoly (a : ℝ) :
    (scalarBlock a).charpoly = Polynomial.X - Polynomial.C a := by
  rw [Matrix.charpoly, Matrix.det_unique]
  rfl

theorem scalarBlock_roots (a : ℝ) :
    ((scalarBlock a).charpoly.map Complex.ofRealHom).roots = {(a : ℂ)} := by
  rw [scalarBlock_charpoly]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.roots_X_sub_C]
  rfl


/-- A typed physical block-root bridge, with all matrix instances at the physical size. -/
theorem upperBlockMatrix_roots {d m : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) :
    ((upperBlockMatrix B U D).charpoly.map Complex.ofRealHom).roots =
      (B.charpoly.map Complex.ofRealHom).roots + (D.charpoly.map Complex.ofRealHom).roots := by
  rw [upperBlockMatrix, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁,
    Polynomial.map_mul,
    Polynomial.roots_mul (mul_ne_zero (mapped_charpoly_ne_zero _) (mapped_charpoly_ne_zero _))]

/-- The exact root multiset of the actual word matrix, without a simple-spectrum premise. -/
theorem schurWordParameter_roots (w : List Bool) :
    ∀ p : SchurWordCells w, SchurWordPositive w p →
      ((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots = schurWordRoots w p := by
  induction w with
  | nil =>
    intro p _
    change ((0 : Matrix (Fin 0) (Fin 0) ℝ).charpoly.map Complex.ofRealHom).roots = 0
    rw [Matrix.charpoly, Matrix.det_isEmpty]
    simp
  | cons b w ih =>
    cases b <;> intro p hp
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      have hK : schurWordParameter (false :: w) p =
          upperBlockMatrix (scalarBlock (h (0, 0))) (schurUpperInput x) (schurWordParameter w t) :=
        schurParameterPhysical_eq scalarHeadParameter (schurWordParameter w) p
      have hr := congrArg (fun M : Matrix (Fin (1 + schurWordSize w))
        (Fin (1 + schurWordSize w)) ℝ => (M.charpoly.map Complex.ofRealHom).roots) hK
      refine hr.trans ((upperBlockMatrix_roots _ _ _).trans ?_)
      rw [scalarBlock_roots, ih t hp]
      rfl
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      change 0 < h (1, 0) ∧ h (1, 0) ≤ h (0, 1) ∧ SchurWordPositive w t at hp
      obtain ⟨hc, hcb, ht⟩ := hp
      have hbc : 0 ≤ h (0, 1) * h (1, 0) := mul_nonneg (hc.le.trans hcb) hc.le
      have hK : schurWordParameter (true :: w) p =
          upperBlockMatrix (schurBlock (h (0, 0)) (h (0, 1)) (h (1, 0)))
            (schurUpperInput x) (schurWordParameter w t) :=
        schurParameterPhysical_eq pairHeadParameter (schurWordParameter w) p
      have hr := congrArg (fun M : Matrix (Fin (2 + schurWordSize w))
        (Fin (2 + schurWordSize w)) ℝ => (M.charpoly.map Complex.ofRealHom).roots) hK
      refine hr.trans ((upperBlockMatrix_roots _ _ _).trans ?_)
      rw [schurBlock_roots _ _ _ hbc, ih t ht]
      simp [schurWordRoots, x, h, t]

/-- Every word supplies exactly N roots, also at repeated and defective spectra. -/
theorem card_schurWordRoots (w : List Bool) :
    ∀ p : SchurWordCells w, (schurWordRoots w p).card = schurWordSize w := by
  induction w with
  | nil => intro p; rfl
  | cons b w ih =>
    cases b <;> intro p <;> simp [schurWordRoots, schurWordSize, ih, Nat.add_comm]
    omega

/-- Actual upper-half-plane and real root multiplicities are the pair and scalar block counts. -/
theorem schurWordRoots_sector_counts (w : List Bool) :
    ∀ p : SchurWordCells w, SchurWordPositive w p →
      ((schurWordRoots w p).filter (fun z : ℂ => 0 < z.im)).card = w.count true ∧
        ((schurWordRoots w p).filter (fun z : ℂ => z.im = 0)).card = w.count false := by
  classical
  induction w with
  | nil => intro p _; simp [schurWordRoots]
  | cons b w ih =>
    cases b <;> intro p hp
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      have ht := ih (schurTailInput x) hp
      constructor
      · simpa [schurWordRoots, List.count_cons, x] using ht.1
      · simpa [schurWordRoots, List.count_cons, x, Nat.add_comm] using congrArg Nat.succ ht.2
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let z := schurRoot (h (0, 0)) (h (0, 1)) (h (1, 0))
      change 0 < h (1, 0) ∧ h (1, 0) ≤ h (0, 1) ∧
        SchurWordPositive w (schurTailInput x) at hp
      obtain ⟨hc, hcb, hp⟩ := hp
      have hz : 0 < z.im := Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hc hcb) hc)
      have hcz : ¬0 < (conj z).im := by rw [Complex.conj_im]; linarith
      have hz0 : z.im ≠ 0 := ne_of_gt hz
      have hcz0 : (conj z).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hz0
      have ht := ih (schurTailInput x) hp
      constructor
      · change ((z ::ₘ conj z ::ₘ schurWordRoots w (schurTailInput x)).filter
          (fun u : ℂ => 0 < u.im)).card = (true :: w).count true
        rw [Multiset.filter_cons_of_pos (p := fun u : ℂ => 0 < u.im) _ hz,
          Multiset.filter_cons_of_neg (p := fun u : ℂ => 0 < u.im) _ hcz]
        simpa [List.count_cons, Nat.add_comm] using congrArg Nat.succ ht.1
      · simpa [schurWordRoots, List.count_cons, x, h, z, hz0, hcz0] using ht.2

/-- The sector counts refer to the actual characteristic roots of the physical word matrix. -/
theorem schurWordParameter_sector_counts (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p) :
    ((((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots).filter
      (fun z : ℂ => 0 < z.im)).card = w.count true ∧
    ((((schurWordParameter w p).charpoly.map Complex.ofRealHom).roots).filter
      (fun z : ℂ => z.im = 0)).card = w.count false := by
  rw [schurWordParameter_roots w p hp]
  exact schurWordRoots_sector_counts w p hp

theorem schurWordSize_eq_counts (w : List Bool) :
    schurWordSize w = w.count false + 2 * w.count true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [schurWordSize, ih] <;> omega

end Paper.Spectral
