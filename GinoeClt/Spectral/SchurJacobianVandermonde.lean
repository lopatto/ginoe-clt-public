/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurVandermonde
public import GinoeClt.Spectral.SchurWordSeparation
public import GinoeClt.Spectral.SchurPhysicalDifferential
@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Paper.Spectral

/-- Exact scalar cross-factor, with the original full MULTISET of tail roots. -/
theorem abs_det_sylvester_word_scalar_prod (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p → ∀ a : ℝ,
      |(sylvesterMatrix (schurWordParameter w p) (scalarBlock a)).det| =
        ((schurWordRoots w p).map (fun z ↦ ‖z-(a : ℂ)‖)).prod := by
  induction w with
  | nil =>
    intro p hp a
    change |(sylvesterMatrix (0 : Matrix (Fin 0) (Fin 0) ℝ) (scalarBlock a)).det| = _
    rw [Matrix.det_isEmpty]
    simp [schurWordRoots]
  | cons tag w ih =>
    cases tag <;> intro p hp a
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      have ht : SchurWordPositive w t := hp
      rw [det_sylvester_word_scalar w p, abs_mul, ih t ht a]
      simp only [schurWordRoots, Multiset.map_cons, Multiset.prod_cons]
      congr 1
      rw [det_sylvester_scalar_scalar]
      simp [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      have hbc : 0 ≤ h (0,1)*h (1,0) := mul_nonneg (hp.1.le.trans hp.2.1) hp.1.le
      rw [det_sylvester_word_pair w p, abs_mul, ih t hp.2.2 a,
        det_sylvester_block_scalar_root _ _ _ a hbc, abs_of_nonneg (sq_nonneg _)]
      simp only [schurWordRoots, Multiset.map_cons, Multiset.prod_cons, norm_conj_sub_real]
      ring

/-- Exact conjugate-pair cross-factor; no full-root injectivity or strict gap is assumed. -/
theorem abs_det_sylvester_word_pair_prod (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p → ∀ a b c : ℝ,
      0 < c → c ≤ b →
      |(sylvesterMatrix (schurWordParameter w p) (schurBlock a b c)).det| =
        ((schurWordRoots w p).map (fun z ↦
          ‖z-schurRoot a b c‖ * ‖z-conj (schurRoot a b c)‖)).prod := by
  induction w with
  | nil =>
    intro p hp a b c hc hcb
    change |(sylvesterMatrix (0 : Matrix (Fin 0) (Fin 0) ℝ) (schurBlock a b c)).det| = _
    rw [Matrix.det_isEmpty]
    simp [schurWordRoots]
  | cons tag w ih =>
    cases tag <;> intro p hp a b c hc hcb
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      have ht : SchurWordPositive w t := hp
      have hbc : 0 ≤ b*c := mul_nonneg (hc.le.trans hcb) hc.le
      rw [det_sylvester_word_scalar w p, abs_mul, ih t ht a b c hc hcb,
        det_sylvester_scalar_block_root _ a b c hbc, abs_of_nonneg (sq_nonneg _)]
      simp only [schurWordRoots, Multiset.map_cons, Multiset.prod_cons, norm_real_sub_conj]
      ring
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      have hhead : 0 ≤ h (0,1)*h (1,0) := mul_nonneg (hp.1.le.trans hp.2.1) hp.1.le
      have hbc : 0 ≤ b*c := mul_nonneg (hc.le.trans hcb) hc.le
      rw [det_sylvester_word_pair w p, abs_mul, ih t hp.2.2 a b c hc hcb,
        abs_det_sylvester_block_block_roots _ _ _ a b c hhead hbc]
      simp only [schurWordRoots, Multiset.map_cons, Multiset.prod_cons,
        norm_conj_sub, starRingEnd_self_apply]
      ring

/-- Scalar-head factorization of the genuine FULL Vandermonde magnitude. -/
theorem norm_vandermonde_fullRoots_false (w : List Bool)
    (p : SchurWordCells (false::w)) (hp : SchurWordPositive (false::w) p) :
    let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
    let h := schurHeadInput x
    let t := schurTailInput x
    ‖(Matrix.vandermonde (schurWordFullRootAt (false::w) p)).det‖ =
      |(sylvesterMatrix (schurWordParameter w t) (scalarBlock (h (0,0)))).det| *
        ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖ := by
  let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
  let h := schurHeadInput x
  let t := schurTailInput x
  have ht : SchurWordPositive w t := hp
  dsimp only
  let v : Fin (schurWordSize w + 1) → ℂ :=
    Fin.cons ((h (0,0) : ℝ) : ℂ) (schurWordFullRootAt w t)
  change ‖(Matrix.vandermonde (fun i : Fin (1+schurWordSize w) ↦
    v (Fin.cast (Nat.one_add _) i))).det‖ = _
  rw [det_vandermonde_finCast (Nat.one_add _) v]
  dsimp only [v]
  rw [norm_det_vandermonde_cons]
  change (∏ i : Fin (schurWordSize w), ‖schurWordFullRootAt w t i - ((h (0,0) : ℝ) : ℂ)‖) *
      ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖ =
    |(sylvesterMatrix (schurWordParameter w t) (scalarBlock (h (0,0)))).det| *
      ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖
  rw [prod_schurWordFullRootAt w t (fun z => ‖z - ((h (0,0) : ℝ) : ℂ)‖),
    abs_det_sylvester_word_scalar_prod w t ht]

/-- Pair-head factorization retains the within-pair factor EXACTLY2*sqrt(b*c). -/
theorem norm_vandermonde_fullRoots_true (w : List Bool)
    (p : SchurWordCells (true::w)) (hp : SchurWordPositive (true::w) p) :
    let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
    let h := schurHeadInput x
    let t := schurTailInput x
    ‖(Matrix.vandermonde (schurWordFullRootAt (true::w) p)).det‖ =
      (2 * Real.sqrt (h (0,1)*h (1,0))) *
        |(sylvesterMatrix (schurWordParameter w t) (schurBlock (h (0,0)) (h (0,1)) (h (1,0)))).det| *
          ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖ := by
  let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
  let h := schurHeadInput x
  let t := schurTailInput x
  let z := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
  change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
  dsimp only
  let v : Fin (schurWordSize w + 2) → ℂ :=
    Fin.cons z (Fin.cons (conj z) (schurWordFullRootAt w t))
  change ‖(Matrix.vandermonde (fun i : Fin (2+schurWordSize w) ↦
    v (Fin.cast (Nat.add_comm 2 _) i))).det‖ = _
  rw [det_vandermonde_finCast (Nat.add_comm 2 _) v]
  dsimp only [v]
  rw [norm_det_vandermonde_cons_two, norm_schurRoot_conj_sub]
  change (2 * Real.sqrt (h (0,1)*h (1,0))) *
      (∏ i : Fin (schurWordSize w), ‖schurWordFullRootAt w t i-z‖ * ‖schurWordFullRootAt w t i-conj z‖) *
      ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖ =
    (2 * Real.sqrt (h (0,1)*h (1,0))) *
      |(sylvesterMatrix (schurWordParameter w t) (schurBlock (h (0,0)) (h (0,1)) (h (1,0)))).det| *
      ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖
  rw [prod_schurWordFullRootAt w t (fun u => ‖u-z‖ * ‖u-conj z‖),
    abs_det_sylvester_word_pair_prod w t hp.2.2 _ _ _ hp.1 hp.2.1]

/-- Physical normalization identity under ORIGINALpositivity only.
Repeated cross roots and zero pair gaps are allowed; only each positive pair's sqrt(b*c) is cancelled. -/
theorem abs_det_schurWordDifferential_eq_vandermonde (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p →
      |LinearMap.det (schurWordDifferential w p)| =
        ‖(Matrix.vandermonde (schurWordFullRootAt w p)).det‖ * schurWordPairRatio w p := by
  induction w with
  | nil =>
    intro p hp
    rw [det_schurWordDifferential_nil p]
    simp only [abs_one, schurWordPairRatio, mul_one]
    change (1 : ℝ) = ‖(Matrix.vandermonde (fun i : Fin 0 => (Fin.elim0 i : ℂ))).det‖
    rw [Matrix.det_isEmpty]
    norm_num
  | cons tag w ih =>
    cases tag <;> intro p hp
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let t := schurTailInput x
      have ht : SchurWordPositive w t := hp
      rw [det_schurWordDifferential_false w p, abs_mul, ih t ht,
        norm_vandermonde_fullRoots_false w p hp]
      change _ = _ * schurWordPairRatio w t
      ring
    · have hpAll := hp
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      let y := Real.sqrt (h (0,1)*h (1,0))
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧ SchurWordPositive w t at hp
      have hy : y ≠ 0 := (Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hp.1 hp.2.1) hp.1)).ne'
      have hgap : 0 ≤ 2*(h (0,1)-h (1,0)) :=
        mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sub_nonneg.mpr hp.2.1)
      have hcancel : y * ((h (0,1)-h (1,0))/y) = h (0,1)-h (1,0) := mul_div_cancel₀ _ hy
      rw [det_schurWordDifferential_true w p, abs_mul, abs_mul,
        abs_of_nonneg hgap, ih t hp.2.2, norm_vandermonde_fullRoots_true w p hpAll]
      change _ = ((2*y) * _ * _) * (((h (0,1)-h (1,0))/y) * schurWordPairRatio w t)
      symm
      calc
        _ = 2 * |(sylvesterMatrix (schurWordParameter w t)
            (schurBlock (h (0,0)) (h (0,1)) (h (1,0)))).det| *
          ‖(Matrix.vandermonde (schurWordFullRootAt w t)).det‖ * schurWordPairRatio w t *
            (y * ((h (0,1)-h (1,0))/y)) := by ring
        _ = _ := by rw [hcancel]; ring

end Paper.Spectral
