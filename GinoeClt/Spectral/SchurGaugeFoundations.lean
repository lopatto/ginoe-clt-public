/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurWordRegularity
public import GinoeClt.Spectral.SchurBlockGauge
public import GinoeClt.Spectral.SchurPairUniqueness
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate
namespace Paper.Spectral

/-- A genuine one-dimensional orthogonal head has exactly two possible frames. -/
theorem orthogonal_scalar_eq_sign (E : Matrix.orthogonalGroup (Fin 1) ℝ) :
    (E : Matrix (Fin 1) (Fin 1) ℝ) = 1 ∨ (E : Matrix (Fin 1) (Fin 1) ℝ) = -1 := by
  have ho := (Matrix.mem_orthogonalGroup_iff (Fin 1) ℝ).mp E.property
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) ho
  have hs : (E : Matrix (Fin 1) (Fin 1) ℝ) 0 0 ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_one, pow_two] using he
  rcases sq_eq_one_iff.mp hs with h | h
  · left
    ext i j
    fin_cases i
    fin_cases j
    exact h
  · right
    ext i j
    fin_cases i
    fin_cases j
    exact h

/-- Exact characteristic polynomials of genuinely orthogonally intertwined matrices. -/
theorem charpoly_eq_of_orthogonal_intertwiner (N : ℕ)
    (A B : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (hT : A * (Q : Matrix (Fin N) (Fin N) ℝ) =
      (Q : Matrix (Fin N) (Fin N) ℝ) * B) : A.charpoly = B.charpoly := by
  have hQtQ := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  have hconj : (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A *
      (Q : Matrix (Fin N) (Fin N) ℝ) = B := by
    rw [Matrix.mul_assoc, hT, ← Matrix.mul_assoc, hQtQ, Matrix.one_mul]
  have h := congrArg Matrix.charpoly hconj
  rw [charpoly_orthogonal_similarity] at h
  exact h

/-- Ordered matching actual heads plus simple full roots provide scalar cross separation. -/
theorem scalar_word_cross_separation (w : List Bool)
    (p q : SchurWordCells (false::w))
    (hp : SchurWordPositive (false::w) p) (hq : SchurWordPositive (false::w) q)
    (hop : SchurWordOrdered (false::w) p) (hoq : SchurWordOrdered (false::w) q)
    (hr : schurWordRoots (false::w) p = schurWordRoots (false::w) q)
    (hn : (schurWordRoots (false::w) p).Nodup) :
    let xp := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
    let xq := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) q
    (sylvesterMatrix (schurWordParameter w (schurTailInput xp))
      (scalarBlock (schurHeadInput xq (0,0)))).det ≠ 0 := by
  let xp := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
  let xq := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) q
  let tp := schurTailInput xp
  let tq := schurTailInput xq
  let ap := schurHeadInput xp (0,0)
  let aq := schurHeadInput xq (0,0)
  have hl := ordered_schurWordHeadRoots_eq (false::w) (false::w) p q hp hq hop hoq hr
  change ((ap : ℂ) :: schurWordHeadRoots w tp) = ((aq : ℂ) :: schurWordHeadRoots w tq) at hl
  have hhead := (List.cons.inj hl).1
  have hn' : ((ap : ℂ) ::ₘ schurWordRoots w tp).Nodup := hn
  have hnot : (aq : ℂ) ∉ schurWordRoots w tp := by
    rw [← hhead]
    exact (Multiset.nodup_cons.mp hn').1
  exact det_sylvester_word_scalar_ne_zero w tp hp aq hnot

/-- The upper-root comparison uses exactly the primed head and unprimed tail. -/
theorem pair_word_cross_separation (w : List Bool)
    (p q : SchurWordCells (true::w))
    (hp : SchurWordPositive (true::w) p) (hq : SchurWordPositive (true::w) q)
    (hop : SchurWordOrdered (true::w) p) (hoq : SchurWordOrdered (true::w) q)
    (hr : schurWordRoots (true::w) p = schurWordRoots (true::w) q)
    (hn : (schurWordRoots (true::w) p).Nodup) :
    let xp := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
    let xq := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) q
    let hq := schurHeadInput xq
    (sylvesterMatrix (schurWordParameter w (schurTailInput xp))
      (schurBlock (hq (0,0)) (hq (0,1)) (hq (1,0)))).det ≠ 0 := by
  let xp := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
  let xq := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) q
  let tp := schurTailInput xp
  let tq := schurTailInput xq
  let hphead := schurHeadInput xp
  let hqhead := schurHeadInput xq
  let zp := schurRoot (hphead (0,0)) (hphead (0,1)) (hphead (1,0))
  let zq := schurRoot (hqhead (0,0)) (hqhead (0,1)) (hqhead (1,0))
  have hl := ordered_schurWordHeadRoots_eq (true::w) (true::w) p q hp hq hop hoq hr
  change zp :: schurWordHeadRoots w tp = zq :: schurWordHeadRoots w tq at hl
  have hhead := (List.cons.inj hl).1
  have hn' : (zp ::ₘ conj zp ::ₘ schurWordRoots w tp).Nodup := hn
  have hnot : zq ∉ schurWordRoots w tp := by
    intro hm
    apply (Multiset.nodup_cons.mp hn').1
    apply Multiset.mem_cons_of_mem
    simpa only [hhead] using hm
  change 0 < hphead (1,0) ∧ hphead (1,0) ≤ hphead (0,1) ∧ SchurWordPositive w tp at hp
  change 0 < hqhead (1,0) ∧ hqhead (1,0) ≤ hqhead (0,1) ∧ SchurWordPositive w tq at hq
  exact det_sylvester_word_pair_ne_zero w tp hp.2.2 _ _ _ hq.1 hq.2.1 hnot

/-- Strict normalized pair heads admit only scalar sign intertwiners. -/
theorem orthogonal_pair_intertwiner_eq_sign
    (a b c a' b' c' : ℝ) (hc : 0 < c) (hcb : c < b)
    (hc' : 0 < c') (hcb' : c' < b')
    (E : Matrix.orthogonalGroup (Fin 2) ℝ)
    (hBE : schurBlock a b c * (E : Matrix (Fin 2) (Fin 2) ℝ) =
      (E : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a' b' c') :
    a = a' ∧ b = b' ∧ c = c' ∧
      ((E : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∨ (E : Matrix (Fin 2) (Fin 2) ℝ) = -1) := by
  have hEEt := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp E.property
  have he : (E : Matrix (Fin 2) (Fin 2) ℝ) * schurBlock a' b' c' *
      (E : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = schurBlock a b c := by
    rw [← hBE, Matrix.mul_assoc, hEEt, Matrix.mul_one]
  obtain ⟨ha,hb,hcc,hsign⟩ := orthogonal_schurBlock_similarity_eq_parameters_and_sign
    a' b' c' a b c hc' hcb' hc hcb E he
  exact ⟨ha.symm,hb.symm,hcc.symm,hsign⟩

/-- A separated scalar head can be removed from a genuine orthogonal intertwiner. -/
theorem scalar_head_intertwiner_frames {m : ℕ} (a a' : ℝ)
    (D D' : Matrix (Fin m) (Fin m) ℝ) (U U' : Matrix (Fin 1) (Fin m) ℝ)
    (Q : Matrix.orthogonalGroup (Fin 1 ⊕ Fin m) ℝ)
    (hsep : (sylvesterMatrix D (scalarBlock a')).det ≠ 0)
    (hT : Matrix.fromBlocks (scalarBlock a) U 0 D *
      (Q : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℝ) =
        (Q : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℝ) *
          Matrix.fromBlocks (scalarBlock a') U' 0 D') :
    ∃ R : Matrix.orthogonalGroup (Fin m) ℝ,
      D * (R : Matrix (Fin m) (Fin m) ℝ) = (R : Matrix (Fin m) (Fin m) ℝ) * D' ∧
      ((Q : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℝ) =
          Matrix.fromBlocks 1 0 0 (R : Matrix (Fin m) (Fin m) ℝ) ∨
        (Q : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℝ) =
          Matrix.fromBlocks (-1) 0 0 (R : Matrix (Fin m) (Fin m) ℝ)) := by
  obtain ⟨E,R,hQ,hBE,hDR,hUR⟩ := orthogonal_schur_intertwiner_blocks
    (scalarBlock a) (scalarBlock a') D D' U U' Q hsep hT
  refine ⟨R,hDR,?_⟩
  rcases orthogonal_scalar_eq_sign E with hE | hE
  · exact Or.inl (by simpa only [hE] using hQ)
  · exact Or.inr (by simpa only [hE] using hQ)

/-- A separated strict pair head can likewise be removed, with exactly two head signs. -/
theorem pair_head_intertwiner_frames {m : ℕ}
    (a b c a' b' c' : ℝ) (hc : 0 < c) (hcb : c < b)
    (hc' : 0 < c') (hcb' : c' < b')
    (D D' : Matrix (Fin m) (Fin m) ℝ) (U U' : Matrix (Fin 2) (Fin m) ℝ)
    (Q : Matrix.orthogonalGroup (Fin 2 ⊕ Fin m) ℝ)
    (hsep : (sylvesterMatrix D (schurBlock a' b' c')).det ≠ 0)
    (hT : Matrix.fromBlocks (schurBlock a b c) U 0 D *
      (Q : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ) =
        (Q : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ) *
          Matrix.fromBlocks (schurBlock a' b' c') U' 0 D') :
    ∃ R : Matrix.orthogonalGroup (Fin m) ℝ,
      D * (R : Matrix (Fin m) (Fin m) ℝ) = (R : Matrix (Fin m) (Fin m) ℝ) * D' ∧
      ((Q : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ) =
          Matrix.fromBlocks 1 0 0 (R : Matrix (Fin m) (Fin m) ℝ) ∨
        (Q : Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) ℝ) =
          Matrix.fromBlocks (-1) 0 0 (R : Matrix (Fin m) (Fin m) ℝ)) := by
  obtain ⟨E,R,hQ,hBE,hDR,hUR⟩ := orthogonal_schur_intertwiner_blocks
    (schurBlock a b c) (schurBlock a' b' c') D D' U U' Q hsep hT
  obtain ⟨ha,hb,hcc,hsign⟩ := orthogonal_pair_intertwiner_eq_sign
    a b c a' b' c' hc hcb hc' hcb' E hBE
  refine ⟨R,hDR,?_⟩
  rcases hsign with hE | hE
  · exact Or.inl (by simpa only [hE] using hQ)
  · exact Or.inr (by simpa only [hE] using hQ)

/-- The literal reindexing of an actual orthogonal matrix remains orthogonal. -/
def schurOrthogonalReindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (Q : Matrix.orthogonalGroup ι ℝ) :
    Matrix.orthogonalGroup κ ℝ := by
  let ρ := Matrix.reindexRingEquiv ℝ e
  refine ⟨ρ (Q : Matrix ι ι ℝ),?_⟩
  apply (Matrix.mem_orthogonalGroup_iff κ ℝ).mpr
  change ρ (Q : Matrix ι ι ℝ) * ρ (Q : Matrix ι ι ℝ)ᵀ = 1
  rw [← map_mul, (Matrix.mem_orthogonalGroup_iff ι ℝ).mp Q.property, map_one]

/-- Genuine physical block intertwiners in the corresponding sum coordinates. -/
theorem schur_physical_intertwiner_to_sum {d m : ℕ}
    (B B' : Matrix (Fin d) (Fin d) ℝ) (D D' : Matrix (Fin m) (Fin m) ℝ)
    (U U' : Matrix (Fin d) (Fin m) ℝ)
    (Q : Matrix.orthogonalGroup (Fin (d+m)) ℝ)
    (hT : upperBlockMatrix B U D * (Q : Matrix (Fin (d+m)) (Fin (d+m)) ℝ) =
      (Q : Matrix (Fin (d+m)) (Fin (d+m)) ℝ) * upperBlockMatrix B' U' D') :
    Matrix.fromBlocks B U 0 D *
      (schurOrthogonalReindex finSumFinEquiv.symm Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) =
      (schurOrthogonalReindex finSumFinEquiv.symm Q : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) *
        Matrix.fromBlocks B' U' 0 D' := by
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d+m))
  have hQ : ρ (schurOrthogonalReindex finSumFinEquiv.symm Q :
      Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ) = Q := by
    ext i j
    simp [ρ, schurOrthogonalReindex, Matrix.reindex_apply]
  apply ρ.injective
  rw [map_mul,map_mul,hQ]
  exact hT

/-- Actual orthogonal word intertwiners have identical full multiplicity root multisets. -/
theorem schurWordRoots_eq_of_intertwiner (w : List Bool) (p q : SchurWordCells w)
    (hp : SchurWordPositive w p) (hq : SchurWordPositive w q)
    (Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hT : schurWordParameter w p * (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) =
      (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) * schurWordParameter w q) :
    schurWordRoots w p = schurWordRoots w q := by
  rw [← schurWordParameter_roots w p hp, ← schurWordParameter_roots w q hq]
  exact congrArg (fun f : Polynomial ℝ => (f.map Complex.ofRealHom).roots)
    (charpoly_eq_of_orthogonal_intertwiner (schurWordSize w) _ _ Q hT)

end Paper.Spectral
