/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SchurRootOrder

/-! Ordered actual scalar/pair Schur coverage, retaining multiplicities and degeneracies. -/
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate

namespace Paper.Spectral

/-- The actual representative list is nondecreasing in the standard root key. -/
def SchurWordOrdered (w : List Bool) (p : SchurWordCells w) : Prop :=
  (schurWordHeadRoots w p).Pairwise (fun z u => schurRootKey z ≤ schurRootKey u)

/-- Actual normalized zero-angle word parameters, now with ordered representatives. -/
def HasOrderedSchurWord (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ w : List Bool, ∃ h : schurWordSize w = N, ∃ p : SchurWordCells w,
    SchurWordPositive w p ∧ schurWordOmega w p = 0 ∧ SchurWordOrdered w p ∧
      ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
        (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ) =
          (schurWordParameter w p).reindex (finCongr h) (finCongr h)

theorem hasOrderedSchurWord_scalar_upper {m : ℕ} (a : ℝ)
    (U : Matrix (Fin 1) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hD : HasOrderedSchurWord m D)
    (hmin : ∀ z : ℂ, z ∈ (D.charpoly.map Complex.ofRealHom).roots → 0 ≤ z.im →
      schurRootKey (a : ℂ) ≤ schurRootKey z) :
    HasOrderedSchurWord (1+m) (upperBlockMatrix (scalarBlock a) U D) := by
  obtain ⟨w, hsize, t, ht, hΩ, hord, R, hR⟩ := hD
  subst m
  have hR' : (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ * D *
      (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordParameter w t := by
    simpa [Matrix.reindex_apply] using hR
  let p := schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))
  obtain ⟨hK, hΩp, hpos⟩ := schurWord_free_scalar w a t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)) hΩ ht
  have hr := roots_eq_schurWordRoots_of_conjugation w t ht D R hR'
  have hsort : SchurWordOrdered (false::w) p := by
    simp only [SchurWordOrdered, schurWordHeadRoots, p, schurStepFreeCells_coordinates,
      schurHeadInput_free, schurTailInput_free]
    rw [List.pairwise_cons]
    refine ⟨?_, hord⟩
    intro z hz
    have hm := (mem_schurWordHeadRoots w t ht z).mp hz
    rw [schurWordParameter_roots w t ht, ← hr] at hm
    exact hmin z hm.1 hm.2
  refine ⟨false::w, rfl, p, hpos, hΩp, hsort, schurTailOrthogonal 1 (schurWordSize w) R, ?_⟩
  rw [schurTailOrthogonal_conjugation, hR']
  refine Eq.trans hK.symm ?_
  ext i j
  rfl

theorem hasOrderedSchurWord_pair_upper {m : ℕ} (a b c : ℝ)
    (U : Matrix (Fin 2) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hc : 0 < c) (hcb : c ≤ b) (hD : HasOrderedSchurWord m D)
    (hmin : ∀ z : ℂ, z ∈ (D.charpoly.map Complex.ofRealHom).roots → 0 ≤ z.im →
      schurRootKey (schurRoot a b c) ≤ schurRootKey z) :
    HasOrderedSchurWord (2+m) (upperBlockMatrix (schurBlock a b c) U D) := by
  obtain ⟨w, hsize, t, ht, hΩ, hord, R, hR⟩ := hD
  subst m
  have hR' : (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)ᵀ * D *
      (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) = schurWordParameter w t := by
    simpa [Matrix.reindex_apply] using hR
  let p := schurStepFreeCells (pairFreeInput a b c) t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ))
  obtain ⟨hK, hΩp, hpos⟩ := schurWord_free_pair w a b c t
    (U * (R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)) hΩ ht hc hcb
  have hr := roots_eq_schurWordRoots_of_conjugation w t ht D R hR'
  have hsort : SchurWordOrdered (true::w) p := by
    simp only [SchurWordOrdered, schurWordHeadRoots, p, schurStepFreeCells_coordinates,
      schurHeadInput_free, schurTailInput_free]
    change (schurRoot a b c :: schurWordHeadRoots w t).Pairwise _
    rw [List.pairwise_cons]
    refine ⟨?_, hord⟩
    intro z hz
    have hm := (mem_schurWordHeadRoots w t ht z).mp hz
    rw [schurWordParameter_roots w t ht, ← hr] at hm
    exact hmin z hm.1 hm.2
  refine ⟨true::w, rfl, p, hpos, hΩp, hsort, schurTailOrthogonal 2 (schurWordSize w) R, ?_⟩
  rw [schurTailOrthogonal_conjugation, hR']
  refine Eq.trans hK.symm ?_
  ext i j
  rfl

theorem hasOrderedSchurWord_of_orthogonal_conjugation (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (h : HasOrderedSchurWord N
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * (Q : Matrix (Fin N) (Fin N) ℝ))) :
    HasOrderedSchurWord N A := by
  obtain ⟨w, hsize, p, hp, hΩ, hord, R, hR⟩ := h
  refine ⟨w, hsize, p, hp, hΩ, hord, Q*R, ?_⟩
  change ((Q : Matrix (Fin N) (Fin N) ℝ) * (R : Matrix (Fin N) (Fin N) ℝ))ᵀ * A *
    ((Q : Matrix (Fin N) (Fin N) ℝ) * (R : Matrix (Fin N) (Fin N) ℝ)) = _
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using hR

/-- A prescribed least head leaves only larger actual representatives in its tail. -/
theorem hasOrderedSchurWord_step {N d m : ℕ} (hsize : d+m=N)
    (A : Matrix (Fin N) (Fin N) ℝ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (hdN : d ≤ N) (B : Matrix (Fin d) (Fin d) ℝ) (μ : ℂ)
    (hmin : ∀ z : ℂ, z ∈ (A.charpoly.map Complex.ofRealHom).roots → 0 ≤ z.im →
      schurRootKey μ ≤ schurRootKey z)
    (htop : ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A *
      (Q : Matrix (Fin N) (Fin N) ℝ)).submatrix (Fin.castLE hdN) (Fin.castLE hdN) = B)
    (hlo : ∀ (i : Fin N) (j : Fin d), d ≤ i.val →
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A *
        (Q : Matrix (Fin N) (Fin N) ℝ)) i (Fin.castLE hdN j) = 0)
    (hupper : ∀ (U : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ),
      HasOrderedSchurWord m D →
      (∀ z : ℂ, z ∈ (D.charpoly.map Complex.ofRealHom).roots → 0 ≤ z.im →
        schurRootKey μ ≤ schurRootKey z) →
      HasOrderedSchurWord (d+m) (upperBlockMatrix B U D))
    (hTail : ∀ D : Matrix (Fin m) (Fin m) ℝ, HasOrderedSchurWord m D) :
    HasOrderedSchurWord N A := by
  subst N
  apply hasOrderedSchurWord_of_orthogonal_conjugation (d+m) A Q
  let M := (Q : Matrix (Fin (d+m)) (Fin (d+m)) ℝ)ᵀ * A *
    (Q : Matrix (Fin (d+m)) (Fin (d+m)) ℝ)
  let U := M.submatrix (Fin.castAdd m) (Fin.natAdd d)
  let D := M.submatrix (Fin.natAdd d) (Fin.natAdd d)
  have hM : M = upperBlockMatrix B U D := upperBlockMatrix_eq_of_corner M hdN B htop hlo
  have hr := mapped_roots_of_orthogonal_upperBlock A Q B U D hM
  change HasOrderedSchurWord (d+m) M
  rw [hM]
  apply hupper U D (hTail D)
  intro z hz him
  apply hmin z _ him
  rw [hr]
  exact Multiset.mem_add.mpr (Or.inr hz)

/-- Every real matrix has an actual normalized word with nondecreasing
real/upper root representatives, without a simple-spectrum hypothesis. -/
theorem exists_ordered_schur_word (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    HasOrderedSchurWord N A := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero =>
      refine ⟨[], rfl, 0, trivial, ?_, ?_, 1, ?_⟩
      · simp [schurWordOmega]
      · simp [SchurWordOrdered, schurWordHeadRoots]
      · exact Subsingleton.elim _ _
    | succ n =>
      obtain ⟨μ, hμ, him, hmin⟩ := exists_least_nonneg_root (n+1) (by omega) A
      rcases lt_or_eq_of_le him with hpos | hzero
      · obtain ⟨h2, b, c, hc, hcb, hbc, Q, htop, hlo⟩ :=
          prescribed_upper_schur_block (n+1) A μ hμ hpos
        have hroot := schurRoot_eq_prescribed μ b c hbc hpos.le
        refine hasOrderedSchurWord_step (d:=2) (m:=n+1-2) (by omega) A Q h2
          (schurBlock μ.re b c) μ hmin htop hlo ?_ (fun D => ih (n+1-2) (by omega) D)
        intro U D hD hminD
        apply hasOrderedSchurWord_pair_upper μ.re b c U D hc hcb hD
        simpa only [hroot] using hminD
      · have hreal : (μ.re : ℂ) = μ := by
          apply Complex.ext
          · rfl
          · simpa using hzero
        have ha : (μ.re : ℂ) ∈ (A.charpoly.map Complex.ofRealHom).roots := hreal.symm ▸ hμ
        obtain ⟨Q, hentry, hlo⟩ := prescribed_real_schur_block n A μ.re ha
        have h1 : 1 ≤ n+1 := by omega
        have htop : ((Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵀ * A *
            (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)).submatrix
              (Fin.castLE h1) (Fin.castLE h1) = scalarBlock μ.re := by
          ext i j
          fin_cases i
          fin_cases j
          exact hentry
        have hlo' : ∀ (i : Fin (n+1)) (j : Fin 1), 1 ≤ i.val →
            ((Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ᵀ * A *
              (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) i (Fin.castLE h1 j) = 0 := by
          intro i j hi
          fin_cases j
          exact hlo i hi
        refine hasOrderedSchurWord_step (d:=1) (m:=n) (by omega) A Q h1
          (scalarBlock μ.re) μ hmin htop hlo' ?_ (fun D => ih n (by omega) D)
        intro U D hD hminD
        apply hasOrderedSchurWord_scalar_upper μ.re U D hD
        simpa only [hreal] using hminD

/-- Sorted representative lists are uniquely determined by the full root multiset. -/
theorem ordered_schurWordHeadRoots_eq (w v : List Bool)
    (p : SchurWordCells w) (q : SchurWordCells v)
    (hp : SchurWordPositive w p) (hq : SchurWordPositive v q)
    (hop : SchurWordOrdered w p) (hoq : SchurWordOrdered v q)
    (hr : schurWordRoots w p = schurWordRoots v q) :
    schurWordHeadRoots w p = schurWordHeadRoots v q := by
  have he : (schurWordHeadRoots w p : Multiset ℂ) = (schurWordHeadRoots v q : Multiset ℂ) := by
    rw [schurWordHeadRoots_eq_filter w p hp, schurWordHeadRoots_eq_filter v q hq, hr]
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => schurRootKey_injective (le_antisymm hab hba)) hop hoq
    (Multiset.coe_eq_coe.mp he)

/-- The representative imaginary parts recover every scalar/pair tag. -/
theorem map_upper_schurWordHeadRoots (w : List Bool) :
    ∀ p : SchurWordCells w, SchurWordPositive w p →
      (schurWordHeadRoots w p).map (fun z : ℂ => decide (0 < z.im)) = w := by
  classical
  induction w with
  | nil => intro p _; rfl
  | cons b w ih =>
    cases b <;> intro p hp
    · simpa [schurWordHeadRoots] using congrArg (List.cons false) (ih _ hp)
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let z := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
      change 0 < h (1,0) ∧ h (1,0) ≤ h (0,1) ∧
        SchurWordPositive w (schurTailInput x) at hp
      obtain ⟨hc, hcb, ht⟩ := hp
      have hz : 0 < z.im := Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hc hcb) hc)
      change (z :: schurWordHeadRoots w (schurTailInput x)).map _ = true :: w
      simp only [List.map_cons, decide_eq_true hz, ih _ ht]

/-- The ordered block word is fixed by the full root multiset, including multiplicities. -/
theorem ordered_schurWord_eq (w v : List Bool)
    (p : SchurWordCells w) (q : SchurWordCells v)
    (hp : SchurWordPositive w p) (hq : SchurWordPositive v q)
    (hop : SchurWordOrdered w p) (hoq : SchurWordOrdered v q)
    (hr : schurWordRoots w p = schurWordRoots v q) : w = v := by
  have h := congrArg (List.map (fun z : ℂ => decide (0 < z.im)))
    (ordered_schurWordHeadRoots_eq w v p q hp hq hop hoq hr)
  simpa only [map_upper_schurWordHeadRoots w p hp, map_upper_schurWordHeadRoots v q hq] using h

end Paper.Spectral
