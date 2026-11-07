/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.FiniteWedges

/-! # Actual selected-pair determinants and their enumeration

This is finite algebra for the two minor-summation steps in the atomic
Pfaffian update. Whole adjacent pair permutations have positive sign.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
open Equiv

namespace Paper.SkewOrthogonal

/-- The literal selected matrix for any bijective enumeration of the pair labels. -/
def selectedPairMatrixOfEquiv {ι : Type*} {m : ℕ}
    (Z : ι → Fin (2 * m) → Fin 2 → ℂ) (s : Finset ι) (e : Fin m ≃ s) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  fun i j ↦ let q := (PfaffianMinor.pairColumnEquiv m).symm j
    Z (e q.1).val i q.2

theorem pairColumnPerm_apply {m : ℕ} (σ : Perm (Fin m)) (i : Fin m) (a : Fin 2) :
    ((PfaffianMinor.pairColumnEquiv m).permCongr (Pfaffian.basePerm σ σ))
      (PfaffianMinor.pairColumnEquiv m (i, a)) =
        PfaffianMinor.pairColumnEquiv m (σ i, a) := by
  simp [Equiv.permCongr_apply, Pfaffian.basePerm, Equiv.prodCongrLeft]

/-- The actual ADMS selected determinant is independent of pair enumeration.
No sign or cardinality factor is introduced, including for the empty selection. -/
theorem selectedPairDetFinset_eq_of_equiv {ι : Type*} [LinearOrder ι] {m : ℕ}
    (Z : ι → Fin (2 * m) → Fin 2 → ℂ) (s : Finset ι) (e : Fin m ≃ s) :
    PfaffianMinor.selectedPairDetFinset Z s = (selectedPairMatrixOfEquiv Z s e).det := by
  have hs : s.card = m := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr e).symm
  let e₀ := PfaffianMinor.sortedPairEquiv s hs
  let σ : Perm (Fin m) := e.trans e₀.symm
  let τ : Perm (Fin (2 * m)) :=
    (PfaffianMinor.pairColumnEquiv m).permCongr (Pfaffian.basePerm σ σ)
  have hM : selectedPairMatrixOfEquiv Z s e =
      (PfaffianMinor.selectedPairMatrix Z (PfaffianMinor.sortedPairVectorOfCard s hs)).submatrix id τ := by
    ext i j
    obtain ⟨⟨q, a⟩, rfl⟩ := (PfaffianMinor.pairColumnEquiv m).surjective j
    simp only [selectedPairMatrixOfEquiv, Equiv.symm_apply_apply, Matrix.submatrix_apply,
      id_eq, τ, pairColumnPerm_apply, PfaffianMinor.selectedPairMatrix_apply]
    change Z (e q).val i a = Z (e₀ (σ q)).val i a
    have he : e₀ (σ q) = e q := by simp [σ]
    rw [he]
  rw [PfaffianMinor.selectedPairDetFinset_eq Z s hs]
  change (PfaffianMinor.selectedPairMatrix Z (PfaffianMinor.sortedPairVectorOfCard s hs)).det = _
  rw [hM, Matrix.det_permute']
  have hsign : Perm.sign τ = 1 := by
    change Perm.sign ((PfaffianMinor.pairColumnEquiv m).permCongr (Pfaffian.basePerm σ σ)) = 1
    rw [Perm.sign_permCongr, Pfaffian.sign_basePerm, Int.units_mul_self]
  rw [hsign]
  simp

theorem det_pairRow_permute {m : ℕ} (M : Matrix (PairedIndex m) (PairedIndex m) ℂ)
    (σ : Perm (Fin m)) : (M.submatrix (Pfaffian.basePerm σ σ) id).det = M.det := by
  rw [Matrix.det_permute]
  have hs : Perm.sign (Pfaffian.basePerm σ σ) = 1 := by
    rw [Pfaffian.sign_basePerm, Int.units_mul_self]
  rw [hs]
  simp

/-- Split a prefix of pair labels, retaining both sides of each adjacent pair. -/
def splitPairedAdd (a b : ℕ) : PairedIndex (a + b) ≃ PairedIndex a ⊕ PairedIndex b :=
  (Equiv.prodCongr (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).symm
    (Equiv.refl (Fin 2))).trans (Equiv.sumProdDistrib (Fin a) (Fin b) (Fin 2))

@[simp] theorem splitPairedAdd_symm_inl (a b : ℕ) (p : PairedIndex a) :
    (splitPairedAdd a b).symm (Sum.inl p) = (Fin.castAdd b p.1, p.2) := rfl

@[simp] theorem splitPairedAdd_symm_inr (a b : ℕ) (p : PairedIndex b) :
    (splitPairedAdd a b).symm (Sum.inr p) = (Fin.natAdd a p.1, p.2) := rfl

/-- Actual identity columns in the first a pairs, followed by b arbitrary feature pairs. -/
def prefixPairMatrix (a b : ℕ) (F : Matrix (PairedIndex (a + b)) (PairedIndex b) ℂ) :
    Matrix (PairedIndex (a + b)) (PairedIndex (a + b)) ℂ :=
  fun p q ↦ Fin.addCases
    (fun i : Fin a ↦ if p = (Fin.castAdd b i, q.2) then 1 else 0)
    (fun j : Fin b ↦ F p (j, q.2)) q.1

theorem prefixPairMatrix_reindex (a b : ℕ)
    (F : Matrix (PairedIndex (a + b)) (PairedIndex b) ℂ) :
    (prefixPairMatrix a b F).submatrix (splitPairedAdd a b).symm (splitPairedAdd a b).symm =
      Matrix.fromBlocks 1 (fun p q ↦ F (Fin.castAdd b p.1, p.2) q) 0
        (fun p q ↦ F (Fin.natAdd a p.1, p.2) q) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q
  · simp [prefixPairMatrix, Matrix.fromBlocks, Matrix.one_apply, Prod.ext_iff, Fin.ext_iff]
  · simp [prefixPairMatrix, Matrix.fromBlocks]
  · have hn : Fin.natAdd a p.1 ≠ Fin.castAdd b q.1 := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [prefixPairMatrix, Matrix.fromBlocks, hn]
  · simp [prefixPairMatrix, Matrix.fromBlocks]

/-- Eliminating whole canonical pairs has positive sign, in every size. -/
theorem det_prefixPairMatrix (a b : ℕ)
    (F : Matrix (PairedIndex (a + b)) (PairedIndex b) ℂ) :
    (prefixPairMatrix a b F).det =
      Matrix.det (fun p q : PairedIndex b ↦ F (Fin.natAdd a p.1, p.2) q) := by
  rw [← Matrix.det_submatrix_equiv_self (splitPairedAdd a b).symm (prefixPairMatrix a b F),
    prefixPairMatrix_reindex]
  simpa only [Matrix.det_one, one_mul] using! Matrix.det_fromBlocks_zero₂₁
    (1 : Matrix (PairedIndex a) (PairedIndex a) ℂ)
    (fun p q ↦ F (Fin.castAdd b p.1, p.2) q)
    (fun p q ↦ F (Fin.natAdd a p.1, p.2) q)

/-- Eliminate any selected canonical pair columns. The two explicit bijections
partition the original rows and the selected columns; no sorted-order convention
or sign is hidden in this statement. -/
theorem selectedPairDetFinset_complement {ι : Type*} [LinearOrder ι]
    {m a b : ℕ} (Z : ι → PairedIndex m → Fin 2 → ℂ) (s : Finset ι)
    (rows : Fin a ⊕ Fin b ≃ Fin m) (cols : Fin a ⊕ Fin b ≃ s)
    (hbase : ∀ (i : Fin a) (p : PairedIndex m) (side : Fin 2),
      Z (cols (Sum.inl i)).val p side = if p = (rows (Sum.inl i), side) then 1 else 0) :
    PfaffianMinor.selectedPairDetFinset
      (fun x i side ↦ Z x ((PfaffianMinor.pairColumnEquiv m).symm i) side) s =
      Matrix.det (fun p q : PairedIndex b ↦
        Z (cols (Sum.inr q.1)).val (rows (Sum.inr p.1), p.2) q.2) := by
  let e : Fin m ≃ s := rows.symm.trans cols
  let r : Fin (a + b) ≃ Fin m :=
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).symm.trans rows
  let E : PairedIndex (a + b) ≃ Fin (2 * m) :=
    (Equiv.prodCongr r (Equiv.refl (Fin 2))).trans (PfaffianMinor.pairColumnEquiv m)
  let F : Matrix (PairedIndex (a + b)) (PairedIndex b) ℂ :=
    fun p q ↦ Z (cols (Sum.inr q.1)).val (r p.1, p.2) q.2
  have he (u : Fin a ⊕ Fin b) : e (r (finSumFinEquiv u)) = cols u := by
    simp [e, r]
  have hr (i : Fin a) : r (Fin.castAdd b i) = rows (Sum.inl i) := by simp [r]
  have hF : (selectedPairMatrixOfEquiv
      (fun x i side ↦ Z x ((PfaffianMinor.pairColumnEquiv m).symm i) side) s e).submatrix E E =
        prefixPairMatrix a b F := by
    ext p q
    simp only [selectedPairMatrixOfEquiv, Matrix.submatrix_apply, E, Equiv.trans_apply,
      Equiv.prodCongr_apply, Equiv.symm_apply_apply, prefixPairMatrix]
    change Z (e (r q.1)).val (r p.1, p.2) q.2 =
      Fin.addCases (fun i : Fin a ↦ if p = (Fin.castAdd b i, q.2) then 1 else 0)
        (fun j : Fin b ↦ F p (j, q.2)) q.1
    obtain ⟨v, hv⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective q.1
    rcases q with ⟨q, side⟩
    dsimp only at hv ⊢
    subst q
    rcases v with i | j
    · rw [he]
      simp only [finSumFinEquiv_apply_left, Fin.addCases_left, hbase]
      have hi : ((r p.1, p.2) = (rows (Sum.inl i), side)) ↔ p = (Fin.castAdd b i, side) := by
        rw [← hr]
        constructor
        · intro h
          exact Prod.ext (r.injective (congrArg (fun x : Fin m × Fin 2 ↦ x.1) h))
            (congrArg (fun x : Fin m × Fin 2 ↦ x.2) h)
        · intro h
          rw [h]
      simp only [hi]
    · rw [he]
      simp only [finSumFinEquiv_apply_right, Fin.addCases_right, F]
  rw [selectedPairDetFinset_eq_of_equiv _ s e,
    ← Matrix.det_submatrix_equiv_self E, hF, det_prefixPairMatrix]
  congr 1
  funext p q
  simp [F, r]

end Paper.SkewOrthogonal
