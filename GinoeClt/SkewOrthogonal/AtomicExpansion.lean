/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.AtomicSubsets

/-! # Finite atomic Pfaffian expansion in actual canonical and feature pairs -/
@[expose] public section
noncomputable section
open scoped BigOperators
open Equiv

namespace Paper.SkewOrthogonal

/-- A concrete order on baseline/atom labels, inherited from their finite concatenation. -/
@[instance_reducible] def baselineAtomOrder (m r : ℕ) : LinearOrder (Fin m ⊕ Fin r) :=
  LinearOrder.lift' (finSumFinEquiv : Fin m ⊕ Fin r ≃ Fin (m + r)) finSumFinEquiv.injective

local instance (m r : ℕ) : LinearOrder (Fin m ⊕ Fin r) := baselineAtomOrder m r

/-- The first labels supply actual canonical columns, the others the given feature pairs. -/
def augmentedPairFeature {m r : ℕ} (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    (Fin m ⊕ Fin r) → PairedIndex m → Fin 2 → ℂ :=
  Sum.elim (fun i p side ↦ if p = (i, side) then 1 else 0) A

/-- The canonical equivalence for a finite disjoint sum of selected labels. -/
def disjSumSubtypeEquiv {α β : Type*} (s : Finset α) (t : Finset β) :
    s ⊕ t ≃ s.disjSum t where
  toFun x := match x with
    | Sum.inl x => ⟨Sum.inl x.val, by simp⟩
    | Sum.inr x => ⟨Sum.inr x.val, by simp⟩
  invFun x := match x with
    | ⟨Sum.inl a, ha⟩ => Sum.inl ⟨a, by simpa using ha⟩
    | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, by simpa using hb⟩
  left_inv x := by rcases x with ⟨x, hx⟩ | ⟨x, hx⟩ <;> rfl
  right_inv x := by rcases x with ⟨x | x, hx⟩ <;> rfl

/-- Selected and missing baseline pairs partition the actual row labels. -/
def baselineRowPartition {m : ℕ} (T : Finset (Fin m)) :
    Fin Tᶜ.card ⊕ Fin T.card ≃ Fin m :=
  let eT : T ≃ {i : Fin m // ¬i ∈ Tᶜ} := Equiv.subtypeEquivRight (fun i ↦ by simp)
  (Equiv.sumCongr (PfaffianMinor.sortedPairEquiv Tᶜ rfl)
    ((PfaffianMinor.sortedPairEquiv T rfl).trans eT)).trans (Equiv.sumCompl (· ∈ Tᶜ))

/-- The selected canonical columns followed by selected atom columns. -/
def selectedColumnPartition {m r : ℕ} (T : Finset (Fin m)) (S : Finset (Fin r))
    (h : S.card = T.card) : Fin Tᶜ.card ⊕ Fin T.card ≃ Tᶜ.disjSum S :=
  (Equiv.sumCongr (PfaffianMinor.sortedPairEquiv Tᶜ rfl)
    (PfaffianMinor.sortedPairEquiv S h)).trans (disjSumSubtypeEquiv Tᶜ S)

/-- The literal square feature submatrix on the missing baseline and selected atom pairs.
Unequal cardinalities are an internal zero extension. -/
def selectedFeatureDet {m r : ℕ} (A : Fin r → PairedIndex m → Fin 2 → ℂ)
    (T : Finset (Fin m)) (S : Finset (Fin r)) : ℂ :=
  if h : S.card = T.card then Matrix.det (fun p q : PairedIndex T.card ↦
    A (PfaffianMinor.sortedPairEquiv S h q.1).val
      ((PfaffianMinor.sortedPairEquiv T rfl p.1).val, p.2) q.2) else 0

/-- The actual selected determinant in the first ADMS step reduces exactly to
its missing-row/selected-feature determinant, with positive sign. -/
theorem augmentedPairFeature_selectedDet {m r : ℕ}
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (T : Finset (Fin m))
    (S : Finset (Fin r)) (h : S.card = T.card) :
    PfaffianMinor.selectedPairDetFinset
      (fun x i side ↦ augmentedPairFeature A x ((PfaffianMinor.pairColumnEquiv m).symm i) side)
      (Tᶜ.disjSum S) = selectedFeatureDet A T S := by
  have hb (i : Fin Tᶜ.card) (p : PairedIndex m) (side : Fin 2) :
      augmentedPairFeature A ((selectedColumnPartition T S h) (Sum.inl i)).val p side =
        if p = (baselineRowPartition T (Sum.inl i), side) then 1 else 0 := by
    simp [augmentedPairFeature, selectedColumnPartition, disjSumSubtypeEquiv,
      baselineRowPartition]
  have hd := selectedPairDetFinset_complement (augmentedPairFeature A)
    (Tᶜ.disjSum S) (baselineRowPartition T) (selectedColumnPartition T S h) hb
  simpa [selectedFeatureDet, h, augmentedPairFeature, selectedColumnPartition,
    disjSumSubtypeEquiv, baselineRowPartition] using! hd

theorem baseline_wedge_sum {m : ℕ} (w : Fin m → ℂ) (p q : PairedIndex m) :
    (∑ i : Fin m, w i *
      ((if p = (i, 0) then 1 else 0) * (if q = (i, 1) then 1 else 0) -
        (if p = (i, 1) then 1 else 0) * (if q = (i, 0) then 1 else 0))) =
      interlacedMatrix (Matrix.diagonal w) p q := by
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;>
    simp [interlacedMatrix, Matrix.diagonal, h, eq_comm]

/-- The literal normalized-base Gram matrix with finite rank-two atom updates. -/
def finiteAtomicGram {m r : ℕ} (w : Fin m → ℂ) (c : Fin r → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) : Matrix (PairedIndex m) (PairedIndex m) ℂ :=
  fun p q ↦ interlacedMatrix (Matrix.diagonal w) p q +
    ∑ x : Fin r, c x * (A x p 0 * A x q 1 - A x p 1 * A x q 0)

theorem finiteAtomicGram_eq_wedges {m r : ℕ} (w : Fin m → ℂ) (c : Fin r → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    finiteAtomicGram w c A = fun p q ↦ ∑ x : Fin m ⊕ Fin r,
      Sum.elim w c x * (augmentedPairFeature A x p 0 * augmentedPairFeature A x q 1 -
        augmentedPairFeature A x p 1 * augmentedPairFeature A x q 0) := by
  ext p q
  rw [Fintype.sum_sum_type]
  simp only [augmentedPairFeature, Sum.elim_inl, Sum.elim_inr]
  rw [baseline_wedge_sum]
  rfl

/-- First ADMS expansion, canonical pair elimination and exact subset regrouping.
The result is an ordinary finite identity; no ensemble or measure law is assumed. -/
theorem pfaffian_finiteAtomicGram_expansion {m r : ℕ}
    (w : Fin m → ℂ) (c : Fin r → ℂ) (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    pfaffian (finiteAtomicGram w c A) =
      ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∑ S ∈ (Finset.univ : Finset (Fin r)).powersetCard T.card,
          ((∏ i ∈ Tᶜ, w i) * (∏ x ∈ S, c x)) * selectedFeatureDet A T S := by
  rw [finiteAtomicGram_eq_wedges, pfaffian_finite_wedges]
  unfold PfaffianMinor.finsetADMSRhs
  rw [sum_powersetCard_disjSum_compl]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro S hS
  have hc := (Finset.mem_powersetCard.mp hS).2
  rw [augmentedPairFeature_selectedDet A T S hc, Finset.prod_disjSum]
  rfl

theorem selectedFeatureDet_eq_of_card {m r k : ℕ}
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (T : Finset (Fin m))
    (S : Finset (Fin r)) (hT : T.card = k) (hS : S.card = k) :
    selectedFeatureDet A T S = Matrix.det (fun p q : PairedIndex k ↦
      A (PfaffianMinor.sortedPairEquiv S hS q.1).val
        ((PfaffianMinor.sortedPairEquiv T hT p.1).val, p.2) q.2) := by
  subst k
  simp only [selectedFeatureDet, dite_eq_left hS]

/-- The literal dual feature contraction against the reciprocal base skew norms. -/
def atomicFeatureKernel {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) : Matrix (PairedIndex r) (PairedIndex r) ℂ :=
  fun p q ↦ ∑ i : Fin m, (w i)⁻¹ *
    (A p.1 (i, 0) p.2 * A q.1 (i, 1) q.2 - A p.1 (i, 1) p.2 * A q.1 (i, 0) q.2)

/-- The actual principal atom blocks selected by S. -/
def selectedAtomicKernel {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (S : Finset (Fin r)) :
    Matrix (PairedIndex S.card) (PairedIndex S.card) ℂ :=
  (atomicFeatureKernel w A).submatrix
    (fun p ↦ ((PfaffianMinor.sortedPairEquiv S rfl p.1).val, p.2))
    (fun p ↦ ((PfaffianMinor.sortedPairEquiv S rfl p.1).val, p.2))

/-- The second ADMS application identifies each actual kernel Pfaffian.
Its transpose determinant has positive sign and no multiplicity factor. -/
theorem pfaffian_selectedAtomicKernel {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (S : Finset (Fin r)) :
    pfaffian (selectedAtomicKernel w A S) =
      ∑ T ∈ (Finset.univ : Finset (Fin m)).powersetCard S.card,
        (∏ i ∈ T, (w i)⁻¹) * selectedFeatureDet A T S := by
  let Z : Fin m → PairedIndex S.card → Fin 2 → ℂ := fun i p side ↦
    A (PfaffianMinor.sortedPairEquiv S rfl p.1).val (i, side) p.2
  change pfaffian (fun p q ↦ ∑ i : Fin m, (w i)⁻¹ *
    (Z i p 0 * Z i q 1 - Z i p 1 * Z i q 0)) = _
  rw [pfaffian_finite_wedges]
  unfold PfaffianMinor.finsetADMSRhs
  apply Finset.sum_congr rfl
  intro T hT
  have hc := (Finset.mem_powersetCard.mp hT).2
  let eT := PfaffianMinor.sortedPairEquiv T hc
  rw [selectedPairDetFinset_eq_of_equiv _ T eT, selectedFeatureDet_eq_of_card A T S hc rfl]
  congr 1
  let M : Matrix (PairedIndex S.card) (PairedIndex S.card) ℂ := fun p q ↦
    A (PfaffianMinor.sortedPairEquiv S rfl q.1).val
      ((PfaffianMinor.sortedPairEquiv T hc p.1).val, p.2) q.2
  have hm : (selectedPairMatrixOfEquiv
      (fun i row side ↦ Z i ((PfaffianMinor.pairColumnEquiv S.card).symm row) side) T eT).submatrix
        (PfaffianMinor.pairColumnEquiv S.card) (PfaffianMinor.pairColumnEquiv S.card) = M.transpose := by
    ext p q
    simp only [Matrix.submatrix_apply, selectedPairMatrixOfEquiv,
      Equiv.symm_apply_apply, Matrix.transpose_apply]
    rfl
  rw [← Matrix.det_submatrix_equiv_self (PfaffianMinor.pairColumnEquiv S.card), hm,
    Matrix.det_transpose]

/-- Exchange equally sized missing-base and selected-atom subsets exactly. -/
theorem sum_equalCard_subsets_swap {B : Type*} [AddCommMonoid B]
    (m r : ℕ) (F : Finset (Fin m) → Finset (Fin r) → B) :
    (∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
      ∑ S ∈ (Finset.univ : Finset (Fin r)).powersetCard T.card, F T S) =
      ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
        ∑ T ∈ (Finset.univ : Finset (Fin m)).powersetCard S.card, F T S := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun P _ ↦ ⟨P.2, P.1⟩) (fun P _ ↦ ⟨P.2, P.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rcases Finset.mem_sigma.mp hP with ⟨hT, hS⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hS).2.symm⟩
  · intro P hP
    rcases Finset.mem_sigma.mp hP with ⟨hS, hT⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hT).2.symm⟩
  · intro P hP
    rfl
  · intro P hP
    rfl
  · intro P hP
    rfl

theorem complement_prod_eq {m : ℕ} (w : Fin m → ℂ) (hw : ∀ i, w i ≠ 0)
    (T : Finset (Fin m)) :
    (∏ i ∈ Tᶜ, w i) = (∏ i : Fin m, w i) * ∏ i ∈ T, (w i)⁻¹ := by
  have hn : (∏ i ∈ T, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi ↦ hw i)
  rw [Finset.prod_inv_distrib, ← Finset.prod_compl_mul_prod T w,
    mul_assoc, mul_inv_cancel₀ hn, mul_one]

/-- The complete finite atomic generating-Pfaffian identity, before division.
All complex atom coefficients are arbitrary; only base skew norms must be nonzero. -/
theorem pfaffian_finiteAtomicGram {m r : ℕ} (w : Fin m → ℂ) (hw : ∀ i, w i ≠ 0)
    (c : Fin r → ℂ) (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    pfaffian (finiteAtomicGram w c A) = (∏ i : Fin m, w i) *
      ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
        (∏ x ∈ S, c x) * pfaffian (selectedAtomicKernel w A S) := by
  rw [pfaffian_finiteAtomicGram_expansion]
  simp_rw [complement_prod_eq w hw]
  rw [sum_equalCard_subsets_swap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [pfaffian_selectedAtomicKernel, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  ring

/-- The finite matrix ratio in the source generating-polynomial route.
The denominator is the actual, proved nonzero normalized-base Gram Pfaffian. -/
theorem pfaffian_finiteAtomicGram_ratio {m r : ℕ} (w : Fin m → ℂ) (hw : ∀ i, w i ≠ 0)
    (c : Fin r → ℂ) (A : Fin r → PairedIndex m → Fin 2 → ℂ) :
    pfaffian (finiteAtomicGram w c A) /
        pfaffian (interlacedMatrix (Matrix.diagonal w)) =
      ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
        (∏ x ∈ S, c x) * pfaffian (selectedAtomicKernel w A S) := by
  rw [pfaffian_interlacedMatrix_det, Matrix.det_diagonal, pfaffian_finiteAtomicGram w hw]
  have hn : (∏ i : Fin m, w i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi ↦ hw i)
  exact mul_div_cancel_left₀ _ hn

end Paper.SkewOrthogonal
