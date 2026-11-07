/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.BoundedAngularMass
public import Mathlib.Order.Disjointed
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped Matrix Matrix.Norms.Elementwise BigOperators
namespace Paper.Spectral

/-- Actual ambient target pieces assigned to their first covering chart. -/
def boundedOrthogonalTargetPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) (i : Fin (m+1)) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  disjointed (fun j => boundedOrthogonalCayleyNeighborhood N (centers j)) i

theorem boundedOrthogonalTargetPiece_subset {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) (i : Fin (m+1)) :
    boundedOrthogonalTargetPiece centers i ⊆ boundedOrthogonalCayleyNeighborhood N (centers i) :=
  disjointed_subset _ i

theorem disjoint_boundedOrthogonalTargetPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) :
    Pairwise (Disjoint on boundedOrthogonalTargetPiece centers) :=
  disjoint_disjointed _

theorem iUnion_boundedOrthogonalTargetPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) :
    (⋃ i, boundedOrthogonalTargetPiece centers i) =
      ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i) :=
  iUnion_disjointed

theorem measurableSet_boundedOrthogonalTargetPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) (i : Fin (m+1)) :
    MeasurableSet (boundedOrthogonalTargetPiece centers i) := by
  rw [boundedOrthogonalTargetPiece,disjointed_eq_inter_compl]
  apply (isOpen_boundedOrthogonalCayleyNeighborhood N (centers i)).measurableSet.inter
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (isOpen_boundedOrthogonalCayleyNeighborhood N (centers j)).measurableSet.compl

theorem boundedOrthogonalTargetPiece_zero {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) :
    boundedOrthogonalTargetPiece centers 0 = boundedOrthogonalCayleyNeighborhood N (centers 0) := by
  exact disjointed_bot _

/-- The finite cover is enumerated by a nonempty ordinary Fin type. -/
theorem exists_finite_bounded_orthogonal_target_atlas (N : ℕ) :
    ∃ m : ℕ, ∃ centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ,
      ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
        M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i) := by
  classical
  obtain ⟨t,ht⟩ := exists_finite_bounded_orthogonal_cayley_cover N
  have hone : (1 : Matrix (Fin N) (Fin N) ℝ) *
      (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ = 1 := by simp
  obtain ⟨Q,hQt,_⟩ := mem_iUnion₂.mp (ht hone)
  have hp : 0 < t.card := Finset.card_pos.mpr ⟨Q,hQt⟩
  let m := t.card-1
  have hm : t.card = m+1 := by dsimp [m]; omega
  let e : ↥t ≃ Fin (m+1) := Fintype.equivFinOfCardEq (by simpa using hm)
  let centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ := fun i => (e.symm i).val
  refine ⟨m,centers,?_⟩
  intro M hM
  obtain ⟨Q,hQ,hMQ⟩ := mem_iUnion₂.mp (ht hM)
  let i := e ⟨Q,hQ⟩
  have hi : centers i = Q := by
    change (e.symm (e ⟨Q,hQ⟩)).val = Q
    rw [e.symm_apply_apply]
  apply mem_iUnion.mpr
  refine ⟨i,?_⟩
  rw [hi]
  exact hMQ

/-- Every covered orthogonal frame receives exactly one target chart index. -/
theorem unique_boundedOrthogonalTargetPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i)) :
    ∃! i : Fin (m+1), M ∈ boundedOrthogonalTargetPiece centers i := by
  have hu : M ∈ ⋃ i, boundedOrthogonalTargetPiece centers i := by
    rwa [iUnion_boundedOrthogonalTargetPiece]
  obtain ⟨i,hi⟩ := mem_iUnion.mp hu
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  exact (Set.disjoint_left.mp (disjoint_boundedOrthogonalTargetPiece centers hji)) hj hi

/-- The actual left-translated bounded-chart frame in native lower coordinates. -/
def boundedAngularFrame (N : ℕ) (Q : Matrix.orthogonalGroup (Fin N) ℝ)
    (a : SkewIndex N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (Q : Matrix (Fin N) (Fin N) ℝ) * cayleyMatrix N (skewFromCoordinates N a)

theorem continuous_boundedAngularFrame (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) : Continuous (boundedAngularFrame N Q) := by
  unfold boundedAngularFrame cayleyMatrix
  exact continuous_const.mul
    ((continuous_cayleyInverseDenominator_coordinates N).mul
      (continuous_const.add ((continuous_skewFromCoordinates_matrix N).const_smul (1/2 : ℝ))))

theorem boundedAngularFrame_mem_ownNeighborhood (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) (a : SkewIndex N → ℝ)
    (ha : a ∈ boundedAngularSource N) :
    boundedAngularFrame N Q a ∈ boundedOrthogonalCayleyNeighborhood N Q := by
  have hQ : (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (Q : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  change (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      ((Q : Matrix (Fin N) (Fin N) ℝ) * cayleyMatrix N (skewFromCoordinates N a)) ∈
    (boundedCayleyLocalHomeomorph N).target
  rw [← Matrix.mul_assoc,hQ,Matrix.one_mul]
  exact (boundedCayleyLocalHomeomorph N).map_source ha

/-- Source pieces are pulled back from the DISJOINT TARGET assignment. -/
def boundedAngularPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) (i : Fin (m+1)) :
    Set (SkewIndex N → ℝ) :=
  boundedAngularSource N ∩ (boundedAngularFrame N (centers i)) ⁻¹'
    boundedOrthogonalTargetPiece centers i

theorem measurableSet_boundedAngularPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) (i : Fin (m+1)) :
    MeasurableSet (boundedAngularPiece centers i) :=
  (isOpen_boundedAngularSource N).measurableSet.inter
    ((measurableSet_boundedOrthogonalTargetPiece centers i).preimage
      (continuous_boundedAngularFrame N (centers i)).measurable)

theorem boundedAngularPiece_zero {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) :
    boundedAngularPiece centers 0 = boundedAngularSource N := by
  apply Set.inter_eq_left.mpr
  intro a ha
  change boundedAngularFrame N (centers 0) a ∈ boundedOrthogonalTargetPiece centers 0
  rw [boundedOrthogonalTargetPiece_zero]
  exact boundedAngularFrame_mem_ownNeighborhood N (centers 0) a ha

theorem integrableOn_boundedAngularPiece {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) (i : Fin (m+1)) :
    IntegrableOn (fun a : SkewIndex N → ℝ => cayleyAngularJacobian N (skewFromCoordinates N a))
      (boundedAngularPiece centers i) volume :=
  (integrableOn_boundedAngularJacobian N).mono_set inter_subset_left

/-- A finite positive, word-independent sum using actual disjoint target pieces.
It is not an assumed Haar mass or a chartwise gauge multiplicity. -/
def boundedAtlasAngularMass {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) : ℝ :=
  ∑ i : Fin (m+1), ∫ a in boundedAngularPiece centers i,
    cayleyAngularJacobian N (skewFromCoordinates N a)

theorem boundedAtlasAngularMass_pos {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) :
    0 < boundedAtlasAngularMass centers := by
  unfold boundedAtlasAngularMass
  apply Finset.sum_pos'
  · intro i _
    exact integral_nonneg (fun a => (cayleyAngularJacobian_pos N (skewFromCoordinates N a)).le)
  · refine ⟨0,Finset.mem_univ _,?_⟩
    rw [boundedAngularPiece_zero]
    exact boundedAngularMass_pos N


/-- The actual relative Cayley bijection makes native bounded angular coordinates injective. -/
theorem boundedAngularFrame_injOn (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    Set.InjOn (boundedAngularFrame N Q) (boundedAngularSource N) := by
  intro a ha b hb he
  have hQ : (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (Q : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  have hc := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
    (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M) he
  have hC : cayleyMatrix N (skewFromCoordinates N a) =
      cayleyMatrix N (skewFromCoordinates N b) := by
    simpa only [boundedAngularFrame,← Matrix.mul_assoc,hQ,Matrix.one_mul] using hc
  have hΩ : (skewFromCoordinates N a : Matrix (Fin N) (Fin N) ℝ) =
      (skewFromCoordinates N b : Matrix (Fin N) (Fin N) ℝ) :=
    (bounded_cayley_relative_bijOn N).injOn
      ⟨ha,skewMatrix_transpose N (skewFromCoordinates N a)⟩
      ⟨hb,skewMatrix_transpose N (skewFromCoordinates N b)⟩ hC
  apply (skewCoordinateEquiv N).injective
  apply Subtype.ext
  exact hΩ

/-- An actual covered orthogonal frame has bounded native angular coordinates. -/
theorem exists_boundedAngularFrame_coordinates (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M * Mᵀ = 1) (hc : M ∈ boundedOrthogonalCayleyNeighborhood N Q) :
    ∃ a : SkewIndex N → ℝ, a ∈ boundedAngularSource N ∧ boundedAngularFrame N Q a = M := by
  have hQQ : (Q : Matrix (Fin N) (Fin N) ℝ) *
      (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp Q.property
  have hQtQ : (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (Q : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  have hP : ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M) *
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M)ᵀ = 1 := by
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    calc
      _ = (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * (M * Mᵀ) * Q := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM,Matrix.mul_one,hQtQ]
  obtain ⟨Ω,hΩ,hC⟩ := (bounded_cayley_relative_bijOn N).surjOn ⟨hc,hP⟩
  let ω : SkewMatrix N := ⟨Ω,by change Ωᵀ = -Ω; exact hΩ.2⟩
  let a := (skewCoordinateEquiv N).symm ω
  have hω : skewFromCoordinates N a = ω := (skewCoordinateEquiv N).apply_symm_apply ω
  have hΩa : (skewFromCoordinates N a : Matrix (Fin N) (Fin N) ℝ) = Ω :=
    congrArg Subtype.val hω
  refine ⟨a,?_,?_⟩
  · change (skewFromCoordinates N a : Matrix (Fin N) (Fin N) ℝ) ∈
      (boundedCayleyLocalHomeomorph N).source
    rw [hΩa]
    exact hΩ.1
  · unfold boundedAngularFrame
    rw [hΩa,hC,← Matrix.mul_assoc,hQQ,Matrix.one_mul]

/-- The WHOLE assigned angular family, with its chart index, gives a unique coordinate pair
for every orthogonal frame covered by the actual finite atlas. -/
theorem existsUnique_boundedAngularPair {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (M : Matrix (Fin N) (Fin N) ℝ) (hM : M * Mᵀ = 1) :
    ∃! p : Fin (m+1) × (SkewIndex N → ℝ),
      p.2 ∈ boundedAngularPiece centers p.1 ∧
        boundedAngularFrame N (centers p.1) p.2 = M := by
  obtain ⟨i,hi,hunique⟩ := unique_boundedOrthogonalTargetPiece centers M (hcover M hM)
  obtain ⟨a,ha,hframe⟩ := exists_boundedAngularFrame_coordinates N (centers i) M hM
    (boundedOrthogonalTargetPiece_subset centers i hi)
  have hpiece : a ∈ boundedAngularPiece centers i := by
    refine ⟨ha,?_⟩
    change boundedAngularFrame N (centers i) a ∈ boundedOrthogonalTargetPiece centers i
    rw [hframe]
    exact hi
  refine ⟨(i,a),⟨hpiece,hframe⟩,?_⟩
  rintro ⟨j,b⟩ hb
  have hj : M ∈ boundedOrthogonalTargetPiece centers j := by
    rw [← hb.2]
    exact hb.1.2
  have hji := hunique j hj
  subst j
  apply Prod.ext
  · rfl
  · exact boundedAngularFrame_injOn N (centers i) hb.1.1 ha (hb.2.trans hframe.symm)

end Paper.Spectral
