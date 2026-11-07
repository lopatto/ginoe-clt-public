/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasAlmostEverywhere
public import GinoeClt.Spectral.CanonicalSchurWord
public import Mathlib.Data.Set.Finite.List
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix ENNReal BigOperators
namespace Paper.Spectral

/-- All actual scalar/pair words of the specified physical size. -/
abbrev SchurWordsOfSize (N : ℕ) := {w : List Bool // schurWordSize w = N}

theorem schurWord_length_le_size (w : List Bool) : w.length ≤ schurWordSize w := by
  induction w with
  | nil => simp [schurWordSize]
  | cons b w ih =>
    cases b <;> simp only [List.length_cons,schurWordSize] <;> omega

instance instFintypeSchurWordsOfSize (N : ℕ) : Fintype (SchurWordsOfSize N) :=
  ((List.finite_length_le Bool N).subset (by
    intro w hw
    exact (schurWord_length_le_size w).trans_eq hw)).fintype

/-- Equality of physical dimensions transports literal cells without any rescaling. -/
def schurCellsCast {M N : ℕ} (h : M = N) :
    ((Fin M × Fin M) → ℝ) ≃ₗ[ℝ] ((Fin N × Fin N) → ℝ) := by
  subst N
  exact LinearEquiv.refl ℝ _

/-- The SAME physical orthogonal frame after equality of its index size. -/
def schurFrameCast {M N : ℕ} (h : M = N)
    (Q : Matrix.orthogonalGroup (Fin M) ℝ) : Matrix.orthogonalGroup (Fin N) ℝ :=
  h ▸ Q

/-- The actual assigned simple/regular atlas image in one COMMON matrix-cell space.
Noncanonical words are retained here; their ordered source will make their image empty. -/
def schurAtlasImageOfSize {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (w : SchurWordsOfSize N) : Set ((Fin N × Fin N) → ℝ) :=
  schurCellsCast w.property ''
    ⋃ i, (fun x => schurAtlasCells w.val
      (fun j => schurFrameCast w.property.symm (centers j)) (i,x)) ''
      {x | schurAtlasSimpleSource w.val
        (fun j => schurFrameCast w.property.symm (centers j)) (i,x)}

theorem measurableSet_schurAtlasImageOfSize {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (w : SchurWordsOfSize N) : MeasurableSet (schurAtlasImageOfSize centers w) := by
  rcases w with ⟨w,h⟩
  subst N
  change MeasurableSet (id '' ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
    {x | schurAtlasSimpleSource w centers (i,x)})
  rw [Set.image_id]
  apply MeasurableSet.iUnion
  intro i
  exact Paper.MeasureTheory.measurable_image_of_strict_derivative_det_ne_zero
    (fun x => schurAtlasCells w centers (i,x)) (schurAtlasCellsDerivative w centers i)
    (measurableSet_schurAtlasSimpleSource w centers i)
    (fun x _ => hasStrictFDerivAt_schurAtlasCells w centers i x)
    (fun x hx => schurAtlasCellsDerivative_det_ne_zero w centers i x hx.1)

/-- Literal cells and physical frames are transported by equal dimension alone. -/
theorem schurCellsCast_vec {M N : ℕ} (h : M = N)
    (A : Matrix (Fin M) (Fin M) ℝ) :
    schurCellsCast h (Matrix.vec A) =
      Matrix.vec (A.reindex (finCongr h) (finCongr h)) := by
  subst N
  rfl

/-- Exact real/upper root counts in each actual image, including multiplicities. -/
theorem schurAtlasImageOfSize_sector_counts {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (w : SchurWordsOfSize N) (y : (Fin N × Fin N) → ℝ)
    (hy : y ∈ schurAtlasImageOfSize centers w) :
    (((Matrix.of (fun i j => y (j,i))).charpoly.map Complex.ofRealHom).roots.filter
      (fun z : ℂ => 0 < z.im)).card = w.val.count true ∧
    (((Matrix.of (fun i j => y (j,i))).charpoly.map Complex.ofRealHom).roots.filter
      (fun z : ℂ => z.im = 0)).card = w.val.count false := by
  rcases w with ⟨w,h⟩
  subst N
  change y ∈ id '' ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
    {x | schurAtlasSimpleSource w centers (i,x)} at hy
  rw [Set.image_id] at hy
  rcases Set.mem_iUnion.mp hy with ⟨i,x,hx,hxy⟩
  subst y
  change (((schurAtlasMatrix w centers (i,x)).charpoly.map Complex.ofRealHom).roots.filter
      (fun z : ℂ => 0 < z.im)).card = w.count true ∧
    (((schurAtlasMatrix w centers (i,x)).charpoly.map Complex.ofRealHom).roots.filter
      (fun z : ℂ => z.im = 0)).card = w.count false
  rw [schurAtlasMatrix_charpoly]
  exact schurWordParameter_sector_counts w x hx.1.2.1

/-- Every nonempty ordered image belongs to the original canonical real/pair word. -/
theorem schurAtlasImageOfSize_word_canonical {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (w : SchurWordsOfSize N) {y : (Fin N × Fin N) → ℝ}
    (hy : y ∈ schurAtlasImageOfSize centers w) :
    w.val = List.replicate (w.val.count false) false ++ List.replicate (w.val.count true) true := by
  rcases w with ⟨w,h⟩
  subst N
  change y ∈ id '' ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
    {x | schurAtlasSimpleSource w centers (i,x)} at hy
  rw [Set.image_id] at hy
  rcases Set.mem_iUnion.mp hy with ⟨i,x,hx,_⟩
  exact ordered_schurWord_eq_canonical w x hx.1.2.1 hx.1.2.2.1

/-- Distinct words have disjoint ACTUAL matrix images, not disjoint chart images. -/
theorem pairwiseDisjoint_schurAtlasImageOfSize {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ) :
    Set.univ.PairwiseDisjoint (schurAtlasImageOfSize centers) := by
  intro w _ v _ hne
  apply Set.disjoint_left.mpr
  intro y hw hv
  apply hne
  apply Subtype.ext
  have hc := schurAtlasImageOfSize_sector_counts centers w y hw
  have hd := schurAtlasImageOfSize_sector_counts centers v y hv
  have hu := hc.1.symm.trans hd.1
  have hr := hc.2.symm.trans hd.2
  rw [schurAtlasImageOfSize_word_canonical centers w hw,
    schurAtlasImageOfSize_word_canonical centers v hv,hu,hr]

/-- Every represented word is covered on a common-volume full set, with its
literal coordinates transported only by equality of physical dimensions. -/
theorem ae_schurAtlasImageOfSize_of_representation {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (w : SchurWordsOfSize N) :
    ∀ᵐ y ∂(volume : Measure ((Fin N × Fin N) → ℝ)),
      ∀ p : SchurWordCells w.val, SchurWordPositive w.val p → SchurWordOrdered w.val p →
      ∀ R : Matrix.orthogonalGroup (Fin (schurWordSize w.val)) ℝ,
      (schurCellsCast w.property).symm y =
        Matrix.vec ((R : Matrix _ _ ℝ) * schurWordParameter w.val p * (R : Matrix _ _ ℝ)ᵀ) →
      y ∈ schurAtlasImageOfSize centers w := by
  rcases w with ⟨w,h⟩
  subst N
  filter_upwards [ae_schurAtlasSimpleSource_coverage w centers hcover] with y hy
  intro p hp ho R he
  obtain ⟨z,hz,hzy⟩ := hy p hp ho R he
  change y ∈ id '' ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
    {x | schurAtlasSimpleSource w centers (i,x)}
  rw [Set.image_id]
  exact Set.mem_iUnion.mpr ⟨z.1,z.2,hz,hzy⟩

/-- The actual finite family covers ordinary matrix volume almost everywhere.
Both root multiplicity and defective/repeated cases remain in the underlying model;
only proved output-null sets are discarded here. -/
theorem ae_mem_iUnion_schurAtlasImageOfSize {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i)) :
    ∀ᵐ y ∂(volume : Measure ((Fin N × Fin N) → ℝ)),
      y ∈ ⋃ w : SchurWordsOfSize N, schurAtlasImageOfSize centers w := by
  have hall : ∀ᵐ y ∂(volume : Measure ((Fin N × Fin N) → ℝ)),
      ∀ w : SchurWordsOfSize N,
      ∀ p : SchurWordCells w.val, SchurWordPositive w.val p → SchurWordOrdered w.val p →
      ∀ R : Matrix.orthogonalGroup (Fin (schurWordSize w.val)) ℝ,
      (schurCellsCast w.property).symm y =
        Matrix.vec ((R : Matrix _ _ ℝ) * schurWordParameter w.val p * (R : Matrix _ _ ℝ)ᵀ) →
      y ∈ schurAtlasImageOfSize centers w :=
    ae_all_iff.mpr (ae_schurAtlasImageOfSize_of_representation centers hcover)
  filter_upwards [hall] with y hy
  let A : Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j => y (j,i))
  obtain ⟨w,h,p,hp,hΩ,ho,Q,hK⟩ := exists_ordered_schur_word N A
  subst N
  let v : SchurWordsOfSize (schurWordSize w) := ⟨w,rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨v,hy v p hp ho Q ?_⟩
  change y = Matrix.vec ((Q : Matrix _ _ ℝ) * schurWordParameter w p * (Q : Matrix _ _ ℝ)ᵀ)
  have hQQ := (Matrix.mem_orthogonalGroup_iff _ _).mp Q.property
  have hc := congrArg (fun M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ =>
    (Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ) hK
  change (Q : Matrix _ _ ℝ) * ((Q : Matrix _ _ ℝ)ᵀ * A * (Q : Matrix _ _ ℝ)) *
      (Q : Matrix _ _ ℝ)ᵀ =
    (Q : Matrix _ _ ℝ) * schurWordParameter w p * (Q : Matrix _ _ ℝ)ᵀ at hc
  have ha : A = (Q : Matrix _ _ ℝ) * schurWordParameter w p * (Q : Matrix _ _ ℝ)ᵀ := by
    calc
      A = ((Q : Matrix _ _ ℝ) * (Q : Matrix _ _ ℝ)ᵀ) * A *
          ((Q : Matrix _ _ ℝ) * (Q : Matrix _ _ ℝ)ᵀ) := by
        rw [hQQ,Matrix.one_mul,Matrix.mul_one]
      _ = (Q : Matrix _ _ ℝ) * ((Q : Matrix _ _ ℝ)ᵀ * A * (Q : Matrix _ _ ℝ)) *
          (Q : Matrix _ _ ℝ)ᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := hc
  exact congrArg Matrix.vec ha

/-- A noncanonical word has EMPTY actual ordered image. -/
theorem schurAtlasImageOfSize_eq_empty_of_not_canonical {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (w : SchurWordsOfSize N)
    (hw : w.val ≠ List.replicate (w.val.count false) false ++
      List.replicate (w.val.count true) true) :
    schurAtlasImageOfSize centers w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact hw (schurAtlasImageOfSize_word_canonical centers w hy)

/-- Exact finite partition of the ordinary matrix-volume integral.
No integrability or finiteness assumption on the nonnegative weight is needed. -/
theorem lintegral_eq_sum_schurAtlasImageOfSize {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (g : ((Fin N × Fin N) → ℝ) → ℝ≥0∞) :
    (∫⁻ y, g y) = ∑ w : SchurWordsOfSize N, ∫⁻ y in schurAtlasImageOfSize centers w, g y := by
  have hd : Pairwise (fun w v : SchurWordsOfSize N =>
      Disjoint (schurAtlasImageOfSize centers w) (schurAtlasImageOfSize centers v)) :=
    fun w v hne => pairwiseDisjoint_schurAtlasImageOfSize centers
      (Set.mem_univ w) (Set.mem_univ v) hne
  have h := lintegral_iUnion (μ := (volume : Measure ((Fin N × Fin N) → ℝ)))
    (measurableSet_schurAtlasImageOfSize centers) hd g
  rw [Measure.restrict_eq_self_of_ae_mem
    (ae_mem_iUnion_schurAtlasImageOfSize centers hcover)] at h
  simpa only [tsum_fintype] using h

end Paper.Spectral
