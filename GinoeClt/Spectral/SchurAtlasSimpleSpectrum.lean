/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasFiber
public import GinoeClt.Spectral.SimpleSpectrum
public import Mathlib.Topology.Algebra.MvPolynomial
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix
namespace Paper.Spectral

/-- The actual simple-spectrum output set in COLUMN-MAJOR matrix cells.
The index flip is essential: the characteristic resultant uses row-column variables. -/
def simpleSpectrumCells (N : ℕ) : Set ((Fin N × Fin N) → ℝ) :=
  {y | MvPolynomial.eval (fun ij => y (ij.2,ij.1)) (matrixCharacteristicResultant N) ≠ 0}

theorem isOpen_simpleSpectrumCells (N : ℕ) : IsOpen (simpleSpectrumCells N) := by
  have hc : Continuous (fun y : (Fin N × Fin N) → ℝ =>
      MvPolynomial.eval (fun ij => y (ij.2,ij.1)) (matrixCharacteristicResultant N)) :=
    (matrixCharacteristicResultant N).continuous_eval.comp
      (continuous_pi fun ij => continuous_apply (ij.2,ij.1))
  exact isOpen_ne.preimage hc

theorem measurableSet_simpleSpectrumCells (N : ℕ) :
    MeasurableSet (simpleSpectrumCells N) :=
  (isOpen_simpleSpectrumCells N).measurableSet

theorem mem_simpleSpectrumCells_vec_iff (N : ℕ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.vec M ∈ simpleSpectrumCells N ↔ M.charpoly.Separable := by
  change MvPolynomial.eval (fun ij => M ij.1 ij.2) (matrixCharacteristicResultant N) ≠ 0 ↔ _
  rw [matrixCharacteristicResultant_eval]
  constructor
  · intro h
    by_contra hs
    exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl M.charpoly_monic.ne_zero,hs⟩)
  · exact Polynomial.resultant_ne_zero M.charpoly M.charpoly.derivative

/-- This restriction discards an actually proved null set for the frozen ensemble. -/
theorem matrixLaw_mem_simpleSpectrumCells_ae (n : ℕ) :
    ∀ᵐ M ∂matrixLaw n, Matrix.vec M ∈ simpleSpectrumCells (n+1) := by
  filter_upwards [matrixLaw_charpoly_separable_ae n] with M hM
  exact (mem_simpleSpectrumCells_vec_iff (n+1) M).mpr hM

theorem schurAtlasMatrix_charpoly (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    (schurAtlasMatrix w centers z).charpoly = (schurWordParameter w z.2).charpoly := by
  have hRR := (Matrix.mem_orthogonalGroup_iff' _ _).mp (schurAtlasFrame_orthogonal w centers z)
  change (schurAtlasFrame w centers z * schurWordParameter w z.2 *
    (schurAtlasFrame w centers z)ᵀ).charpoly = _
  rw [Matrix.charpoly_mul_comm,← Matrix.mul_assoc,hRR,Matrix.one_mul]

theorem schurWordRoots_nodup_of_simpleSpectrumCells (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) (hp : SchurWordPositive w z.2)
    (hs : schurAtlasCells w centers z ∈ simpleSpectrumCells (schurWordSize w)) :
    (schurWordRoots w z.2).Nodup := by
  have hsep := (mem_simpleSpectrumCells_vec_iff (schurWordSize w)
    (schurAtlasMatrix w centers z)).mp hs
  rw [schurAtlasMatrix_charpoly] at hsep
  rw [← schurWordParameter_roots w z.2 hp]
  exact Polynomial.nodup_roots hsep.map

/-- An EXPLICIT new restriction to the actual simple-spectrum output set.
The original physical source and the principal definitions are unchanged. -/
def schurAtlasSimpleSource (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) : Prop :=
  schurAtlasSource w centers z ∧
    schurAtlasCells w centers z ∈ simpleSpectrumCells (schurWordSize w)

theorem schurAtlasSimpleSource_fiber_encard (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (z0 : Fin (m+1) × SchurWordCells w) (h0 : schurAtlasSimpleSource w centers z0) :
    ({z : Fin (m+1) × SchurWordCells w | schurAtlasSimpleSource w centers z ∧
      schurAtlasCells w centers z = schurAtlasCells w centers z0}).encard = (2 : ℕ∞)^w.length := by
  have he : {z : Fin (m+1) × SchurWordCells w | schurAtlasSimpleSource w centers z ∧
      schurAtlasCells w centers z = schurAtlasCells w centers z0} =
      {z : Fin (m+1) × SchurWordCells w | schurAtlasSource w centers z ∧
      schurAtlasCells w centers z = schurAtlasCells w centers z0} := by
    ext z
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · intro h
      exact ⟨⟨h.1,h.2 ▸ h0.2⟩,h.2⟩
  rw [he]
  exact schurAtlasCells_fiber_encard w centers hcover z0 h0.1
    (schurWordRoots_nodup_of_simpleSpectrumCells w centers z0 h0.1.2.1 h0.2)

/-- The literal total fiber count on the ACTUAL restricted family image.
This supplies, rather than assumes, the cardinality prerequisite of finite-family COV. -/
theorem schurAtlasSimpleSource_total_fiber (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (y : SchurWordCells w)
    (hy : y ∈ ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
      {x | schurAtlasSimpleSource w centers (i,x)}) :
    ({z : Fin (m+1) × SchurWordCells w | schurAtlasSimpleSource w centers z ∧
      schurAtlasCells w centers z = y}).encard = (2 : ℕ∞)^w.length := by
  rcases Set.mem_iUnion.mp hy with ⟨i,x,hx,hxy⟩
  rw [← hxy]
  exact schurAtlasSimpleSource_fiber_encard w centers hcover (i,x) hx

end Paper.Spectral
