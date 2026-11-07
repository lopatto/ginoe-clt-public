/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto

-/
module
public import GinoeClt.Spectral.SchurGaugeFrames
public import GinoeClt.Spectral.SchurWordParameters
public import GinoeClt.Spectral.OrderedSchurCoverage
@[expose] public section
noncomputable section
open scoped Matrix
namespace Paper.Spectral

/-- Exact physical block conjugation. The head sign is scalar, so the entire
head matrix is unchanged; this identity needs no orthogonality premise on R. -/
theorem schurGaugeExtension_conjugation {d m : ℕ} (b : Bool)
    (R : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (U : Matrix (Fin d) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ) :
    (schurGaugeExtension d m (b,R))ᵀ * upperBlockMatrix B U D *
      schurGaugeExtension d m (b,R) =
        upperBlockMatrix B ((schurGaugeHead d b)ᵀ * U * R) (Rᵀ * D * R) := by
  let E := schurGaugeHead d b
  let P : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.fromBlocks E 0 0 R
  let M : Matrix (Fin d ⊕ Fin m) (Fin d ⊕ Fin m) ℝ := Matrix.fromBlocks B U 0 D
  let ρ := Matrix.reindexRingEquiv ℝ (finSumFinEquiv : Fin d ⊕ Fin m ≃ Fin (d+m))
  have hhead : Eᵀ * B * E = B := by
    cases b <;> simp [E, schurGaugeHead]
  have hblock : Pᵀ * M * P =
      Matrix.fromBlocks B (Eᵀ * U * R) 0 (Rᵀ * D * R) := by
    simp only [P, M, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, hhead]
  change ρ Pᵀ * ρ M * ρ P = ρ (Matrix.fromBlocks B (Eᵀ * U * R) 0 (Rᵀ * D * R))
  rw [← map_mul, ← map_mul]
  exact congrArg ρ hblock

/-- Every actual block-sign gauge conjugate is realized by positive zero-angle
free parameters with EXACTLY the same ordered head-root LIST. Input angular
coordinates are arbitrary. No simple-spectrum or regularity premise is used.
Strict pair-gap data is retained as an iff, not assumed. -/
theorem exists_schurWord_gauge_orbit (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p →
      ∀ Q ∈ schurWordGaugeFrames w,
      ∃ q : SchurWordCells w,
        SchurWordPositive w q ∧ schurWordOmega w q = 0 ∧
          schurWordHeadRoots w q = schurWordHeadRoots w p ∧
          schurWordParameter w q = Qᵀ * schurWordParameter w p * Q ∧
          (SchurWordPairGaps w q ↔ SchurWordPairGaps w p) := by
  classical
  induction w with
  | nil =>
    intro p hp Q hQ
    refine ⟨0, trivial, ?_, rfl, ?_, ?_⟩
    · simp [schurWordOmega]
    · simp [schurWordParameter]
    · rfl
  | cons tag w ih =>
    cases tag <;> intro p hp Q hQ
    · change Q ∈ ((Finset.univ ×ˢ schurWordGaugeFrames w).image
        (schurGaugeExtension 1 (schurWordSize w))) at hQ
      obtain ⟨⟨b,R⟩,hprod,rfl⟩ := Finset.mem_image.mp hQ
      have hR : R ∈ schurWordGaugeFrames w := (Finset.mem_product.mp hprod).2
      let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let H := schurHeadInput x
      let tp := schurTailInput x
      let U := schurUpperInput x
      let a := H (0,0)
      have htp : SchurWordPositive w tp := hp
      obtain ⟨t,ht,hΩt,hrt,hKt,hgt⟩ := ih tp htp R hR
      let U' := (schurGaugeHead 1 b)ᵀ * U * R
      let q : SchurWordCells (false::w) := schurStepFreeCells (fun _ : Fin 1 × Fin 1 ↦ a) t U'
      obtain ⟨hKq,hΩq,hq⟩ := schurWord_free_scalar w a t U' hΩt ht
      have hKp : schurWordParameter (false::w) p =
          upperBlockMatrix (scalarBlock a) U (schurWordParameter w tp) :=
        schurParameterPhysical_eq scalarHeadParameter (schurWordParameter w) p
      refine ⟨q,hq,hΩq,?_,?_,?_⟩
      · simp only [schurWordHeadRoots, q, schurStepFreeCells_coordinates,
          schurHeadInput_free, schurTailInput_free]
        exact congrArg (List.cons (a : ℂ)) hrt
      · have htail := congrArg (upperBlockMatrix (scalarBlock a) U') hKt
        have hcon := schurGaugeExtension_conjugation b R (scalarBlock a) U (schurWordParameter w tp)
        have hwhole := congrArg (fun T : Matrix (Fin (1+schurWordSize w)) (Fin (1+schurWordSize w)) ℝ ↦
          (schurGaugeExtension 1 (schurWordSize w) (b,R))ᵀ * T *
            schurGaugeExtension 1 (schurWordSize w) (b,R)) hKp.symm
        exact hKq.trans (htail.trans (hcon.symm.trans hwhole))
      · simpa only [SchurWordPairGaps, q, schurStepFreeCells_coordinates,
          schurTailInput_free] using hgt
    · change Q ∈ ((Finset.univ ×ˢ schurWordGaugeFrames w).image
        (schurGaugeExtension 2 (schurWordSize w))) at hQ
      obtain ⟨⟨b,R⟩,hprod,rfl⟩ := Finset.mem_image.mp hQ
      have hR : R ∈ schurWordGaugeFrames w := (Finset.mem_product.mp hprod).2
      let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let H := schurHeadInput x
      let tp := schurTailInput x
      let U := schurUpperInput x
      change 0 < H (1,0) ∧ H (1,0) ≤ H (0,1) ∧ SchurWordPositive w tp at hp
      obtain ⟨hc,hcb,htp⟩ := hp
      obtain ⟨t,ht,hΩt,hrt,hKt,hgt⟩ := ih tp htp R hR
      let U' := (schurGaugeHead 2 b)ᵀ * U * R
      let q : SchurWordCells (true::w) := schurStepFreeCells (pairFreeInput (H (0,0)) (H (0,1)) (H (1,0))) t U'
      obtain ⟨hKq,hΩq,hq⟩ := schurWord_free_pair w (H (0,0)) (H (0,1)) (H (1,0)) t U' hΩt ht hc hcb
      have hKp : schurWordParameter (true::w) p =
          upperBlockMatrix (schurBlock (H (0,0)) (H (0,1)) (H (1,0))) U (schurWordParameter w tp) :=
        schurParameterPhysical_eq pairHeadParameter (schurWordParameter w) p
      refine ⟨q,hq,hΩq,?_,?_,?_⟩
      · simp only [schurWordHeadRoots, q, schurStepFreeCells_coordinates,
          schurHeadInput_free, schurTailInput_free]
        exact congrArg (List.cons (schurRoot (H (0,0)) (H (0,1)) (H (1,0)))) hrt
      · have htail := congrArg (upperBlockMatrix
          (schurBlock (H (0,0)) (H (0,1)) (H (1,0))) U') hKt
        have hcon := schurGaugeExtension_conjugation b R
          (schurBlock (H (0,0)) (H (0,1)) (H (1,0))) U (schurWordParameter w tp)
        have hwhole := congrArg (fun T : Matrix (Fin (2+schurWordSize w)) (Fin (2+schurWordSize w)) ℝ ↦
          (schurGaugeExtension 2 (schurWordSize w) (b,R))ᵀ * T *
            schurGaugeExtension 2 (schurWordSize w) (b,R)) hKp.symm
        exact hKq.trans (htail.trans (hcon.symm.trans hwhole))
      · simp only [SchurWordPairGaps, q, schurStepFreeCells_coordinates,
          schurHeadInput_free, schurTailInput_free]
        exact and_congr_right (fun _ ↦ hgt)

/-- Order is inherited from the EXACT list equality, without selecting or sorting roots again. -/
theorem exists_ordered_schurWord_gauge_orbit (w : List Bool)
    (p : SchurWordCells w) (hp : SchurWordPositive w p) (ho : SchurWordOrdered w p)
    (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)
    (hQ : Q ∈ schurWordGaugeFrames w) :
    ∃ q : SchurWordCells w,
      SchurWordPositive w q ∧ schurWordOmega w q = 0 ∧ SchurWordOrdered w q ∧
        schurWordHeadRoots w q = schurWordHeadRoots w p ∧
        schurWordParameter w q = Qᵀ * schurWordParameter w p * Q ∧
        (SchurWordPairGaps w q ↔ SchurWordPairGaps w p) := by
  obtain ⟨q,hq,hΩ,hr,hK,hg⟩ := exists_schurWord_gauge_orbit w p hp Q hQ
  refine ⟨q,hq,hΩ,?_,hr,hK,hg⟩
  change (schurWordHeadRoots w q).Pairwise _
  rw [hr]
  exact ho

end Paper.Spectral
