/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurAtlasRepresentation
public import GinoeClt.Spectral.SchurWordGaugeClassification
public import GinoeClt.Spectral.SchurGaugeOrbit
public import GinoeClt.Spectral.SchurRegularCriterion
public import Mathlib.Data.Set.Card
@[expose] public section
noncomputable section
open Set
open scoped Matrix
namespace Paper.Spectral

/-- The SAME physical frame recovers the actual parameter matrix from its output. -/
theorem schurAtlas_parameter_recovery (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (z : Fin (m+1) × SchurWordCells w) :
    (schurAtlasFrame w centers z)ᵀ * schurAtlasMatrix w centers z *
      schurAtlasFrame w centers z = schurWordParameter w z.2 := by
  have hRR := (Matrix.mem_orthogonalGroup_iff' _ _).mp (schurAtlasFrame_orthogonal w centers z)
  change (schurAtlasFrame w centers z)ᵀ *
      (schurAtlasFrame w centers z * schurWordParameter w z.2 * (schurAtlasFrame w centers z)ᵀ) *
        schurAtlasFrame w centers z = _
  calc
    _ = ((schurAtlasFrame w centers z)ᵀ * schurAtlasFrame w centers z) *
        schurWordParameter w z.2 *
          ((schurAtlasFrame w centers z)ᵀ * schurAtlasFrame w centers z) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hRR,Matrix.one_mul,Matrix.mul_one]

/-- Genuine assigned raw coordinates are unique for one frame and one regular K. -/
theorem schurAtlas_source_eq_of_frame_parameter_eq (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (z z' : Fin (m+1) × SchurWordCells w)
    (hz : schurAtlasSource w centers z) (hz' : schurAtlasSource w centers z')
    (hR : schurAtlasFrame w centers z = schurAtlasFrame w centers z')
    (hK : schurWordParameter w z.2 = schurWordParameter w z'.2) : z = z' := by
  let R : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ :=
    ⟨schurAtlasFrame w centers z,schurAtlasFrame_orthogonal w centers z⟩
  obtain ⟨u,hu,huniq⟩ := existsUnique_schurAtlas_frame_parameter w centers hcover z.2
    hz.2.1 hz.2.2.1 hz.2.2.2 R
  exact (huniq z ⟨hz,rfl,rfl⟩).trans (huniq z' ⟨hz',hR.symm,hK.symm⟩).symm

/-- Relative physical frames biject the ACTUAL WHOLE assigned-atlas fiber with
its finite block-sign family. This is not a chartwise multiplicity statement. -/
theorem schurAtlas_relativeFrame_bijOn (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (z0 : Fin (m+1) × SchurWordCells w) (h0 : schurAtlasSource w centers z0)
    (hn0 : (schurWordRoots w z0.2).Nodup) :
    Set.BijOn (fun z : Fin (m+1) × SchurWordCells w ↦
        (schurAtlasFrame w centers z0)ᵀ * schurAtlasFrame w centers z)
      {z | schurAtlasSource w centers z ∧ schurAtlasMatrix w centers z = schurAtlasMatrix w centers z0}
      (schurWordGaugeFrames w : Set (Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)) := by
  classical
  let R0 := schurAtlasFrame w centers z0
  let K0 := schurWordParameter w z0.2
  let ρ := fun z : Fin (m+1) × SchurWordCells w ↦ R0ᵀ * schurAtlasFrame w centers z
  have h00 : R0 * R0ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff _ _).mp (schurAtlasFrame_orthogonal w centers z0)
  have h00' : R0ᵀ * R0 = 1 :=
    (Matrix.mem_orthogonalGroup_iff' _ _).mp (schurAtlasFrame_orthogonal w centers z0)
  have hframe (z : Fin (m+1) × SchurWordCells w) : R0 * ρ z = schurAtlasFrame w centers z := by
    change R0 * (R0ᵀ * schurAtlasFrame w centers z) = _
    rw [← Matrix.mul_assoc,h00,Matrix.one_mul]
  have hrel (z : Fin (m+1) × SchurWordCells w) :
      ρ z ∈ Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ := by
    have hzz := (Matrix.mem_orthogonalGroup_iff _ _).mp (schurAtlasFrame_orthogonal w centers z)
    apply (Matrix.mem_orthogonalGroup_iff _ _).mpr
    change (R0ᵀ * schurAtlasFrame w centers z) * (R0ᵀ * schurAtlasFrame w centers z)ᵀ = 1
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    calc
      _ = R0ᵀ * (schurAtlasFrame w centers z * (schurAtlasFrame w centers z)ᵀ) * R0 := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hzz,Matrix.mul_one,h00']
  have hg0 : SchurWordPairGaps w z0.2 := schurWordPairGaps_of_regular w z0.2 h0.2.1 h0.2.2.2
  change Set.BijOn ρ _ _
  refine ⟨?_,?_,?_⟩
  · intro z hz
    let Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ := ⟨ρ z,hrel z⟩
    have hzz' := (Matrix.mem_orthogonalGroup_iff' _ _).mp (schurAtlasFrame_orthogonal w centers z)
    have hT : K0 * ρ z = ρ z * schurWordParameter w z.2 := by
      calc
        _ = (R0ᵀ * R0) * K0 * (R0ᵀ * schurAtlasFrame w centers z) := by rw [h00',Matrix.one_mul]
        _ = R0ᵀ * schurAtlasMatrix w centers z0 * schurAtlasFrame w centers z := by
          simp only [schurAtlasMatrix,R0,K0,Matrix.mul_assoc]
        _ = R0ᵀ * schurAtlasMatrix w centers z * schurAtlasFrame w centers z :=
          congrArg (fun M ↦ R0ᵀ * M * schurAtlasFrame w centers z) hz.2.symm
        _ = (ρ z * schurWordParameter w z.2) *
            ((schurAtlasFrame w centers z)ᵀ * schurAtlasFrame w centers z) := by
          simp only [ρ,schurAtlasMatrix,Matrix.mul_assoc]
        _ = _ := by rw [hzz',Matrix.mul_one]
    exact orthogonal_ordered_word_intertwiner_gauge w z0.2 z.2 h0.2.1 hz.1.2.1
      h0.2.2.1 hz.1.2.2.1 hg0
      (schurWordPairGaps_of_regular w z.2 hz.1.2.1 hz.1.2.2.2) hn0 Q hT
  · intro z hz z' hz' he
    have hR : schurAtlasFrame w centers z = schurAtlasFrame w centers z' :=
      (hframe z).symm.trans ((congrArg (fun Q ↦ R0 * Q) he).trans (hframe z'))
    have hK : schurWordParameter w z.2 = schurWordParameter w z'.2 := by
      calc
        _ = (schurAtlasFrame w centers z)ᵀ * schurAtlasMatrix w centers z *
            schurAtlasFrame w centers z := (schurAtlas_parameter_recovery w centers z).symm
        _ = (schurAtlasFrame w centers z')ᵀ * schurAtlasMatrix w centers z' *
            schurAtlasFrame w centers z' := by rw [hR,hz.2,hz'.2]
        _ = _ := schurAtlas_parameter_recovery w centers z'
    exact schurAtlas_source_eq_of_frame_parameter_eq w centers hcover z z' hz.1 hz'.1 hR hK
  · intro Q hQ
    have hQorth := schurWordGaugeFrames_orthogonal w Q hQ
    have hQQ := (Matrix.mem_orthogonalGroup_iff _ _).mp hQorth
    let Qg : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ := ⟨Q,hQorth⟩
    obtain ⟨q,hq,hΩq,hoq,hrq,hKq,hgq⟩ :=
      exists_ordered_schurWord_gauge_orbit w z0.2 h0.2.1 h0.2.2.1 Q hQ
    have hT : schurWordParameter w z0.2 * Q = Q * schurWordParameter w q := by
      rw [hKq]
      calc
        _ = (Q * Qᵀ) * schurWordParameter w z0.2 * Q := by rw [hQQ,Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hroots : schurWordRoots w z0.2 = schurWordRoots w q :=
      schurWordRoots_eq_of_intertwiner w z0.2 q h0.2.1 hq Qg hT
    have hnq : (schurWordRoots w q).Nodup := by rw [← hroots]; exact hn0
    have hdq : LinearMap.det (schurWordDifferential w q) ≠ 0 :=
      schurWord_regular_of_pairGaps_nodup w q hq hoq (hgq.mpr hg0) hnq
    let R : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ :=
      ⟨R0 * Q,(Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ).mul_mem
        (schurAtlasFrame_orthogonal w centers z0) hQorth⟩
    obtain ⟨z,hz,hzu⟩ := existsUnique_schurAtlas_frame_parameter w centers hcover q hq hoq hdq R
    have hRz : schurAtlasFrame w centers z = R0 * Q := hz.2.1
    have hKz : schurWordParameter w z.2 = schurWordParameter w q := hz.2.2
    have hout : schurAtlasMatrix w centers z = schurAtlasMatrix w centers z0 := by
      change schurAtlasFrame w centers z * schurWordParameter w z.2 *
        (schurAtlasFrame w centers z)ᵀ = R0 * K0 * R0ᵀ
      rw [hRz,hKz,hKq,Matrix.transpose_mul]
      calc
        _ = R0 * (Q * Qᵀ) * K0 * (Q * Qᵀ) * R0ᵀ := by
          simp only [K0,Matrix.mul_assoc]
        _ = _ := by simp only [hQQ,Matrix.mul_one]
    refine ⟨z,⟨hz.1,hout⟩,?_⟩
    change R0ᵀ * schurAtlasFrame w centers z = Q
    rw [hRz,← Matrix.mul_assoc,h00',Matrix.one_mul]

/-- Exact finite cardinality of the WHOLE assigned-atlas fiber over an actual
regular simple-spectrum source point. No chartwise factor is inserted. -/
theorem schurAtlas_fiber_encard (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (z0 : Fin (m+1) × SchurWordCells w) (h0 : schurAtlasSource w centers z0)
    (hn0 : (schurWordRoots w z0.2).Nodup) :
    ({z : Fin (m+1) × SchurWordCells w | schurAtlasSource w centers z ∧
      schurAtlasMatrix w centers z = schurAtlasMatrix w centers z0}).encard = (2 : ℕ∞) ^ w.length := by
  have h := schurAtlas_relativeFrame_bijOn w centers hcover z0 h0 hn0
  calc
    _ = (schurWordGaugeFrames w : Set (Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)).encard :=
      Set.encard_congr h.equiv
    _ = _ := by rw [Set.encard_coe_eq_coe_finsetCard,card_schurWordGaugeFrames]; norm_cast

/-- The SAME exact count in the actual column-major output cells used by COV. -/
theorem schurAtlasCells_fiber_encard (w : List Bool) {m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ)
    (hcover : ∀ M : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ,
      M * Mᵀ = 1 → M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood (schurWordSize w) (centers i))
    (z0 : Fin (m+1) × SchurWordCells w) (h0 : schurAtlasSource w centers z0)
    (hn0 : (schurWordRoots w z0.2).Nodup) :
    ({z : Fin (m+1) × SchurWordCells w | schurAtlasSource w centers z ∧
      schurAtlasCells w centers z = schurAtlasCells w centers z0}).encard = (2 : ℕ∞) ^ w.length := by
  have he : {z : Fin (m+1) × SchurWordCells w | schurAtlasSource w centers z ∧
      schurAtlasCells w centers z = schurAtlasCells w centers z0} =
      {z : Fin (m+1) × SchurWordCells w | schurAtlasSource w centers z ∧
      schurAtlasMatrix w centers z = schurAtlasMatrix w centers z0} := by
    ext z
    simp only [schurAtlasCells,Matrix.vec_inj]
  rw [he]
  exact schurAtlas_fiber_encard w centers hcover z0 h0 hn0

end Paper.Spectral
