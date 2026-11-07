/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.OrthogonalCharts
@[expose] public section
noncomputable section
open Set
open scoped Matrix Matrix.Norms.Elementwise
namespace Paper.Spectral

/-- Restrict the actual ambient Cayley chart to bounded coordinates. -/
def boundedCayleyLocalHomeomorph (N : ℕ) :
    OpenPartialHomeomorph (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) :=
  (cayleyUnitLocalHomeomorph N).restrOpen (Metric.ball 0 1) Metric.isOpen_ball

theorem boundedCayleyLocalHomeomorph_apply (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ) :
    boundedCayleyLocalHomeomorph N Ω = cayleyMatrix N Ω := rfl

theorem zero_mem_boundedCayleyLocalHomeomorph_source (N : ℕ) :
    (0 : Matrix (Fin N) (Fin N) ℝ) ∈ (boundedCayleyLocalHomeomorph N).source := by
  refine ⟨zero_mem_cayleyUnitLocalHomeomorph_source N,?_⟩
  simp

theorem boundedCayley_source_norm_lt_one (N : ℕ) (Ω : Matrix (Fin N) (Fin N) ℝ)
    (hΩ : Ω ∈ (boundedCayleyLocalHomeomorph N).source) : ‖Ω‖ < 1 := by
  simpa only [Metric.mem_ball, dist_zero_right] using hΩ.2

theorem one_mem_boundedCayleyLocalHomeomorph_target (N : ℕ) :
    (1 : Matrix (Fin N) (Fin N) ℝ) ∈ (boundedCayleyLocalHomeomorph N).target := by
  have h := (boundedCayleyLocalHomeomorph N).map_source
    (zero_mem_boundedCayleyLocalHomeomorph_source N)
  simpa only [boundedCayleyLocalHomeomorph_apply, cayleyMatrix_zero] using h

theorem boundedCayleyLocalHomeomorph_isImage (N : ℕ) :
    (boundedCayleyLocalHomeomorph N).IsImage
      {Ω | Ωᵀ = -Ω} {Q | Q * Qᵀ = 1} := by
  intro Ω hΩ
  change cayleyMatrix N Ω * (cayleyMatrix N Ω)ᵀ = 1 ↔ Ωᵀ = -Ω
  exact cayley_orthogonal_iff_skew N Ω hΩ.1.2

theorem bounded_cayley_relative_bijOn (N : ℕ) :
    Set.BijOn (cayleyMatrix N)
      ((boundedCayleyLocalHomeomorph N).source ∩ {Ω | Ωᵀ = -Ω})
      ((boundedCayleyLocalHomeomorph N).target ∩ {Q | Q * Qᵀ = 1}) :=
  (boundedCayleyLocalHomeomorph_isImage N).toPartialEquiv.restr.bijOn

/-- Ambient open neighborhood of a center, later restricted to the orthogonal group. -/
def boundedOrthogonalCayleyNeighborhood (N : ℕ) (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  (fun M => (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M) ⁻¹'
    (boundedCayleyLocalHomeomorph N).target

lemma isOpen_boundedOrthogonalCayleyNeighborhood (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    IsOpen (boundedOrthogonalCayleyNeighborhood N Q) :=
  (boundedCayleyLocalHomeomorph N).open_target.preimage (by fun_prop)

lemma center_mem_boundedOrthogonalCayleyNeighborhood (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    (Q : Matrix (Fin N) (Fin N) ℝ) ∈ boundedOrthogonalCayleyNeighborhood N Q := by
  change (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * Q ∈ (boundedCayleyLocalHomeomorph N).target
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property]
  exact one_mem_boundedCayleyLocalHomeomorph_target N

theorem exists_finite_bounded_orthogonal_cayley_cover (N : ℕ) :
    ∃ t : Finset (Matrix.orthogonalGroup (Fin N) ℝ),
      {M : Matrix (Fin N) (Fin N) ℝ | M * Mᵀ = 1} ⊆
        ⋃ Q ∈ t, boundedOrthogonalCayleyNeighborhood N Q := by
  apply (isCompact_orthogonal_matrices N).elim_finite_subcover
    (boundedOrthogonalCayleyNeighborhood N) (isOpen_boundedOrthogonalCayleyNeighborhood N)
  intro M hM
  exact mem_iUnion.mpr ⟨⟨M, (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr hM⟩,
    center_mem_boundedOrthogonalCayleyNeighborhood N _⟩

/-- Every orthogonal matrix, including either determinant component, has coordinates
in one of finitely many translates of the genuine relative Cayley chart. -/
theorem exists_finite_bounded_orthogonal_cayley_coordinates (N : ℕ) :
    ∃ t : Finset (Matrix.orthogonalGroup (Fin N) ℝ),
      ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
        ∃ Q ∈ t, ∃ Ω ∈ (boundedCayleyLocalHomeomorph N).source,
          Ωᵀ = -Ω ∧ M = (Q : Matrix (Fin N) (Fin N) ℝ) * cayleyMatrix N Ω := by
  classical
  obtain ⟨t, ht⟩ := exists_finite_bounded_orthogonal_cayley_cover N
  refine ⟨t, fun M hM => ?_⟩
  obtain ⟨Q, hQt, hQM⟩ := mem_iUnion₂.mp (ht hM)
  have hQQ : (Q : Matrix (Fin N) (Fin N) ℝ) *
      (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp Q.property
  have hQtQ : (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (Q : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property
  have hP : ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M) *
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M)ᵀ = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * (M * Mᵀ) * Q := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, Matrix.mul_one, hQtQ]
  obtain ⟨Ω, hΩ, hC⟩ := (bounded_cayley_relative_bijOn N).surjOn ⟨hQM, hP⟩
  refine ⟨Q, hQt, Ω, hΩ.1, hΩ.2, ?_⟩
  rw [hC, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]

end Paper.Spectral
