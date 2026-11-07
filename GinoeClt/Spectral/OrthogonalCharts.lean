/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.CayleyRestriction
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded

/-! # Finite coverage of the actual orthogonal group by relative Cayley charts -/

@[expose] public section
noncomputable section
open Set
open scoped Matrix Matrix.Norms.Elementwise

namespace Paper.Spectral

theorem isCompact_orthogonal_matrices (N : ℕ) :
    IsCompact {Q : Matrix (Fin N) (Fin N) ℝ | Q * Qᵀ = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
    intro Q hQ
    exact entrywise_sup_norm_bound_of_unitary
      ((Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr hQ)

/-- Ambient open neighborhood of a center, later restricted to the orthogonal group. -/
def orthogonalCayleyNeighborhood (N : ℕ) (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  (fun M => (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * M) ⁻¹'
    (cayleyUnitLocalHomeomorph N).target

lemma isOpen_orthogonalCayleyNeighborhood (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    IsOpen (orthogonalCayleyNeighborhood N Q) :=
  (cayleyUnitLocalHomeomorph N).open_target.preimage (by fun_prop)

lemma center_mem_orthogonalCayleyNeighborhood (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    (Q : Matrix (Fin N) (Fin N) ℝ) ∈ orthogonalCayleyNeighborhood N Q := by
  change (Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * Q ∈ (cayleyUnitLocalHomeomorph N).target
  rw [(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp Q.property]
  exact one_mem_cayleyUnitLocalHomeomorph_target N

theorem exists_finite_orthogonal_cayley_cover (N : ℕ) :
    ∃ t : Finset (Matrix.orthogonalGroup (Fin N) ℝ),
      {M : Matrix (Fin N) (Fin N) ℝ | M * Mᵀ = 1} ⊆
        ⋃ Q ∈ t, orthogonalCayleyNeighborhood N Q := by
  apply (isCompact_orthogonal_matrices N).elim_finite_subcover
    (orthogonalCayleyNeighborhood N) (isOpen_orthogonalCayleyNeighborhood N)
  intro M hM
  exact mem_iUnion.mpr ⟨⟨M, (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr hM⟩,
    center_mem_orthogonalCayleyNeighborhood N _⟩

/-- Every orthogonal matrix, including either determinant component, has coordinates
in one of finitely many translates of the genuine relative Cayley chart. -/
theorem exists_finite_orthogonal_cayley_coordinates (N : ℕ) :
    ∃ t : Finset (Matrix.orthogonalGroup (Fin N) ℝ),
      ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
        ∃ Q ∈ t, ∃ Ω ∈ (cayleyUnitLocalHomeomorph N).source,
          Ωᵀ = -Ω ∧ M = (Q : Matrix (Fin N) (Fin N) ℝ) * cayleyMatrix N Ω := by
  classical
  obtain ⟨t, ht⟩ := exists_finite_orthogonal_cayley_cover N
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
  obtain ⟨Ω, hΩ, hC⟩ := (cayley_relative_bijOn N).surjOn ⟨hQM, hP⟩
  refine ⟨Q, hQt, Ω, hΩ.1, hΩ.2, ?_⟩
  rw [hC, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]

end Paper.Spectral
