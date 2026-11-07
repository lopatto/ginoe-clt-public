/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.NormalizedEigenblock
import Mathlib.Tactic.FinCases

/-! # A source-shaped first real Schur block for every real matrix

The result is a first-block existence theorem, including the normalized
nonreal 2×2 shape. It does not assert a global coordinate chart or Jacobian.
-/

@[expose] public section
noncomputable section
open Module
open scoped Matrix BigOperators ComplexConjugate

namespace Paper.Spectral

/-- An actual invariant orthonormal frame with action matrix B extends to an
orthogonal matrix whose first block is exactly B and whose lower-left block is zero. -/
theorem orthogonal_frame_block (N d : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (e : Fin d → EuclideanSpace ℝ (Fin N)) (he : Orthonormal ℝ e)
    (B : Matrix (Fin d) (Fin d) ℝ)
    (hact : ∀ j, A.toEuclideanLin (e j) = ∑ l, B l j • e l) :
    ∃ hdN : d ≤ N, ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
      ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * Q).submatrix
          (Fin.castLE hdN) (Fin.castLE hdN) = B ∧
        ∀ (i : Fin N) (j : Fin d), d ≤ i.val →
          ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * Q) i (Fin.castLE hdN j) = 0 := by
  classical
  have hdN : d ≤ N := by
    simpa only [Fintype.card_fin, finrank_euclideanSpace_fin] using
      he.linearIndependent.fintype_card_le_finrank
  obtain ⟨o, ho⟩ := exists_orthonormalBasis_extending_fin N d (by simp) hdN e he
  let s := EuclideanSpace.basisFun (Fin N) ℝ
  let Q := s.toBasis.toMatrix o
  let R := o.toBasis.toMatrix s
  have hQ : Q ∈ Matrix.orthogonalGroup (Fin N) ℝ :=
    s.toMatrix_orthonormalBasis_mem_orthogonal o
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hQ
  have hRQ : R * Q = 1 := by
    change o.toBasis.toMatrix s.toBasis * s.toBasis.toMatrix o.toBasis = 1
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hR : R = Qᵀ := by
    calc R = R * (Q * Qᵀ) := by rw [hQQ, Matrix.mul_one]
         _ = (R * Q) * Qᵀ := by rw [Matrix.mul_assoc]
         _ = Qᵀ := by rw [hRQ, Matrix.one_mul]
  have hmat : LinearMap.toMatrix s.toBasis s.toBasis A.toEuclideanLin = A := by
    simp only [s, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hconj : Qᵀ * A * Q = LinearMap.toMatrix o.toBasis o.toBasis A.toEuclideanLin := by
    calc Qᵀ * A * Q = R * LinearMap.toMatrix s.toBasis s.toBasis A.toEuclideanLin * Q := by
           rw [hR, hmat]
         _ = LinearMap.toMatrix o.toBasis o.toBasis A.toEuclideanLin := by
           change o.toBasis.toMatrix s.toBasis *
             LinearMap.toMatrix s.toBasis s.toBasis A.toEuclideanLin *
             s.toBasis.toMatrix o.toBasis = LinearMap.toMatrix o.toBasis o.toBasis A.toEuclideanLin
           exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
             o.toBasis s.toBasis o.toBasis s.toBasis A.toEuclideanLin
  have hcol (i : Fin N) (j : Fin d) :
      (Qᵀ * A * Q) i (Fin.castLE hdN j) =
        ∑ l : Fin d, B l j * (if i = Fin.castLE hdN l then 1 else 0) := by
    rw [hconj]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply]
    rw [ho j, hact j]
    simp_rw [← ho]
    simp [Pi.single_apply]
  refine ⟨hdN, ⟨Q, hQ⟩, ?_, ?_⟩
  · ext i j
    change (Qᵀ * A * Q) (Fin.castLE hdN i) (Fin.castLE hdN j) = B i j
    simp [hcol]
  · intro i j hi
    have hne : ∀ l : Fin d, i ≠ Fin.castLE hdN l := by
      intro l hh
      have hval := congrArg Fin.val hh
      simp only [Fin.val_castLE] at hval
      omega
    change (Qᵀ * A * Q) i (Fin.castLE hdN j) = 0
    simp [hcol, hne]

theorem real_eigenvalue_orthogonal_block (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (a : ℝ)
    (u : Fin (n + 1) → ℝ) (hu : u ≠ 0) (he : A *ᵥ u = a • u) :
    ∃ Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ,
      ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q) 0 0 = a ∧
        ∀ i : Fin (n + 1), 1 ≤ i.val →
          ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q) i 0 = 0 := by
  let w : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 u
  have hw : w ≠ 0 := fun hh => hu ((WithLp.toLp_eq_zero 2).mp hh)
  let e : Fin 1 → EuclideanSpace ℝ (Fin (n + 1)) := fun _ => (‖w‖⁻¹ : ℝ) • w
  have horth : Orthonormal ℝ e := by
    refine ⟨fun _ => ?_, Subsingleton.pairwise⟩
    simp [e, norm_smul, norm_ne_zero_iff.mpr hw]
  have hwa : A.toEuclideanLin w = a • w := by
    change WithLp.toLp 2 (A *ᵥ u) = _
    rw [he, WithLp.toLp_smul]
  have hact : ∀ j : Fin 1, A.toEuclideanLin (e j) =
      ∑ l : Fin 1, (fun _ _ : Fin 1 => a) l j • e l := by
    intro j
    simp only [Fintype.sum_unique]
    change A.toEuclideanLin ((‖w‖⁻¹ : ℝ) • w) = a • ((‖w‖⁻¹ : ℝ) • w)
    rw [map_smul, hwa]
    simp only [smul_smul]
    congr 1
    ring
  obtain ⟨hdN, Q, hB, hlo⟩ := orthogonal_frame_block (n + 1) 1 A e horth
    (fun _ _ => a) hact
  have hemb : Fin.castLE hdN (0 : Fin 1) = (0 : Fin (n + 1)) := rfl
  refine ⟨Q, ?_, fun i hi => ?_⟩
  · have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) hB
    simpa only [Matrix.submatrix_apply, hemb] using hh
  · simpa only [hemb] using hlo i 0 hi

theorem real_matrix_conj_eigenvector {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (μ : ℂ) (v : ι → ℂ)
    (he : A.map Complex.ofRealHom *ᵥ v = μ • v) :
    A.map Complex.ofRealHom *ᵥ (fun i => conj (v i)) =
      conj μ • (fun i => conj (v i)) := by
  funext i
  have hh := congrArg conj (congrFun he i)
  simpa [Matrix.mulVec, dotProduct] using hh

/-- Every positive-size real matrix has either a real one-dimensional first
orthogonal block or a source-normalized nonreal two-dimensional first block.
This is the complete first-block dichotomy, not a full Schur decomposition. -/
theorem exists_source_first_block (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (∃ a : ℝ, ∃ Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ,
      ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q) 0 0 = a ∧
        ∀ i : Fin (n + 1), 1 ≤ i.val →
          ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q) i 0 = 0) ∨
    (∃ h2N : 2 ≤ n + 1, ∃ a b c : ℝ, 0 < c ∧ c ≤ b ∧
      ∃ Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ,
        ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q).submatrix
            (Fin.castLE h2N) (Fin.castLE h2N) = !![a, b; -c, a] ∧
          ∀ (i : Fin (n + 1)) (j : Fin 2), 2 ≤ i.val →
            ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q) i (Fin.castLE h2N j) = 0) := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.map Complex.ofRealHom).toLin'
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have he : A.map Complex.ofRealHom *ᵥ v = μ • v := hv.apply_eq_smul
  by_cases hreal : μ.im = 0
  · obtain ⟨u, hu, hue⟩ := real_eigenvector_of_real_eigenvalue A μ v hv0 he hreal
    obtain ⟨Q, hQ⟩ := real_eigenvalue_orthogonal_block n A μ.re u hu hue
    exact Or.inl ⟨μ.re, Q, hQ⟩
  · apply Or.inr
    by_cases hpos : 0 < μ.im
    · obtain ⟨h2, b, c, hc, hcb, _, Q, hQ⟩ :=
        nonreal_eigenvalue_orthogonal_block (n + 1) A μ v hv0 he hpos
      exact ⟨h2, μ.re, b, c, hc, hcb, Q, hQ⟩
    · have hconjpos : 0 < (conj μ).im := by
        simp only [Complex.conj_im]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hreal)
      have hconjv : (fun i => conj (v i)) ≠ 0 := by
        intro hh
        apply hv0
        funext i
        have hi := congrArg conj (congrFun hh i)
        simpa using hi
      obtain ⟨h2, b, c, hc, hcb, _, Q, hQ⟩ :=
        nonreal_eigenvalue_orthogonal_block (n + 1) A (conj μ) (fun i => conj (v i))
          hconjv (real_matrix_conj_eigenvector A μ v he) hconjpos
      exact ⟨h2, (conj μ).re, b, c, hc, hcb, Q, hQ⟩

end Paper.Spectral
