/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.RealEigenplane
public import GinoeClt.Spectral.OrthogonalInvariantBlock
import Mathlib.Tactic.FinCases

/-! # The normalized real block associated with a nonreal eigenvalue

All vector norms in this file belong to actual real inner product spaces.
The ordinary Pi matrix representation and its norm are unchanged.
-/

@[expose] public section
noncomputable section
open Module
open scoped Matrix BigOperators RealInnerProductSpace

namespace Paper.Spectral

theorem normalized_pair_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u w : E) (hu : u ≠ 0) (hw : w ≠ 0)
    (horth : inner ℝ u w = 0) :
    Orthonormal ℝ ![(‖u‖⁻¹ : ℝ) • u, (‖w‖⁻¹ : ℝ) • w] := by
  constructor
  · intro i
    fin_cases i
    · simp [norm_smul, norm_ne_zero_iff.mpr hu]
    · simp [norm_smul, norm_ne_zero_iff.mpr hw]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simp [inner_smul_left, inner_smul_right, horth]
    · have hrev : inner ℝ w u = 0 := by rw [real_inner_comm]; exact horth
      simp [inner_smul_left, inner_smul_right, hrev]
    · exact (hij rfl).elim

/-- Normalizing an ordered orthogonal real eigenplane gives the exact source
block with positive off-diagonal parameters c≤b and product b*c=β². -/
theorem normalized_eigenplane_block {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E →ₗ[ℝ] E) (a β : ℝ) (hβ : 0 < β)
    (u w : E) (hu : u ≠ 0) (hw : w ≠ 0) (horth : inner ℝ u w = 0)
    (horder : ‖w‖ ≤ ‖u‖)
    (hfu : f u = a • u - β • w) (hfw : f w = β • u + a • w) :
    ∃ e : Fin 2 → E, Orthonormal ℝ e ∧
      ∃ b c : ℝ, 0 < c ∧ c ≤ b ∧ b * c = β ^ 2 ∧
        f (e 0) = a • e 0 - c • e 1 ∧ f (e 1) = b • e 0 + a • e 1 := by
  let e : Fin 2 → E := ![(‖u‖⁻¹ : ℝ) • u, (‖w‖⁻¹ : ℝ) • w]
  let b := β * ‖u‖ / ‖w‖
  let c := β * ‖w‖ / ‖u‖
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hbc : c ≤ b := by
    dsimp only [b, c]
    apply (div_le_div_iff₀ hup hwp).mpr
    have hsq : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr horder
    nlinarith only [mul_le_mul_of_nonneg_left hsq hβ.le]
  refine ⟨e, normalized_pair_orthonormal u w hu hw horth, b, c, by dsimp [c]; positivity,
    hbc, ?_, ?_, ?_⟩
  · dsimp only [b, c]
    field_simp
  · change f ((‖u‖⁻¹ : ℝ) • u) =
      a • ((‖u‖⁻¹ : ℝ) • u) - c • ((‖w‖⁻¹ : ℝ) • w)
    rw [map_smul, hfu, smul_sub]
    simp only [smul_smul]
    congr 1
    · congr 1
      ring
    · congr 1
      dsimp only [c]
      field_simp
  · change f ((‖w‖⁻¹ : ℝ) • w) =
      b • ((‖u‖⁻¹ : ℝ) • u) + a • ((‖w‖⁻¹ : ℝ) • w)
    rw [map_smul, hfw, smul_add]
    simp only [smul_smul]
    congr 1
    · congr 1
      dsimp only [b]
      field_simp
    · congr 1
      ring

/-- The source-normalized real eigenplane for an actual upper-half-plane
eigenvalue of a real matrix. The action uses Mathlib's Euclidean realization. -/
theorem nonreal_eigenvalue_normalized_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : A.map Complex.ofRealHom *ᵥ v = μ • v) (hμ : 0 < μ.im) :
    ∃ e : Fin 2 → EuclideanSpace ℝ ι, Orthonormal ℝ e ∧
      ∃ b c : ℝ, 0 < c ∧ c ≤ b ∧ b * c = μ.im ^ 2 ∧
        A.toEuclideanLin (e 0) = μ.re • e 0 - c • e 1 ∧
          A.toEuclideanLin (e 1) = b • e 0 + μ.re • e 1 := by
  obtain ⟨z, hz, hze, hLI, horth, hord⟩ :=
    exists_orthogonal_eigenplane A μ v hv he hμ.ne'
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (z i).re)
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (z i).im)
  have hu0 : u ≠ 0 := by
    have hh := hLI.ne_zero (0 : Fin 2)
    change (fun i => (z i).re) ≠ 0 at hh
    intro hzero
    exact hh ((WithLp.toLp_eq_zero 2).mp hzero)
  have hw0 : w ≠ 0 := by
    have hh := hLI.ne_zero (1 : Fin 2)
    change (fun i => (z i).im) ≠ 0 at hh
    intro hzero
    exact hh ((WithLp.toLp_eq_zero 2).mp hzero)
  have huorth : inner ℝ u w = 0 := by
    rw [PiLp.inner_apply]
    change (∑ i, inner ℝ (z i).re (z i).im) = 0
    simpa only [Real.inner_apply] using horth
  have horder : ‖w‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg u)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    exact hord
  have huact : A.toEuclideanLin u = μ.re • u - μ.im • w := by
    change WithLp.toLp 2 (A *ᵥ (fun i => (z i).re)) = _
    rw [(eigenvector_real_imag A μ z hze).1, WithLp.toLp_sub,
      WithLp.toLp_smul, WithLp.toLp_smul]
  have hwact : A.toEuclideanLin w = μ.im • u + μ.re • w := by
    change WithLp.toLp 2 (A *ᵥ (fun i => (z i).im)) = _
    rw [(eigenvector_real_imag A μ z hze).2, WithLp.toLp_add,
      WithLp.toLp_smul, WithLp.toLp_smul]
  exact normalized_eigenplane_block A.toEuclideanLin μ.re μ.im hμ
    u w hu0 hw0 huorth horder huact hwact

/-- Extend a finite orthonormal frame while preserving its position as the
initial coordinates of an ambient orthonormal basis. -/
theorem exists_orthonormalBasis_extending_fin {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (N d : ℕ)
    (hN : finrank ℝ E = N) (hdN : d ≤ N) (e : Fin d → E) (he : Orthonormal ℝ e) :
    ∃ o : OrthonormalBasis (Fin N) ℝ E, ∀ j : Fin d, o (Fin.castLE hdN j) = e j := by
  classical
  let s : Set (Fin N) := {i | i.val < d}
  let v : Fin N → E := fun i => if hi : i.val < d then e ⟨i.val, hi⟩ else 0
  let g : s → Fin d := fun i => ⟨i.val.val, i.property⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun j : Fin d => j.val) hij
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    convert he.comp g hg using 1
    funext i
    have hi : i.val.val < d := i.property
    change (if h : i.val.val < d then e ⟨i.val.val, h⟩ else 0) = _
    rw [dite_eq_left hi]
    rfl
  obtain ⟨o, ho⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simpa only [Fintype.card_fin] using hN)
  refine ⟨o, fun j => ?_⟩
  rw [ho _ j.isLt]
  change (if hi : j.val < d then e ⟨j.val, hi⟩ else 0) = e j
  rw [dite_eq_left j.isLt]

/-- An actual upper-half-plane eigenvalue determines an actual orthogonal
first block [a,b;-c,a], with 0<c≤b and b*c=(Im μ)². No global Schur chart or
Jacobian is asserted. -/
theorem nonreal_eigenvalue_orthogonal_block (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (μ : ℂ) (v : Fin N → ℂ) (hv : v ≠ 0)
    (he : A.map Complex.ofRealHom *ᵥ v = μ • v) (hμ : 0 < μ.im) :
    ∃ h2N : 2 ≤ N, ∃ b c : ℝ, 0 < c ∧ c ≤ b ∧ b * c = μ.im ^ 2 ∧
      ∃ Q : Matrix.orthogonalGroup (Fin N) ℝ,
        ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * Q).submatrix
            (Fin.castLE h2N) (Fin.castLE h2N) = !![μ.re, b; -c, μ.re] ∧
          ∀ (i : Fin N) (j : Fin 2), 2 ≤ i.val →
            ((Q : Matrix (Fin N) (Fin N) ℝ)ᵀ * A * Q) i (Fin.castLE h2N j) = 0 := by
  classical
  obtain ⟨e, heorth, b, c, hc, hcb, hbc, ha0, ha1⟩ :=
    nonreal_eigenvalue_normalized_frame A μ v hv he hμ
  have h2N : 2 ≤ N := by
    simpa only [Fintype.card_fin, finrank_euclideanSpace_fin] using
      heorth.linearIndependent.fintype_card_le_finrank
  obtain ⟨o, ho⟩ := exists_orthonormalBasis_extending_fin N 2
    (by simp) h2N e heorth
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
  have hcol0 (i : Fin N) :
      (Qᵀ * A * Q) i (Fin.castLE h2N 0) =
        μ.re * (if i = Fin.castLE h2N 0 then 1 else 0) -
          c * (if i = Fin.castLE h2N 1 then 1 else 0) := by
    rw [hconj]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply]
    rw [ho 0, ha0, ← ho 0, ← ho 1]
    simp [PiLp.single_apply]
  have hcol1 (i : Fin N) :
      (Qᵀ * A * Q) i (Fin.castLE h2N 1) =
        b * (if i = Fin.castLE h2N 0 then 1 else 0) +
          μ.re * (if i = Fin.castLE h2N 1 then 1 else 0) := by
    rw [hconj]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply]
    rw [ho 1, ha1, ← ho 0, ← ho 1]
    simp [PiLp.single_apply]
  refine ⟨h2N, b, c, hc, hcb, hbc, ⟨Q, hQ⟩, ?_, ?_⟩
  · ext i j
    change (Qᵀ * A * Q) (Fin.castLE h2N i) (Fin.castLE h2N j) = _
    fin_cases i <;> fin_cases j <;> simp [hcol0, hcol1]
  · intro i j hi
    have hi0 : i ≠ Fin.castLE h2N 0 := by
      intro hh
      have hh' := congrArg Fin.val hh
      simp only [Fin.val_castLE, Fin.val_zero] at hh'
      omega
    have hi1 : i ≠ Fin.castLE h2N 1 := by
      intro hh
      have hh' := congrArg Fin.val hh
      simp only [Fin.val_castLE, Fin.val_one] at hh'
      omega
    change (Qᵀ * A * Q) i (Fin.castLE h2N j) = 0
    fin_cases j <;> simp [hcol0, hcol1, hi0, hi1]

end Paper.Spectral
