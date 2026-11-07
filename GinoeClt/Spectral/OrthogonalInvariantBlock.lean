/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.RealInvariantBlock
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Basis

/-! # The first orthogonal invariant block of a real matrix

Only the first block step is proved here; no Schur-sector normalization or
Jacobian is asserted.
-/

@[expose] public section
noncomputable section
open Module Submodule
open scoped Matrix

namespace Paper.Spectral

/-- A finite-dimensional real subspace is spanned by an initial segment of
some orthonormal basis of the ambient space. -/
theorem exists_orthonormalBasis_adapted {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (N : ℕ) (hN : finrank ℝ E = N) (V : Submodule ℝ E) :
    ∃ o : OrthonormalBasis (Fin N) ℝ E,
      Submodule.span ℝ (o '' {i : Fin N | i.val < finrank ℝ V}) = V := by
  classical
  let k := finrank ℝ V
  have hk : k ≤ N := (Submodule.finrank_le V).trans_eq hN
  let b := stdOrthonormalBasis ℝ V
  let s : Set (Fin N) := {i | i.val < k}
  let v : Fin N → E := fun i => if hi : i.val < k then (b ⟨i.val, hi⟩ : E) else 0
  let e : s → Fin k := fun i => ⟨i.val.val, i.property⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun j : Fin k => j.val) hij
  have hb := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    convert hb.comp e he using 1
    funext i
    have hi : i.val.val < k := i.property
    change (if h : i.val.val < k then (b ⟨i.val.val, h⟩ : E) else 0) = _
    rw [dite_eq_left hi]
    rfl
  obtain ⟨o, ho⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simpa only [Fintype.card_fin] using hN)
  have hfirst : ∀ j : Fin k, o (Fin.castLE hk j) = (b j : E) := by
    intro j
    rw [ho _ j.isLt]
    change (if hi : j.val < k then (b ⟨j.val, hi⟩ : E) else 0) = (b j : E)
    rw [dite_eq_left j.isLt]
  refine ⟨o, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    rw [ho i hi]
    have hi' : i.val < k := hi
    change (if h : i.val < k then (b ⟨i.val, h⟩ : E) else 0) ∈ V
    rw [dite_eq_left hi']
    exact (b ⟨i.val, hi'⟩).property
  · have hbspan : Submodule.span ℝ (Set.range (fun j : Fin k => (b j : E))) = V := by
      have hh := Submodule.map_span V.subtype (Set.range b)
      have hbtop : Submodule.span ℝ (Set.range b) = ⊤ := by
        simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
      rw [hbtop, Submodule.map_subtype_top] at hh
      simpa only [← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using hh.symm
    calc V = Submodule.span ℝ (Set.range (fun j : Fin k => (b j : E))) := hbspan.symm
         _ ≤ Submodule.span ℝ (o '' {i : Fin N | i.val < finrank ℝ V}) := by
           apply Submodule.span_mono
           rintro _ ⟨j, rfl⟩
           exact ⟨Fin.castLE hk j, j.isLt, hfirst j⟩

/-- The first real orthogonal block step, for every positive-size real matrix.
The initial block has size one or two; the lower-left rectangular block vanishes. -/
theorem exists_orthogonal_invariant_block (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ k ≤ n + 1 ∧
      ∃ Q : Matrix.orthogonalGroup (Fin (n + 1)) ℝ,
        ∀ i j : Fin (n + 1), k ≤ i.val → j.val < k →
          ((Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ᵀ * A * Q) i j = 0 := by
  classical
  obtain ⟨V, _, hpos, htwo, hInv⟩ := exists_real_invariant_block n A
  let e := WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)
  let W := V.map e.symm.toLinearMap
  let f := e.symm.toLinearMap.comp (A.toLin'.comp e.toLinearMap)
  have hdim : finrank ℝ W = finrank ℝ V := e.symm.finrank_map_eq V
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
  let k := finrank ℝ W
  have hk12 : k = 1 ∨ k = 2 := by
    dsimp only [k]
    rw [hdim]
    omega
  have hkN : k ≤ n + 1 := (Submodule.finrank_le W).trans_eq hE
  have hWInv : ∀ x ∈ W, f x ∈ W := by
    rintro x ⟨y, hy, rfl⟩
    change e.symm (A *ᵥ e (e.symm y)) ∈ W
    rw [e.apply_symm_apply]
    exact Submodule.mem_map_of_mem (hInv y hy)
  obtain ⟨o, ho⟩ := exists_orthonormalBasis_adapted (n + 1) hE W
  let s := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  let Q := s.toBasis.toMatrix o
  let R := o.toBasis.toMatrix s
  have hQ : Q ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
    s.toMatrix_orthonormalBasis_mem_orthogonal o
  have hQQ : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hQ
  have hRQ : R * Q = 1 := by
    change o.toBasis.toMatrix s.toBasis * s.toBasis.toMatrix o.toBasis = 1
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hR : R = Qᵀ := by
    calc R = R * (Q * Qᵀ) := by rw [hQQ, Matrix.mul_one]
         _ = (R * Q) * Qᵀ := by rw [Matrix.mul_assoc]
         _ = Qᵀ := by rw [hRQ, Matrix.one_mul]
  have hmat : LinearMap.toMatrix s.toBasis s.toBasis f = A := by
    ext i j
    simp [LinearMap.toMatrix_apply, s, f, e, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.toLin'_apply]
  have hconj : Qᵀ * A * Q = LinearMap.toMatrix o.toBasis o.toBasis f := by
    rw [← hR, ← hmat]
    change o.toBasis.toMatrix s.toBasis * LinearMap.toMatrix s.toBasis s.toBasis f *
      s.toBasis.toMatrix o.toBasis = LinearMap.toMatrix o.toBasis o.toBasis f
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      o.toBasis s.toBasis o.toBasis s.toBasis f
  refine ⟨k, hk12, hkN, ⟨Q, hQ⟩, fun i j hi hj => ?_⟩
  change (Qᵀ * A * Q) i j = 0
  rw [hconj]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply]
  change o.repr (f (o j)) i = 0
  have hjW : o j ∈ W := by
    rw [← ho]
    exact Submodule.subset_span (Set.mem_image_of_mem o hj)
  have hfW := hWInv (o j) hjW
  rw [← ho] at hfW
  have hf' : f (o j) ∈ Submodule.span ℝ
      (o.toBasis '' {i : Fin (n + 1) | i.val < finrank ℝ W}) := by
    simpa only [OrthonormalBasis.coe_toBasis] using hfW
  have hs := o.toBasis.repr_support_subset_of_mem_span
    {i : Fin (n + 1) | i.val < finrank ℝ W} hf'
  have hz := (Finsupp.mem_supported' _ _).mp ((Finsupp.mem_supported ℝ _).mpr hs) i
    (show i ∉ {i : Fin (n + 1) | i.val < finrank ℝ W} from not_lt.mpr hi)
  simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using hz

end Paper.Spectral
