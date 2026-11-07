/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SimpleSpectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-! # Characteristic polynomials and root multisets under scalar matrix scaling

The identities are pointwise and retain algebraic multiplicities. Simplicity
is not used to relate the frozen normalized matrix to its raw real ensemble.
-/

@[expose] public section
noncomputable section
open Polynomial Matrix
open scoped BigOperators Classical
namespace Paper.Spectral

variable {K : Type*} [Field K]

theorem charpoly_smul (N : ℕ) (M : Matrix (Fin N) (Fin N) K) (c : K) (hc : c ≠ 0) :
    (c • M).charpoly =
      Polynomial.C (c ^ N) * M.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) := by
  let f : K[X] →+* K[X] := Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)
  have hcc : (Polynomial.C c : K[X]) * Polynomial.C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  have hm : Matrix.charmatrix (c • M) = Polynomial.C c • f.mapMatrix M.charmatrix := by
    ext i j : 1
    change Matrix.charmatrix (c • M) i j =
      Polynomial.C c * (Matrix.charmatrix M i j).comp (Polynomial.C c⁻¹ * Polynomial.X)
    by_cases hij : i = j
    · subst j
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, smul_eq_mul,
        Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_mul]
      rw [mul_sub, ← mul_assoc, hcc, one_mul]
    · simp [Matrix.charmatrix_apply_ne, Matrix.smul_apply, smul_eq_mul, hij]
  calc
    (c • M).charpoly = Matrix.det (Polynomial.C c • f.mapMatrix M.charmatrix) :=
      congrArg Matrix.det hm
    _ = (Polynomial.C c) ^ N * (f.mapMatrix M.charmatrix).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    _ = (Polynomial.C c) ^ N * f M.charpoly :=
      congrArg (fun p => (Polynomial.C c) ^ N * p) (f.map_det M.charmatrix).symm
    _ = _ := by rw [← Polynomial.C_pow]; rfl

theorem roots_charpoly_smul (N : ℕ) (M : Matrix (Fin N) (Fin N) K) (c : K) (hc : c ≠ 0) :
    (c • M).charpoly.roots = M.charpoly.roots.map (fun z => c * z) := by
  rw [charpoly_smul N M c hc, Polynomial.roots_C_mul _ (pow_ne_zero N hc)]
  have hh := Polynomial.map_roots_comp_C_mul_X_add_C M.charpoly c⁻¹ 0
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hc))
  simp only [Polynomial.C_0, add_zero] at hh
  have he := congrArg (Multiset.map (fun z => c * z)) hh
  simp only [Multiset.map_map, Function.comp_def, ← mul_assoc, mul_inv_cancel₀ hc, one_mul] at he
  change Multiset.map id (M.charpoly.comp (C c⁻¹ * X)).roots = _ at he
  rw [Multiset.map_id] at he
  exact he


theorem complexRoots_smul (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    ((c • M).charpoly.map Complex.ofRealHom).roots =
      (M.charpoly.map Complex.ofRealHom).roots.map (fun z => (c : ℂ) * z) := by
  have hm : (c • M).map Complex.ofRealHom = (c : ℂ) • M.map Complex.ofRealHom := by
    ext i j
    change ((c * M i j : ℝ) : ℂ) = (c : ℂ) * (M i j : ℂ)
    exact Complex.ofReal_mul _ _
  rw [← Matrix.charpoly_map, hm,
    roots_charpoly_smul N (M.map Complex.ofRealHom) (c : ℂ) (by exact_mod_cast hc),
    Matrix.charpoly_map]

theorem eigenvalues_eq_scaled_rawRoots (n : ℕ) (M : SampleSpace n) :
    eigenvalues n M =
      (M.charpoly.map Complex.ofRealHom).roots.map
        (fun z => (((Real.sqrt (n + 1 : ℝ))⁻¹ : ℝ) : ℂ) * z) := by
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  exact complexRoots_smul (n + 1) M _ (inv_ne_zero hs)

theorem eigenvalues_nodup_ae (n : ℕ) :
    ∀ᵐ M ∂matrixLaw n, (eigenvalues n M).Nodup := by
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc : ((((Real.sqrt (n + 1 : ℝ))⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero hs
  filter_upwards [matrixLaw_complexRoots_nodup_ae n] with M hM
  rw [eigenvalues_eq_scaled_rawRoots]
  exact Multiset.Nodup.map (mul_right_injective₀ hc) hM

/-- The exact scaled count is the raw multiplicity count in sqrt(N) A,
pointwise even when roots repeat. -/
theorem count_eq_raw_count_scaled_domain (A : Set ℂ) (n : ℕ) (M : SampleSpace n) :
    count A n M =
      ((M.charpoly.map Complex.ofRealHom).roots.filter
        (fun z => z ∈ (fun w : ℂ => (Real.sqrt (n + 1 : ℝ) : ℂ) * w) '' A)).card := by
  classical
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hc : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold count
  rw [eigenvalues_eq_scaled_rawRoots, Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro z _
  constructor
  · intro hz
    refine ⟨(((Real.sqrt (n + 1 : ℝ))⁻¹ : ℝ) : ℂ) * z, hz, ?_⟩
    change (Real.sqrt (n + 1 : ℝ) : ℂ) *
      ((((Real.sqrt (n + 1 : ℝ))⁻¹ : ℝ) : ℂ) * z) = z
    rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  · rintro ⟨w, hw, rfl⟩
    change ((((Real.sqrt (n + 1 : ℝ))⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt (n + 1 : ℝ) : ℂ) * w)) ∈ A
    rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    exact hw

end Paper.Spectral
