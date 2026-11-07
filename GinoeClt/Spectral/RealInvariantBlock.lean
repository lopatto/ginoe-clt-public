/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-! # A real invariant subspace of dimension one or two

This finite linear-algebra prerequisite holds for every nonempty real square
matrix, with no simple-spectrum hypothesis. It is not a Schur decomposition or
a change-of-variables/Jacobian theorem.
-/

@[expose] public section
noncomputable section
open scoped Matrix
open Module

namespace Paper.Spectral

theorem eigenvector_real_imag {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (μ : ℂ) (v : ι → ℂ)
    (hv : A.map Complex.ofRealHom *ᵥ v = μ • v) :
    A *ᵥ (fun i => (v i).re) = μ.re • (fun i => (v i).re) - μ.im • (fun i => (v i).im) ∧
      A *ᵥ (fun i => (v i).im) = μ.im • (fun i => (v i).re) + μ.re • (fun i => (v i).im) := by
  constructor
  · funext i
    have hi := congrArg (fun x : ι → ℂ => (x i).re) hv
    simpa [Matrix.mulVec, dotProduct, Complex.mul_re] using hi
  · funext i
    have hi := congrArg (fun x : ι → ℂ => (x i).im) hv
    simpa [Matrix.mulVec, dotProduct, Complex.mul_im, add_comm] using hi

/-- Every positive-size real matrix has a nonzero invariant real subspace of
dimension at most two. Repeated eigenvalues and defective matrices are included. -/
theorem exists_real_invariant_block (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ V : Submodule ℝ (Fin (n + 1) → ℝ),
      V ≠ ⊥ ∧ 0 < finrank ℝ V ∧ finrank ℝ V ≤ 2 ∧
        ∀ x ∈ V, A *ᵥ x ∈ V := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.map Complex.ofRealHom).toLin'
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have he : A.map Complex.ofRealHom *ᵥ v = μ • v := hv.apply_eq_smul
  let u : Fin (n + 1) → ℝ := fun i => (v i).re
  let w : Fin (n + 1) → ℝ := fun i => (v i).im
  have hre : A *ᵥ u = μ.re • u - μ.im • w := (eigenvector_real_imag A μ v he).1
  have him : A *ᵥ w = μ.im • u + μ.re • w := (eigenvector_real_imag A μ v he).2
  let V : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ (Set.range ![u, w])
  have hu : u ∈ V := Submodule.subset_span ⟨0, rfl⟩
  have hw : w ∈ V := Submodule.subset_span ⟨1, rfl⟩
  have hV : V ≠ ⊥ := by
    intro hh
    have hu0 : u = 0 := by simpa only [hh, Submodule.mem_bot] using hu
    have hw0 : w = 0 := by simpa only [hh, Submodule.mem_bot] using hw
    apply (Module.End.hasEigenvector_iff.mp hv).2
    funext i
    apply Complex.ext
    · exact congrFun hu0 i
    · exact congrFun hw0 i
  have hdim : finrank ℝ V ≤ 2 := by
    simpa only [V, Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := ℝ) ![u, w])
  have hinv : ∀ x ∈ V, A *ᵥ x ∈ V := by
    intro x hx
    apply Submodule.span_induction (p := fun x _ => A *ᵥ x ∈ V) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · change A *ᵥ u ∈ V
        rw [hre]
        exact V.sub_mem (V.smul_mem _ hu) (V.smul_mem _ hw)
      · change A *ᵥ w ∈ V
        rw [him]
        exact V.add_mem (V.smul_mem _ hu) (V.smul_mem _ hw)
    · simpa only [Matrix.mulVec_zero] using V.zero_mem
    · intro x y hx hy hfx hfy
      simpa only [Matrix.mulVec_add] using V.add_mem hfx hfy
    · intro c x hx hfx
      simpa only [Matrix.mulVec_smul] using V.smul_mem c hfx
  exact ⟨V, hV, Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hV), hdim, hinv⟩

end Paper.Spectral
