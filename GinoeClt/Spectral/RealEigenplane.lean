/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.RealInvariantBlock
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Eigenvalue-sensitive real invariant eigenplanes

The phase normalization uses Euclidean coordinate sums explicitly; it never
identifies the ambient Pi norm with the Euclidean norm.
-/

@[expose] public section
noncomputable section
open Module
open scoped Matrix ComplexConjugate BigOperators

namespace Paper.Spectral

def realifyingPhase (z : ℂ) : ℂ := Complex.exp (-(z.arg : ℂ) / 2 * Complex.I)

theorem realifyingPhase_norm (z : ℂ) : ‖realifyingPhase z‖ = 1 := by
  simp [realifyingPhase, Complex.norm_exp]

theorem realifyingPhase_sq_mul (z : ℂ) :
    realifyingPhase z ^ 2 * z = (‖z‖ : ℂ) := by
  have hc : realifyingPhase z ^ 2 = Complex.exp (-(z.arg : ℂ) * Complex.I) := by
    unfold realifyingPhase
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  calc
    realifyingPhase z ^ 2 * z =
        Complex.exp (-(z.arg : ℂ) * Complex.I) *
          ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) := by
      rw [hc]
      exact congrArg (fun w : ℂ => Complex.exp (-(z.arg : ℂ) * Complex.I) * w)
        (Complex.norm_mul_exp_arg_mul_I z).symm
    _ = (‖z‖ : ℂ) * (Complex.exp (-(z.arg : ℂ) * Complex.I) *
        Complex.exp ((z.arg : ℂ) * Complex.I)) := by ring
    _ = (‖z‖ : ℂ) := by
      rw [← Complex.exp_add]
      simp

lemma complex_vector_eq_zero_of_re_im {ι : Type*} (v : ι → ℂ)
    (hr : (fun i => (v i).re) = 0) (hi : (fun i => (v i).im) = 0) : v = 0 := by
  funext i
  exact Complex.ext (congrFun hr i) (congrFun hi i)

/-- A real complex eigenvalue yields a nonzero real eigenline, without
simplicity or diagonalizability. -/
theorem real_eigenvector_of_real_eigenvalue {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : A.map Complex.ofRealHom *ᵥ v = μ • v) (hμ : μ.im = 0) :
    ∃ u : ι → ℝ, u ≠ 0 ∧ A *ᵥ u = μ.re • u := by
  obtain ⟨hr, hi⟩ := eigenvector_real_imag A μ v he
  by_cases hu : (fun i => (v i).re) = 0
  · refine ⟨fun i => (v i).im, ?_, ?_⟩
    · intro hw
      exact hv (complex_vector_eq_zero_of_re_im v hu hw)
    · simpa only [hμ, zero_smul, zero_add] using hi
  · exact ⟨fun i => (v i).re, hu, by simpa only [hμ, zero_smul, sub_zero] using hr⟩

/-- For a nonreal eigenvalue, the actual real and imaginary parts of its
nonzero eigenvector form a real basis of its invariant plane. -/
theorem real_imag_linearIndependent_of_nonreal {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : A.map Complex.ofRealHom *ᵥ v = μ • v) (hμ : μ.im ≠ 0) :
    LinearIndependent ℝ ![(fun i => (v i).re), (fun i => (v i).im)] := by
  let u : ι → ℝ := fun i => (v i).re
  let w : ι → ℝ := fun i => (v i).im
  have hr : A *ᵥ u = μ.re • u - μ.im • w := (eigenvector_real_imag A μ v he).1
  have hi : A *ᵥ w = μ.im • u + μ.re • w := (eigenvector_real_imag A μ v he).2
  have hw : w ≠ 0 := by
    intro hw0
    have hz : μ.im • u = 0 := by simpa only [hw0, Matrix.mulVec_zero, smul_zero, add_zero] using hi.symm
    have hu0 : u = 0 := (smul_eq_zero.mp hz).resolve_left hμ
    exact hv (complex_vector_eq_zero_of_re_im v hu0 hw0)
  apply linearIndependent_fin2.mpr
  change w ≠ 0 ∧ ∀ a : ℝ, a • w ≠ u
  refine ⟨hw, fun a ha => ?_⟩
  have hh : a • (μ.im • u + μ.re • w) = μ.re • u - μ.im • w := by
    rw [← hi, ← Matrix.mulVec_smul, ha, hr]
  obtain ⟨i, hwi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hn
    apply hw
    funext i
    exact Classical.not_not.mp (fun hi => hn ⟨i, hi⟩)
  have hcomp := congrFun hh i
  have hrel := congrFun ha i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at hcomp hrel
  rw [← hrel] at hcomp
  have hz : (μ.im * (a ^ 2 + 1)) * w i = 0 := by nlinarith only [hcomp]
  have hz' : μ.im * (a ^ 2 + 1) = 0 := (mul_eq_zero.mp hz).resolve_right hwi
  have hfactor : a ^ 2 + 1 ≠ 0 := by positivity
  exact hfactor ((mul_eq_zero.mp hz').resolve_left hμ)

/-- A unit complex phase makes the real and imaginary parts orthogonal for
the Euclidean dot product, with the real squared coordinate norm at least the
imaginary squared coordinate norm. -/
theorem exists_phase_orthogonal_ordered {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (∑ i, (c * v i).re * (c * v i).im) = 0 ∧
        (∑ i, (c * v i).im ^ 2) ≤ ∑ i, (c * v i).re ^ 2 := by
  classical
  let q : ℂ := ∑ i, v i ^ 2
  let c := realifyingPhase q
  have hsum : (∑ i, (c * v i) ^ 2) = (‖q‖ : ℂ) := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact realifyingPhase_sq_mul q
  have him : (∑ i, (c * v i) ^ 2).im =
      2 * ∑ i, (c * v i).re * (c * v i).im := by
    rw [← Complex.imCLM_apply, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.imCLM_apply, pow_two, Complex.mul_im]
    ring
  have hre : (∑ i, (c * v i) ^ 2).re =
      (∑ i, (c * v i).re ^ 2) - ∑ i, (c * v i).im ^ 2 := by
    rw [← Complex.reCLM_apply, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.reCLM_apply, pow_two, Complex.mul_re]
  refine ⟨c, realifyingPhase_norm q, ?_, ?_⟩
  · have hz : 2 * (∑ i, (c * v i).re * (c * v i).im) = 0 := by
      rw [← him, hsum]
      rfl
    linarith
  · have hz : 0 ≤ (∑ i, (c * v i) ^ 2).re := by
      rw [hsum]
      exact norm_nonneg q
    rw [hre] at hz
    linarith

/-- A nonreal eigenvalue admits an eigenvector whose real and imaginary parts
are independent, Euclidean-orthogonal, and ordered by squared Euclidean norm.
This is a genuine source-gauge prerequisite, not a Schur or Jacobian claim. -/
theorem exists_orthogonal_eigenplane {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (he : A.map Complex.ofRealHom *ᵥ v = μ • v) (hμ : μ.im ≠ 0) :
    ∃ w : ι → ℂ, w ≠ 0 ∧ A.map Complex.ofRealHom *ᵥ w = μ • w ∧
      LinearIndependent ℝ ![(fun i => (w i).re), (fun i => (w i).im)] ∧
        (∑ i, (w i).re * (w i).im) = 0 ∧
          (∑ i, (w i).im ^ 2) ≤ ∑ i, (w i).re ^ 2 := by
  obtain ⟨c, hc, ho, hord⟩ := exists_phase_orthogonal_ordered v
  have hc0 : c ≠ 0 := by
    intro hh
    simp [hh] at hc
  have hw : c • v ≠ 0 := smul_ne_zero hc0 hv
  have hew : A.map Complex.ofRealHom *ᵥ (c • v) = μ • (c • v) := by
    rw [Matrix.mulVec_smul, he, smul_comm]
  refine ⟨c • v, hw, hew, real_imag_linearIndependent_of_nonreal A μ (c • v) hw hew hμ, ?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using ho
  · simpa only [Pi.smul_apply, smul_eq_mul] using hord

end Paper.Spectral
