/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.GraphArea

/-! # Measurable linear-approximation pieces for a real Lipschitz graph

The scalar derivative estimate uses Mathlib's Lebesgue-density theorem. No
pointwise uniqueness of a derivative within an arbitrary measurable set is assumed.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Paper.Geometry.GraphArea

lemma real_clm_eq_smul_id (A : ℝ →L[ℝ] ℝ) :
    A = A 1 • ContinuousLinearMap.id ℝ ℝ := by
  ext; simp

/-- Linear approximation controls the ordinary derivative almost everywhere,
by the Lebesgue-density estimate on the measurable parameter set. -/
theorem ae_abs_deriv_sub_le {f : ℝ → ℝ} {S : Set ℝ} {a : ℝ} {ε : ℝ≥0}
    (hS : MeasurableSet S) (hD : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (h : ApproximatesLinearOn f (a • ContinuousLinearMap.id ℝ ℝ) S ε) :
    ∀ᵐ x ∂volume.restrict S, |deriv f x - a| ≤ (ε : ℝ) := by
  have hFD : ∀ x ∈ S, HasFDerivWithinAt f (fderiv ℝ f x) S x :=
    fun x hx => (hD x hx).hasFDerivAt.hasFDerivWithinAt
  have hAE := h.norm_fderiv_sub_le (μ := volume) hS (fderiv ℝ f) hFD
  filter_upwards [hAE] with x hx
  have hop : ‖fderiv ℝ f x - a • ContinuousLinearMap.id ℝ ℝ‖ ≤ (ε : ℝ) := by
    exact_mod_cast hx
  have heval := (fderiv ℝ f x - a • ContinuousLinearMap.id ℝ ℝ).le_opNorm (1 : ℝ)
  have heval' : |deriv f x - a| ≤
      ‖fderiv ℝ f x - a • ContinuousLinearMap.id ℝ ℝ‖ := by
    simpa [fderiv_apply_one_eq_deriv, Real.norm_eq_abs] using heval
  exact heval'.trans hop

/-- Countably many genuine measurable pieces, with scalar slopes, both a
uniform difference estimate and almost-everywhere ordinary derivative control. -/
theorem exists_approximating_partition {f : ℝ → ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hD : ∀ x ∈ S, DifferentiableAt ℝ f x)
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (u : ℕ → Set ℝ) (a : ℕ → ℝ),
      (∀ n, MeasurableSet (u n)) ∧ Pairwise (Function.onFun Disjoint u) ∧
      (⋃ n, u n) = S ∧ (∀ n, u n ⊆ S) ∧
      (∀ n, ApproximatesLinearOn f (a n • ContinuousLinearMap.id ℝ ℝ) (u n) ε) ∧
      (∀ n, ∀ᵐ x ∂volume.restrict (u n), |deriv f x - a n| ≤ (ε : ℝ)) := by
  obtain ⟨t, A, hdisj, hmeas, hcover, happ, _⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f S (fderiv ℝ f)
      (fun x hx => (hD x hx).hasFDerivAt.hasFDerivWithinAt)
      (fun _ => ε) (fun _ => hε.ne')
  let u : ℕ → Set ℝ := fun n => S ∩ t n
  let a : ℕ → ℝ := fun n => A n 1
  have hum : ∀ n, MeasurableSet (u n) := fun n => hS.inter (hmeas n)
  have hus : ∀ n, u n ⊆ S := fun _ => inter_subset_left
  have hua : ∀ n, ApproximatesLinearOn f (a n • ContinuousLinearMap.id ℝ ℝ) (u n) ε := by
    intro n
    rw [← real_clm_eq_smul_id (A n)]
    exact happ n
  refine ⟨u, a, hum, ?_, ?_, hus, hua, ?_⟩
  · intro i j hij
    exact Disjoint.mono inter_subset_right inter_subset_right (hdisj hij)
  · apply Set.Subset.antisymm
    · exact iUnion_subset hus
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨n, hx, hn⟩
  · intro n
    exact ae_abs_deriv_sub_le (hum n) (fun x hx => hD x (hus n hx)) (hua n)

end Paper.Geometry.GraphArea
