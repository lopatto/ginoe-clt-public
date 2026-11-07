/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.GaussianIntegrals
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Group.Integral

/-! # Absolute Gaussian path bounds before applying Fubini -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Topology

namespace Paper.Trace

/-- The open path with initial vertex z and n further vertices. -/
def pathGaussian (a : ℝ) : (n : ℕ) → ℂ → (Fin n → ℂ) → ℝ
  | 0, _, _ => 1
  | n + 1, z, u => Real.exp (-a * ‖u 0 - z‖ ^ 2) *
      pathGaussian a n (u 0) (Fin.tail u)

theorem pathGaussian_nonneg (a : ℝ) (n : ℕ) (z : ℂ) (u : Fin n → ℂ) :
    0 ≤ pathGaussian a n z u := by
  induction n generalizing z with
  | zero => simp [pathGaussian]
  | succ n ih => exact mul_nonneg (Real.exp_pos _).le (ih _ _)

theorem continuous_pathGaussian (a : ℝ) (n : ℕ) :
    Continuous (fun p : ℂ × (Fin n → ℂ) => pathGaussian a n p.1 p.2) := by
  induction n with
  | zero => simpa only [pathGaussian] using continuous_const (y := (1 : ℝ))
  | succ n ih =>
    have he : Continuous (fun p : ℂ × (Fin (n + 1) → ℂ) =>
        Real.exp (-a * ‖p.2 0 - p.1‖ ^ 2)) := by fun_prop
    have ht : Continuous (fun p : ℂ × (Fin (n + 1) → ℂ) =>
        pathGaussian a n (p.2 0) (Fin.tail p.2)) :=
      ih.comp (((continuous_apply 0).comp continuous_snd).prodMk
        (continuous_pi fun i : Fin n => (continuous_apply i.succ).comp continuous_snd))
    exact he.mul ht

theorem integrable_gaussian_sub {a : ℝ} (ha : 0 < a) (z : ℂ) :
    Integrable (fun w : ℂ => Real.exp (-a * ‖w - z‖ ^ 2)) :=
  (GaussianIntegrals.integrable_gaussian ha).comp_sub_right z

theorem integral_gaussian_sub {a : ℝ} (ha : 0 < a) (z : ℂ) :
    (∫ w : ℂ, Real.exp (-a * ‖w - z‖ ^ 2)) = Real.pi / a :=
  (integral_sub_right_eq_self (fun w : ℂ => Real.exp (-a * ‖w‖ ^ 2)) z).trans
    (GaussianIntegrals.gaussian_mass ha)

theorem integrable_integral_pathGaussian {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) :
    Integrable (pathGaussian a n z) ∧
      (∫ u : Fin n → ℂ, pathGaussian a n z u) = (Real.pi / a) ^ n := by
  induction n generalizing z with
  | zero =>
    have hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
      change (Measure.pi (fun _ : Fin 0 => (volume : Measure ℂ))) Set.univ = 1
      simp
    simp [pathGaussian, measureReal_def, hv]
  | succ n ih =>
    let F : (ℂ × (Fin n → ℂ)) → ℝ := fun p =>
      Real.exp (-a * ‖p.1 - z‖ ^ 2) * pathGaussian a n p.1 p.2
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hm : MeasurePreserving e.symm (volume : Measure (ℂ × (Fin n → ℂ))) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
    have heq : (pathGaussian a (n + 1) z) ∘ e.symm = F := by
      funext p
      simp [e, F, pathGaussian, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.zero_succAbove]
    have hFc : Continuous F := by
      change Continuous (fun p : ℂ × (Fin n → ℂ) =>
        Real.exp (-a * ‖p.1 - z‖ ^ 2) * pathGaussian a n p.1 p.2)
      have he : Continuous (fun p : ℂ × (Fin n → ℂ) =>
          Real.exp (-a * ‖p.1 - z‖ ^ 2)) := by fun_prop
      exact he.mul (continuous_pathGaussian a n)
    have hFnonneg (p : ℂ × (Fin n → ℂ)) : 0 ≤ F p :=
      mul_nonneg (Real.exp_pos _).le (pathGaussian_nonneg _ _ _ _)
    have hnorm (w : ℂ) : (∫ u : Fin n → ℂ, ‖F (w, u)‖) =
        Real.exp (-a * ‖w - z‖ ^ 2) * (Real.pi / a) ^ n := by
      calc
        (∫ u : Fin n → ℂ, ‖F (w, u)‖) = ∫ u : Fin n → ℂ, F (w, u) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun u => Real.norm_of_nonneg (hFnonneg (w, u))
        _ = _ := by
          dsimp only [F]
          rw [integral_const_mul, (ih w).2]
    have hFi : Integrable F := by
      apply (integrable_prod_iff hFc.aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall fun w =>
          (ih w).1.const_mul (Real.exp (-a * ‖w - z‖ ^ 2))
      · simpa only [hnorm] using
          (integrable_gaussian_sub ha z).mul_const ((Real.pi / a) ^ n)
    have hpath : Integrable (pathGaussian a (n + 1) z) := by
      apply (hm.integrable_comp_emb e.symm.measurableEmbedding).mp
      rw [heq]
      exact hFi
    refine ⟨hpath, ?_⟩
    calc
      (∫ u : Fin (n + 1) → ℂ, pathGaussian a (n + 1) z u) = ∫ p, F p := by
        rw [← hm.integral_comp' (pathGaussian a (n + 1) z)]
        change (∫ p, ((pathGaussian a (n + 1) z) ∘ e.symm) p) = ∫ p, F p
        rw [heq]
      _ = ∫ w : ℂ, ∫ u : Fin n → ℂ, F (w, u) := integral_prod F hFi
      _ = ∫ w : ℂ, Real.exp (-a * ‖w - z‖ ^ 2) * (Real.pi / a) ^ n := by
        apply integral_congr_ae
        filter_upwards with w
        dsimp only [F]
        rw [integral_const_mul, (ih w).2]
      _ = (Real.pi / a) ^ (n + 1) := by
        rw [integral_mul_const, integral_gaussian_sub ha z, pow_succ]
        ring

end Paper.Trace
