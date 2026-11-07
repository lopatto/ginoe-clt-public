/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.NonlocalCrossing
public import GinoeClt.Analysis.GaussianIntegrals
public import GinoeClt.Cumulants.AsymptoticCumulants

/-! # The two manuscript Gaussian crossing normalizations -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace Paper.Geometry

def gaussianCrossing (A : Set ℂ) (a : ℝ) (N : ℕ) : ℝ :=
  ∫ z in A, ∫ w in Aᶜ, Real.exp (-a * (N : ℝ) * ‖z - w‖ ^ 2)

lemma norm_rescale_sq (N : ℕ) (z : ℂ) : ‖Real.sqrt (N : ℝ) • z‖ ^ 2 = (N : ℝ) * ‖z‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg N)]

lemma gaussian_crossing_tendsto_of_normalization {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) {a c : ℝ} (hc : 0 < c)
    (hnorm : (∫ z : ℂ, ‖z‖ * (c * Real.exp (-a * ‖z‖ ^ 2))) = 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) * gaussianCrossing A a N) atTop
      (𝓝 ((Paper.boundaryMeasure A).toReal / (c * Real.pi))) := by
  let J : ℂ → ℝ := fun z => c * Real.exp (-a * ‖z‖ ^ 2)
  have hJm : Measurable J := by unfold J; fun_prop
  have hJnn : ∀ z, 0 ≤ J z := fun z => mul_nonneg hc.le (Real.exp_pos _).le
  have hJr : Function.IsRadial J := by
    intro z w hzw
    change c * Real.exp (-a * ‖z‖ ^ 2) = c * Real.exp (-a * ‖w‖ ^ 2)
    rw [show ‖z‖ = ‖w‖ from hzw]
  have hh := (Paper.nonlocal_perimeter_limit hA hJm hJnn hJr hnorm).const_mul c⁻¹
  have hkernel : ∀ N : ℕ, (∫ z in A, ∫ w in Aᶜ,
      J (Real.sqrt (N : ℝ) • (z - w))) = c * gaussianCrossing A a N := by
    intro N
    have heq : ∀ z w : ℂ, J (Real.sqrt (N : ℝ) • (z - w)) =
        c * Real.exp (-a * (N : ℝ) * ‖z - w‖ ^ 2) := by
      intro z w
      dsimp only [J]
      rw [norm_rescale_sq]
      congr 2
      ring
    simp_rw [heq, integral_const_mul]
    rfl
  have heq : (fun N : ℕ => c⁻¹ * ((N : ℝ) ^ (3 / 2 : ℝ) *
      (∫ z in A, ∫ w in Aᶜ, J (Real.sqrt (N : ℝ) • (z - w))))) =
      (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) * gaussianCrossing A a N) := by
    funext N
    rw [hkernel]
    field_simp
  rw [heq] at hh
  convert! hh using 1
  congr 1
  field_simp

/-- Both literal normalized kernels used in the manuscript satisfy Lemma 2.5. -/
theorem unit_normalized_gaussian_crossing_tendsto {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) *
      (∫ z in A, ∫ w in Aᶜ, (2 / Real.pi ^ (3 / 2 : ℝ)) *
        Real.exp (-‖Real.sqrt (N : ℝ) • (z - w)‖ ^ 2))) atTop
      (𝓝 ((Paper.boundaryMeasure A).toReal / Real.pi)) := by
  convert! Paper.nonlocal_perimeter_limit hA
    (J := fun z : ℂ => (2 / Real.pi ^ (3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2)) ?_ ?_ ?_ ?_ using 1
  · fun_prop
  · intro z
    positivity
  · intro z w hzw
    change (2 / Real.pi ^ (3 / 2 : ℝ)) * Real.exp (-‖z‖ ^ 2) =
      (2 / Real.pi ^ (3 / 2 : ℝ)) * Real.exp (-‖w‖ ^ 2)
    rw [show ‖z‖ = ‖w‖ from hzw]
  · exact Paper.GaussianIntegrals.unit_crossing_normalization

theorem half_normalized_gaussian_crossing_tendsto {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) *
      (∫ z in A, ∫ w in Aᶜ, (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) *
        Real.exp (-‖Real.sqrt (N : ℝ) • (z - w)‖ ^ 2 / 2))) atTop
      (𝓝 ((Paper.boundaryMeasure A).toReal / Real.pi)) := by
  convert! Paper.nonlocal_perimeter_limit hA
    (J := fun z : ℂ => (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) * Real.exp (-‖z‖ ^ 2 / 2)) ?_ ?_ ?_ ?_ using 1
  · fun_prop
  · intro z
    positivity
  · intro z w hzw
    change (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) * Real.exp (-‖z‖ ^ 2 / 2) =
      (1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) * Real.exp (-‖w‖ ^ 2 / 2)
    rw [show ‖z‖ = ‖w‖ from hzw]
  · exact Paper.GaussianIntegrals.half_crossing_normalization

/-- Equation (15): the unnormalized unit Gaussian crossing limit. -/
theorem unit_gaussian_crossing_tendsto {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) * gaussianCrossing A 1 N) atTop
      (𝓝 (Real.sqrt Real.pi / 2 * (Paper.boundaryMeasure A).toReal)) := by
  have hn : (∫ z : ℂ, ‖z‖ * ((2 / Real.pi ^ (3 / 2 : ℝ)) * Real.exp (-(1 : ℝ) * ‖z‖ ^ 2))) = 1 := by
    simpa only [neg_mul, one_mul] using Paper.GaussianIntegrals.unit_crossing_normalization
  have hh := gaussian_crossing_tendsto_of_normalization hA (by positivity : 0 < 2 / Real.pi ^ (3 / 2 : ℝ)) hn
  convert! hh using 1
  congr 1
  rw [show Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]]
  field_simp

/-- The second Gaussian crossing required by the path trace estimate. -/
theorem half_gaussian_crossing_tendsto {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) * gaussianCrossing A (1 / 2) N) atTop
      (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi * (Paper.boundaryMeasure A).toReal)) := by
  have hn : (∫ z : ℂ, ‖z‖ * ((1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) *
      Real.exp (-(1 / 2 : ℝ) * ‖z‖ ^ 2))) = 1 := by
    convert! Paper.GaussianIntegrals.half_crossing_normalization using 1
    congr 1
    ext z
    congr 2
    ring
  have hh := gaussian_crossing_tendsto_of_normalization hA
    (by positivity : 0 < 1 / (Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ))) hn
  convert! hh using 1
  congr 1
  rw [show Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]]
  field_simp

lemma crossing_bigO_of_tendsto {A : Set ℂ} {a v : ℝ}
    (hh : Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) * gaussianCrossing A a N) atTop (𝓝 v)) :
    (fun N : ℕ => gaussianCrossing A a N) =O[atTop] (fun N => (N : ℝ) ^ (-3 / 2 : ℝ)) := by
  have hgf : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-3 / 2 : ℝ) = 0 → gaussianCrossing A a N = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN hzero
    exact False.elim ((Real.rpow_pos_of_pos (by exact_mod_cast hN) (-3 / 2 : ℝ)).ne' hzero)
  apply Asymptotics.isBigO_of_div_tendsto_nhds hgf v
  convert! hh using 1
  ext N
  change gaussianCrossing A a N / ((N : ℝ) ^ (-3 / 2 : ℝ)) = (N : ℝ) ^ (3 / 2 : ℝ) * gaussianCrossing A a N
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg (Nat.cast_nonneg N), div_inv_eq_mul]
  ring

theorem unit_gaussian_crossing_bigO {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) :
    (fun N : ℕ => gaussianCrossing A 1 N) =O[atTop] (fun N => (N : ℝ) ^ (-3 / 2 : ℝ)) :=
  crossing_bigO_of_tendsto (unit_gaussian_crossing_tendsto hA)

theorem half_gaussian_crossing_bigO {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) :
    (fun N : ℕ => gaussianCrossing A (1 / 2) N) =O[atTop] (fun N => (N : ℝ) ^ (-3 / 2 : ℝ)) :=
  crossing_bigO_of_tendsto (half_gaussian_crossing_tendsto hA)

end Paper.Geometry
