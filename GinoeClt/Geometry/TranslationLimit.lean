/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.SmoothTranslation
public import GinoeClt.Geometry.SmoothDuality
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Directional translation quotients of an actual Lipschitz domain -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Paper.Geometry

lemma test_differenceQuotient_tendsto {A : Set ℂ} (hb : Bornology.IsBounded A)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφC : HasCompactSupport φ) (u : ℂ) :
    Tendsto (fun t : ℝ => ∫ y in A, (φ (y - t • u) - φ y) / t) (𝓝[>] 0)
      (𝓝 (-∫ y in A, fderiv ℝ φ y u)) := by
  obtain ⟨K, hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hφC one_ne_zero
  have hFm : ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun y => (φ (y - t • u) - φ y) / t) (volume.restrict A) := by
    exact Eventually.of_forall (fun t =>
      ((hφ.continuous.comp (continuous_id.sub continuous_const)).sub hφ.continuous).div_const t |>.aestronglyMeasurable)
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ y ∂volume.restrict A,
      ‖(φ (y - t • u) - φ y) / t‖ ≤ (K : ℝ) * ‖u‖ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ae_of_all _ (fun y => by
      have hh := hK.dist_le_mul (y - t • u) y
      have hdist : dist (y - t • u) y = t * ‖u‖ := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      rw [Real.dist_eq, hdist] at hh
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, div_le_iff₀ ht]
      nlinarith)
  have hlim : ∀ᵐ y ∂volume.restrict A, Tendsto
      (fun t : ℝ => (φ (y - t • u) - φ y) / t) (𝓝[>] 0) (𝓝 (-fderiv ℝ φ y u)) := by
    filter_upwards with y
    have hh := (line_hasDerivAt hφ y (-u) 0).tendsto_slope_zero_right
    have hh' : Tendsto (fun t : ℝ => t⁻¹ * (φ (y - t • u) - φ y)) (𝓝[>] 0)
        (𝓝 (-fderiv ℝ φ y u)) := by
      simpa only [zero_add, zero_smul, add_zero, smul_neg, ← sub_eq_add_neg,
        sub_zero, map_neg, smul_eq_mul] using hh
    convert! hh' using 1
    ext t
    simp only [div_eq_mul_inv]
    ring
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict A) (fun _ : ℂ => (K : ℝ) * ‖u‖) hFm hbound
      (integrableOn_const hb.measure_lt_top.ne) hlim
  simpa only [integral_neg] using hh

lemma test_differenceQuotient_boundary_tendsto {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφC : HasCompactSupport φ) (u : ℂ) :
    Tendsto (fun t : ℝ => ∫ y in A, (φ (y - t • u) - φ y) / t) (𝓝[>] 0)
      (𝓝 (-∫ y, φ y * inner ℝ u (boundaryNormal A hA y) ∂boundarySurface A)) := by
  simpa only [(boundaryNormal_spec hA).2.2 φ hφ hφC u, boundarySurface] using
    test_differenceQuotient_tendsto (Paper.admissible_isBounded hA) hφ hφC u

lemma integrable_mul_bounded_one {f ψ : ℂ → ℝ} (hf : Integrable f)
    (hψ : Measurable ψ) (hψb : ∀ x, |ψ x| ≤ 1) : Integrable (fun x => f x * ψ x) := by
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hψ.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hψb x)

lemma indicator_test_translation_eq {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) {φ : ℂ → ℝ} (hφ : Measurable φ)
    (hφb : ∀ x, |φ x| ≤ 1) (v : ℂ) :
    (∫ x, (A.indicator (1 : ℂ → ℝ) (x + v) - A.indicator (1 : ℂ → ℝ) x) * φ x) =
      ∫ y in A, φ (y - v) - φ y := by
  classical
  let b : ℂ → ℝ := A.indicator 1
  have hbi : Integrable b := indicator_integrable hA hb
  have hp0 := integrable_mul_bounded_one hbi hφ hφb
  have hp1 := integrable_mul_bounded_one (hbi.comp_add_right v) hφ hφb
  have hsi0 : IntegrableOn φ A := by
    refine (integrableOn_const (C := (1 : ℝ)) hb.measure_lt_top.ne).mono' hφ.aestronglyMeasurable.restrict ?_
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hφb x)
  have hsi1 : IntegrableOn (fun y => φ (y - v)) A := by
    refine (integrableOn_const (C := (1 : ℝ)) hb.measure_lt_top.ne).mono'
      (hφ.comp (measurable_id.sub measurable_const)).aestronglyMeasurable.restrict ?_
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hφb (x - v))
  have hind : ∀ ψ : ℂ → ℝ, (∫ y, b y * ψ y) = ∫ y in A, ψ y := by
    intro ψ
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ A <;> simp [b, hy]
  have hshift : (∫ x, b (x + v) * φ x) = ∫ y in A, φ (y - v) := by
    calc
      (∫ x, b (x + v) * φ x) = ∫ y, b y * φ (y - v) := by
        simpa only [add_sub_cancel_right] using
          (integral_add_right_eq_self (fun y : ℂ => b y * φ (y - v)) v)
      _ = _ := hind _
  calc (∫ x, (b (x + v) - b x) * φ x) =
      (∫ x, b (x + v) * φ x) - (∫ x, b x * φ x) := by
        rw [← integral_sub hp1 hp0]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => sub_mul _ _ _)
    _ = _ := by rw [hshift, hind, integral_sub hsi1 hsi0]

lemma abs_indicator_test_translation_le {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) {φ : ℂ → ℝ} (hφ : Measurable φ)
    (hφb : ∀ x, |φ x| ≤ 1) (u : ℂ) {t : ℝ} (ht : 0 < t) :
    |∫ y in A, (φ (y - t • u) - φ y) / t| ≤
      (∫ x, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t := by
  rw [integral_div, ← indicator_test_translation_eq hA hb hφ hφb, abs_div, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  calc |∫ x, (A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x) * φ x| ≤
      ∫ x, |(A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x) * φ x| :=
        abs_integral_le_integral_abs
    _ ≤ _ := by
      have hbi := indicator_integrable hA hb
      have hdi : Integrable (fun x => A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x) := by
        convert! (hbi.comp_add_right (t • u)).sub hbi using 1
      apply integral_mono
        (by simpa only [Real.norm_eq_abs] using (integrable_mul_bounded_one hdi hφ hφb).norm)
        (integrable_abs_sub (hbi.comp_add_right (t • u)) hbi)
      intro x
      change |(A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x) * φ x| ≤
        |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hφb x)

/-- The actual directional first variation of the indicator in L¹. Both inequalities
are proved: mollification gives the upper bound and smooth-test duality the lower. -/
theorem indicator_translation_quotient_tendsto {A : Set ℂ}
    (hA : Paper.IsAdmissibleLipschitzDomain A) (u : ℂ) :
    Tendsto (fun t : ℝ =>
      (∫ x, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t)
      (𝓝[>] 0) (𝓝 (directionalPerimeter A hA u)) := by
  let : IsFiniteMeasure (boundarySurface A) := ⟨boundarySurface_lt_top hA⟩
  let a : ℂ → ℝ := fun y => inner ℝ u (boundaryNormal A hA y)
  have ham : Measurable a := (innerSL ℝ u).continuous.measurable.comp (boundaryNormal_spec hA).1
  have hab : ∀ᵐ y ∂boundarySurface A, |a y| ≤ ‖u‖ := by
    filter_upwards [(boundaryNormal_spec hA).2.1] with y hy
    simpa only [a, hy, mul_one] using abs_real_inner_le_norm u (boundaryNormal A hA y)
  apply tendsto_order.2
  constructor
  · intro c hc
    have hε : 0 < (directionalPerimeter A hA u - c) / 2 := by linarith
    obtain ⟨φ, hφ, hφC, hφb, hφerr⟩ := exists_smoothTest_integral_abs_sub_le
      (boundarySurface A) ham (norm_nonneg u) hab hε
    have hIgt : c < ∫ y, φ y * a y ∂boundarySurface A := by
      change directionalPerimeter A hA u - (∫ y, φ y * a y ∂boundarySurface A) ≤ _ at hφerr
      linarith
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hweak := (test_differenceQuotient_boundary_tendsto hA hφ1 hφC u).neg
    have hweak' : Tendsto (fun t : ℝ => -(∫ y in A, (φ (y - t • u) - φ y) / t))
        (𝓝[>] 0) (𝓝 (∫ y, φ y * a y ∂boundarySurface A)) := by
      simpa only [neg_neg, a] using hweak
    have hev := (tendsto_order.1 hweak').1 c hIgt
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htp
    exact ht.trans_le ((neg_le_abs _).trans
      (abs_indicator_test_translation_le hA.1.measurableSet (Paper.admissible_isBounded hA)
        hφ.continuous.measurable hφb u htp))
  · intro c hc
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply lt_of_le_of_lt _ hc
    apply (div_le_iff₀ ht).2
    simpa only [mul_comm] using indicator_translation_le hA u ht.le

end Paper.Geometry
