/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.TranslationLimit
public import GinoeClt.Geometry.RadialProjection

/-! # Integrating the directional first variation against a radial first moment -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Paper.Geometry

lemma measurable_indicator_translation_norm {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable (fun v : ℂ => ∫ x : ℂ,
      |A.indicator (1 : ℂ → ℝ) (x + v) - A.indicator (1 : ℂ → ℝ) x|) := by
  have hb : Measurable (A.indicator (1 : ℂ → ℝ)) := measurable_one.indicator hA
  have hm : Measurable (fun p : ℂ × ℂ =>
      |A.indicator (1 : ℂ → ℝ) (p.2 + p.1) - A.indicator (1 : ℂ → ℝ) p.2|) :=
    continuous_abs.measurable.comp ((hb.comp (measurable_snd.add measurable_fst)).sub
      (hb.comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma directionalPerimeter_le {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A) (u : ℂ) :
    directionalPerimeter A hA u ≤ ‖u‖ * (boundarySurface A).real univ := by
  let : IsFiniteMeasure (boundarySurface A) := ⟨boundarySurface_lt_top hA⟩
  have hb : ∀ᵐ y ∂boundarySurface A, |inner ℝ u (boundaryNormal A hA y)| ≤ ‖u‖ := by
    filter_upwards [(boundaryNormal_spec hA).2.1] with y hy
    simpa only [hy, mul_one] using abs_real_inner_le_norm u (boundaryNormal A hA y)
  have hi : Integrable (fun y => |inner ℝ u (boundaryNormal A hA y)|) (boundarySurface A) := by
    simpa only [Real.norm_eq_abs] using (integrable_boundaryNormal_component hA u).norm
  have hh := integral_mono_ae hi (integrable_const ‖u‖) hb
  change (∫ y, |inner ℝ u (boundaryNormal A hA y)| ∂boundarySurface A) ≤ _
  simpa only [integral_const, smul_eq_mul, mul_comm] using hh

lemma integral_kernel_directionalPerimeter {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z) (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) :
    (∫ u : ℂ, J u * directionalPerimeter A hA u) =
      (2 / Real.pi) * (boundarySurface A).real univ := by
  let σ := boundarySurface A
  let ν := boundaryNormal A hA
  let : IsFiniteMeasure σ := ⟨boundarySurface_lt_top hA⟩
  have hνm : Measurable ν := (boundaryNormal_spec hA).1
  have hνp : ∀ᵐ p : ℂ × ℂ ∂(volume.prod σ), ‖ν p.2‖ = 1 := by
    have hm : Measurable (fun p : ℂ × ℂ => ‖ν p.2‖) := hνm.norm.comp measurable_snd
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).2
    exact ae_of_all _ (fun _ => (boundaryNormal_spec hA).2.1)
  have hMm : Integrable (fun z : ℂ => ‖z‖ * J z) := integrable_firstMoment hmoment
  have hpi : Integrable (fun p : ℂ × ℂ => J p.1 * |inner ℝ p.1 (ν p.2)|) (volume.prod σ) := by
    have hb := hMm.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℂ => (1 : ℝ)) σ)
    refine hb.mono' ?_ ?_
    · exact ((hJm.comp measurable_fst).mul (continuous_abs.measurable.comp
        ((continuous_inner (𝕜 := ℝ)).measurable.comp
          (measurable_fst.prodMk (hνm.comp measurable_snd))))).aestronglyMeasurable
    · filter_upwards [hνp] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hJnn _) (abs_nonneg _)), mul_one]
      have hh : |inner ℝ p.1 (ν p.2)| ≤ ‖p.1‖ := by
        simpa only [hp, mul_one] using abs_real_inner_le_norm p.1 (ν p.2)
      nlinarith [hJnn p.1]
  calc (∫ u : ℂ, J u * directionalPerimeter A hA u) =
      ∫ u : ℂ, ∫ y, J u * |inner ℝ u (ν y)| ∂σ := by
        apply integral_congr_ae
        filter_upwards with u
        rw [integral_const_mul]
        rfl
    _ = ∫ y, ∫ u : ℂ, J u * |inner ℝ u (ν y)| ∂volume ∂σ := integral_integral_swap hpi
    _ = ∫ _y : ℂ, 2 / Real.pi ∂σ := by
      apply integral_congr_ae
      filter_upwards [(boundaryNormal_spec hA).2.1] with y hy
      simpa only [mul_comm] using radial_projection_integral hJ hmoment hy
    _ = _ := by simp only [integral_const, smul_eq_mul, σ, mul_comm]

/-- Dominated convergence applies to the actual L¹ translation quotient using
only the radial kernel's normalized first moment. -/
theorem radial_translation_integral_tendsto {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z) (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, J u *
      ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t))
      (𝓝[>] 0) (𝓝 ((2 / Real.pi) * (boundarySurface A).real univ)) := by
  let B : ℝ := (boundarySurface A).real univ
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hboundInt : Integrable (fun u : ℂ => (‖u‖ * J u) * B) :=
    (integrable_firstMoment hmoment).mul_const B
  have hm : ∀ᶠ t : ℝ in 𝓝[>] 0, AEStronglyMeasurable (fun u : ℂ => J u *
      ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t)) volume := by
    apply Eventually.of_forall
    intro t
    have hs : Measurable (fun u : ℂ => t • u) := (continuous_const_smul t).measurable
    have hl := (measurable_indicator_translation_norm hA.1.measurableSet).comp hs
    exact (hJm.mul (hl.div_const t)).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ u : ℂ ∂volume,
      ‖J u * ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t)‖ ≤
        (‖u‖ * J u) * B := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ae_of_all _ (fun u => by
      have hq0 : 0 ≤ (∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t :=
        div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) ht.le
      have hq : (∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t ≤
          ‖u‖ * B := by
        apply (div_le_iff₀ ht).2
        have hh := (indicator_translation_le hA u ht.le).trans
          (mul_le_mul_of_nonneg_left (directionalPerimeter_le hA u) ht.le)
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hJnn _) hq0)]
      nlinarith [hJnn u])
  have hlim : ∀ᵐ u : ℂ ∂volume, Tendsto (fun t : ℝ => J u *
      ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t))
      (𝓝[>] 0) (𝓝 (J u * directionalPerimeter A hA u)) := by
    exact ae_of_all _ (fun u => (indicator_translation_quotient_tendsto hA u).const_mul (J u))
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℂ => (‖u‖ * J u) * B) hm hbound hboundInt hlim
  simpa only [integral_kernel_directionalPerimeter hA hJm hJnn hJ hmoment] using hh

lemma integrable_kernel_translation_norm {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun u : ℂ => J u *
      (∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|)) := by
  have hs : Measurable (fun u : ℂ => t • u) := (continuous_const_smul t).measurable
  have hm := (measurable_indicator_translation_norm hA.1.measurableSet).comp hs
  refine ((integrable_firstMoment hmoment).mul_const
    (t * (boundarySurface A).real univ)).mono' (hJm.mul hm).aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hJnn _)
    (integral_nonneg (fun _ => abs_nonneg _)))]
  have hh := (indicator_translation_le hA u ht).trans
    (mul_le_mul_of_nonneg_left (directionalPerimeter_le hA u) ht)
  have hmul := mul_le_mul_of_nonneg_left hh (hJnn u)
  nlinarith

end Paper.Geometry
