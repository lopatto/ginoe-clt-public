/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.IndicatorApproximation
public import GinoeClt.Geometry.MollifiedBoundary
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Smooth translation estimates and their transfer to the indicator -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ENNReal Topology

namespace Paper.Geometry

lemma line_hasDerivAt {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (x u : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (x + r • u)) (fderiv ℝ f (x + s • u) u) s := by
  have hline : HasDerivAt (fun r : ℝ => x + r • u) u s := by
    simpa using ((hasDerivAt_id s).smul_const u).const_add x
  exact (hf.differentiable one_ne_zero (x + s • u)).hasFDerivAt.comp_hasDerivAt s hline

lemma line_translation_abs_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (x u : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    |f (x + t • u) - f x| ≤ ∫ s in Ioc 0 t, |fderiv ℝ f (x + s • u) u| := by
  have hD : Continuous (fun z => fderiv ℝ f z u) :=
    (ContinuousLinearMap.apply ℝ ℝ u).continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hcont : Continuous (fun s : ℝ => fderiv ℝ f (x + s • u) u) :=
    hD.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ uIcc 0 t) => line_hasDerivAt hf x u s) (hcont.intervalIntegrable 0 t)
  simp only [zero_smul, add_zero] at hFTC
  rw [← hFTC]
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_of_le ht] using
    (intervalIntegral.norm_integral_le_integral_norm (f := fun s => fderiv ℝ f (x + s • u) u) ht)

/-- The FTC estimate is integrated only after proving genuine product integrability. -/
theorem integral_abs_translation_sub_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfi : Integrable f) (u : ℂ) (hDi : Integrable (fun x => fderiv ℝ f x u))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |f (x + t • u) - f x|) ≤ t * (∫ x, |fderiv ℝ f x u|) := by
  let D : ℂ → ℝ := fun x => |fderiv ℝ f x u|
  have hDc : Continuous D := continuous_abs.comp
    ((ContinuousLinearMap.apply ℝ ℝ u).continuous.comp (hf.continuous_fderiv one_ne_zero))
  have hDi' : Integrable D := by simpa only [D, Real.norm_eq_abs] using hDi.norm
  have hshift : ∀ s : ℝ, (∫ x, D (x + s • u)) = ∫ x, D x :=
    fun s => integral_add_right_eq_self D (s • u)
  have hprod : Integrable (fun q : ℝ × ℂ => D (q.2 + q.1 • u))
      (((volume : Measure ℝ).restrict (Ioc 0 t)).prod (volume : Measure ℂ)) := by
    have hm : Continuous (fun q : ℝ × ℂ => D (q.2 + q.1 • u)) :=
      hDc.comp (continuous_snd.add (continuous_fst.smul continuous_const))
    refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact ae_of_all _ (fun s => hDi'.comp_add_right (s • u))
    · have heq : (fun s : ℝ => ∫ x, ‖D (x + s • u)‖) = fun _ => ∫ x, D x := by
        funext s
        simpa only [D, Real.norm_eq_abs, abs_abs] using hshift s
      rw [heq]
      exact integrableOn_const measure_Ioc_lt_top.ne
  have hupperInt : Integrable (fun x : ℂ => ∫ s in Ioc 0 t, D (x + s • u)) :=
    hprod.integral_prod_right
  have hdiffInt : Integrable (fun x => |f (x + t • u) - f x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hfi.comp_add_right (t • u)).sub hfi).norm
  calc (∫ x, |f (x + t • u) - f x|) ≤ ∫ x, ∫ s in Ioc 0 t, D (x + s • u) :=
      integral_mono hdiffInt hupperInt (fun x => line_translation_abs_le hf x u ht)
    _ = ∫ s in Ioc 0 t, ∫ x, D (x + s • u) := (integral_integral_swap hprod).symm
    _ = t * (∫ x, |fderiv ℝ f x u|) := by
      simp_rw [hshift]
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal ht, smul_eq_mul, D]

lemma smoothIndicator_integrable {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) (n : ℕ) : Integrable (smoothIndicator A n) :=
  (smoothIndicator_contDiff hA n).continuous.integrable_of_hasCompactSupport
    (smoothIndicator_hasCompactSupport hb n)

/-- Every concrete smooth approximation has the manuscript's perimeter upper bound. -/
theorem smoothIndicator_translation_le {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    (u : ℂ) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    (∫ x, |smoothIndicator A n (x + t • u) - smoothIndicator A n x|) ≤
      t * directionalPerimeter A hA u := by
  have hderiv := mollifiedIndicator_fderiv_l1_le hA (mollifierKernel_contDiff n)
    (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n) (mollifierKernel_integral n) u
  have hh := integral_abs_translation_sub_le (smoothIndicator_contDiff hA.1.measurableSet n)
    (smoothIndicator_integrable hA.1.measurableSet (Paper.admissible_isBounded hA) n) u hderiv.1 ht
  exact hh.trans (mul_le_mul_of_nonneg_left hderiv.2 ht)

lemma integrable_abs_sub {f g : ℂ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => |f x - g x|) := by
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hf.sub hg).norm

lemma translation_perturbation_le {f g : ℂ → ℝ} (hf : Integrable f) (hg : Integrable g) (v : ℂ) :
    (∫ x, |f (x + v) - f x|) ≤
      2 * (∫ x, |g x - f x|) + (∫ x, |g (x + v) - g x|) := by
  have h1 := integrable_abs_sub (hf.comp_add_right v) (hg.comp_add_right v)
  have h2 := integrable_abs_sub (hg.comp_add_right v) hg
  have h3 := integrable_abs_sub hg hf
  calc (∫ x, |f (x + v) - f x|) ≤
      ∫ x, (|f (x + v) - g (x + v)| + |g (x + v) - g x| + |g x - f x|) := by
        refine integral_mono (integrable_abs_sub (hf.comp_add_right v) hf) ((h1.add h2).add h3) ?_
        intro x
        calc |f (x + v) - f x| =
            |(f (x + v) - g (x + v)) + (g (x + v) - g x) + (g x - f x)| := by ring_nf
          _ ≤ |f (x + v) - g (x + v)| + |g (x + v) - g x| + |g x - f x| :=
            (abs_add_le _ _).trans (by linarith [abs_add_le (f (x + v) - g (x + v)) (g (x + v) - g x)])
    _ = 2 * (∫ x, |g x - f x|) + (∫ x, |g (x + v) - g x|) := by
      rw [integral_add (f := fun x => |f (x + v) - g (x + v)| + |g (x + v) - g x|)
        (g := fun x => |g x - f x|) (by convert! h1.add h2 using 1) h3,
        integral_add h1 h2]
      rw [integral_add_right_eq_self (fun x : ℂ => |f x - g x|) v]
      have heq : (∫ x, |f x - g x|) = ∫ x, |g x - f x| := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => abs_sub_comm _ _)
      rw [heq]
      ring

lemma indicator_integrable {A : Set ℂ} (hA : MeasurableSet A) (hb : Bornology.IsBounded A) :
    Integrable (A.indicator (1 : ℂ → ℝ)) := by
  rw [integrable_indicator_iff hA]
  exact integrableOn_const hb.measure_lt_top.ne

/-- The original mollification route gives the perimeter upper bound for the actual indicator. -/
theorem indicator_translation_le {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    (u : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) ≤
      t * directionalPerimeter A hA u := by
  have hb := Paper.admissible_isBounded hA
  have hbi := indicator_integrable hA.1.measurableSet hb
  have hbound : ∀ n : ℕ,
      (∫ x, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) ≤
        2 * (∫ x, |smoothIndicator A n x - A.indicator (1 : ℂ → ℝ) x|) +
          t * directionalPerimeter A hA u := by
    intro n
    exact (translation_perturbation_le hbi (smoothIndicator_integrable hA.1.measurableSet hb n) (t • u)).trans
      (by linarith [smoothIndicator_translation_le hA u ht n])
  have hlim := ((smoothIndicator_l1_tendsto hA.1.measurableSet hb).const_mul 2).add_const
    (t * directionalPerimeter A hA u)
  simpa only [mul_zero, zero_add] using ge_of_tendsto' hlim hbound

end Paper.Geometry
