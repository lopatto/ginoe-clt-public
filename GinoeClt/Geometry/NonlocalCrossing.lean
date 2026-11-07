/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Geometry.NonlocalTranslation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Actual crossing integrals and the nonlocal perimeter scaling -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Paper.Geometry

lemma integrable_indicator_crossing {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) (v : ℂ) :
    Integrable (fun x : ℂ => A.indicator (1 : ℂ → ℝ) x *
      (1 - A.indicator (1 : ℂ → ℝ) (x + v))) := by
  have hm : Measurable (fun x : ℂ => 1 - A.indicator (1 : ℂ → ℝ) (x + v)) :=
    measurable_const.sub ((measurable_one.indicator hA).comp (measurable_id.add measurable_const))
  apply integrable_mul_bounded_one (indicator_integrable hA hb) hm
  intro x
  have hi := indicator_mem_Icc A (x + v)
  rw [abs_le]
  constructor <;> linarith [hi.1, hi.2]

lemma indicator_crossing_eq_half_translation {A : Set ℂ} (hA : MeasurableSet A)
    (hb : Bornology.IsBounded A) (v : ℂ) :
    (∫ x : ℂ, A.indicator (1 : ℂ → ℝ) x * (1 - A.indicator (1 : ℂ → ℝ) (x + v))) =
      (1 / 2 : ℝ) * (∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + v) - A.indicator (1 : ℂ → ℝ) x|) := by
  classical
  let b : ℂ → ℝ := A.indicator 1
  have hbi : Integrable b := indicator_integrable hA hb
  have hdi : Integrable (fun x : ℂ => b (x + v) - b x) := by
    convert! (hbi.comp_add_right v).sub hbi using 1
  have hci : Integrable (fun x : ℂ => b x * (1 - b (x + v))) := integrable_indicator_crossing hA hb v
  have hid : ∀ x : ℂ, |b (x + v) - b x| =
      (b (x + v) - b x) + 2 * (b x * (1 - b (x + v))) := by
    intro x
    by_cases hx : x ∈ A <;> by_cases hv : x + v ∈ A <;> norm_num [b, hx, hv]
  have heq : (∫ x : ℂ, |b (x + v) - b x|) = 2 * (∫ x : ℂ, b x * (1 - b (x + v))) := by
    calc (∫ x : ℂ, |b (x + v) - b x|) =
        (∫ x : ℂ, b (x + v) - b x) + 2 * (∫ x : ℂ, b x * (1 - b (x + v))) := by
          simp_rw [hid]
          rw [integral_add hdi (hci.const_mul 2), integral_const_mul]
      _ = _ := by
        rw [integral_sub (hbi.comp_add_right v) hbi, integral_add_right_eq_self b v, sub_self, zero_add]
  nlinarith

lemma scaled_crossing_section {A : Set ℂ} (hA : MeasurableSet A)
    {J : ℂ → ℝ} (hJeven : Function.Even J) {t : ℝ} (ht : 0 < t) (x : ℂ) :
    (∫ u : ℂ, J u * (1 - A.indicator (1 : ℂ → ℝ) (x + t • u))) =
      (t ^ 2)⁻¹ * (∫ y in Aᶜ, J (t⁻¹ • (x - y))) := by
  classical
  let f : ℂ → ℝ := Aᶜ.indicator (fun y => J (t⁻¹ • (x - y)))
  have hx : ∀ u : ℂ, t⁻¹ • (x - (x + t • u)) = -u := by
    intro u
    simp only [sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg, smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul]
  have hf : ∀ u : ℂ, f (x + t • u) = J u * (1 - A.indicator (1 : ℂ → ℝ) (x + t • u)) := by
    intro u
    change Aᶜ.indicator (fun y => J (t⁻¹ • (x - y))) (x + t • u) =
      J u * (1 - A.indicator (1 : ℂ → ℝ) (x + t • u))
    by_cases hu : x + t • u ∈ A
    · rw [Set.indicator_of_notMem (show x + t • u ∉ Aᶜ from fun hn => hn hu), Set.indicator_of_mem hu]
      norm_num
    · rw [Set.indicator_of_mem (show x + t • u ∈ Aᶜ from hu), Set.indicator_of_notMem hu, hx u, hJeven u]
      norm_num
  have haff : (∫ u : ℂ, f (x + t • u)) = (t ^ 2)⁻¹ * (∫ y : ℂ, f y) := by
    calc
      (∫ u : ℂ, f (x + t • u)) = (t ^ 2)⁻¹ * (∫ y : ℂ, f (x + y)) := by
        simpa only [Complex.finrank_real_complex, smul_eq_mul] using
          (Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ) (fun y : ℂ => f (x + y)) t (hR := ht.le))
      _ = _ := by rw [integral_add_left_eq_self]
  rw [← integral_indicator hA.compl]
  convert! haff using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun u => (hf u).symm)

/-- The crossing identity uses actual product integrability inferred from the
first-moment translation bound, before applying Fubini. -/
theorem half_translation_eq_scaled_crossing {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z) (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) {t : ℝ} (ht : 0 < t) :
    (1 / 2 : ℝ) * (∫ u : ℂ, J u *
      (∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|)) =
      (t ^ 2)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y))) := by
  classical
  let b : ℂ → ℝ := A.indicator 1
  let F : ℂ × ℂ → ℝ := fun p => J p.1 * (b p.2 * (1 - b (p.2 + t • p.1)))
  have hb : Measurable b := measurable_one.indicator hA.1.measurableSet
  have hFnn : ∀ p : ℂ × ℂ, 0 ≤ F p := by
    intro p
    exact mul_nonneg (hJnn _) (mul_nonneg (indicator_mem_Icc A p.2).1
      (by linarith [(indicator_mem_Icc A (p.2 + t • p.1)).2]))
  have hFm : Measurable F := by
    have hs : Measurable (fun p : ℂ × ℂ => p.2 + t • p.1) :=
      (continuous_snd.add ((continuous_const_smul t).comp continuous_fst)).measurable
    exact (hJm.comp measurable_fst).mul ((hb.comp measurable_snd).mul
      (measurable_const.sub (hb.comp hs)))
  have hsect : ∀ u : ℂ, Integrable (fun x : ℂ => F (u, x)) := by
    intro u
    exact (integrable_indicator_crossing hA.1.measurableSet (Paper.admissible_isBounded hA) (t • u)).const_mul (J u)
  have hsectEq : ∀ u : ℂ, (∫ x : ℂ, F (u, x)) =
      (1 / 2 : ℝ) * (J u * (∫ x : ℂ, |b (x + t • u) - b x|)) := by
    intro u
    change (∫ x : ℂ, J u * (b x * (1 - b (x + t • u)))) = _
    rw [integral_const_mul, indicator_crossing_eq_half_translation hA.1.measurableSet
      (Paper.admissible_isBounded hA)]
    ring
  have hprod : Integrable F (volume.prod volume) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨ae_of_all _ hsect, ?_⟩
    have hh := (integrable_kernel_translation_norm hA hJm hJnn hmoment ht.le).const_mul (1 / 2 : ℝ)
    convert! hh using 1
    ext u
    rw [show (fun x : ℂ => ‖F (u, x)‖) = (fun x : ℂ => F (u, x)) from
      funext (fun x => Real.norm_of_nonneg (hFnn (u, x)))]
    exact hsectEq u
  calc (1 / 2 : ℝ) * (∫ u : ℂ, J u * (∫ x : ℂ, |b (x + t • u) - b x|)) =
      ∫ u : ℂ, ∫ x : ℂ, F (u, x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun u => (hsectEq u).symm)
    _ = ∫ x : ℂ, ∫ u : ℂ, F (u, x) := integral_integral_swap hprod
    _ = ∫ x : ℂ, (t ^ 2)⁻¹ * (b x * (∫ y in Aᶜ, J (t⁻¹ • (x - y)))) := by
      apply integral_congr_ae
      filter_upwards with x
      have heq : (fun u : ℂ => F (u, x)) =
          (fun u : ℂ => b x * (J u * (1 - b (x + t • u)))) := by
        funext u
        dsimp only [F]
        ring
      rw [heq, integral_const_mul, scaled_crossing_section hA.1.measurableSet hJ.even ht]
      ring
    _ = (t ^ 2)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y))) := by
      rw [integral_const_mul, ← integral_indicator hA.1.measurableSet]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ A <;> simp [b, hx]

lemma scaled_crossing_eq_half_quotient {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z) (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) {t : ℝ} (ht : 0 < t) :
    (t ^ 3)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y))) =
      (1 / 2 : ℝ) * (∫ u : ℂ, J u *
        ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t)) := by
  have hi := half_translation_eq_scaled_crossing hA hJm hJnn hJ hmoment ht
  have hquot : (∫ u : ℂ, J u *
      ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t)) =
      (∫ u : ℂ, J u * (∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|)) / t := by
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with u
    ring
  rw [hquot]
  calc (t ^ 3)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y))) =
      ((t ^ 2)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y)))) / t := by
        field_simp
    _ = _ := by rw [← hi]; ring

/-- The complete nonlocal crossing limit in the small-length parameter. -/
theorem nonlocal_crossing_tendsto {A : Set ℂ} (hA : Paper.IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z) (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) :
    Tendsto (fun t : ℝ => (t ^ 3)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y))))
      (𝓝[>] 0) (𝓝 ((boundarySurface A).real univ / Real.pi)) := by
  have hh := (radial_translation_integral_tendsto hA hJm hJnn hJ hmoment).const_mul (1 / 2 : ℝ)
  have heq : (fun t : ℝ => (t ^ 3)⁻¹ * (∫ x in A, ∫ y in Aᶜ, J (t⁻¹ • (x - y)))) =ᶠ[𝓝[>] 0]
      (fun t : ℝ => (1 / 2 : ℝ) * (∫ u : ℂ, J u *
        ((∫ x : ℂ, |A.indicator (1 : ℂ → ℝ) (x + t • u) - A.indicator (1 : ℂ → ℝ) x|) / t))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact scaled_crossing_eq_half_quotient hA hJm hJnn hJ hmoment ht
  have hout := hh.congr' heq.symm
  convert! hout using 1
  congr 1
  ring

end Paper.Geometry

namespace Paper

/-- Lemma 2.5: the original crossing integral in ordinary planar area measure,
with its exact Euclidean Hausdorff boundary length and all natural sizes. -/
theorem nonlocal_perimeter_limit {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {J : ℂ → ℝ} (hJm : Measurable J) (hJnn : ∀ z, 0 ≤ J z) (hJ : Function.IsRadial J)
    (hmoment : (∫ z : ℂ, ‖z‖ * J z) = 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (3 / 2 : ℝ) *
      (∫ z in A, ∫ w in Aᶜ, J (Real.sqrt (N : ℝ) • (z - w))))
      atTop (𝓝 ((boundaryMeasure A).toReal / Real.pi)) := by
  have hzero : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2 ⟨hzero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast hN))
  have hh := (Geometry.nonlocal_crossing_tendsto hA hJm hJnn hJ hmoment).comp ht
  have hmass : (Geometry.boundarySurface A).real univ = (boundaryMeasure A).toReal := by
    simp only [Geometry.boundarySurface, Measure.real, Measure.restrict_apply_univ, boundaryMeasure]
  rw [hmass] at hh
  convert! hh using 1
  ext N
  have hrpow : (N : ℝ) ^ (3 / 2 : ℝ) = (Real.sqrt (N : ℝ)) ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt (3 : ℝ) (Nat.cast_nonneg N)]
    exact Real.rpow_natCast _ 3
  simp only [Function.comp_apply, hrpow, inv_pow, inv_inv]

end Paper
