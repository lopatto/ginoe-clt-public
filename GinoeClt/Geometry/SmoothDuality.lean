/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Bounded smooth tests detect a finite-measure scalar density -/

@[expose] public section
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace Paper.Geometry

lemma exists_smoothSign_on_compacts {Kp Km : Set ℂ} (hp : IsCompact Kp) (hm : IsCompact Km)
    (hdis : Disjoint Kp Km) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x, |φ x| ≤ 1) ∧ (∀ x ∈ Kp, φ x = 1) ∧ (∀ x ∈ Km, φ x = -1) := by
  obtain ⟨R, _, hR⟩ := (hp.union hm).isBounded.subset_ball_lt 0 (0 : ℂ)
  let Up : Set ℂ := ball 0 R ∩ Kmᶜ
  let Um : Set ℂ := ball 0 R ∩ Kpᶜ
  have hpU : Kp ⊆ Up := fun x hx => ⟨hR (Or.inl hx), fun hy => Set.disjoint_left.mp hdis hx hy⟩
  have hmU : Km ⊆ Um := fun x hx => ⟨hR (Or.inr hx), fun hy => Set.disjoint_left.mp hdis hy hx⟩
  obtain ⟨fp, hfp, hfpRange, hfpSupp, hfpOne⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (isOpen_ball.inter hm.isClosed.isOpen_compl) hp.isClosed hpU
  obtain ⟨fm, hfm, hfmRange, hfmSupp, hfmOne⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (isOpen_ball.inter hp.isClosed.isOpen_compl) hm.isClosed hmU
  have hfpC : HasCompactSupport fp := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℂ) R) (by rw [hfpSupp]; exact inter_subset_left.trans ball_subset_closedBall)
  have hfmC : HasCompactSupport fm := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℂ) R) (by rw [hfmSupp]; exact inter_subset_left.trans ball_subset_closedBall)
  have hp0 : ∀ x ∈ Km, fp x = 0 := by
    intro x hx
    by_contra hn
    have hh : x ∈ Function.support fp := hn
    rw [hfpSupp] at hh
    exact hh.2 hx
  have hm0 : ∀ x ∈ Kp, fm x = 0 := by
    intro x hx
    by_contra hn
    have hh : x ∈ Function.support fm := hn
    rw [hfmSupp] at hh
    exact hh.2 hx
  refine ⟨fun x => fp x - fm x, hfp.sub hfm, hfpC.sub hfmC, ?_, ?_, ?_⟩
  · intro x
    have hpv := hfpRange (mem_range_self x)
    have hmv := hfmRange (mem_range_self x)
    rw [abs_le]
    constructor <;> linarith [hpv.1, hpv.2, hmv.1, hmv.2]
  · intro x hx
    change fp x - fm x = 1
    rw [(hfpOne x).mp hx, hm0 x hx, sub_zero]
  · intro x hx
    change fp x - fm x = -1
    rw [hp0 x hx, (hfmOne x).mp hx]
    norm_num

/-- For a finite Borel measure, the L¹ norm of a measurable bounded density is
approximated by compactly supported infinitely smooth tests bounded by one. -/
theorem exists_smoothTest_integral_abs_sub_le (μ : Measure ℂ) [IsFiniteMeasure μ]
    {a : ℂ → ℝ} (ha : Measurable a) {B : ℝ} (hB : 0 ≤ B)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ (∀ x, |φ x| ≤ 1) ∧
      (∫ x, |a x| ∂μ) - (∫ x, φ x * a x ∂μ) ≤ ε := by
  let δ : ℝ := ε / (4 * (B + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  let Sp : Set ℂ := {x | 0 ≤ a x}
  let Sm : Set ℂ := {x | a x < 0}
  have hSp : MeasurableSet Sp := measurableSet_le measurable_const ha
  have hSm : MeasurableSet Sm := measurableSet_lt ha measurable_const
  obtain ⟨Kp, hpSub, hpC, hpμ⟩ := hSp.exists_isCompact_sdiff_lt (measure_ne_top μ Sp)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  obtain ⟨Km, hmSub, hmC, hmμ⟩ := hSm.exists_isCompact_sdiff_lt (measure_ne_top μ Sm)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  have hdis : Disjoint Kp Km := Set.disjoint_left.mpr (by
    intro x hxp hxm
    have hxpos : 0 ≤ a x := hpSub hxp
    have hxneg : a x < 0 := hmSub hxm
    linarith)
  obtain ⟨φ, hφ, hφC, hφb, hφp, hφm⟩ := exists_smoothSign_on_compacts hpC hmC hdis
  have hai : Integrable a μ := (integrable_const B).mono' ha.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hab)
  have hprodBound : ∀ᵐ x ∂μ, |φ x * a x| ≤ B := by
    filter_upwards [hab] with x hx
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hφb x)).trans hx
  have hφai : Integrable (fun x => φ x * a x) μ := (integrable_const B).mono'
    (hφ.continuous.measurable.mul ha).aestronglyMeasurable (by
      simpa only [Real.norm_eq_abs] using hprodBound)
  let g : ℂ → ℝ := fun x => |a x| - φ x * a x
  have hgi : Integrable g μ := by
    convert! hai.norm.sub hφai using 1
  have hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ 2 * B := by
    filter_upwards [hab, hprodBound] with x hx hy
    have hh := norm_sub_le (|a x|) (φ x * a x)
    simp only [Real.norm_eq_abs, abs_abs] at hh
    change |(|a x|) - φ x * a x| ≤ 2 * B
    linarith
  let K : Set ℂ := Kp ∪ Km
  have hKc : IsCompact K := hpC.union hmC
  have hg0 : ∀ x ∈ K, g x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · have hxpos : 0 ≤ a x := hpSub hx
      change |a x| - φ x * a x = 0
      rw [hφp x hx, one_mul, abs_of_nonneg hxpos, sub_self]
    · have hxneg : a x < 0 := hmSub hx
      change |a x| - φ x * a x = 0
      rw [hφm x hx, abs_of_neg hxneg]
      ring
  have hset0 : (∫ x in K, g x ∂μ) = 0 := by
    rw [setIntegral_congr_fun hKc.measurableSet hg0, integral_zero]
  have hbad : Kᶜ ⊆ (Sp \ Kp) ∪ (Sm \ Km) := by
    intro x hx
    by_cases hxa : 0 ≤ a x
    · exact Or.inl ⟨hxa, fun hxK => hx (Or.inl hxK)⟩
    · exact Or.inr ⟨lt_of_not_ge hxa, fun hxK => hx (Or.inr hxK)⟩
  have hpδ : μ.real (Sp \ Kp) ≤ δ := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hpμ.le).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hmδ : μ.real (Sm \ Km) ≤ δ := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmμ.le).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hKμ : μ.real Kᶜ ≤ 2 * δ := by
    have hh := (measureReal_mono (μ := μ) hbad).trans (measureReal_union_le (μ := μ) _ _)
    linarith
  have herr : (∫ x, |a x| ∂μ) - (∫ x, φ x * a x ∂μ) ≤ μ.real Kᶜ * (2 * B) := by
    have hh := norm_integral_sub_setIntegral_le hgb hKc.measurableSet hgi
    rw [hset0, sub_zero] at hh
    calc (∫ x, |a x| ∂μ) - (∫ x, φ x * a x ∂μ) = ∫ x, g x ∂μ := by
          symm
          exact integral_sub (by simpa only [Real.norm_eq_abs] using hai.norm) hφai
      _ ≤ ‖∫ x, g x ∂μ‖ := le_abs_self _
      _ ≤ _ := hh
  refine ⟨φ, hφ, hφC, hφb, herr.trans ?_⟩
  have hδε : δ * (4 * (B + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hKμ (by positivity : 0 ≤ 2 * B)
  nlinarith

end Paper.Geometry
