/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Bounds
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Exact distance of an admissible bulk domain to the half-disk boundary -/

@[expose] public section
noncomputable section
open MeasureTheory Set Metric
open scoped Topology NNReal

namespace Paper.Kernel

def upperUnitDisk : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}

/-- The distance between A and the frontier is the infimum over A of the
standard point-to-set distance. This is the source d_A, not a chosen smaller constant. -/
def bulkDistance (A : Set ℂ) : ℝ :=
  sInf ((fun z : ℂ => Metric.infDist z (frontier upperUnitDisk)) '' A)

theorem isOpen_upperUnitDisk : IsOpen upperUnitDisk :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem upperUnitDisk_ne_univ : upperUnitDisk ≠ Set.univ := by
  intro h
  have hz : (0 : ℂ) ∈ upperUnitDisk := h.symm ▸ Set.mem_univ _
  simp [upperUnitDisk] at hz

theorem bulkDistance_le_infDist {A : Set ℂ} {z : ℂ} (hz : z ∈ A) :
    bulkDistance A ≤ Metric.infDist z (frontier upperUnitDisk) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨w, hw, rfl⟩
    exact Metric.infDist_nonneg
  · exact Set.mem_image_of_mem _ hz

theorem bulkDistance_le_infDist_closure {A : Set ℂ} {z : ℂ} (hz : z ∈ closure A) :
    bulkDistance A ≤ Metric.infDist z (frontier upperUnitDisk) := by
  have hc : IsClosed {z : ℂ | bulkDistance A ≤ Metric.infDist z (frontier upperUnitDisk)} :=
    isClosed_le continuous_const (Metric.continuous_infDist_pt _)
  exact closure_minimal (fun _ hw => bulkDistance_le_infDist hw) hc hz

theorem bulkDistance_pos {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    0 < bulkDistance A := by
  obtain ⟨z₀, hz₀, hmin⟩ := (admissible_closure_isCompact hA).exists_isMinOn
    hA.2.1.nonempty.closure (Metric.continuous_infDist_pt (frontier upperUnitDisk)).continuousOn
  have hzD : z₀ ∈ upperUnitDisk := hA.2.2.1 hz₀
  obtain ⟨b, hb, _⟩ := exists_mem_frontier_infDist_compl_eq_dist hzD upperUnitDisk_ne_univ
  have hznot : z₀ ∉ frontier upperUnitDisk := by
    rw [isOpen_upperUnitDisk.frontier_eq]
    exact fun hz => hz.2 hzD
  have hp : 0 < Metric.infDist z₀ (frontier upperUnitDisk) :=
    (isClosed_frontier.notMem_iff_infDist_pos ⟨b, hb⟩).mp hznot
  apply hp.trans_le
  apply le_csInf (hA.2.1.nonempty.image _)
  rintro r ⟨w, hw, rfl⟩
  exact hmin (subset_closure hw)

theorem infDist_frontier_le_dist_compl {z w : ℂ} (hz : z ∈ upperUnitDisk)
    (hw : w ∉ upperUnitDisk) :
    Metric.infDist z (frontier upperUnitDisk) ≤ dist z w := by
  obtain ⟨b, hb, hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hz upperUnitDisk_ne_univ
  calc
    Metric.infDist z (frontier upperUnitDisk) ≤ dist z b := Metric.infDist_le_dist_of_mem hb
    _ = Metric.infDist z upperUnitDiskᶜ := hd.symm
    _ ≤ dist z w := Metric.infDist_le_dist_of_mem hw

theorem infDist_frontier_le_im {z : ℂ} (hz : z ∈ upperUnitDisk) :
    Metric.infDist z (frontier upperUnitDisk) ≤ z.im := by
  have hw : (z.re : ℂ) ∉ upperUnitDisk := by simp [upperUnitDisk]
  have he : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
  have hd : dist z (z.re : ℂ) = z.im := by
    rw [dist_eq_norm, he, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz.2]
  exact (infDist_frontier_le_dist_compl hz hw).trans_eq hd

theorem infDist_frontier_le_one_sub_norm {z : ℂ} (hz : z ∈ upperUnitDisk) :
    Metric.infDist z (frontier upperUnitDisk) ≤ 1 - ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simpa [h] using hz.2)
  let w : ℂ := (‖z‖⁻¹ : ℝ) • z
  have hw1 : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hw : w ∉ upperUnitDisk := by
    intro hh
    exact (hw1 ▸ hh.1).false
  have he : z - w = (1 - ‖z‖⁻¹ : ℝ) • z := by
    dsimp only [w]
    rw [sub_smul, one_smul]
  have hc : 1 - ‖z‖⁻¹ ≤ 0 := sub_nonpos.mpr ((one_le_inv₀ hn).mpr hz.1.le)
  have hd : dist z w = 1 - ‖z‖ := by
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonpos hc]
    calc
      -(1 - ‖z‖⁻¹) * ‖z‖ = (‖z‖⁻¹ - 1) * ‖z‖ := by ring
      _ = 1 - ‖z‖ := by rw [sub_mul, inv_mul_cancel₀ hn.ne', one_mul]
  exact (infDist_frontier_le_dist_compl hz hw).trans_eq hd

theorem bulkDistance_le_im {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {z : ℂ} (hz : z ∈ closure A) : bulkDistance A ≤ z.im :=
  (bulkDistance_le_infDist_closure hz).trans (infDist_frontier_le_im (hA.2.2.1 hz))

theorem bulkDistance_le_norm {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {z : ℂ} (hz : z ∈ closure A) : bulkDistance A ≤ ‖z‖ :=
  (bulkDistance_le_im hA hz).trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))

theorem norm_le_one_sub_bulkDistance {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {z : ℂ} (hz : z ∈ closure A) : ‖z‖ ≤ 1 - bulkDistance A := by
  have hh := (bulkDistance_le_infDist_closure hz).trans
    (infDist_frontier_le_one_sub_norm (hA.2.2.1 hz))
  linarith

theorem admissible_area_le_pi {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    volume.real A ≤ Real.pi := by
  have hs : A ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right] using (hA.2.2.1 (subset_closure hz)).1
  have hh := measureReal_mono (μ := (volume : Measure ℂ)) hs
  simpa [measureReal_def, Complex.volume_ball] using hh

/-- The exact bulk separation and area facts used by the manuscript's kernel estimates. -/
theorem bulk_separation {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    0 < bulkDistance A ∧
      (∀ z ∈ closure A, bulkDistance A ≤ z.im ∧
        bulkDistance A ≤ ‖z‖ ∧ ‖z‖ ≤ 1 - bulkDistance A) ∧ volume.real A ≤ Real.pi :=
  ⟨bulkDistance_pos hA, fun _ hz => ⟨bulkDistance_le_im hA hz,
    bulkDistance_le_norm hA hz, norm_le_one_sub_bulkDistance hA hz⟩, admissible_area_le_pi hA⟩


/-- The nested point-to-frontier infimum is exactly the infimum of all pairwise
distances between A and the half-disk frontier. -/
theorem bulkDistance_eq_sInf_dist {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    bulkDistance A = sInf {r : ℝ | ∃ z ∈ A, ∃ w ∈ frontier upperUnitDisk, r = dist z w} := by
  obtain ⟨z₀, hz₀⟩ := hA.2.1.nonempty
  obtain ⟨w₀, hw₀, _⟩ := exists_mem_frontier_infDist_compl_eq_dist
    (hA.2.2.1 (subset_closure hz₀)) upperUnitDisk_ne_univ
  have hne : {r : ℝ | ∃ z ∈ A, ∃ w ∈ frontier upperUnitDisk, r = dist z w}.Nonempty :=
    ⟨dist z₀ w₀, z₀, hz₀, w₀, hw₀, rfl⟩
  have hbb : BddBelow {r : ℝ | ∃ z ∈ A, ∃ w ∈ frontier upperUnitDisk, r = dist z w} := by
    refine ⟨0, ?_⟩
    rintro r ⟨z, hz, w, hw, rfl⟩
    exact dist_nonneg
  apply le_antisymm
  · apply le_csInf hne
    rintro r ⟨z, hz, w, hw, rfl⟩
    exact (bulkDistance_le_infDist hz).trans (Metric.infDist_le_dist_of_mem hw)
  · apply le_csInf (hA.2.1.nonempty.image _)
    rintro r ⟨z, hz, rfl⟩
    apply (Metric.le_infDist ⟨w₀, hw₀⟩).mpr
    intro w hw
    exact csInf_le hbb ⟨z, hz, w, hw, rfl⟩

theorem bulkDistance_le_half {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    bulkDistance A ≤ 1 / 2 := by
  obtain ⟨z, hz⟩ := hA.2.1.nonempty
  have h1 := bulkDistance_le_norm hA (subset_closure hz)
  have h2 := norm_le_one_sub_bulkDistance hA (subset_closure hz)
  linarith

theorem bulk_radius_mem_Ioo {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    (1 - bulkDistance A) ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hp := bulkDistance_pos hA
  have hh := bulkDistance_le_half hA
  constructor <;> nlinarith

theorem norm_mul_le_bulk_radius {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {z w : ℂ} (hz : z ∈ closure A) (hw : w ∈ closure A) :
    ‖z * w‖ ≤ (1 - bulkDistance A) ^ 2 := by
  rw [norm_mul, pow_two]
  exact mul_le_mul (norm_le_one_sub_bulkDistance hA hz) (norm_le_one_sub_bulkDistance hA hw)
    (norm_nonneg _) (by have := bulkDistance_le_half hA; linarith)

theorem norm_mul_conj_le_bulk_radius {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A)
    {z w : ℂ} (hz : z ∈ closure A) (hw : w ∈ closure A) :
    ‖z * starRingEnd ℂ w‖ ≤ (1 - bulkDistance A) ^ 2 := by
  simpa only [norm_mul, Complex.norm_conj] using norm_mul_le_bulk_radius hA hz hw

end Paper.Kernel
