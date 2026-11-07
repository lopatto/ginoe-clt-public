/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.AmplitudeError
public import GinoeClt.Trace.GaussianBounds
public import GinoeClt.Cumulants.AsymptoticCumulants

/-! # The original weak near/far cutoff for cyclic trace amplitudes -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Real Topology BigOperators

namespace Paper.Trace

def traceCutoff (δ : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ) + δ)

theorem traceCutoff_pos (δ : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < traceCutoff δ N :=
  Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _

theorem size_mul_traceCutoff (δ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * traceCutoff δ N = (N : ℝ) ^ ((1 / 2 : ℝ) + δ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold traceCutoff
  calc
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ) + δ) := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ (1 + (-(1 / 2 : ℝ) + δ)) := (Real.rpow_add hn _ _).symm
    _ = _ := by congr 1; ring

theorem size_mul_traceCutoff_sq (δ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * traceCutoff δ N ^ 2 = (N : ℝ) ^ (2 * δ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold traceCutoff
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ ((-(1 / 2 : ℝ) + δ) * 2) := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ (1 + (-(1 / 2 : ℝ) + δ) * 2) := (Real.rpow_add hn _ _).symm
    _ = _ := by congr 1; ring

theorem farCutoff_bigO {δ : ℝ} (hδ : 0 < δ) :
    (fun n : ℕ => (n + 1 : ℝ) * Real.exp (-(n + 1 : ℝ) ^ (2 * δ) / 4)) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  let q : ℝ := ((1 / 2 : ℝ) - δ) / (2 * δ)
  have hδ2 : 0 < 2 * δ := by linarith
  have ht := (tendsto_rpow_atTop hδ2).comp Cumulants.tendsto_matrixSize
  have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q (1 / 4) (by norm_num)).comp ht
  apply Cumulants.isBigO_of_normalized_tendsto (v := 0)
  convert hl using 1
  funext n
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hp : ((n + 1 : ℝ) ^ (2 * δ)) ^ q = (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - δ) := by
    rw [← Real.rpow_mul hn.le]
    congr 1
    dsimp [q]
    field_simp
  unfold Cumulants.sizePower
  simp only [Function.comp_apply]
  rw [hp]
  calc
    _ = ((n + 1 : ℝ) ^ (-((1 / 2 : ℝ) + δ)) * (n + 1 : ℝ)) *
        Real.exp (-(n + 1 : ℝ) ^ (2 * δ) / 4) := by ring
    _ = ((n + 1 : ℝ) ^ (-((1 / 2 : ℝ) + δ)) * (n + 1 : ℝ) ^ (1 : ℝ)) *
        Real.exp (-(n + 1 : ℝ) ^ (2 * δ) / 4) := by rw [Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_add hn]
      congr 2 <;> ring

/-- Both terms of the original near/far partition, combined pointwise before integration. -/
theorem nearFar_pointwise {a r t Q : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (ht2 : t ≤ 2) (hQ : t ^ 2 ≤ Q) :
    Real.exp (-a * Q / 2) * t ≤
      r * Real.exp (-a * Q / 2) +
        2 * Real.exp (-a * r ^ 2 / 4) * Real.exp (-a * Q / 4) := by
  by_cases hnear : t ≤ r
  · have hh := mul_le_mul_of_nonneg_left hnear (Real.exp_pos (-a * Q / 2)).le
    have hfar : 0 ≤ 2 * Real.exp (-a * r ^ 2 / 4) * Real.exp (-a * Q / 4) := by positivity
    nlinarith only [hh, hfar]
  · have hfar : r < t := lt_of_not_ge hnear
    have hrQ : r ^ 2 ≤ Q := (sq_le_sq₀ hr ht).mpr hfar.le |>.trans hQ
    have he : Real.exp (-a * Q / 2) ≤
        Real.exp (-a * r ^ 2 / 4) * Real.exp (-a * Q / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [ha, hrQ]
    have hh := mul_le_mul he ht2 ht (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    have hnear0 : 0 ≤ r * Real.exp (-a * Q / 2) := by positivity
    nlinarith only [hh, hnear0]

theorem cycle_edge_distance_le_two {n : ℕ} {A : Set ℂ}
    (hA : ∀ z ∈ A, ‖z‖ ≤ 1) {z : Fin (n + 1) → ℂ}
    (hz : z ∈ Set.univ.pi (fun _ : Fin (n + 1) => A)) (i : Fin (n + 1)) :
    ‖z i - z (finRotate (n + 1) i)‖ ≤ 2 := by
  have hi : ‖z i‖ ≤ 1 := hA _ (hz i (Set.mem_univ i))
  have hj : ‖z (finRotate (n + 1) i)‖ ≤ 1 := hA _ (hz _ (Set.mem_univ _))
  have hh := norm_sub_le (z i) (z (finRotate (n + 1) i))
  linarith only [hi, hj, hh]

theorem cycle_edge_sq_le_energy {k : ℕ} (z : Fin k → ℂ) (i : Fin k) :
    ‖z i - z (finRotate k i)‖ ^ 2 ≤ cycleEnergy z :=
  Finset.single_le_sum (fun j _ => sq_nonneg ‖z j - z (finRotate k j)‖) (Finset.mem_univ i)

/-- The source's two cutoff integrals, kept with their original Gaussian scales. -/
theorem cycle_distance_integral_nearFar {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r)
    (n : ℕ) {A : Set ℂ} (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (i : Fin (n + 1)) :
    IntegrableOn (fun z : Fin (n + 1) → ℂ =>
      Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate (n + 1) i)‖)
      (Set.univ.pi (fun _ : Fin (n + 1) => A)) ∧
    (∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
      Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate (n + 1) i)‖) ≤
        r * (volume.real A * (Real.pi / (a / 2)) ^ n) +
          (2 * Real.exp (-a * r ^ 2 / 4)) *
            (volume.real A * (Real.pi / (a / 4)) ^ n) := by
  let B := Set.univ.pi (fun _ : Fin (n + 1) => A)
  have hB : MeasurableSet B := MeasurableSet.pi Set.countable_univ (fun _ _ => hAmeas)
  have hmem : ∀ᵐ z ∂volume.restrict B, z ∈ B := ae_restrict_mem hB
  have ha2 : 0 < a / 2 := by positivity
  have ha4 : 0 < a / 4 := by positivity
  have hg2 := (cycleGaussian_integral_split ha2 n A hAfin).1
  have hg4 := (cycleGaussian_integral_split ha4 n A hAfin).1
  have hc : Continuous (fun z : Fin (n + 1) → ℂ =>
      Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate (n + 1) i)‖) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_cycleEnergy (n + 1)))).mul
      (((continuous_apply i).sub (continuous_apply (finRotate (n + 1) i))).norm)
  have hw : Integrable (fun z : Fin (n + 1) → ℂ =>
      Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate (n + 1) i)‖)
      (volume.restrict B) := by
    apply (hg2.const_mul 2).mono' hc.aestronglyMeasurable
    filter_upwards [hmem] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_left
      (cycle_edge_distance_le_two hAbound hz i) (Real.exp_pos _).le).trans_eq (by ring)
  refine ⟨hw, ?_⟩
  have hleft := hg2.const_mul r
  have hright := hg4.const_mul (2 * Real.exp (-a * r ^ 2 / 4))
  calc
    _ ≤ ∫ z in B, r * Real.exp (-(a / 2) * cycleEnergy z) +
        (2 * Real.exp (-a * r ^ 2 / 4)) * Real.exp (-(a / 4) * cycleEnergy z) := by
      apply integral_mono_ae hw (hleft.add hright)
      filter_upwards [hmem] with z hz
      have hh := nearFar_pointwise ha.le hr (norm_nonneg _)
        (cycle_edge_distance_le_two hAbound hz i) (cycle_edge_sq_le_energy z i)
      change Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate (n + 1) i)‖ ≤
        r * Real.exp (-(a / 2) * cycleEnergy z) +
          2 * Real.exp (-a * r ^ 2 / 4) * Real.exp (-(a / 4) * cycleEnergy z)
      rw [show -(a / 2) * cycleEnergy z = -a * cycleEnergy z / 2 by ring,
        show -(a / 4) * cycleEnergy z = -a * cycleEnergy z / 4 by ring]
      exact hh
    _ = r * (∫ z in B, Real.exp (-(a / 2) * cycleEnergy z)) +
        (2 * Real.exp (-a * r ^ 2 / 4)) *
          (∫ z in B, Real.exp (-(a / 4) * cycleEnergy z)) := by
      rw [integral_add hleft hright, integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (cycleGaussian_bound ha2 n A hAfin) hr)
      (mul_le_mul_of_nonneg_left (cycleGaussian_bound ha4 n A hAfin) (by positivity))

def cycleDistanceMoment (a : ℝ) {k : ℕ} (A : Set ℂ) (i : Fin k) : ℝ :=
  ∫ z in Set.univ.pi (fun _ : Fin k => A),
    Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate k i)‖

theorem scaled_cycleDistanceMoment_bound (δ : ℝ) (n m : ℕ) {A : Set ℂ}
    (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (i : Fin (n + 1)) :
    (m + 1 : ℝ) ^ (n + 1) * cycleDistanceMoment (m + 1) A i ≤
      volume.real A * (2 * Real.pi) ^ n * Cumulants.sizePower ((1 / 2 : ℝ) + δ) m +
        (2 * volume.real A * (4 * Real.pi) ^ n) *
          ((m + 1 : ℝ) * Real.exp (-(m + 1 : ℝ) ^ (2 * δ) / 4)) := by
  have hn : 0 < (m + 1 : ℝ) := by positivity
  have hcut := traceCutoff_pos δ (N := m + 1) (by omega)
  have hh := (cycle_distance_integral_nearFar hn hcut.le n hAmeas hAfin hAbound i).2
  have he : -(m + 1 : ℝ) * traceCutoff δ (m + 1) ^ 2 / 4 =
      -(m + 1 : ℝ) ^ (2 * δ) / 4 := by
    rw [show -(m + 1 : ℝ) * traceCutoff δ (m + 1) ^ 2 =
      -((m + 1 : ℝ) * traceCutoff δ (m + 1) ^ 2) by ring]
    have hsq := size_mul_traceCutoff_sq δ (N := m + 1) (by omega)
    push_cast at hsq
    rw [hsq]
  rw [he] at hh
  have h2 : Real.pi / ((m + 1 : ℝ) / 2) = (2 * Real.pi) / (m + 1 : ℝ) := by field_simp
  have h4 : Real.pi / ((m + 1 : ℝ) / 4) = (4 * Real.pi) / (m + 1 : ℝ) := by field_simp
  rw [h2, h4] at hh
  have hpow : 0 ≤ (m + 1 : ℝ) ^ (n + 1) := pow_nonneg hn.le _
  apply (mul_le_mul_of_nonneg_left hh hpow).trans_eq
  unfold Cumulants.sizePower
  have hnear := size_mul_traceCutoff δ (N := m + 1) (by omega)
  push_cast at hnear
  rw [← hnear]
  rw [pow_succ, div_pow, div_pow]
  field_simp

/-- The source weak N^(1/2+δ) estimate for a representative cyclic difference factor. -/
theorem cycleDistanceMoment_bigO {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2))
    (n : ℕ) {A : Set ℂ} (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (i : Fin (n + 1)) :
    (fun m : ℕ => (m + 1 : ℝ) ^ (n + 1) * cycleDistanceMoment (m + 1) A i) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  let f : ℕ → ℝ := fun m => (m + 1 : ℝ) ^ (n + 1) * cycleDistanceMoment (m + 1) A i
  let g : ℕ → ℝ := fun m =>
    volume.real A * (2 * Real.pi) ^ n * Cumulants.sizePower ((1 / 2 : ℝ) + δ) m +
      (2 * volume.real A * (4 * Real.pi) ^ n) *
        ((m + 1 : ℝ) * Real.exp (-(m + 1 : ℝ) ^ (2 * δ) / 4))
  have hf : f =O[atTop] g := by
    apply Eventually.isBigO
    apply Filter.Eventually.of_forall
    intro m
    have hpos : 0 ≤ f m := by
      dsimp [f, cycleDistanceMoment]
      apply mul_nonneg (by positivity)
      exact integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    change |f m| ≤ g m
    rw [abs_of_nonneg hpos]
    exact scaled_cycleDistanceMoment_bound δ n m hAmeas hAfin hAbound i
  have hg : g =O[atTop] Cumulants.sizePower ((1 / 2 : ℝ) + δ) :=
    ((isBigO_refl (Cumulants.sizePower ((1 / 2 : ℝ) + δ)) atTop).const_mul_left
      (volume.real A * (2 * Real.pi) ^ n)).add
      ((farCutoff_bigO hδ.1).const_mul_left (2 * volume.real A * (4 * Real.pi) ^ n))
  exact hf.trans hg

end Paper.Trace
