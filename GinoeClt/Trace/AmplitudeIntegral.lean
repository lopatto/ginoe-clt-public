/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.NearFar

/-! # Integrated first-order amplitude error in the original weak trace estimate -/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Real Topology BigOperators ComplexConjugate

namespace Paper.Trace

def cycleAmplitudeRemainder (a : ℝ) {k : ℕ} (z : Fin k → ℂ) : ℂ :=
  Complex.exp (cycleExponent a z) * (cycleAmplitude z - (Real.pi : ℂ)⁻¹ ^ k)

theorem measurable_cycleAmplitudeRemainder (a : ℝ) (k : ℕ) :
    Measurable (cycleAmplitudeRemainder a (k := k)) := by
  unfold cycleAmplitudeRemainder cycleAmplitude cycleExponent squareMass cyclePairing
  fun_prop

theorem cycleAmplitudeRemainder_integral_bound {d : ℝ} (hd : 0 < d) (n : ℕ)
    {A : Set ℂ} (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (hAim : ∀ z ∈ A, d ≤ z.im) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a →
      IntegrableOn (cycleAmplitudeRemainder a (k := n + 1))
        (Set.univ.pi (fun _ : Fin (n + 1) => A)) ∧
      ‖∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A), cycleAmplitudeRemainder a z‖ ≤
        C * ∑ i : Fin (n + 1), cycleDistanceMoment a A i := by
  obtain ⟨C, hC, hAmp⟩ := cycleAmplitude_error hd (n + 1)
  refine ⟨C, hC, fun a ha => ?_⟩
  let B := Set.univ.pi (fun _ : Fin (n + 1) => A)
  have hB : MeasurableSet B := MeasurableSet.pi Set.countable_univ (fun _ _ => hAmeas)
  have hmem : ∀ᵐ z ∂volume.restrict B, z ∈ B := ae_restrict_mem hB
  have hgi (i : Fin (n + 1)) := (cycle_distance_integral_nearFar ha (r := 1)
    zero_le_one n hAmeas hAfin hAbound i).1
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hgi i)
  have hdom := hsum.const_mul C
  have hpoint : ∀ᵐ z ∂volume.restrict B, ‖cycleAmplitudeRemainder a z‖ ≤
      C * ∑ i : Fin (n + 1),
        Real.exp (-(a / 2) * cycleEnergy z) * ‖z i - z (finRotate (n + 1) i)‖ := by
    filter_upwards [hmem] with z hz
    have hzA (i : Fin (n + 1)) : z i ∈ A := hz i (Set.mem_univ i)
    have hh := hAmp z (fun i => hAim _ (hzA i)) (fun i => hAbound _ (hzA i))
    unfold cycleAmplitudeRemainder
    rw [norm_mul, norm_exp_cycleExponent]
    exact (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans_eq (by
      rw [← Finset.mul_sum]
      ring)
  have hi : Integrable (cycleAmplitudeRemainder a (k := n + 1)) (volume.restrict B) :=
    hdom.mono' (measurable_cycleAmplitudeRemainder a (n + 1)).aestronglyMeasurable hpoint
  refine ⟨hi, ?_⟩
  have hh := norm_integral_le_of_norm_le hdom hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hgi i)] at hh
  exact hh

theorem cycleAmplitudeRemainder_bigO {δ d : ℝ} (hd : 0 < d)
    (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) (n : ℕ) {A : Set ℂ}
    (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (hAim : ∀ z ∈ A, d ≤ z.im) :
    (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
      ∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
        cycleAmplitudeRemainder (m + 1) z) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  obtain ⟨C, hC, hBound⟩ := cycleAmplitudeRemainder_integral_bound hd n hAmeas hAfin hAbound hAim
  let g : ℕ → ℝ := fun m => C * ∑ i : Fin (n + 1),
    (m + 1 : ℝ) ^ (n + 1) * cycleDistanceMoment (m + 1) A i
  have hf : (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
      ∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
        cycleAmplitudeRemainder (m + 1) z) =O[atTop] g := by
    apply Eventually.isBigO
    apply Filter.Eventually.of_forall
    intro m
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    push_cast
    have hh := (hBound (m + 1) (by positivity)).2
    exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (m + 1 : ℝ) ^ (n + 1))).trans_eq (by
      dsimp [g]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring)
  have hg : g =O[atTop] Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
    have hh := (IsBigO.sum (s := Finset.univ) (fun i _ =>
      cycleDistanceMoment_bigO hδ n hAmeas hAfin hAbound i)).const_mul_left C
    dsimp only [g]
    simpa only [Finset.sum_apply] using hh
  exact hf.trans hg

theorem integrable_cyclePhase {a : ℝ} (ha : 0 < a) (n : ℕ) {A : Set ℂ}
    (hAfin : volume A ≠ ⊤) :
    IntegrableOn (fun z : Fin (n + 1) → ℂ => Complex.exp (cycleExponent a z))
      (Set.univ.pi (fun _ : Fin (n + 1) => A)) := by
  have hm : Measurable (fun z : Fin (n + 1) → ℂ => Complex.exp (cycleExponent a z)) := by
    unfold cycleExponent squareMass cyclePairing
    fun_prop
  have hg := (cycleGaussian_integral_split (by positivity : 0 < a / 2) n A hAfin).1
  apply hg.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => (norm_exp_cycleExponent a z).le

theorem U_cycle_integral_difference {d : ℝ} (hd : 0 < d) (n : ℕ)
    {A : Set ℂ} (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (hAim : ∀ z ∈ A, d ≤ z.im)
    {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun z : Fin (n + 1) → ℂ =>
      ∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i)))
        (Set.univ.pi (fun _ : Fin (n + 1) => A)) ∧
    (∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
        ∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i))) -
      (Real.pi : ℂ)⁻¹ ^ (n + 1) *
        (∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A), Complex.exp (cycleExponent (N : ℝ) z)) =
      ∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A), cycleAmplitudeRemainder (N : ℝ) z := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨C, hC, hBound⟩ := cycleAmplitudeRemainder_integral_bound hd n hAmeas hAfin hAbound hAim
  have hErr := (hBound (N : ℝ) hn).1
  have hPhi := integrable_cyclePhase hn n hAfin
  let B := Set.univ.pi (fun _ : Fin (n + 1) => A)
  have hB : MeasurableSet B := MeasurableSet.pi Set.countable_univ (fun _ _ => hAmeas)
  have hmem : ∀ᵐ z ∂volume.restrict B, z ∈ B := ae_restrict_mem hB
  have hU : Integrable (fun z : Fin (n + 1) → ℂ =>
      ∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i))) (volume.restrict B) := by
    apply (hErr.add (hPhi.const_mul ((Real.pi : ℂ)⁻¹ ^ (n + 1)))).congr
    filter_upwards [hmem] with z hz
    have hz0 (i : Fin (n + 1)) : 0 < (z i).im := hd.trans_le (hAim _ (hz i (Set.mem_univ i)))
    rw [prod_U_eq_exp_cycleExponent_mul_amplitude N z hz0]
    change cycleAmplitudeRemainder (N : ℝ) z +
      (Real.pi : ℂ)⁻¹ ^ (n + 1) * Complex.exp (cycleExponent (N : ℝ) z) = _
    unfold cycleAmplitudeRemainder
    ring
  refine ⟨hU, ?_⟩
  have he : ∀ᵐ z ∂volume.restrict B,
      (∏ i, Kernel.U N (z i) (z (finRotate (n + 1) i))) -
        (Real.pi : ℂ)⁻¹ ^ (n + 1) * Complex.exp (cycleExponent (N : ℝ) z) =
          cycleAmplitudeRemainder (N : ℝ) z := by
    filter_upwards [hmem] with z hz
    have hz0 (i : Fin (n + 1)) : 0 < (z i).im := hd.trans_le (hAim _ (hz i (Set.mem_univ i)))
    rw [prod_U_eq_exp_cycleExponent_mul_amplitude N z hz0]
    unfold cycleAmplitudeRemainder
    ring
  have hh := integral_congr_ae he
  rw [integral_sub hU (hPhi.const_mul ((Real.pi : ℂ)⁻¹ ^ (n + 1))), integral_const_mul] at hh
  exact hh

/-- The source leading-cycle comparison: its error is the original weak power. -/
theorem U_cycle_leading_error_bigO {δ d : ℝ} (hd : 0 < d)
    (hδ : δ ∈ Ioo (0 : ℝ) (1 / 2)) (n : ℕ) {A : Set ℂ}
    (hAmeas : MeasurableSet A) (hAfin : volume A ≠ ⊤)
    (hAbound : ∀ z ∈ A, ‖z‖ ≤ 1) (hAim : ∀ z ∈ A, d ≤ z.im) :
    (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (n + 1) *
      ((∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
        ∏ i, Kernel.U (m + 1) (z i) (z (finRotate (n + 1) i))) -
        (Real.pi : ℂ)⁻¹ ^ (n + 1) *
          (∫ z in Set.univ.pi (fun _ : Fin (n + 1) => A),
            Complex.exp (cycleExponent (m + 1) z)))) =O[atTop]
      Cumulants.sizePower ((1 / 2 : ℝ) + δ) := by
  have hh := cycleAmplitudeRemainder_bigO hd hδ n hAmeas hAfin hAbound hAim
  apply hh.congr_left
  intro m
  have he := (U_cycle_integral_difference hd n hAmeas hAfin hAbound hAim
    (N := m + 1) (by omega)).2
  have he' := congrArg (fun v : ℂ => ((m + 1 : ℕ) : ℂ) ^ (n + 1) * v) he.symm
  simpa only [Nat.cast_add, Nat.cast_one] using he'

end Paper.Trace
