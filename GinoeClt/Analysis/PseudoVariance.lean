/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Analysis.VarianceProxy
public import GinoeClt.Cumulants.CountKernelComparison

/-! # The second determinantal pseudo-cumulant and count variance reduction

The analytic pseudo-cumulant limit is unconditional. Actual count conclusions
explicitly retain the open finite-ensemble identity from CountKernelComparison.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Real Topology ComplexConjugate

namespace Paper.Kernel

lemma cycleIntegral_two_eq_doubleIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ)
    (hi : Integrable (fun p : Ω × Ω => K p.1 p.2 * K p.2 p.1) (μ.prod μ)) :
    KernelIntegrals.cycleIntegral μ K 2 = ∫ z, ∫ w, K z w * K w z ∂μ ∂μ := by
  rw [KernelIntegrals.cycleIntegral, ite_eq_right (by decide)]
  unfold KernelIntegrals.permutationIntegral KernelIntegrals.permutationIntegrand
  simp only [Fin.prod_univ_two, show finRotate 2 0 = 1 from by decide,
    show finRotate 2 1 = 0 from by decide]
  have ht := (measurePreserving_finTwoArrow μ).integral_comp'
    (fun p : Ω × Ω => K p.1 p.2 * K p.2 p.1)
  change (∫ x : Fin 2 → Ω, K (x 0) (x 1) * K (x 1) (x 0)
    ∂Measure.pi (fun _ => μ)) = _ at ht
  rw [ht]
  exact integral_prod _ hi

lemma cyclicTrace_one_eq_source {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    cyclicTrace A N 1 = (N : ℂ) * ∫ z in A, S N (rescale N z) (rescale N z) := by
  let := isFiniteMeasure_area hA
  simp only [cyclicTrace, pow_one, KernelIntegrals.cycleIntegral_one, rescaledS]

lemma cyclicTrace_two_eq_squared {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    cyclicTrace A N 2 =
      (((N : ℝ) ^ 2 * ∫ z in A, ∫ w in A,
        ‖S N (rescale N z) (rescale N w)‖ ^ 2 : ℝ) : ℂ) := by
  let := isFiniteMeasure_area hA
  have hS : Continuous (Function.uncurry (rescaledS N)) :=
    continuous_rescaledKernel _ (continuous_S N) N
  have hcont : Continuous (fun p : ℂ × ℂ =>
      rescaledS N p.1 p.2 * rescaledS N p.2 p.1) :=
    hS.mul (hS.comp continuous_swap)
  have hi := integrable_doubleKernel_of_continuous hA
    (K := fun z w => rescaledS N z w * rescaledS N w z) hcont
  rw [cyclicTrace, cycleIntegral_two_eq_doubleIntegral _ _ hi]
  have hker : ∀ z w : ℂ, rescaledS N z w * rescaledS N w z =
      ((‖S N (rescale N z) (rescale N w)‖ ^ 2 : ℝ) : ℂ) := by
    intro z w
    rw [rescaledS_hermitian N z w]
    simpa only [rescaledS, Complex.ofReal_pow] using Complex.mul_conj' (rescaledS N z w)
  simp_rw [hker, integral_complex_ofReal]
  push_cast
  rfl

lemma realDeterminantalPseudoCumulant_two_eq_kernel {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (N : ℕ) :
    (realDeterminantalPseudoCumulant A N 2 : ℂ) =
      varianceKernelExpression A N + diKernelTerm A N := by
  rw [ofReal_realDeterminantalPseudoCumulant,
    determinantalPseudoCumulant_cycle_formula hA, Cumulants.cycleStirlingTransform_two,
    cyclicTrace_one_eq_source hA, cyclicTrace_two_eq_squared hA]
  unfold varianceKernelExpression
  ring

/-- Unconditional analytic second pseudo-cumulant boundary-length limit. -/
theorem realDeterminantalPseudoCumulant_two_tendsto {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) :
    Tendsto (fun N : ℕ => realDeterminantalPseudoCumulant A N 2 / Real.sqrt (N : ℝ))
      atTop (𝓝 ((Paper.boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)))) := by
  have hi : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hiz : Tendsto (fun N : ℕ => ((Real.sqrt (N : ℝ))⁻¹ : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_inv] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hi
  have hD := (diKernelTerm_tendsto_zero hA).mul hiz
  have hout := (varianceKernelExpression_tendsto hA).add hD
  have hcomplex : Tendsto
      (fun N : ℕ => (realDeterminantalPseudoCumulant A N 2 : ℂ) / (Real.sqrt (N : ℝ) : ℂ))
      atTop (𝓝 (((Paper.boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)) : ℝ) : ℂ)) := by
    convert! hout using 1
    · funext N
      rw [realDeterminantalPseudoCumulant_two_eq_kernel hA]
      ring
    · simp only [zero_mul, add_zero]
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa only [Function.comp_def, ← Complex.ofReal_div, Complex.ofReal_re] using hr

end Paper.Kernel

namespace Paper

/-- Conditional actual raw-count variance-cumulant limit. The finite-ensemble
identity remains an explicit unresolved proof parameter. -/
theorem countCumulant_two_tendsto_of_finiteLaw {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    Tendsto (fun n : ℕ => countCumulant A n 2 / Real.sqrt (n + 1 : ℝ))
      atTop (𝓝 ((boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)))) := by
  obtain ⟨c, hc, hE⟩ := countCumulant_determinantal_exp_close hA hLaw
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have he : Tendsto (fun n : ℕ => Real.exp (-c * (n + 1 : ℝ))) atTop (𝓝 0) := by
    have hh := (Kernel.nat_pow_mul_exp_tendsto_zero hc 0).comp hshift
    simpa only [Function.comp_def, pow_zero, one_mul, Nat.cast_add, Nat.cast_one] using hh
  have hd := (hE 2 (by decide)).trans_tendsto he
  have hi : Tendsto (fun n : ℕ => (Real.sqrt (n + 1 : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Cumulants.tendsto_matrixSize)
  have hz := hd.mul hi
  have hp := (Kernel.realDeterminantalPseudoCumulant_two_tendsto hA).comp hshift
  have hout := hz.add hp
  convert! hout using 1
  · funext n
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [zero_mul, zero_add]

/-- The reviewed normalized statistic has the same second-cumulant limit,
conditional on the explicitly named finite-ensemble identity. -/
theorem cumulant_two_tendsto_of_finiteLaw {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    Tendsto (fun n : ℕ => cumulant A n 2) atTop
      (𝓝 ((boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)))) := by
  have hh := countCumulant_two_tendsto_of_finiteLaw hA hLaw
  convert! hh using 1
  funext n
  rw [cumulant_eq_countCumulant (countMeasurable_of_isOpen A hA.1) n 2 (by decide)]
  have hp : ((n + 1 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (n + 1 : ℝ) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (n + 1 : ℝ))]
    norm_num [Real.sqrt_eq_rpow]
  rw [inv_pow, hp]
  ring

/-- Actual variance of the reviewed normalized statistic; the open ensemble
identity is displayed rather than assumed or hidden in the definition. -/
theorem statistic_variance_tendsto_of_finiteLaw {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (hLaw : CountPfaffianMomentIdentity A) :
    Tendsto (fun n : ℕ => ProbabilityTheory.variance (statistic A n) (matrixLaw n)) atTop
      (𝓝 ((boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)))) := by
  simpa only [cumulant_two_eq_variance (countMeasurable_of_isOpen A hA.1)] using
    cumulant_two_tendsto_of_finiteLaw hA hLaw

end Paper
