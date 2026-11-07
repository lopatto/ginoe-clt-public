/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.CountFactorialIdentity
public import GinoeClt.Kernel.Scaling
public import GinoeClt.FiniteLawReduction
public import GinoeClt.Analysis.CountVarianceApproximation
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace Paper
open Paper.Spectral Paper.SkewOrthogonal

/-- The exact RAW count domain; the frozen kernel already has this rescaling. -/
theorem scaledCountDomain_eq_rescale_image (n : ℕ) (A : Set ℂ) :
    scaledCountDomain n A = Kernel.rescale (n+1) '' A := by
  have he : (fun z : ℂ ↦ (Real.sqrt (n+1 : ℝ) : ℂ)*z) = Kernel.rescale (n+1) := by
    funext z
    simp [Kernel.rescale]
  exact congrArg (fun f : ℂ → ℂ ↦ f '' A) he

/-- Ordinary restricted product area is exactly ordinary product-area restriction. -/
theorem pi_restrict_complex_eq_restrict (k : ℕ) (B : Set ℂ) :
    Measure.pi (fun _ : Fin k => (volume : Measure ℂ).restrict B) =
      (volume : Measure (Fin k → ℂ)).restrict (Set.univ.pi (fun _ : Fin k => B)) :=
  (Measure.restrict_pi_pi (μ := fun _ : Fin k => (volume : Measure ℂ)) (fun _ => B)).symm

/-- One planar Jacobian per root: the factor is precisely (n+1)^k. -/
theorem pow_mul_setIntegral_scaledCountDomain (A : Set ℂ) (n k : ℕ)
    (f : (Fin k → ℂ) → ℂ) :
    (((n+1 : ℕ) : ℂ)^k) * (∫ z in Set.univ.pi (fun _ : Fin k => A),
      f (fun i => Kernel.rescale (n+1) (z i))) =
      ∫ z, f z ∂Measure.pi (fun _ : Fin k => volume.restrict (scaledCountDomain n A)) := by
  rw [pi_restrict_complex_eq_restrict,scaledCountDomain_eq_rescale_image]
  exact Kernel.pow_mul_setIntegral_rescale A k (n+1) (by omega) f

/-- ALL actual factorial moments, every positive physical size and every order.
No density claim for arbitrary test configurations is inferred from this theorem. -/
theorem actual_countFactorialMoment_eq_pfaffianKernelMoment (A : Set ℂ) (hA : IsOpen A)
    (hupper : ∀ a ∈ A, 0 < a.im) (n k : ℕ) :
    (countFactorialMoment A n k : ℂ) = Kernel.pfaffianKernelMoment A (n+1) k := by
  by_cases hk : k = 0
  · subst k
    simp only [countFactorialMoment_zero,Complex.ofReal_one,Kernel.pfaffianKernelMoment_zero]
  rw [Kernel.pfaffianKernelMoment,ite_eq_right hk]
  have hProd : MeasurableSet (Set.univ.pi (fun _ : Fin k => A)) :=
    MeasurableSet.univ_pi (fun _ => hA.measurableSet)
  rcases Nat.even_or_odd (n+1) with ⟨m,hm⟩ | ⟨m,hm⟩
  · have hN : n+1 = 2*m := by omega
    let f : (Fin k → ℂ) → ℂ := fun z => pfaffian
      (atomicFeatureKernel (fun i : Fin m => skewNorm i.val)
        (balancedFeatures (fun u p => (pairedPolynomial m p).eval u) z))
    calc
      _ = ∫ z, f z ∂Measure.pi (fun _ : Fin k => volume.restrict (scaledCountDomain n A)) :=
        countFactorialMoment_eq_balancedIntegral_even A hA n m hN hupper k
      _ = (((n+1 : ℕ) : ℂ)^k) * ∫ z in Set.univ.pi (fun _ : Fin k => A),
          f (fun i => Kernel.rescale (n+1) (z i)) :=
        (pow_mul_setIntegral_scaledCountDomain A n k f).symm
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hProd] with z hz
        have hz0 : ∀ i, 0 ≤ (z i).im := fun i => (hupper (z i) (hz i (Set.mem_univ i))).le
        have he := balancedEvenKernel_eq_frozen m z hz0
        rw [← hN] at he
        exact congrArg pfaffian he
  · have hN : n+1 = 2*m+1 := by omega
    let f : (Fin k → ℂ) → ℂ := fun z => pfaffian
      (atomicFeatureKernel (oddNormWeight m) (balancedFeatures (adjustedOddEvaluation m) z))
    calc
      _ = ∫ z, f z ∂Measure.pi (fun _ : Fin k => volume.restrict (scaledCountDomain n A)) :=
        countFactorialMoment_eq_balancedIntegral_odd A hA n m hN hupper k
      _ = (((n+1 : ℕ) : ℂ)^k) * ∫ z in Set.univ.pi (fun _ : Fin k => A),
          f (fun i => Kernel.rescale (n+1) (z i)) :=
        (pow_mul_setIntegral_scaledCountDomain A n k f).symm
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hProd] with z hz
        have hz0 : ∀ i, 0 ≤ (z i).im := fun i => (hupper (z i) (hz i (Set.mem_univ i))).le
        have he := balancedOddKernel_eq_frozen m z hz0
        rw [← hN] at he
        exact congrArg pfaffian he

/-- The existing eventual finite-law proposition is now discharged by an ALL-size identity. -/
theorem countPfaffianMomentIdentity_of_isOpen_upper (A : Set ℂ) (hA : IsOpen A)
    (hupper : ∀ a ∈ A, 0 < a.im) : CountPfaffianMomentIdentity A := by
  intro k
  exact Filter.Eventually.of_forall fun n =>
    actual_countFactorialMoment_eq_pfaffianKernelMoment A hA hupper n k

theorem countPfaffianMomentIdentity_of_admissible {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) : CountPfaffianMomentIdentity A :=
  countPfaffianMomentIdentity_of_isOpen_upper A hA.1
    (fun _z hz => (hA.2.2.1 (subset_closure hz)).2)

/-- Unconditional main CLT, retaining EVERY frozen admissibility hypothesis. -/
theorem mainTheorem_unconditional (A : Set ℂ) (hA : IsAdmissibleLipschitzDomain A) : MainConclusion A :=
  mainTheorem_of_momentIdentity A hA (countPfaffianMomentIdentity_of_admissible hA)

/-- Exactly the reviewed unconditional principal target, with no intermediate premises. -/
theorem principalTheorem : PrincipalStatement := by
  intro A hA
  exact mainTheorem_unconditional A hA

/-- The original count variance approximation, for each admissible domain. -/
theorem countVariance_error_bigO {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    (fun n : ℕ ↦ ProbabilityTheory.variance (fun M : SampleSpace n ↦ (count A n M : ℝ))
      (matrixLaw n) - Kernel.gaussianVarianceExpression A (n+1))
        =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
  countVariance_error_bigO_of_finiteLaw hA (countPfaffianMomentIdentity_of_admissible hA)

/-- The actual normalized-statistic variance has the manuscript's exact limit. -/
theorem statistic_variance_tendsto {A : Set ℂ} (hA : IsAdmissibleLipschitzDomain A) :
    Tendsto (fun n : ℕ ↦ ProbabilityTheory.variance (statistic A n) (matrixLaw n)) atTop
      (𝓝 ((boundaryMeasure A).toReal / (2 * Real.pi ^ (3 / 2 : ℝ)))) :=
  statistic_variance_tendsto_of_finiteLaw hA (countPfaffianMomentIdentity_of_admissible hA)

/-- The source exponential comparison, with one positive rate before all fixed orders. -/
theorem countCumulant_determinantal_exp_close_unconditional {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r →
      (fun n ↦ countCumulant A n r -
        Kernel.realDeterminantalPseudoCumulant A (n+1) r) =O[atTop]
          (fun n ↦ Real.exp (-c * (n+1 : ℝ))) :=
  countCumulant_determinantal_exp_close hA (countPfaffianMomentIdentity_of_admissible hA)

/-- All actual cumulant limits under exactly the original admissibility conditions. -/
theorem cumulantLimits_of_admissible {A : Set ℂ}
    (hA : IsAdmissibleLipschitzDomain A) (ell : ℝ≥0)
    (hell : (ell : ℝ≥0∞) = boundaryMeasure A) : CumulantLimits A ell :=
  cumulantLimits_of_momentIdentity hA (countPfaffianMomentIdentity_of_admissible hA) ell hell

end Paper
