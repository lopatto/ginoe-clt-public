/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Reduction
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Analytic prerequisites for the count cumulants

Bounds below are at each fixed matrix size. No uniform exponential-moment
hypothesis is imposed on the sequence of normalized counts.
-/

public section
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace Paper

/-- Boundedness supplies the integrability needed for the genuine analytic cgf. -/
theorem statistic_exp_integrable {A : Set ℂ} (h : CountMeasurable A)
    (n : ℕ) (t : ℝ) :
    Integrable (fun M : SampleSpace n ↦ Real.exp (t * statistic A n M)) (matrixLaw n) := by
  apply integrable_exp_mul_of_mem_Icc (statistic_aemeasurable h n)
  apply ae_of_all
  intro M
  exact abs_le.mp ((Real.norm_eq_abs _).symm ▸ statistic_norm_le A n M)

/-- Every real parameter belongs to the exponential-integrability domain. -/
theorem statistic_integrableExpSet {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    integrableExpSet (statistic A n) (matrixLaw n) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact statistic_exp_integrable h n t

theorem statistic_mem_interior_integrableExpSet {A : Set ℂ}
    (h : CountMeasurable A) (n : ℕ) (t : ℝ) :
    t ∈ interior (integrableExpSet (statistic A n) (matrixLaw n)) := by
  rw [statistic_integrableExpSet h n, interior_univ]
  trivial

/-- The manuscript's analytic cumulants exist at every fixed size. -/
theorem statistic_cgf_analytic {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    AnalyticOnNhd ℝ (cgf (statistic A n) (matrixLaw n)) Set.univ := by
  intro t _
  exact analyticAt_cgf (statistic_mem_interior_integrableExpSet h n t)

theorem statistic_integral {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    (∫ M, statistic A n M ∂matrixLaw n) = 0 := by
  unfold statistic
  rw [integral_div, integral_sub (count_integrable h n) (integrable_const _)]
  simp [meanCount]

theorem cumulant_zero (A : Set ℂ) (n : ℕ) : cumulant A n 0 = 0 := by
  simp [cumulant]

/-- Exact centering kills the first genuine cumulant. -/
theorem cumulant_one {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    cumulant A n 1 = 0 := by
  rw [cumulant, iteratedDeriv_one,
    deriv_cgf_zero (statistic_mem_interior_integrableExpSet h n 0)]
  simp [statistic_integral h n]

/-- The second analytic cumulant is the actual centered second moment. -/
theorem cumulant_two {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    cumulant A n 2 = moment A n 2 := by
  rw [cumulant, iteratedDeriv_two_cgf (statistic_mem_interior_integrableExpSet h n 0)]
  simp [moment, statistic_integral h n,
    deriv_cgf_zero (statistic_mem_interior_integrableExpSet h n 0)]

theorem cumulant_two_eq_variance {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    cumulant A n 2 = variance (statistic A n) (matrixLaw n) := by
  rw [cumulant_two h n,
    variance_of_integral_eq_zero (statistic_aemeasurable h n) (statistic_integral h n)]
  rfl

/-- All mgf derivatives at zero are the exact normalized-count moments. -/
theorem statistic_mgf_derivative {A : Set ℂ} (h : CountMeasurable A) (n r : ℕ) :
    iteratedDeriv r (mgf (statistic A n) (matrixLaw n)) 0 = moment A n r := by
  exact iteratedDeriv_mgf_zero (statistic_mem_interior_integrableExpSet h n 0) r

/-- Raw-count cumulants before exact centering and the CLT normalization. -/
@[expose] noncomputable def countCumulant (A : Set ℂ) (n r : ℕ) : ℝ :=
  iteratedDeriv r (cgf (fun M : SampleSpace n ↦ (count A n M : ℝ)) (matrixLaw n)) 0

theorem count_exp_integrable {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) (t : ℝ) :
    Integrable (fun M : SampleSpace n ↦ Real.exp (t * (count A n M : ℝ)))
      (matrixLaw n) := by
  apply integrable_exp_mul_of_mem_Icc (a := 0) (b := (n + 1 : ℝ)) (h n).aemeasurable
  apply ae_of_all
  intro M
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast count_le A n M⟩

theorem count_mem_interior_integrableExpSet {A : Set ℂ}
    (h : CountMeasurable A) (n : ℕ) (t : ℝ) :
    t ∈ interior (integrableExpSet (fun M : SampleSpace n ↦ (count A n M : ℝ))
      (matrixLaw n)) := by
  have hset : integrableExpSet (fun M : SampleSpace n ↦ (count A n M : ℝ))
      (matrixLaw n) = Set.univ := by
    ext u
    simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact count_exp_integrable h n u
  rw [hset, interior_univ]
  trivial

theorem count_cgf_analytic {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) :
    AnalyticOnNhd ℝ
      (cgf (fun M : SampleSpace n ↦ (count A n M : ℝ)) (matrixLaw n)) Set.univ := by
  intro t _
  exact analyticAt_cgf (count_mem_interior_integrableExpSet h n t)

/-- Pointwise identity for the cgf of the exactly centered and normalized count. -/
theorem statistic_cgf_eq {A : Set ℂ} (h : CountMeasurable A) (n : ℕ) (t : ℝ) :
    cgf (statistic A n) (matrixLaw n) t =
      cgf (fun M : SampleSpace n ↦ (count A n M : ℝ)) (matrixLaw n)
        (((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹ * t) -
      (((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹ * t) * meanCount A n := by
  have hfun : statistic A n = fun M : SampleSpace n ↦
      ((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹ * ((count A n M : ℝ) + -meanCount A n) := by
    funext M
    simp [statistic, div_eq_inv_mul, sub_eq_add_neg]
  rw [hfun, cgf, mgf_const_mul, mgf_add_const,
    Real.log_mul (mgf_pos (count_exp_integrable h n _)).ne' (Real.exp_ne_zero _)]
  simp [cgf, sub_eq_add_neg]

/-- Cumulants of order at least two are invariant under centering and
homogeneous under the precise CLT normalization. -/
theorem cumulant_eq_countCumulant {A : Set ℂ} (h : CountMeasurable A)
    (n r : ℕ) (hr : 2 ≤ r) :
    cumulant A n r = (((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ r * countCumulant A n r := by
  let c : ℝ := ((n + 1 : ℝ) ^ (1 / 4 : ℝ))⁻¹
  let K : ℝ → ℝ :=
    cgf (fun M : SampleSpace n ↦ (count A n M : ℝ)) (matrixLaw n)
  have hc : ContDiff ℝ r K := (count_cgf_analytic h n).contDiff
  have hcomp : ContDiff ℝ r (fun t : ℝ ↦ K (c * t)) :=
    hc.comp (contDiff_const.mul contDiff_id)
  have hlin : ContDiff ℝ r (fun t : ℝ ↦ c * t * meanCount A n) := by fun_prop
  have heq : cgf (statistic A n) (matrixLaw n) =
      fun t : ℝ ↦ K (c * t) - c * t * meanCount A n :=
    funext (statistic_cgf_eq h n)
  have hr0 : r ≠ 0 := by omega
  have hr1 : r ≠ 1 := by omega
  have hlinear : iteratedDeriv r (fun t : ℝ ↦ c * t * meanCount A n) 0 = 0 := by
    have hfn : (fun t : ℝ ↦ c * t * meanCount A n) =
        (fun t : ℝ ↦ t * (c * meanCount A n)) := by
      funext t
      ring
    rw [hfn, iteratedDeriv_mul_const_field]
    simp only [iteratedDeriv_fun_id, ite_eq_right hr0, ite_eq_right hr1, zero_mul]
  rw [cumulant, heq, iteratedDeriv_fun_sub hcomp.contDiffAt hlin.contDiffAt,
    hlinear, sub_zero, iteratedDeriv_comp_const_mul hc]
  simp only [mul_zero]
  rfl

end Paper
