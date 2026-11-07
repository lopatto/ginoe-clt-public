/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.ErfcDomination
public import GinoeClt.Analysis.GaussianIntegrals
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Basic.Sign.Defs

/-! # The exact complex Gaussian skew weight

This is the upper-half-plane weight at tau = 0 in Forrester--Nagao,
arXiv:0806.0055v1, Theorem 1 and Corollary 2. It uses the project's actual
Gaussian-tail definition of `erfc`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set

namespace Paper.SkewOrthogonal

/-- The literal planar weight in the complex part of the real Ginibre skew form. -/
def complexWeight (z : ℂ) : ℝ :=
  Real.exp (-(z ^ 2).re) * Kernel.erfc (Real.sqrt 2 * z.im)

theorem complexWeight_nonneg (z : ℂ) : 0 ≤ complexWeight z :=
  mul_nonneg (Real.exp_pos _).le (Kernel.erfc_nonneg _)

theorem continuous_complexWeight : Continuous complexWeight := by
  exact (Real.continuous_exp.comp
    ((Complex.continuous_re.comp (continuous_id.pow 2)).neg)).mul
    (Kernel.continuous_erfc.comp (continuous_const.mul Complex.continuous_im))

/-- Global Gaussian domination on the closed upper half-plane. -/
theorem complexWeight_le_gaussian {z : ℂ} (hz : 0 ≤ z.im) :
    complexWeight z ≤ Real.exp (-‖z‖ ^ 2) := by
  have htail := Kernel.erfc_le_gaussian (mul_nonneg (Real.sqrt_nonneg 2) hz)
  have hre : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hs : (Real.sqrt 2 * z.im) ^ 2 = 2 * z.im ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    complexWeight z ≤ Real.exp (-(z ^ 2).re) *
        Real.exp (-(Real.sqrt 2 * z.im) ^ 2) :=
      mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    _ = Real.exp (-‖z‖ ^ 2) := by
      rw [← Real.exp_add, hre, hnorm, hs]
      congr 1
      ring

/-- Every radial polynomial moment of a genuine planar Gaussian is integrable. -/
theorem integrable_norm_pow_gaussian (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ n * Real.exp (-a * ‖z‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := (n : ℝ)) (b := a) (by norm_num) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) ha
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  rw [h]
  exact (mul_pos
    (mul_pos (div_pos (mul_pos (by norm_num) Real.pi_pos) (by norm_num))
      (Real.rpow_pos_of_pos ha _))
    (Real.Gamma_pos_of_pos (by positivity))).ne'

/-- Mixed ordinary/conjugate monomials have all planar Gaussian moments. -/
theorem integrable_gaussian_monomials (n m : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
      z ^ n * (starRingEnd ℂ z) ^ m) := by
  have hc : Continuous (fun z : ℂ ↦ (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
      z ^ n * (starRingEnd ℂ z) ^ m) :=
    ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))).mul
        (continuous_id.pow n)).mul (Complex.continuous_conj.pow m)
  apply (integrable_norm_pow_gaussian (n + m) ha).mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_pow, Complex.norm_conj, pow_add]
  ring_nf
  exact le_rfl

/-- Arbitrary ordinary/conjugate polynomial products are genuinely Gaussian-integrable. -/
theorem integrable_gaussian_polynomials (P Q : Polynomial ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
      P.eval z * Q.eval (starRingEnd ℂ z)) := by
  have heq : (fun z : ℂ ↦ (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
      P.eval z * Q.eval (starRingEnd ℂ z)) =
      fun z ↦ ∑ n ∈ P.support, ∑ m ∈ Q.support,
        (P.coeff n * Q.coeff m) *
          ((Real.exp (-a * ‖z‖ ^ 2) : ℂ) * z ^ n * (starRingEnd ℂ z) ^ m) := by
    funext z
    simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [mul_assoc]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [heq]
  apply integrable_finsetSum P.support
  intro n _
  apply integrable_finsetSum Q.support
  intro m _
  exact (integrable_gaussian_monomials n m ha).const_mul (P.coeff n * Q.coeff m)

/-- The literal complex part of the skew form is integrable before any Fubini or IBP. -/
theorem integrableOn_complexWeight_polynomials (P Q : Polynomial ℂ) :
    IntegrableOn (fun z : ℂ ↦ (complexWeight z : ℂ) *
      P.eval z * Q.eval (starRingEnd ℂ z)) {z : ℂ | 0 < z.im} := by
  have hc : Continuous (fun z : ℂ ↦ (complexWeight z : ℂ) *
      P.eval z * Q.eval (starRingEnd ℂ z)) :=
    ((Complex.continuous_ofReal.comp continuous_complexWeight).mul P.continuous).mul
      (Q.continuous.comp Complex.continuous_conj)
  apply ((integrable_gaussian_polynomials P Q (a := 1) (by norm_num)).norm.integrableOn).mono'
    hc.aestronglyMeasurable
  have hs : MeasurableSet {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im |>.measurableSet
  filter_upwards [ae_restrict_mem hs] with z hz
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (complexWeight_nonneg z),
    abs_of_pos (Real.exp_pos _), neg_mul, one_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (complexWeight_le_gaussian hz.le) (norm_nonneg _))
    (norm_nonneg _)

/-- Every scalar monomial times a real Gaussian is integrable, with complex values. -/
theorem integrable_real_gaussian_monomial (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ) * (x : ℂ) ^ n) := by
  have h : Integrable (fun x : ℝ ↦ x ^ n * Real.exp (-a * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using
      (_root_.integrable_rpow_mul_exp_neg_mul_sq (s := (n : ℝ)) ha
        (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith))
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, mul_comm] using
    (h.ofReal : Integrable (fun x : ℝ ↦ ((x ^ n * Real.exp (-a * x ^ 2) : ℝ) : ℂ)))

/-- Polynomial restrictions to the real axis have genuine Gaussian moments. -/
theorem integrable_real_gaussian_polynomial (P : Polynomial ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ) * P.eval (x : ℂ)) := by
  have heq : (fun x : ℝ ↦ (Real.exp (-a * x ^ 2) : ℂ) * P.eval (x : ℂ)) =
      fun x ↦ ∑ n ∈ P.support, P.coeff n *
        ((Real.exp (-a * x ^ 2) : ℂ) * (x : ℂ) ^ n) := by
    funext x
    simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq]
  apply integrable_finsetSum P.support
  intro n _
  exact (integrable_real_gaussian_monomial n ha).const_mul (P.coeff n)

/-- Two real polynomial variables are integrable against the exact joint Gaussian. -/
theorem integrable_real_gaussian_pair (P Q : Polynomial ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ ↦ (Real.exp (-a * (p.1 ^ 2 + p.2 ^ 2)) : ℂ) *
      P.eval (p.1 : ℂ) * Q.eval (p.2 : ℂ)) := by
  have h := (integrable_real_gaussian_polynomial P ha).mul_prod
    (integrable_real_gaussian_polynomial Q ha)
  rw [← Measure.volume_eq_prod] at h
  convert h using 1
  funext p
  have he : Real.exp (-a * (p.1 ^ 2 + p.2 ^ 2)) =
      Real.exp (-a * p.1 ^ 2) * Real.exp (-a * p.2 ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, Complex.ofReal_mul]
  ring

/-- The standard sign, cast into the complex numbers, is Borel measurable. -/
theorem measurable_complex_sign : Measurable (fun x : ℝ ↦ (SignType.sign x : ℂ)) := by
  have heq : (fun x : ℝ ↦ (SignType.sign x : ℂ)) =
      fun x ↦ if 0 < x then (1 : ℂ) else if x < 0 then -1 else 0 := by
    funext x
    by_cases hp : 0 < x <;> by_cases hn : x < 0 <;> simp [sign_apply, hp, hn]
  rw [heq]
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

/-- The real part of the skew form has an actually integrable joint integrand. -/
theorem integrable_real_skew_polynomials (P Q : Polynomial ℂ) :
    Integrable (fun p : ℝ × ℝ ↦ (SignType.sign (p.2 - p.1) : ℂ) *
      ((Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) : ℂ) *
        P.eval (p.1 : ℂ) * Q.eval (p.2 : ℂ))) := by
  let F : ℝ × ℝ → ℂ := fun p ↦ (Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) : ℂ) *
    P.eval (p.1 : ℂ) * Q.eval (p.2 : ℂ)
  have hF : Integrable F := by
    have h := integrable_real_gaussian_pair P Q (a := 1 / 2) (by norm_num)
    convert h using 1
    funext p
    dsimp only [F]
    rw [show -(p.1 ^ 2 + p.2 ^ 2) / 2 = -(1 / 2) * (p.1 ^ 2 + p.2 ^ 2) by ring]
  have hc : Continuous F := by
    exact (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (((continuous_fst.pow 2).add (continuous_snd.pow 2)).neg.div_const 2))).mul
        (P.continuous.comp (Complex.continuous_ofReal.comp continuous_fst))).mul
      (Q.continuous.comp (Complex.continuous_ofReal.comp continuous_snd)))
  have hs : Measurable (fun p : ℝ × ℝ ↦ (SignType.sign (p.2 - p.1) : ℂ)) :=
    measurable_complex_sign.comp (measurable_snd.sub measurable_fst)
  apply hF.norm.mono' (hs.mul hc.measurable).aestronglyMeasurable
  filter_upwards [] with p
  have hsign : ‖(SignType.sign (p.2 - p.1) : ℂ)‖ ≤ 1 := by
    by_cases hp : 0 < p.2 - p.1 <;> by_cases hn : p.2 - p.1 < 0 <;>
      simp [sign_apply, hp, hn]
  simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs, abs_norm, one_mul] using
    mul_le_mul_of_nonneg_right hsign (norm_nonneg (F p))

end Paper.SkewOrthogonal
