/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurPairChangeOfVariables
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper.Spectral

lemma ofReal_mul_inv_pos (r s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (r*s) * ENNReal.ofReal (1/s) = ENNReal.ofReal r := by
  rw [mul_comm,← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The exact pair-ratio factor of the full-word Vandermonde normalization.
This is ordinary raw free-head volume on the ORIGINAL b≥c>0 domain. -/
theorem lintegral_pairHead_gaussian_ratio (H : ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ h in pairHeadDomain,
      ENNReal.ofReal ((h 1-h 2)/Real.sqrt (h 1*h 2) *
        Real.exp (-(2*h 0^2+h 1^2+h 2^2)/2)) *
        H ((h 0 : ℂ)+(Real.sqrt (h 1*h 2) : ℂ)*Complex.I)) =
      ∫⁻ z in {z : ℂ | 0 < z.im},
        ENNReal.ofReal (Real.sqrt (2*Real.pi)*Real.exp (z.im^2-z.re^2)*
          Paper.Kernel.erfc (Real.sqrt 2*z.im)) * H z := by
  let J : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(2*z.im))*H z
  have hJ : Measurable J := by unfold J; fun_prop
  calc
    _ = ∫⁻ h in pairHeadDomain,
        ENNReal.ofReal (2*(h 1-h 2)*Real.exp (-(2*h 0^2+h 1^2+h 2^2)/2)) *
          J ((h 0 : ℂ)+(Real.sqrt (h 1*h 2) : ℂ)*Complex.I) := by
      apply setLIntegral_congr_fun measurableSet_pairHeadDomain
      intro h hh
      have hc : 0 < h 2 := hh.1
      have hb : 0 < h 1 := lt_of_lt_of_le hc hh.2
      have hy : 0 < Real.sqrt (h 1*h 2) := Real.sqrt_pos.mpr (mul_pos hb hc)
      have he : 2*(h 1-h 2)*Real.exp (-(2*h 0^2+h 1^2+h 2^2)/2) =
          ((h 1-h 2)/Real.sqrt (h 1*h 2) *
            Real.exp (-(2*h 0^2+h 1^2+h 2^2)/2)) * (2*Real.sqrt (h 1*h 2)) := by
        field_simp
      dsimp only [J]
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_add,add_zero]
      rw [← mul_assoc,he,ofReal_mul_inv_pos _ _ (mul_pos (by norm_num) hy)]
    _ = ∫⁻ z in {z : ℂ | 0 < z.im},
        ENNReal.ofReal (2*Real.sqrt (2*Real.pi)*z.im*Real.exp (z.im^2-z.re^2)*
          Paper.Kernel.erfc (Real.sqrt 2*z.im)) * J z :=
      lintegral_pairHead_gaussian_complex J hJ
    _ = _ := by
      apply setLIntegral_congr_fun
        (isOpen_lt continuous_const Complex.continuous_im).measurableSet
      intro z hz
      have hy : 0 < z.im := hz
      have he : 2*Real.sqrt (2*Real.pi)*z.im*Real.exp (z.im^2-z.re^2)*
          Paper.Kernel.erfc (Real.sqrt 2*z.im) =
        (Real.sqrt (2*Real.pi)*Real.exp (z.im^2-z.re^2)*
          Paper.Kernel.erfc (Real.sqrt 2*z.im)) * (2*z.im) := by ring
      dsimp only [J]
      rw [← mul_assoc,he,ofReal_mul_inv_pos _ _ (mul_pos (by norm_num) hy)]

end Paper.Spectral
