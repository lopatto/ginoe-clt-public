/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Erfc
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Exact finite-N kernels

The manuscript uses truncatedExponential (N-1), hence truncation at degree N-2
for N ≥ 2. The formulas are defined at every natural N; the extra small-size
values are internal extensions, not ensemble correlation assertions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate Real

namespace Paper.Kernel

def truncatedExponential (m : ℕ) (u : ℂ) : ℂ :=
  Complex.exp (-u) * ∑ j ∈ Finset.range m, u ^ j / (j.factorial : ℂ)

def gaussianAmplitude (z w : ℂ) : ℝ :=
  Real.sqrt (erfc (Real.sqrt 2 * z.im) * erfc (Real.sqrt 2 * w.im))

def S (N : ℕ) (z w : ℂ) : ℂ :=
  Complex.I / (Real.sqrt (2 * Real.pi) : ℂ) * (conj w - z) *
    Complex.exp (-(z - conj w) ^ 2 / 2) * (gaussianAmplitude z w : ℂ) *
      truncatedExponential (N - 1) (z * conj w)

def D (N : ℕ) (z w : ℂ) : ℂ :=
  (1 / (Real.sqrt (2 * Real.pi) : ℂ)) * (w - z) *
    Complex.exp (-(z - w) ^ 2 / 2) * (gaussianAmplitude z w : ℂ) *
      truncatedExponential (N - 1) (z * w)

def I (N : ℕ) (z w : ℂ) : ℂ :=
  (1 / (Real.sqrt (2 * Real.pi) : ℂ)) * (conj z - conj w) *
    Complex.exp (-(conj z - conj w) ^ 2 / 2) * (gaussianAmplitude z w : ℂ) *
      truncatedExponential (N - 1) (conj z * conj w)

def U (N : ℕ) (z w : ℂ) : ℂ :=
  (Complex.I * (conj w - z)) /
      ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ) *
    Complex.exp (-(N : ℂ) / 2 * (z - conj w) ^ 2 -
      (N : ℂ) * ((z.im : ℂ) ^ 2 + (w.im : ℂ) ^ 2))

def rescale (N : ℕ) (z : ℂ) : ℂ := (Real.sqrt (N : ℝ) : ℂ) * z

def scaledS (N : ℕ) (z w : ℂ) : ℂ := (N : ℂ) * S N (rescale N z) (rescale N w)

theorem continuous_truncatedExponential (m : ℕ) : Continuous (truncatedExponential m) := by
  unfold truncatedExponential
  fun_prop

theorem continuous_gaussianAmplitude : Continuous (Function.uncurry gaussianAmplitude) := by
  have h1 : Continuous (fun x : ℂ × ℂ => erfc (Real.sqrt 2 * x.1.im)) :=
    continuous_erfc.comp (continuous_const.mul (Complex.continuous_im.comp continuous_fst))
  have h2 : Continuous (fun x : ℂ × ℂ => erfc (Real.sqrt 2 * x.2.im)) :=
    continuous_erfc.comp (continuous_const.mul (Complex.continuous_im.comp continuous_snd))
  exact (h1.mul h2).sqrt

theorem gaussianAmplitude_nonneg (z w : ℂ) : 0 ≤ gaussianAmplitude z w := Real.sqrt_nonneg _

theorem gaussianAmplitude_comm (z w : ℂ) : gaussianAmplitude z w = gaussianAmplitude w z := by
  simp only [gaussianAmplitude, mul_comm]

theorem continuous_S (N : ℕ) : Continuous (Function.uncurry (S N)) := by
  unfold S
  have hg := Complex.continuous_ofReal.comp continuous_gaussianAmplitude
  have ht := continuous_truncatedExponential (N - 1)
  fun_prop

theorem continuous_D (N : ℕ) : Continuous (Function.uncurry (D N)) := by
  unfold D
  have hg := Complex.continuous_ofReal.comp continuous_gaussianAmplitude
  have ht := continuous_truncatedExponential (N - 1)
  fun_prop

theorem continuous_I (N : ℕ) : Continuous (Function.uncurry (I N)) := by
  unfold I
  have hg := Complex.continuous_ofReal.comp continuous_gaussianAmplitude
  have ht := continuous_truncatedExponential (N - 1)
  fun_prop

theorem continuous_rescale (N : ℕ) : Continuous (rescale N) := continuous_const.mul continuous_id

theorem continuous_scaledS (N : ℕ) : Continuous (Function.uncurry (scaledS N)) := by
  have h := (continuous_S N).comp
    (((continuous_rescale N).comp continuous_fst).prodMk
      ((continuous_rescale N).comp continuous_snd))
  exact continuous_const.mul h

theorem conj_truncatedExponential (m : ℕ) (u : ℂ) :
    conj (truncatedExponential m u) = truncatedExponential m (conj u) := by
  simp [truncatedExponential, map_mul, map_sum, map_div₀, map_pow, ← Complex.exp_conj]

theorem S_hermitian (N : ℕ) (z w : ℂ) : S N w z = conj (S N z w) := by
  simp only [S, map_mul, map_div₀, map_sub, map_neg, map_pow, map_ofNat,
    Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj, ← Complex.exp_conj,
    conj_truncatedExponential]
  rw [gaussianAmplitude_comm w z]
  have he : -(w - conj z) ^ 2 / (2 : ℂ) = -(conj z - w) ^ 2 / 2 := by ring
  rw [he, mul_comm (conj z) w]
  ring

theorem I_eq_neg_conj_D (N : ℕ) (z w : ℂ) : I N z w = -conj (D N z w) := by
  simp only [I, D, map_mul, map_div₀, map_sub, map_neg, map_pow, map_ofNat,
    map_one, Complex.conj_ofReal, ← Complex.exp_conj, conj_truncatedExponential]
  ring

theorem scaledS_hermitian (N : ℕ) (z w : ℂ) :
    scaledS N w z = conj (scaledS N z w) := by
  simp only [scaledS, map_mul, map_natCast, ← S_hermitian]


theorem continuousAt_U (N : ℕ) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    ContinuousAt (Function.uncurry (U N)) (z, w) := by
  have hn : Continuous (fun x : ℂ × ℂ => Complex.I * (conj x.2 - x.1)) := by fun_prop
  have hd : Continuous (fun x : ℂ × ℂ =>
      ((2 * Real.pi * Real.sqrt (x.1.im * x.2.im) : ℝ) : ℂ)) := by fun_prop
  have he : Continuous (fun x : ℂ × ℂ =>
      Complex.exp (-(N : ℂ) / 2 * (x.1 - conj x.2) ^ 2 -
        (N : ℂ) * ((x.1.im : ℂ) ^ 2 + (x.2.im : ℂ) ^ 2))) := by fun_prop
  have hd0 : ((2 * Real.pi * Real.sqrt (z.im * w.im) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  exact (hn.continuousAt.div hd.continuousAt hd0).mul he.continuousAt

end Paper.Kernel
