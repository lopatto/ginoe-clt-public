/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.AsymptoticCumulants
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Fixed-polynomial propagation of exponentially small errors

Polynomial factors are retained throughout the algebra. The exponential rate
is decreased only once, after the fixed polynomial has been evaluated.
-/

@[expose] public section
noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Paper.ExponentialErrors

def PowerBound (f : ℕ → ℝ) : Prop := ∃ a : ℝ, f =O[atTop] Cumulants.sizePower a

def ExpPowerBound (c : ℝ) (f : ℕ → ℝ) : Prop :=
  ∃ a : ℝ, f =O[atTop] fun n =>
    Cumulants.sizePower a n * Real.exp (-c * (n + 1 : ℝ))

theorem PowerBound.const (r : ℝ) : PowerBound (fun _ => r) := by
  refine ⟨0, ?_⟩
  have hz : Cumulants.sizePower 0 = fun _ : ℕ => (1 : ℝ) := by
    funext n
    simp [Cumulants.sizePower]
  rw [hz]
  exact isBigO_const_one ℝ r (atTop : Filter ℕ)

theorem PowerBound.add {f g : ℕ → ℝ} (hf : PowerBound f) (hg : PowerBound g) :
    PowerBound (fun n => f n + g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨max a b, (ha.trans (Cumulants.sizePower_mono_bigO (le_max_left a b))).add
    (hb.trans (Cumulants.sizePower_mono_bigO (le_max_right a b)))⟩

theorem PowerBound.mul {f g : ℕ → ℝ} (hf : PowerBound f) (hg : PowerBound g) :
    PowerBound (fun n => f n * g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, ?_⟩
  simpa only [Cumulants.sizePower_mul] using ha.mul hb

theorem ExpPowerBound.zero (c : ℝ) : ExpPowerBound c (fun _ => 0) :=
  ⟨0, isBigO_zero ..⟩

theorem ExpPowerBound.add {c : ℝ} {f g : ℕ → ℝ}
    (hf : ExpPowerBound c f) (hg : ExpPowerBound c g) :
    ExpPowerBound c (fun n => f n + g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have hexp := isBigO_refl (fun n : ℕ => Real.exp (-c * (n + 1 : ℝ))) atTop
  exact ⟨max a b,
    (ha.trans ((Cumulants.sizePower_mono_bigO (le_max_left a b)).mul hexp)).add
      (hb.trans ((Cumulants.sizePower_mono_bigO (le_max_right a b)).mul hexp))⟩

theorem ExpPowerBound.mul_power {c : ℝ} {f g : ℕ → ℝ}
    (hf : ExpPowerBound c f) (hg : PowerBound g) :
    ExpPowerBound c (fun n => f n * g n) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨a + b, ?_⟩
  have hh := ha.mul hb
  simpa only [mul_right_comm _ _ (Cumulants.sizePower b _),
    Cumulants.sizePower_mul] using hh

theorem ExpPowerBound.exp_close {c : ℝ} {f : ℕ → ℝ}
    (hc : 0 < c) (hf : ExpPowerBound c f) :
    f =O[atTop] fun n => Real.exp (-(c / 2) * (n + 1 : ℝ)) := by
  obtain ⟨a, ha⟩ := hf
  have h := (isLittleO_exp_mul_rpow_of_lt a
    (a := -c) (b := -(c / 2)) (by linarith)).comp_tendsto Cumulants.tendsto_matrixSize
  have hh : (fun n : ℕ => Real.exp (-c * (n + 1 : ℝ)) * (n + 1 : ℝ) ^ a) =O[atTop]
      (fun n => Real.exp (-(c / 2) * (n + 1 : ℝ))) := h.isBigO
  exact ha.trans (by simpa only [Cumulants.sizePower, mul_comm] using hh)

theorem powerBound_eval {σ : Type*} (p : MvPolynomial σ ℝ) (x : σ → ℕ → ℝ)
    (hx : ∀ i, PowerBound (x i)) :
    PowerBound (fun n => MvPolynomial.eval (fun i => x i n) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [MvPolynomial.eval_C] using PowerBound.const r
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul (hx i)

theorem expPowerBound_eval_sub {σ : Type*} {c : ℝ} (p : MvPolynomial σ ℝ)
    (x y : σ → ℕ → ℝ) (hx : ∀ i, PowerBound (x i)) (hy : ∀ i, PowerBound (y i))
    (hxy : ∀ i, ExpPowerBound c (fun n => x i n - y i n)) :
    ExpPowerBound c (fun n =>
      MvPolynomial.eval (fun i => x i n) p - MvPolynomial.eval (fun i => y i n) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [MvPolynomial.eval_C, sub_self] using ExpPowerBound.zero c
  | add p q hp hq =>
    have hh := hp.add hq
    convert hh using 1
    funext n
    simp only [MvPolynomial.eval_add]
    ring
  | mul_X p i hp =>
    have h1 := hp.mul_power (hx i)
    have h2 := (hxy i).mul_power (powerBound_eval p y hy)
    have hh := h1.add h2
    convert hh using 1
    funext n
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    ring

/-- One final absorption: the rate c/2 depends on the input rate, not on p. -/
theorem polynomial_exp_close {σ : Type*} {c : ℝ} (hc : 0 < c)
    (p : MvPolynomial σ ℝ) (x y : σ → ℕ → ℝ)
    (hx : ∀ i, PowerBound (x i)) (hy : ∀ i, PowerBound (y i))
    (hxy : ∀ i, ExpPowerBound c (fun n => x i n - y i n)) :
    (fun n => MvPolynomial.eval (fun i => x i n) p -
      MvPolynomial.eval (fun i => y i n) p) =O[atTop]
        fun n => Real.exp (-(c / 2) * (n + 1 : ℝ)) :=
  (expPowerBound_eval_sub p x y hx hy hxy).exp_close hc

end Paper.ExponentialErrors
