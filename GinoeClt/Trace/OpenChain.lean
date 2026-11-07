/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.CycleExponent
public import GinoeClt.Trace.ComplexGaussian

/-! # Absolutely integrable open-chain Gaussian and endpoint elimination -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Paper.Trace

theorem continuous_squareMass (n : ℕ) : Continuous (squareMass (k := n)) := by
  change Continuous (fun u : Fin n → ℂ => ∑ i, ‖u i‖ ^ 2)
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).norm.pow 2

theorem continuous_chainInteraction (n : ℕ) : Continuous (chainInteraction n) := by
  cases n with
  | zero =>
    change Continuous (fun _ : Fin 0 → ℂ => (0 : ℂ))
    exact continuous_const
  | succ n =>
    change Continuous (fun u : Fin (n + 1) → ℂ => ∑ i : Fin n,
      u i.castSucc * conj (u i.succ))
    exact continuous_finsetSum _ fun i _ =>
      (continuous_apply i.castSucc).mul (continuous_star.comp (continuous_apply i.succ))

theorem continuous_openChainGaussian (a : ℝ) (n : ℕ) :
    Continuous (openChainGaussian a n) := by
  unfold openChainGaussian
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul (continuous_squareMass n))).add
      (continuous_const.mul (continuous_chainInteraction n)))

theorem norm_openChainGaussian_le {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℂ) :
    ‖openChainGaussian a n u‖ ≤
      Real.exp (-(a / (2 * ((n + 1 : ℝ) * (n : ℝ)))) * squareMass u) := by
  have hC : 0 < (n + 1 : ℝ) * (n : ℝ) := by positivity
  have hb : 0 < a / (2 * ((n + 1 : ℝ) * (n : ℝ))) := by positivity
  have hs := squareMass_le_anchored_cycleEnergy n u
  push_cast at hs
  have hh := mul_le_mul_of_nonneg_left hs hb.le
  have hc : a / (2 * ((n + 1 : ℝ) * (n : ℝ))) *
      ((n + 1 : ℝ) * (n : ℝ)) = a / 2 := by field_simp
  conv_rhs at hh => rw [← mul_assoc, hc]
  rw [norm_openChainGaussian]
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using neg_le_neg hh

theorem integrable_openChainGaussian {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (openChainGaussian a n) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
    let b : ℝ := a / (2 * ((n + 1 : ℝ) * (n : ℝ)))
    have hb : 0 < b := by dsimp [b]; positivity
    have he : (fun u : Fin n → ℂ => Real.exp (-b * squareMass u)) =
        (fun u : Fin n → ℂ => ∏ i, Real.exp (-b * ‖u i‖ ^ 2)) := by
      funext u
      rw [squareMass, Finset.mul_sum, Real.exp_sum]
    have hi : Integrable (fun u : Fin n → ℂ => Real.exp (-b * squareMass u)) := by
      rw [he]
      exact Integrable.fintype_prod (fun _ : Fin n => GaussianIntegrals.integrable_gaussian hb)
    apply hi.mono' (continuous_openChainGaussian a n).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun u => norm_openChainGaussian_le ha hn0 u

theorem openChainGaussian_cons (a : ℝ) {n : ℕ} (w : ℂ) (u : Fin n → ℂ) :
    openChainGaussian a (n + 1) (Fin.cons w u) =
      endpointGaussian a ((a : ℂ) * conj (chainHead n u)) w * openChainGaussian a n u := by
  simp only [openChainGaussian, squareMass_cons, chainInteraction_cons, endpointGaussian]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_openChainGaussian {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ u : Fin n → ℂ, openChainGaussian a n u) = (((Real.pi / a : ℝ) : ℂ)) ^ n := by
  induction n with
  | zero =>
    have hv : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
      change (Measure.pi (fun _ : Fin 0 => (volume : Measure ℂ))) Set.univ = 1
      simp
    simp [openChainGaussian, squareMass, chainInteraction, measureReal_def, hv]
  | succ n ih =>
    let F : (ℂ × (Fin n → ℂ)) → ℂ := fun p =>
      endpointGaussian a ((a : ℂ) * conj (chainHead n p.2)) p.1 * openChainGaussian a n p.2
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hm : MeasurePreserving e.symm (volume : Measure (ℂ × (Fin n → ℂ))) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
    have heq : (openChainGaussian a (n + 1)) ∘ e.symm = F := by
      funext p
      simp [e, F, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.zero_succAbove, openChainGaussian_cons]
    have hFi : Integrable F := by
      rw [← heq]
      exact (hm.integrable_comp_emb e.symm.measurableEmbedding).mpr
        (integrable_openChainGaussian ha (n + 1))
    calc
      (∫ u : Fin (n + 1) → ℂ, openChainGaussian a (n + 1) u) = ∫ p, F p := by
        rw [← hm.integral_comp' (openChainGaussian a (n + 1))]
        change (∫ p, ((openChainGaussian a (n + 1)) ∘ e.symm) p) = ∫ p, F p
        rw [heq]
      _ = ∫ u : Fin n → ℂ, ∫ w : ℂ, F (w, u) := integral_prod_symm F hFi
      _ = ∫ u : Fin n → ℂ, (((Real.pi / a : ℝ) : ℂ)) * openChainGaussian a n u := by
        apply integral_congr_ae
        filter_upwards with u
        dsimp only [F]
        rw [integral_mul_const, integral_endpointGaussian ha]
      _ = _ := by rw [integral_const_mul, ih, pow_succ]; ring

end Paper.Trace
