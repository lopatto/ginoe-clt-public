/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Trace.OpenChain
public import GinoeClt.Trace.CycleTranslation

/-! # Haar translation of the anchored cycle integral -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Paper.Trace

theorem cycleAnchor_eq_shift (a : ℝ) (n : ℕ) (z : ℂ) :
    (fun u : Fin n → ℂ => Complex.exp (cycleExponent a (Fin.cons z u))) =
      (fun u : Fin n → ℂ => openChainGaussian a n (u - fun _ => z)) := by
  funext u
  exact exp_cycleExponent_anchor a z u

theorem integrable_cycleAnchor {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) :
    Integrable (fun u : Fin n → ℂ => Complex.exp (cycleExponent a (Fin.cons z u))) := by
  rw [cycleAnchor_eq_shift]
  exact (integrable_openChainGaussian ha n).comp_sub_right (fun _ : Fin n => z)

theorem integral_cycleAnchor {a : ℝ} (ha : 0 < a) (n : ℕ) (z : ℂ) :
    (∫ u : Fin n → ℂ, Complex.exp (cycleExponent a (Fin.cons z u))) =
      (((Real.pi / a : ℝ) : ℂ)) ^ n := by
  rw [cycleAnchor_eq_shift, integral_sub_right_eq_self, integral_openChainGaussian ha]

theorem continuous_cycleExponent (a : ℝ) (k : ℕ) :
    Continuous (cycleExponent a (k := k)) := by
  have hp : Continuous (cyclePairing (k := k)) := by
    change Continuous (fun z : Fin k → ℂ => ∑ i, z i * conj (z (finRotate k i)))
    exact continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul (continuous_star.comp (continuous_apply (finRotate k i)))
  unfold cycleExponent
  exact (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_squareMass k))).add
    (continuous_const.mul hp)

theorem integrable_anchorProduct {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    Integrable (fun p : ℂ × (Fin n → ℂ) =>
      Complex.exp (cycleExponent a (Fin.cons p.1 p.2)))
      ((volume.restrict A).prod volume) := by
  let F : (ℂ × (Fin n → ℂ)) → ℂ := fun p =>
    Complex.exp (cycleExponent a (Fin.cons p.1 p.2))
  have hc : Continuous F := by
    have hcons : Continuous (fun p : ℂ × (Fin n → ℂ) =>
        (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ)) :=
      continuous_pi fun i => Fin.cases continuous_fst
        (fun j => (continuous_apply j).comp continuous_snd) i
    exact Complex.continuous_exp.comp ((continuous_cycleExponent a (n + 1)).comp hcons)
  have hnorm (z : ℂ) : (∫ u : Fin n → ℂ, ‖F (z, u)‖) =
      ∫ u : Fin n → ℂ, ‖openChainGaussian a n u‖ := by
    have he : (fun u : Fin n → ℂ => ‖F (z, u)‖) =
        (fun u : Fin n → ℂ => ‖openChainGaussian a n (u - fun _ => z)‖) := by
      funext u
      exact congrArg norm (exp_cycleExponent_anchor a z u)
    rw [he]
    exact integral_sub_right_eq_self (fun u : Fin n → ℂ => ‖openChainGaussian a n u‖)
      (fun _ : Fin n => z)
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun z => integrable_cycleAnchor ha n z
  · simp only [hnorm]
    exact integrableOn_const (C := ∫ u : Fin n → ℂ, ‖openChainGaussian a n u‖) hA

theorem integral_anchorProduct {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    (∫ p : ℂ × (Fin n → ℂ), Complex.exp (cycleExponent a (Fin.cons p.1 p.2))
      ∂((volume.restrict A).prod volume)) =
      ((volume.real A : ℝ) : ℂ) * (((Real.pi / a : ℝ) : ℂ)) ^ n := by
  rw [integral_prod _ (integrable_anchorProduct ha n A hA)]
  simp_rw [integral_cycleAnchor ha n]
  rw [setIntegral_const, Complex.real_smul]

/-- The actual I₀ domain: only the first coordinate is restricted to A. -/
theorem anchored_cycle_integral {a : ℝ} (ha : 0 < a) (n : ℕ)
    (A : Set ℂ) (hA : volume A ≠ ⊤) :
    IntegrableOn (fun x : Fin (n + 1) → ℂ => Complex.exp (cycleExponent a x))
      {x | x 0 ∈ A} ∧
    (∫ x : Fin (n + 1) → ℂ in {x | x 0 ∈ A}, Complex.exp (cycleExponent a x)) =
      ((volume.real A : ℝ) : ℂ) * (((Real.pi / a : ℝ) : ℂ)) ^ n := by
  let B : Set (Fin (n + 1) → ℂ) := {x | x 0 ∈ A}
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
  have hm : MeasurePreserving e.symm (volume : Measure (ℂ × (Fin n → ℂ))) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
  have hb : e.symm ⁻¹' B = A ×ˢ (Set.univ : Set (Fin n → ℂ)) := by
    ext p
    simp [e, B, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hr : MeasurePreserving e.symm ((volume.restrict A).prod volume)
      (volume.restrict B) := by
    have h := hm.restrict_preimage_emb e.symm.measurableEmbedding B
    rw [hb, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h
  have he : (fun x => Complex.exp (cycleExponent a x)) ∘ e.symm =
      (fun p : ℂ × (Fin n → ℂ) => Complex.exp (cycleExponent a (Fin.cons p.1 p.2))) := by
    funext p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.zero_succAbove]
  have hi : Integrable (fun x : Fin (n + 1) → ℂ => Complex.exp (cycleExponent a x))
      (volume.restrict B) := by
    apply (hr.integrable_comp_emb e.symm.measurableEmbedding).mp
    rw [he]
    exact integrable_anchorProduct ha n A hA
  refine ⟨hi, ?_⟩
  calc
    (∫ x in B, Complex.exp (cycleExponent a x)) =
        ∫ p : ℂ × (Fin n → ℂ), Complex.exp (cycleExponent a (Fin.cons p.1 p.2))
          ∂((volume.restrict A).prod volume) := by
      rw [← hr.integral_comp' (fun x => Complex.exp (cycleExponent a x))]
      change (∫ p, ((fun x => Complex.exp (cycleExponent a x)) ∘ e.symm) p
        ∂((volume.restrict A).prod volume)) = _
      rw [he]
    _ = _ := integral_anchorProduct ha n A hA

end Paper.Trace
