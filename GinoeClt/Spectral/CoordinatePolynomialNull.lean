/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.PolynomialNull
@[expose] public section
noncomputable section
open MeasureTheory
namespace Paper.Spectral

/-- Polynomial nullity after a genuine permutation of the same finite coordinates. -/
theorem realMvPolynomial_eval_precompose_ne_zero_ae {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) [SigmaFinite μ] [NullSingletonClass μ]
    (e : ι ≃ ι) (p : MvPolynomial ι ℝ) (hp : p ≠ 0) :
    ∀ᵐ y ∂Measure.pi (fun _ : ι => μ),
      MvPolynomial.eval (fun i => y (e i)) p ≠ 0 := by
  have h := realMvPolynomial_eval_ne_zero_ae μ p hp
  have he := (measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm).quasiMeasurePreserving.ae h
  filter_upwards [he] with y hy
  have hf : (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm y) =
      (fun i => y (e i)) := by
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => ℝ) y (e i)
    simpa only [Equiv.symm_apply_apply] using h
  rw [hf] at hy
  exact hy

end Paper.Spectral
