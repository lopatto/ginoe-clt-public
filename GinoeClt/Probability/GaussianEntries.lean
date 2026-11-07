/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.SimpleSpectrum
public import Mathlib.Probability.Independence.Basic

/-! # Actual standard real Gaussian matrix-entry laws -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Paper

theorem matrixEntry_measurePreserving (n : ℕ) (i j : Fin (n + 1)) :
    MeasurePreserving (fun M : SampleSpace n => M i j) (matrixLaw n) (gaussianReal 0 1) := by
  have h1 := measurePreserving_eval
    (fun _ : Fin (n + 1) => Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) i
  have h2 := measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) j
  exact h2.comp h1

theorem matrixEntry_map (n : ℕ) (i j : Fin (n + 1)) :
    Measure.map (fun M : SampleSpace n => M i j) (matrixLaw n) = gaussianReal 0 1 :=
  (matrixEntry_measurePreserving n i j).map_eq

theorem matrixEntries_independent (n : ℕ) :
    iIndepFun (fun ij : Fin (n + 1) × Fin (n + 1) =>
      fun M : SampleSpace n => M ij.1 ij.2) (matrixLaw n) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (μ := matrixLaw n)
    (f := fun ij : Fin (n + 1) × Fin (n + 1) => fun M : SampleSpace n => M ij.1 ij.2)
    (fun ij => (by fun_prop : Measurable (fun M : SampleSpace n => M ij.1 ij.2)).aemeasurable)).mpr
  simp_rw [matrixEntry_map]
  exact Spectral.matrixLaw_uncurry_map n

end Paper
