/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Probability.GaussianEntries
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.LinearAlgebra.Matrix.Vec

/-! # The actual matrix law in Euclidean Frobenius coordinates

The ordinary matrix/Pi norm is unchanged. EuclideanSpace supplies the genuine
sum-of-squares norm on the flattened coordinates.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Paper

abbrev MatrixCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))

def matrixVector (n : ℕ) (M : SampleSpace n) : MatrixCoordinates n :=
  WithLp.toLp 2 (Matrix.vec M)

theorem matrixLaw_vec_map (n : ℕ) :
    (matrixLaw n).map (Matrix.vec : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) =
      Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) × Fin (n + 1) => ℝ)
    (Equiv.prodComm (Fin (n + 1)) (Fin (n + 1)))
  have he : (Matrix.vec : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) =
      e ∘ Function.uncurry := by
    funext M ij
    rfl
  have hu : Measurable (Function.uncurry : SampleSpace n →
      (Fin (n + 1) × Fin (n + 1) → ℝ)) := by fun_prop
  have hh : (matrixLaw n).map (Matrix.vec : SampleSpace n →
      (Fin (n + 1) × Fin (n + 1) → ℝ)) =
      ((matrixLaw n).map (Function.uncurry : SampleSpace n →
        (Fin (n + 1) × Fin (n + 1) → ℝ))).map e := by
    exact (congrArg (fun f : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ) =>
      (matrixLaw n).map f) he).trans (Measure.map_map e.measurable hu).symm
  rw [hh, Spectral.matrixLaw_uncurry_map]
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1)
    (Equiv.prodComm (Fin (n + 1)) (Fin (n + 1)))).map_eq

/-- The frozen nested real iid Gaussian law is exactly the standard Gaussian
in the actual Euclidean/Frobenius matrix coordinates. -/
theorem matrixLaw_matrixVector_map (n : ℕ) :
    (matrixLaw n).map (matrixVector n) = stdGaussian (MatrixCoordinates n) := by
  have he : matrixVector n = (WithLp.toLp 2) ∘
      (Matrix.vec : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) := rfl
  have hv : Measurable (Matrix.vec : SampleSpace n →
      (Fin (n + 1) × Fin (n + 1) → ℝ)) := by
    unfold Matrix.vec
    fun_prop
  have hh : (matrixLaw n).map (matrixVector n) =
      ((matrixLaw n).map (Matrix.vec : SampleSpace n →
        (Fin (n + 1) × Fin (n + 1) → ℝ))).map (WithLp.toLp 2) := by
    exact (congrArg (fun f : SampleSpace n → MatrixCoordinates n =>
      (matrixLaw n).map f) he).trans (Measure.map_map (by fun_prop) hv).symm
  rw [hh, matrixLaw_vec_map]
  exact map_pi_eq_stdGaussian

end Paper
