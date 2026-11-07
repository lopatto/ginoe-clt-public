/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.ConjugationDeterminant
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Matrix Kronecker
namespace Paper.Spectral

/-- Orthogonal conjugation preserves literal column-major Pi Lebesgue measure.
The determinant-one identity includes either orthogonal component and N=0. -/
theorem volume_preserving_orthogonalConjugation_cells (N : ℕ)
    (Q : Matrix.orthogonalGroup (Fin N) ℝ) :
    MeasurePreserving
      (Matrix.toLin' ((Q : Matrix (Fin N) (Fin N) ℝ) ⊗ₖ
        (Q : Matrix (Fin N) (Fin N) ℝ))) volume volume := by
  let M := ((Q : Matrix (Fin N) (Fin N) ℝ) ⊗ₖ
    (Q : Matrix (Fin N) (Fin N) ℝ))
  have hd : M.det = 1 := det_orthogonalConjugation_kronecker N Q
  have hn : M.det ≠ 0 := by rw [hd]; exact one_ne_zero
  refine ⟨(Matrix.toLin' M).toContinuousLinearMap.continuous.measurable,?_⟩
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hn
  simpa only [hd,inv_one,abs_one,ENNReal.ofReal_one,one_smul] using hm

end Paper.Spectral
