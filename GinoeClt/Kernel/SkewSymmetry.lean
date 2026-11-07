/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Kernel.PfaffianApproximation
public import GinoeClt.Algebra.PfaffianAgreement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Literal skew symmetry of the exact finite-N complex-complex kernel. -/
@[expose] public section
noncomputable section
open scoped ComplexConjugate
namespace Paper.Kernel

theorem D_swap (N : ℕ) (z w : ℂ) : D N w z = -D N z w := by
  unfold D
  rw [gaussianAmplitude_comm w z]
  have hs : -(w - z) ^ 2 / (2 : ℂ) = -(z - w) ^ 2 / 2 := by ring
  rw [hs, mul_comm w z]
  ring

theorem I_swap (N : ℕ) (z w : ℂ) : I N w z = -I N z w := by
  rw [I_eq_neg_conj_D, I_eq_neg_conj_D, D_swap, map_neg, neg_neg]

theorem pfaffianKernelMatrix_skew (N : ℕ) {k : ℕ} (z : Fin k → ℂ) :
    ∀ p q, pfaffianKernelMatrix N z q p = -pfaffianKernelMatrix N z p q := by
  rintro ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b
  · simpa [pfaffianKernelMatrix] using
      D_swap N (rescale N (z i)) (rescale N (z j))
  · simp [pfaffianKernelMatrix]
  · simp [pfaffianKernelMatrix]
  · simpa [pfaffianKernelMatrix] using
      I_swap N (rescale N (z i)) (rescale N (z j))

theorem pfaffianKernelMatrix_eq_recursivePf (N : ℕ) {k : ℕ} (z : Fin k → ℂ) :
    pfaffian (pfaffianKernelMatrix N z) = PfaffianMinor.recursivePf k
      ((pfaffianKernelMatrix N z).submatrix (PfaffianMinor.pairColumnEquiv k).symm
        (PfaffianMinor.pairColumnEquiv k).symm) :=
  Paper.pfaffian_eq_recursivePf _ (pfaffianKernelMatrix_skew N z)

end Paper.Kernel
