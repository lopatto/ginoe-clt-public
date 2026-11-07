/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Algebra.PfaffianAgreement
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Sign.Defs
@[expose] public section
noncomputable section
open scoped Matrix
namespace Paper.Spectral

/-- The ordered real sign kernel: +1 strictly above the diagonal, -1 below. -/
def upperSignMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i < j then 1 else if j < i then -1 else 0

theorem upperSignMatrix_skew (n : ℕ) :
    ∀ i j, upperSignMatrix n j i = -upperSignMatrix n i j := by
  intro i j
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt_of_ge hij.le
    simp [upperSignMatrix,hij,hji]
  · by_cases hji : j < i <;> simp [upperSignMatrix,hij,hji]

theorem upperSignMatrix_submatrix {n m : ℕ} (f : Fin n → Fin m) (hf : StrictMono f) :
    (upperSignMatrix m).submatrix f f = upperSignMatrix n := by
  ext i j
  simp only [Matrix.submatrix_apply,upperSignMatrix,hf.lt_iff_lt]

theorem recursivePf_upperSignMatrix (m : ℕ) :
    Paper.PfaffianMinor.recursivePf m (upperSignMatrix (2*m)) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Paper.PfaffianMinor.recursivePf]
    have hminor (k : Fin (2*m+1)) :
        (upperSignMatrix (2*(m+1))).submatrix
          (fun i => Fin.succ (k.succAbove i))
          (fun i => Fin.succ (k.succAbove i)) = upperSignMatrix (2*m) :=
      upperSignMatrix_submatrix _ (Fin.strictMono_succ.comp (Fin.strictMono_succAbove k))
    have hrow (k : Fin (2*m+1)) : upperSignMatrix (2*(m+1)) 0 (Fin.succ k) = 1 := by
      simp only [upperSignMatrix,ite_eq_left (Fin.succ_pos k)]
    simp_rw [hminor,ih,hrow,mul_one]
    rw [Fin.sum_neg_one_pow]
    have ho : Odd (2*m+1) := ⟨m,by omega⟩
    exact ite_eq_right (Nat.not_even_iff_odd.mpr ho)

/-- The ACTUAL frozen full normalized permutation Pfaffian has the ordered
sign-kernel value one, including the empty family. -/
theorem pfaffian_upperSignMatrix (m : ℕ) :
    Paper.pfaffian ((upperSignMatrix (2*m)).submatrix
      (Paper.PfaffianMinor.pairColumnEquiv m) (Paper.PfaffianMinor.pairColumnEquiv m)) = 1 :=
  (Paper.PfaffianBridge.pfaffian_coordinates_eq_recursivePf _
    (upperSignMatrix_skew _)).trans (recursivePf_upperSignMatrix m)

/-- The literal sign convention in the actual real Gaussian skew form. -/
def realSignMatrix {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (SignType.sign (x j-x i) : ℂ)

theorem realSignMatrix_eq_upper_of_strictMono {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) :
    realSignMatrix x = upperSignMatrix n := by
  ext i j
  by_cases hij : i < j
  · have hp : 0 < x j-x i := sub_pos.mpr (hx hij)
    simp [realSignMatrix,upperSignMatrix,hij,hp]
  · by_cases hji : j < i
    · have hn : x j-x i < 0 := sub_neg.mpr (hx hji)
      simp [realSignMatrix,upperSignMatrix,hij,hji,hn]
    · have he : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [realSignMatrix,upperSignMatrix,sign_apply]

theorem pfaffian_realSignMatrix_of_strictMono (m : ℕ) (x : Fin (2*m) → ℝ)
    (hx : StrictMono x) :
    Paper.pfaffian ((realSignMatrix x).submatrix
      (Paper.PfaffianMinor.pairColumnEquiv m) (Paper.PfaffianMinor.pairColumnEquiv m)) = 1 := by
  rw [realSignMatrix_eq_upper_of_strictMono x hx]
  exact pfaffian_upperSignMatrix m

end Paper.Spectral
