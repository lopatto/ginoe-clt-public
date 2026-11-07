/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFreeCoordinateSplit
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Paper.Spectral

/-- Literal ordinary between-block cells, with coefficient ONE in the squared
Frobenius norm and no normalization or coordinate rescaling. -/
def schurUpperGaussian {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ :=
  Real.exp (-(∑ i, u i ^ 2) / 2)

theorem schurUpperGaussian_eq_prod {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    schurUpperGaussian u = ∏ i, Real.exp (-u i ^ 2 / 2) := by
  unfold schurUpperGaussian
  rw [← Real.exp_sum,← Finset.sum_div,Finset.sum_neg_distrib]

theorem integrable_schurUpperGaussian {ι : Type*} [Fintype ι] :
    Integrable (schurUpperGaussian (ι := ι)) := by
  have h : Integrable (fun x : ℝ => Real.exp (-x^2/2)) := by
    have he : (fun x : ℝ => Real.exp (-x^2/2)) =
        (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) := by
      funext x
      congr 1
      ring
    rw [he]
    exact integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  change Integrable (fun u : ι → ℝ => schurUpperGaussian u)
  simpa only [schurUpperGaussian_eq_prod] using!
    (Integrable.fintype_prod (fun _ : ι => h))

theorem integral_schurUpperGaussian {ι : Type*} [Fintype ι] :
    (∫ u : ι → ℝ, schurUpperGaussian u) =
      (Real.sqrt (2*Real.pi)) ^ Fintype.card ι := by
  simp_rw [schurUpperGaussian_eq_prod]
  have hp := integral_fintype_prod_volume_eq_pow (ι := ι)
    (fun x : ℝ => Real.exp (-x^2/2))
  rw [hp]
  have he : (fun x : ℝ => Real.exp (-x^2/2)) =
      (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) := by
    funext x
    congr 1
    ring
  rw [he,integral_gaussian,show Real.pi / (1/2) = 2*Real.pi by ring]

/-- Nonnegative mass, retaining dimension zero, with genuine L1 before conversion. -/
theorem lintegral_schurUpperGaussian (d n : ℕ) :
    (∫⁻ u : Fin n × Fin d → ℝ, ENNReal.ofReal (schurUpperGaussian u)) =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^ (n*d)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_schurUpperGaussian
    (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le),
    integral_schurUpperGaussian]
  simp only [Fintype.card_prod,Fintype.card_fin]

/-- The first actual upper-cell Gaussian factor, with any remaining nonnegative
weight a, including zero/infinity; no mass cancellation or finiteness premise. -/
theorem lintegral_schurUpperGaussian_mul (d n : ℕ) (a : ℝ≥0∞) :
    (∫⁻ u : Fin n × Fin d → ℝ, ENNReal.ofReal (schurUpperGaussian u) * a) =
      ENNReal.ofReal ((Real.sqrt (2*Real.pi)) ^ (n*d)) * a := by
  have h : Measurable (fun u : Fin n × Fin d → ℝ =>
      ENNReal.ofReal (schurUpperGaussian u)) := by
    unfold schurUpperGaussian
    fun_prop
  rw [lintegral_mul_const a h,lintegral_schurUpperGaussian]

/-- Actual Frobenius square in physical block coordinates; each between-block
upper cell has coefficient one, lower cells vanish. Valid in dimension zero. -/
theorem sum_sq_upperBlockMatrix {d n : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i : Fin (d+n), ∑ j : Fin (d+n), upperBlockMatrix B U D i j ^ 2) =
      (∑ i : Fin d, ∑ j : Fin d, B i j ^ 2) +
      (∑ i : Fin d, ∑ j : Fin n, U i j ^ 2) +
      (∑ i : Fin n, ∑ j : Fin n, D i j ^ 2) := by
  simp only [Fin.sum_univ_add,upperBlockMatrix_left_left,upperBlockMatrix_left_right,
    upperBlockMatrix_right_left,upperBlockMatrix_right_right,Finset.sum_add_distrib]
  norm_num only [Finset.sum_const_zero]
  ring

theorem sum_sq_scalarBlock (a : ℝ) :
    (∑ i : Fin 1, ∑ j : Fin 1, scalarBlock a i j ^ 2) = a^2 := by
  simp [scalarBlock]

theorem sum_sq_schurBlock (a b c : ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, schurBlock a b c i j ^ 2) = 2*a^2+b^2+c^2 := by
  simp [Fin.sum_univ_two,schurBlock]
  ring

/-- Literal column-major vectorization preserves the entrywise squared sum. -/
theorem sum_sq_matrix_vec {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℝ) :
    (∑ ij : Fin n × Fin d, Matrix.vec M ij ^ 2) =
      ∑ i : Fin d, ∑ j : Fin n, M i j ^ 2 := by
  simp only [Fintype.sum_prod_type,Matrix.vec]
  exact Finset.sum_comm

/-- Actual Gaussian factorization before integrating the upper cells. -/
theorem schurUpperGaussian_vec_upperBlockMatrix {d n : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (U : Matrix (Fin d) (Fin n) ℝ)
    (D : Matrix (Fin n) (Fin n) ℝ) :
    schurUpperGaussian (Matrix.vec (upperBlockMatrix B U D)) =
      schurUpperGaussian (Matrix.vec B) * schurUpperGaussian (Matrix.vec U) *
        schurUpperGaussian (Matrix.vec D) := by
  unfold schurUpperGaussian
  simp_rw [sum_sq_matrix_vec]
  rw [sum_sq_upperBlockMatrix,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

theorem schurUpperGaussian_vec_scalarBlock (a : ℝ) :
    schurUpperGaussian (Matrix.vec (scalarBlock a)) = Real.exp (-a^2/2) := by
  unfold schurUpperGaussian
  rw [sum_sq_matrix_vec,sum_sq_scalarBlock]

theorem schurUpperGaussian_vec_schurBlock (a b c : ℝ) :
    schurUpperGaussian (Matrix.vec (schurBlock a b c)) =
      Real.exp (-(2*a^2+b^2+c^2)/2) := by
  unfold schurUpperGaussian
  rw [sum_sq_matrix_vec,sum_sq_schurBlock]

end Paper.Spectral
