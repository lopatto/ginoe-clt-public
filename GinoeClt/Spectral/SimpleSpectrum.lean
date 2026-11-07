/-
Narrow real-field adaptations of GinibrePoincare.Analysis.MatrixSimpleSpectrum
and MatrixGaussianMeasure, from djalilchafai/ginibre-poincare,
revision fb58b4fd765f19a65c46cb82fb647fb0d94e28ca.
Original portions retain the following license:

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

New adaptations: Copyright (c) 2026 Patrick Lopatto; Apache-2.0.
-/
module

public import GinoeClt.Definitions
public import GinoeClt.Spectral.PolynomialNull
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable

/-! # Actual real Gaussian matrices have simple spectrum almost surely

This is a proved null-set fact for the original matrix law, not a hypothesis
on any matrix counted in the principal theorem. Pointwise multiplicity counts
and the frozen model are unchanged.
-/

@[expose] public section
noncomputable section
open MeasureTheory Matrix Polynomial ProbabilityTheory
open scoped BigOperators

namespace Paper.Spectral

def matrixCharacteristicResultant (N : ℕ) : MvPolynomial (Fin N × Fin N) ℝ :=
  let p := Matrix.charpoly.univ ℝ (Fin N)
  Polynomial.resultant p p.derivative N (N - 1)

theorem matrixCharacteristicResultant_eval (N : ℕ) (G : Matrix (Fin N) (Fin N) ℝ) :
    MvPolynomial.eval (fun ij => G ij.1 ij.2) (matrixCharacteristicResultant N) =
      Polynomial.resultant G.charpoly G.charpoly.derivative := by
  unfold matrixCharacteristicResultant
  rw [← Polynomial.resultant_map_map]
  have hc : (Matrix.charpoly.univ ℝ (Fin N)).map
      (MvPolynomial.eval (fun ij => G ij.1 ij.2)) = G.charpoly := by
    change (Matrix.charpoly.univ ℝ (Fin N)).map
      (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij => G ij.1 ij.2)) = G.charpoly
    exact Matrix.charpoly.univ_map_eval₂Hom (Fin N) (RingHom.id ℝ)
      (fun ij => G ij.1 ij.2)
  rw [← Polynomial.derivative_map, hc]
  simp only [Polynomial.natDegree_derivative, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

theorem matrixCharacteristicResultant_ne_zero (N : ℕ) :
    matrixCharacteristicResultant N ≠ 0 := by
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (fun i => (i.val : ℝ))
  have hsep : D.charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    apply Polynomial.separable_prod_X_sub_C_iff.mpr
    intro i j hij
    apply Fin.ext
    change (i.val : ℝ) = (j.val : ℝ) at hij
    exact_mod_cast hij
  have hres := Polynomial.resultant_ne_zero D.charpoly D.charpoly.derivative hsep
  intro hzero
  apply hres
  rw [← matrixCharacteristicResultant_eval N D, hzero, map_zero]

theorem matrixLaw_uncurry_map (n : ℕ) :
    Measure.map (Function.uncurry : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ))
        (matrixLaw n) =
      Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1) := by
  change Measure.map Function.uncurry
      (Measure.pi (fun _ : Fin (n + 1) =>
        Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))) = _
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem matrixLaw_uncurry_preserving (n : ℕ) :
    MeasurePreserving
      (Function.uncurry : SampleSpace n → (Fin (n + 1) × Fin (n + 1) → ℝ))
      (matrixLaw n) (Measure.pi (fun _ : Fin (n + 1) × Fin (n + 1) => gaussianReal 0 1)) :=
  ⟨by fun_prop, matrixLaw_uncurry_map n⟩

/-- Every nonzero real entry polynomial is almost surely nonzero under the
actual frozen iterated product of standard real Gaussian measures. -/
theorem matrixLaw_polynomial_ne_zero_ae (n : ℕ)
    (p : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℝ) (hp : p ≠ 0) :
    ∀ᵐ M ∂matrixLaw n, MvPolynomial.eval (fun ij => M ij.1 ij.2) p ≠ 0 := by
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  exact (matrixLaw_uncurry_preserving n).quasiMeasurePreserving.ae
    (realMvPolynomial_eval_ne_zero_ae (gaussianReal 0 1) p hp)

theorem matrixLaw_charpoly_separable_ae (n : ℕ) :
    ∀ᵐ M ∂matrixLaw n, M.charpoly.Separable := by
  filter_upwards [matrixLaw_polynomial_ne_zero_ae n
    (matrixCharacteristicResultant (n + 1)) (matrixCharacteristicResultant_ne_zero (n + 1))]
    with M hM
  rw [matrixCharacteristicResultant_eval] at hM
  by_contra hs
  apply hM
  exact Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl M.charpoly_monic.ne_zero, hs⟩

theorem matrixLaw_complexCharpoly_separable_ae (n : ℕ) :
    ∀ᵐ M ∂matrixLaw n, (M.charpoly.map Complex.ofRealHom).Separable := by
  filter_upwards [matrixLaw_charpoly_separable_ae n] with M hM
  exact hM.map


/-- The determinant of the generic real entry matrix. -/
def matrixDeterminantPolynomial (N : ℕ) : MvPolynomial (Fin N × Fin N) ℝ :=
  Matrix.det (fun i j : Fin N => MvPolynomial.X (i, j))

theorem matrixDeterminantPolynomial_eval (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ) :
    MvPolynomial.eval (fun ij => M ij.1 ij.2) (matrixDeterminantPolynomial N) = M.det := by
  unfold matrixDeterminantPolynomial
  have hmat :
      (MvPolynomial.eval (fun ij : Fin N × Fin N => M ij.1 ij.2)).mapMatrix
        (fun i j : Fin N => (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℝ)) = M := by
    ext i j
    change (MvPolynomial.eval (fun ij : Fin N × Fin N => M ij.1 ij.2))
      (MvPolynomial.X (i, j)) = M i j
    exact MvPolynomial.eval_X (i, j)
  exact (RingHom.map_det (MvPolynomial.eval (fun ij : Fin N × Fin N => M ij.1 ij.2))
    (fun i j : Fin N => (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℝ))).trans
      (congrArg Matrix.det hmat)

theorem matrixDeterminantPolynomial_ne_zero (N : ℕ) : matrixDeterminantPolynomial N ≠ 0 := by
  intro hz
  have hh := matrixDeterminantPolynomial_eval N (1 : Matrix (Fin N) (Fin N) ℝ)
  rw [hz, map_zero, Matrix.det_one] at hh
  exact zero_ne_one hh

theorem matrixLaw_det_ne_zero_ae (n : ℕ) :
    ∀ᵐ M ∂matrixLaw n, M.det ≠ 0 := by
  filter_upwards [matrixLaw_polynomial_ne_zero_ae n
    (matrixDeterminantPolynomial (n + 1)) (matrixDeterminantPolynomial_ne_zero (n + 1))]
    with M hM
  simpa only [matrixDeterminantPolynomial_eval] using hM

theorem matrixLaw_complexRoots_nodup_ae (n : ℕ) :
    ∀ᵐ M ∂matrixLaw n, (M.charpoly.map Complex.ofRealHom).roots.Nodup := by
  filter_upwards [matrixLaw_complexCharpoly_separable_ae n] with M hM
  exact Polynomial.nodup_roots hM

end Paper.Spectral
