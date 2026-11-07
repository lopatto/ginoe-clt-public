/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.MixedRootMeaning
public import GinoeClt.Spectral.RealAlternatingIntegration
@[expose] public section
noncomputable section
open MeasureTheory Equiv
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal

/-- Extend a real-coordinate permutation by the identity on the complex-pair roots. -/
def realBlockPerm (k l : ℕ) (σ : Perm (Fin k)) : Perm (Fin (k+2*l)) :=
  (finSumFinEquiv : Fin k ⊕ Fin (2*l) ≃ Fin (k+2*l)).permCongr (σ.sumCongr 1)

theorem mixedRoots_realPerm (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ)
    (σ : Perm (Fin k)) :
    mixedRoots k l (x ∘ σ) z = mixedRoots k l x z ∘ realBlockPerm k l σ := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [mixedRoots,realBlockPerm,Equiv.permCongr_apply]

theorem mixedDeterminantWeight_realPerm (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (x : Fin k → ℝ) (z : Fin l → ℂ) (σ : Perm (Fin k)) :
    mixedDeterminantWeight B t k l (x ∘ σ) z = mixedDeterminantWeight B t k l x z := by
  unfold mixedDeterminantWeight
  congr 1
  exact Equiv.prod_comp σ (fun i ↦ (Real.exp (-(x i)^2/2) : ℂ))

theorem mixedVandermonde_realPerm (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ)
    (σ : Perm (Fin k)) :
    (Matrix.vandermonde (mixedRoots k l (x ∘ σ) z)).det =
      permutationSign σ * (Matrix.vandermonde (mixedRoots k l x z)).det := by
  rw [mixedRoots_realPerm]
  change ((Matrix.vandermonde (mixedRoots k l x z)).submatrix (realBlockPerm k l σ) id).det = _
  rw [Matrix.det_permute]
  simp [permutationSign,realBlockPerm,Perm.sign_permCongr,Perm.sign_sumCongr]

/-- The literal Gaussian/count-weighted full determinant, as a function of real roots. -/
def weightedMixedVandermonde (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (z : Fin l → ℂ) (x : Fin k → ℝ) : ℂ :=
  mixedDeterminantWeight B t k l x z * (Matrix.vandermonde (mixedRoots k l x z)).det

theorem weightedMixedVandermonde_alternating (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (z : Fin l → ℂ) (σ : Perm (Fin k)) (x : Fin k → ℝ) :
    weightedMixedVandermonde B t k l z (x ∘ σ) =
      permutationSign σ * weightedMixedVandermonde B t k l z x := by
  rw [weightedMixedVandermonde,mixedDeterminantWeight_realPerm,mixedVandermonde_realPerm,
    weightedMixedVandermonde]
  ring

theorem weightedMixedVandermonde_eq_zero (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (z : Fin l → ℂ) (x : Fin k → ℝ) (hx : ¬ Function.Injective x) :
    weightedMixedVandermonde B t k l z x = 0 := by
  have hd : (Matrix.vandermonde (mixedRoots k l x z)).det = 0 := by
    by_contra hn
    have hi := Matrix.det_vandermonde_ne_zero_iff.mp hn
    apply hx
    intro i j hij
    have he : mixedRoots k l x z (Fin.castAdd (2*l) i) =
        mixedRoots k l x z (Fin.castAdd (2*l) j) := by
      simp only [mixedRoots,Fin.append_left,hij]
    exact Fin.ext (congrArg (fun a : Fin (k+2*l) ↦ a.val) (hi he))
  rw [weightedMixedVandermonde,hd,mul_zero]

/-- Fixed complex roots are finite constants, so real-variable L1 holds at EVERY z. -/
theorem integrable_mixedDeterminant_fixed_complex (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (P : Fin (k+2*l) → Polynomial ℂ) (z : Fin l → ℂ) :
    Integrable (fun x : Fin k → ℝ ↦ mixedDeterminantWeight B t k l x z *
      (Matrix.of (fun i j ↦ (P i).eval (mixedRoots k l x z j))).det)
      (Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))) := by
  simp_rw [Matrix.det_apply',Finset.mul_sum]
  apply integrable_finsetSum
  intro σ hσ
  have hr := Integrable.fintype_prod (fun i : Fin k ↦ integrable_realGaussianPolynomial
    (P (σ (Fin.castAdd (2*l) i))))
  have h := hr.mul_const (∏ j : Fin l,
    complexCountPolynomial B t
      (P (σ (Fin.natAdd k (PfaffianMinor.pairColumnEquiv l (j,0)))))
      (P (σ (Fin.natAdd k (PfaffianMinor.pairColumnEquiv l (j,1))))) (z j))
  apply (h.const_mul ((Perm.sign σ : ℤ) : ℂ)).congr
  filter_upwards [] with x
  simp only [Matrix.of_apply]
  have he := mixedWeight_mul_permTerm B t k l P σ x z
  dsimp only [mixedPolynomialProduct] at he
  rw [← he]
  ring

theorem integrable_weightedMixedVandermonde (B : Set ℂ) (t : ℝ≥0) (k l : ℕ)
    (z : Fin l → ℂ) :
    Integrable (weightedMixedVandermonde B t k l z)
      (Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))) := by
  have h := integrable_mixedDeterminant_fixed_complex B t k l
    (fun i : Fin (k+2*l) ↦ (Polynomial.X : Polynomial ℂ)^i.val) z
  apply h.congr
  filter_upwards [] with x
  rw [mixedPolynomial_det_eq k l _
    (fun i ↦ Polynomial.natDegree_X_pow i.val)
    (fun i ↦ Polynomial.monic_X_pow i.val)]
  rfl

/-- Actual EVEN real-variable averaging, with all analytic premises proved. -/
theorem integral_weightedMixedVandermonde_even (B : Set ℂ) (t : ℝ≥0) (r l : ℕ)
    (z : Fin l → ℂ) :
    (∫ x : Fin (2*r) → ℝ, weightedMixedVandermonde B t (2*r) l z x *
      Paper.Spectral.realPairSign (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
        (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) x) =
      ((2 : ℂ)^r*(r.factorial : ℂ)) *
        ∫ x in {x : Fin (2*r) → ℝ | Monotone x},
          weightedMixedVandermonde B t (2*r) l z x := by
  exact Paper.Spectral.integral_even_realPairSign volume r _
    (integrable_weightedMixedVandermonde B t (2*r) l z)
    (weightedMixedVandermonde_alternating B t (2*r) l z)
    (weightedMixedVandermonde_eq_zero B t (2*r) l z)

/-- Actual ODD averaging, with the FIRST real coordinate unpaired. -/
theorem integral_weightedMixedVandermonde_odd (B : Set ℂ) (t : ℝ≥0) (r l : ℕ)
    (z : Fin l → ℂ) :
    (∫ x : Fin (2*r+1) → ℝ, weightedMixedVandermonde B t (2*r+1) l z x *
      Paper.Spectral.realPairSign (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,0)).succ)
        (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,1)).succ) x) =
      ((2 : ℂ)^r*(r.factorial : ℂ)) *
        ∫ x in {x : Fin (2*r+1) → ℝ | Monotone x},
          weightedMixedVandermonde B t (2*r+1) l z x := by
  exact Paper.Spectral.integral_odd_realPairSign volume r _
    (integrable_weightedMixedVandermonde B t (2*r+1) l z)
    (weightedMixedVandermonde_alternating B t (2*r+1) l z)
    (weightedMixedVandermonde_eq_zero B t (2*r+1) l z)

end Paper.SkewOrthogonal
