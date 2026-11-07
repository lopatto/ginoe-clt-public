/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnPairMeasure
public import GinoeClt.SkewOrthogonal.PairDeterminantSymmetry
public import GinoeClt.SkewOrthogonal.PairedPolynomialDegree
public import GinoeClt.SkewOrthogonal.RealPairFlatten
public import GinoeClt.SkewOrthogonal.MixedRealAlternation
@[expose] public section
noncomputable section
open Classical
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal

/-- The two literal roots represented by an actual real or complex pair. -/
def deBruijnPairRoot : ((ℝ × ℝ) ⊕ ℂ) → Fin 2 → ℂ
  | Sum.inl xy, a => if a = 0 then (xy.1 : ℂ) else (xy.2 : ℂ)
  | Sum.inr z, a => if a = 0 then z else conj z

/-- Exact scalar on each of the two original feature columns. -/
def deBruijnPairScalar (B : Set ℂ) (t : ℝ≥0) : ((ℝ × ℝ) ⊕ ℂ) → Fin 2 → ℂ
  | Sum.inl xy, a => if a = 0 then (1/2 : ℂ)*(SignType.sign (xy.2-xy.1) : ℂ) *
      (Real.exp (-xy.1^2/2) : ℂ) else (Real.exp (-xy.2^2/2) : ℂ)
  | Sum.inr z, a => if a = 0 then (2*Complex.I)*(complexWeight z : ℂ) *
      (if z ∈ B then 1+(t : ℂ) else 1) else 1

/-- Factor the ACTUAL feature, keeping the polynomial coefficients unconjugated. -/
theorem deBruijnPairFeature_factorization {κ : Type*} (B : Set ℂ) (t : ℝ≥0)
    (P : κ → Polynomial ℂ) (s : (ℝ × ℝ) ⊕ ℂ) (p : κ) (a : Fin 2) :
    deBruijnPairFeature B t P s p a =
      deBruijnPairScalar B t s a * (P p).eval (deBruijnPairRoot s a) := by
  cases s with
  | inl xy =>
    fin_cases a <;>
      simp [deBruijnPairFeature,realPairFeature,realGaussianPolynomial,
        deBruijnPairScalar,deBruijnPairRoot,mul_assoc]
  | inr z =>
    fin_cases a <;>
      simp [deBruijnPairFeature,complexPairFeature,deBruijnPairScalar,deBruijnPairRoot]

/-- The ACTUAL source determinant is the full polynomial Vandermonde times
the exact column scalars. No distinctness, positivity or cancellation is needed. -/
theorem deBruijn_sourceDet_eq (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (y : Fin m → ((ℝ × ℝ) ⊕ ℂ)) :
    (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t (pairedPolynomial m) (y i))).det =
      (∏ i, deBruijnPairScalar B t (y i) 0 * deBruijnPairScalar B t (y i) 1) *
        (Matrix.vandermonde (fun j : Fin (2*m) ↦
          let p := (PfaffianMinor.pairColumnEquiv m).symm j
          deBruijnPairRoot (y p.1) p.2)).det := by
  have he : (fun i p a ↦ deBruijnPairFeature B t (pairedPolynomial m) (y i) p a) =
      (fun i p a ↦ if a = 0 then deBruijnPairScalar B t (y i) 0 *
          (pairedPolynomial m p).eval (deBruijnPairRoot (y i) 0)
        else deBruijnPairScalar B t (y i) 1 *
          (pairedPolynomial m p).eval (deBruijnPairRoot (y i) 1)) := by
    funext i p a
    fin_cases a <;> simp [deBruijnPairFeature_factorization]
  rw [he]
  have hs := pairedFeatureMatrix_det_scale_pairs
    (fun i p a ↦ (pairedPolynomial m p).eval (deBruijnPairRoot (y i) a))
    (fun i ↦ deBruijnPairScalar B t (y i) 0) (fun i ↦ deBruijnPairScalar B t (y i) 1)
  exact hs.trans (congrArg (fun c : ℂ ↦
    (∏ i, deBruijnPairScalar B t (y i) 0 * deBruijnPairScalar B t (y i) 1)*c)
    (det_pairedPolynomial_eval m (fun p ↦ deBruijnPairRoot (y p.1) p.2)))

/-- Exact scalar product after the REAL pairs and then COMPLEX pairs are concatenated. -/
theorem deBruijnPairScalar_canonical_prod (B : Set ℂ) (t : ℝ≥0) (r l : ℕ)
    (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    (∏ i : Fin (r+l), deBruijnPairScalar B t
      (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j)) i) 0 *
        deBruijnPairScalar B t
          (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j)) i) 1) =
      (1/2 : ℂ)^r * (2*Complex.I)^l *
        (∏ j : Fin r, (SignType.sign ((xy j).2-(xy j).1) : ℂ)) *
        ((∏ j : Fin r, (Real.exp (-(xy j).1^2/2) : ℂ) *
          (Real.exp (-(xy j).2^2/2) : ℂ)) *
            ∏ j : Fin l, (complexWeight (z j) : ℂ) *
              (if z j ∈ B then 1+(t : ℂ) else 1)) := by
  simp only [Fin.prod_univ_add,Fin.append_left,Fin.append_right,deBruijnPairScalar,
    Fin.isValue,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  ring

theorem prod_gaussian_realPairFlatten (r : ℕ) (xy : Fin r → ℝ × ℝ) :
    (∏ i : Fin (2*r), (Real.exp (-(realPairFlatten r xy i)^2/2) : ℂ)) =
      ∏ j : Fin r, (Real.exp (-(xy j).1^2/2) : ℂ) * (Real.exp (-(xy j).2^2/2) : ℂ) := by
  rw [← Equiv.prod_comp (PfaffianMinor.pairColumnEquiv r)
    (fun i ↦ (Real.exp (-(realPairFlatten r xy i)^2/2) : ℂ))]
  rw [Fintype.prod_prod_type]
  simp [Fin.prod_univ_two,realPairFlatten_apply_zero,realPairFlatten_apply_one]

theorem realPairSign_realPairFlatten (r : ℕ) (xy : Fin r → ℝ × ℝ) :
    Paper.Spectral.realPairSign (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
      (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) (realPairFlatten r xy) =
        ∏ j : Fin r, (SignType.sign ((xy j).2-(xy j).1) : ℂ) := by
  simp only [Paper.Spectral.realPairSign,realPairFlatten_apply_zero,realPairFlatten_apply_one]

/-- Canonical source scalars are exactly the sign kernel times the existing
mixed Gaussian/count weight, with the physical half-real/2i-complex factors. -/
theorem deBruijnPairScalar_canonical_eq_weight (B : Set ℂ) (t : ℝ≥0) (r l : ℕ)
    (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    (∏ i : Fin (r+l), deBruijnPairScalar B t
      (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j)) i) 0 *
        deBruijnPairScalar B t
          (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j)) i) 1) =
      (1/2 : ℂ)^r * (2*Complex.I)^l *
        Paper.Spectral.realPairSign (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
          (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) (realPairFlatten r xy) *
            mixedDeterminantWeight B t (2*r) l (realPairFlatten r xy) z := by
  rw [deBruijnPairScalar_canonical_prod,realPairSign_realPairFlatten,mixedDeterminantWeight,
    prod_gaussian_realPairFlatten]

end Paper.SkewOrthogonal
