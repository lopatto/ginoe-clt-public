/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.OddFirstSingleDeterminant
public import GinoeClt.SkewOrthogonal.DeBruijnCanonicalRoots
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal Classical
namespace Paper.SkewOrthogonal

/-- The full odd root list retains the unpaired real root first and every pair. -/
theorem oddFirst_canonicalRoots_list (r l : ℕ) (x : ℝ)
    (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    List.ofFn (oddFirstRootVector (r+l) x
      (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j)))) =
      ((x : ℂ) :: (List.ofFn (realPairFlatten r xy)).map Complex.ofReal) ++
        (List.ofFn z).flatMap (fun a ↦ [a,conj a]) := by
  simp only [oddFirstRootVector,List.ofFn_cons,deBruijn_canonicalRoots_list,List.cons_append]

theorem oddFirst_canonicalRoots_vandermonde (r l : ℕ) (x : ℝ)
    (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    (Matrix.vandermonde (oddFirstRootVector (r+l) x
      (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j))))).det =
      (Matrix.vandermonde (mixedRoots (2*r+1) l
        (Fin.cons x (realPairFlatten r xy)) z)).det := by
  rw [← Paper.Spectral.listVandermondeDet_ofFn,oddFirst_canonicalRoots_list,
    ← Paper.Spectral.listVandermondeDet_ofFn,mixedRoots_list,List.ofFn_cons,List.map_cons]

theorem mixedDeterminantWeight_cons (B : Set ℂ) (t : ℝ≥0)
    (k l : ℕ) (x : ℝ) (u : Fin k → ℝ) (z : Fin l → ℂ) :
    mixedDeterminantWeight B t (k+1) l (Fin.cons x u) z =
      (Real.exp (-x^2/2) : ℂ)*mixedDeterminantWeight B t k l u z := by
  simp only [mixedDeterminantWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

theorem realPairSign_cons (r : ℕ) (x : ℝ) (u : Fin (2*r) → ℝ) :
    Paper.Spectral.realPairSign
      (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,0)).succ)
      (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,1)).succ) (Fin.cons x u) =
    Paper.Spectral.realPairSign
      (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
      (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) u := by
  simp only [Paper.Spectral.realPairSign,Fin.cons_succ]

/-- The actual canonical odd determinant, with the original unmodified family,
has precisely the same half-real/2i-complex factors as its even counterpart. -/
theorem deBruijn_odd_canonicalSourceDet_eq (B : Set ℂ) (t : ℝ≥0) (r l : ℕ) (x : ℝ)
    (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    (pairedFeatureMatrix (fun i : Fin (r+l+1) ↦
      deBruijnBorderFeature B t (rawOddPolynomial (r+l)) (Fin.last (r+l),1)
        (Fin.cons (α := fun _ ↦ (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x)
          (fun j ↦ Sum.inl
            (Fin.append (fun a ↦ Sum.inl (xy a)) (fun a ↦ Sum.inr (z a)) j)) i))).det =
      (1/2 : ℂ)^r*(2*Complex.I)^l *
        Paper.Spectral.realPairSign
          (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,0)).succ)
          (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,1)).succ)
            (Fin.cons x (realPairFlatten r xy)) *
        weightedMixedVandermonde B t (2*r+1) l z (Fin.cons x (realPairFlatten r xy)) := by
  rw [det_first_single_border_vandermonde,deBruijnPairScalar_canonical_eq_weight,
    oddFirst_canonicalRoots_vandermonde,weightedMixedVandermonde,
    mixedDeterminantWeight_cons,realPairSign_cons]
  ring

end Paper.SkewOrthogonal
