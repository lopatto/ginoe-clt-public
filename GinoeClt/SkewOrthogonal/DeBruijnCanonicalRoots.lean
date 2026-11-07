/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnSourceDeterminant
public import GinoeClt.SkewOrthogonal.MixedRootMeaning
@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal
open Paper.Spectral

/-- ANY interlaced family is its original LIST of consecutive two-element blocks.
No injectivity, positivity, or cardinality-of-support replacement enters. -/
theorem interlacedRoot_list {α : Type*} (m : ℕ) (w : Fin m → Fin 2 → α) :
    List.ofFn (fun j : Fin (2*m) =>
      let p := (PfaffianMinor.pairColumnEquiv m).symm j
      w p.1 p.2) = (List.ofFn (fun i : Fin m => [w i 0,w i 1])).flatten := by
  rw [List.ofFn_mul']
  have hp (i : Fin m) (j : Fin 2) :
      PfaffianMinor.pairColumnEquiv m (i,j) =
        (⟨2*i.val+j.val,by omega⟩ : Fin (2*m)) := by
    apply Fin.ext
    exact pairColumnEquiv_val m (i,j)
  simp_rw [← hp,Equiv.symm_apply_apply]
  simp [List.ofFn_succ,List.ofFn_zero]

/-- The EXACT real-root order induced by the proved ordinary-volume equivalence. -/
theorem realPairFlatten_list (r : ℕ) (xy : Fin r → ℝ × ℝ) :
    List.ofFn (realPairFlatten r xy) = (List.ofFn xy).flatMap (fun p => [p.1,p.2]) := by
  have h := interlacedRoot_list r (fun j a => if a = 0 then (xy j).1 else (xy j).2)
  have he : (fun i : Fin (2*r) =>
      let p := (PfaffianMinor.pairColumnEquiv r).symm i
      if p.2 = 0 then (xy p.1).1 else (xy p.1).2) = realPairFlatten r xy := by
    funext i
    obtain ⟨⟨j,a⟩,rfl⟩ := (PfaffianMinor.pairColumnEquiv r).surjective i
    simp only [Equiv.symm_apply_apply]
    fin_cases a
    · exact (realPairFlatten_apply_zero r xy j).symm
    · exact (realPairFlatten_apply_one r xy j).symm
  rw [he] at h
  simpa [List.flatMap,List.map_ofFn,Function.comp_def] using h

/-- The original source pair order, with real pairs FIRST and upper pairs LAST,
is exactly the existing mixed-root LIST after real flattening. ALL collisions
and r/l=0 are included; this is equality of lists rather than finite supports. -/
theorem deBruijn_canonicalRoots_list (r l : ℕ) (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    List.ofFn (fun j : Fin (2*(r+l)) =>
      let p := (PfaffianMinor.pairColumnEquiv (r+l)).symm j
      deBruijnPairRoot
        (Fin.append (fun i => Sum.inl (xy i)) (fun i => Sum.inr (z i)) p.1) p.2) =
      (List.ofFn (realPairFlatten r xy)).map Complex.ofReal ++
        (List.ofFn z).flatMap (fun a => [a,conj a]) := by
  have h := interlacedRoot_list (r+l) (fun j a => deBruijnPairRoot
    (Fin.append (fun i => Sum.inl (xy i)) (fun i => Sum.inr (z i)) j) a)
  have hb : (fun j : Fin (r+l) =>
      [deBruijnPairRoot (Fin.append (fun i => Sum.inl (xy i)) (fun i => Sum.inr (z i)) j) 0,
       deBruijnPairRoot (Fin.append (fun i => Sum.inl (xy i)) (fun i => Sum.inr (z i)) j) 1]) =
      Fin.append (fun i : Fin r => [((xy i).1 : ℂ),((xy i).2 : ℂ)])
        (fun i : Fin l => [z i,conj (z i)]) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [Fin.append_left,deBruijnPairRoot]
    · simp [Fin.append_right,deBruijnPairRoot]
  have hr : (List.ofFn (fun i : Fin r => [((xy i).1 : ℂ),((xy i).2 : ℂ)])).flatten =
      (List.ofFn (realPairFlatten r xy)).map Complex.ofReal := by
    rw [realPairFlatten_list]
    simp [List.flatMap,List.map_ofFn,Function.comp_def]
  have hc : (List.ofFn (fun i : Fin l => [z i,conj (z i)])).flatten =
      (List.ofFn z).flatMap (fun a => [a,conj a]) := by
    simp [List.flatMap,List.map_ofFn,Function.comp_def]
  rw [hb,List.ofFn_fin_append,List.flatten_append,hr,hc] at h
  exact h

/-- The ACTUAL source determinant root family and the existing mixed roots have
identical Vandermonde determinants. The LIST bridge avoids a dimension-cast registry. -/
theorem deBruijn_canonicalRoots_vandermonde (r l : ℕ) (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    (Matrix.vandermonde (fun j : Fin (2*(r+l)) =>
      let p := (PfaffianMinor.pairColumnEquiv (r+l)).symm j
      deBruijnPairRoot
        (Fin.append (fun i => Sum.inl (xy i)) (fun i => Sum.inr (z i)) p.1) p.2)).det =
      (Matrix.vandermonde (mixedRoots (2*r) l (realPairFlatten r xy) z)).det := by
  rw [← listVandermondeDet_ofFn,deBruijn_canonicalRoots_list,
    ← mixedRoots_list (2*r) l (realPairFlatten r xy) z,listVandermondeDet_ofFn]

/-- The ACTUAL canonical source determinant is the existing weighted mixed
Vandermonde times the precise half-real/2i-complex factors and real signs. -/
theorem deBruijn_canonicalSourceDet_eq (B : Set ℂ) (t : ℝ≥0) (r l : ℕ)
    (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
    (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t (pairedPolynomial (r+l))
      (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j)) i))).det =
      (1/2 : ℂ)^r*(2*Complex.I)^l *
        Paper.Spectral.realPairSign (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
          (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) (realPairFlatten r xy) *
            weightedMixedVandermonde B t (2*r) l z (realPairFlatten r xy) := by
  rw [deBruijn_sourceDet_eq,deBruijnPairScalar_canonical_eq_weight,
    deBruijn_canonicalRoots_vandermonde,weightedMixedVandermonde]
  ring

end Paper.SkewOrthogonal
