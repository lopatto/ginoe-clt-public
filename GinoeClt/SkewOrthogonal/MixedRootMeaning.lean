/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.MixedDeterminantIntegrability
public import GinoeClt.Spectral.SchurVandermondePhase
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal
namespace Paper.SkewOrthogonal
open Paper.Spectral

theorem pairedRoots_list (l : ℕ) (z : Fin l → ℂ) :
    List.ofFn (fun i : Fin (2*l) ↦
      let p := (PfaffianMinor.pairColumnEquiv l).symm i
      if p.2 = 0 then z p.1 else conj (z p.1)) =
      (List.ofFn z).flatMap (fun a ↦ [a,conj a]) := by
  rw [List.ofFn_mul']
  have hp (i : Fin l) (j : Fin 2) :
      (PfaffianMinor.pairColumnEquiv l) (i,j) =
        (⟨2*i.val+j.val,by omega⟩ : Fin (2*l)) := by
    ext
    simp [PfaffianMinor.pairColumnEquiv,finProdFinEquiv,Nat.add_comm]
  simp_rw [← hp,Equiv.symm_apply_apply]
  simp [List.ofFn_succ,List.ofFn_zero,List.flatMap,List.map_ofFn,Function.comp_def]

/-- Literal LIST agreement with the actual canonical full roots. -/
theorem mixedRoots_list (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    List.ofFn (mixedRoots k l x z) =
      (List.ofFn x).map Complex.ofReal ++ (List.ofFn z).flatMap (fun a ↦ [a,conj a]) := by
  rw [mixedRoots,List.ofFn_fin_append,pairedRoots_list]
  rw [List.ofFn_comp' x Complex.ofReal]

/-- The actual canonical determinant, preserving root order and all multiplicities. -/
theorem mixedRoots_vandermonde (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    (Matrix.vandermonde (mixedRoots k l x z)).det =
      (Matrix.vandermonde (schurFullRootsFromHeads (schurCanonicalWord k l)
        (schurCanonicalHeads k l x z))).det := by
  rw [← listVandermondeDet_ofFn,mixedRoots_list,← fullRoots_canonical_list,
    listVandermondeDet_ofFn]

/-- Any degree-ordered monic polynomial family gives the same determinant. -/
theorem mixedPolynomial_det_eq (k l : ℕ) (P : Fin (k+2*l) → Polynomial ℂ)
    (hdeg : ∀ i, (P i).natDegree = i.val) (hmonic : ∀ i, (P i).Monic)
    (x : Fin k → ℝ) (z : Fin l → ℂ) :
    (Matrix.of (fun i j ↦ (P i).eval (mixedRoots k l x z j))).det =
      (Matrix.vandermonde (mixedRoots k l x z)).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (mixedRoots k l x z) P hdeg hmonic
  exact (Matrix.det_transpose (Matrix.of (fun i j ↦ (P j).eval (mixedRoots k l x z i)))).trans h.symm

/-- The actual mixed Vandermonde has genuine L1 with the count weights. -/
theorem integrable_mixedVandermonde (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (k l : ℕ) :
    Integrable (fun xz : (Fin k → ℝ) × (Fin l → ℂ) ↦
      mixedDeterminantWeight B t k l xz.1 xz.2 *
        (Matrix.vandermonde (mixedRoots k l xz.1 xz.2)).det)
      ((Measure.pi (fun _ : Fin k ↦ (volume : Measure ℝ))).prod
        (Measure.pi (fun _ : Fin l ↦ volume.restrict {z : ℂ | 0 < z.im}))) := by
  have h := integrable_mixedDeterminant B hB t k l
    (fun i : Fin (k+2*l) ↦ (Polynomial.X : Polynomial ℂ)^i.val)
  apply h.congr
  filter_upwards [] with xz
  rw [mixedPolynomial_det_eq k l _
    (fun i ↦ Polynomial.natDegree_X_pow i.val)
    (fun i ↦ Polynomial.monic_X_pow i.val)]

/-- The polynomial determinant has the exact already-reviewed complex phase. -/
theorem mixedPolynomial_phase (k l : ℕ) (P : Fin (k+2*l) → Polynomial ℂ)
    (hdeg : ∀ i, (P i).natDegree = i.val) (hmonic : ∀ i, (P i).Monic)
    (x : Fin k → ℝ) (z : Fin l → ℂ)
    (hx : Monotone x) (hz : ∀ i, 0 < (z i).im) :
    Complex.I^l * (Matrix.of (fun i j ↦ (P i).eval (mixedRoots k l x z j))).det =
      (schurHeadVandermondeNorm (schurCanonicalWord k l) (schurCanonicalHeads k l x z) : ℂ) := by
  rw [mixedPolynomial_det_eq k l P hdeg hmonic,mixedRoots_vandermonde]
  exact canonical_vandermonde_phase k l x z hx hz

end Paper.SkewOrthogonal
