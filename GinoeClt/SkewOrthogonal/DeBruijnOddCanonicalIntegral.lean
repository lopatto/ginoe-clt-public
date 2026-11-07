/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.OddCanonicalRoots
public import GinoeClt.SkewOrthogonal.OddRealPairFlatten
public import GinoeClt.SkewOrthogonal.MixedCountBochner
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal Classical
namespace Paper.SkewOrthogonal
open Paper.Spectral

/-- The full canonical odd sector integrates to r! 2^l times its genuine spectral
mass. Joint L1 precedes every Fubini step, including the first real singleton. -/
theorem deBruijn_odd_canonical_integral (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (r l : ℕ) :
    (∫ x : ℝ, ∫ xy : Fin r → ℝ × ℝ, ∫ z : Fin l → ℂ,
      (pairedFeatureMatrix (fun i : Fin (r+l+1) ↦
        deBruijnBorderFeature B t (rawOddPolynomial (r+l)) (Fin.last (r+l),1)
          (Fin.cons (α := fun _ ↦ (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x)
            (fun j ↦ Sum.inl
              (Fin.append (fun a ↦ Sum.inl (xy a)) (fun a ↦ Sum.inr (z a)) j)) i))).det
        ∂Measure.pi (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})) =
      (r.factorial : ℂ)*(2 : ℂ)^l *
        Complex.ofReal (mixedCountIntegral B t (2*r+1) l).toReal := by
  let ν : Measure (Fin l → ℂ) := Measure.pi
    (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})
  let H : (Fin (2*r+1) → ℝ) × (Fin l → ℂ) → ℂ := fun p ↦
    weightedMixedVandermonde B t (2*r+1) l p.2 p.1 *
      realPairSign (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,0)).succ)
        (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,1)).succ) p.1
  let c : ℂ := (1/2 : ℂ)^r*(2*Complex.I)^l
  let J : ℂ := ∫ u in {u : Fin (2*r+1) → ℝ | Monotone u},
    (∫ z, weightedMixedVandermonde B t (2*r+1) l z u ∂ν)
  have hD := integrable_mixedVandermonde B hB t (2*r+1) l
  have hG : Measurable (fun p : (Fin (2*r+1) → ℝ) × (Fin l → ℂ) ↦
      realPairSign (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,0)).succ)
        (fun a ↦ (PfaffianMinor.pairColumnEquiv r (a,1)).succ) p.1) :=
    (measurable_realPairSign _ _).comp measurable_fst
  have hH : Integrable H ((volume : Measure (Fin (2*r+1) → ℝ)).prod ν) := by
    simpa only [volume_pi] using! hD.mul_bdd hG.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p ↦ norm_realPairSign_le_one _ _ p.1)
  have hPull : Integrable
      (fun p : (ℝ × (Fin r → ℝ × ℝ)) × (Fin l → ℂ) ↦
        H (Fin.cons p.1.1 (realPairFlatten r p.1.2),p.2))
      ((volume : Measure (ℝ × (Fin r → ℝ × ℝ))).prod ν) := by
    simpa only [← oddRealPairFlatten_apply] using!
      (measurePreserving_oddRealPairFlatten_prod ν r).integrable_comp_of_integrable hH
  have hFlat :
      (∫ x : ℝ, ∫ xy : Fin r → ℝ × ℝ, ∫ z, H (Fin.cons x (realPairFlatten r xy),z) ∂ν) =
        ∫ u : Fin (2*r+1) → ℝ, ∫ z, H (u,z) ∂ν := by
    calc
      _ = ∫ p : ℝ × (Fin r → ℝ × ℝ), ∫ z,
          H (Fin.cons p.1 (realPairFlatten r p.2),z) ∂ν :=
        (integral_prod _ hPull.integral_prod_left).symm
      _ = _ := integral_oddRealPairFlatten r (fun u ↦ ∫ z, H (u,z) ∂ν)
  have hOrd := integrable_ordered_weightedMixedVandermonde B hB t (2*r+1) l
  have hAvg (z : Fin l → ℂ) :
      (∫ u : Fin (2*r+1) → ℝ, H (u,z)) =
        ((2 : ℂ)^r*(r.factorial : ℂ)) *
          ∫ u in {u : Fin (2*r+1) → ℝ | Monotone u},
            weightedMixedVandermonde B t (2*r+1) l z u := by
    exact integral_weightedMixedVandermonde_odd B t r l z
  have hJ :
      (∫ z, (∫ u in {u : Fin (2*r+1) → ℝ | Monotone u},
        weightedMixedVandermonde B t (2*r+1) l z u) ∂ν) = J := by
    simpa only [J,volume_pi] using! (integral_integral_swap hOrd).symm
  have hPhase : Complex.I^l*J = Complex.ofReal (mixedCountIntegral B t (2*r+1) l).toReal := by
    simpa only [J,ν,volume_pi] using! (mixedCountIntegral_toReal_eq_bochner B hB t (2*r+1) l).symm
  have hcancel : (1/2 : ℂ)^r*(2 : ℂ)^r = 1 := by
    rw [← mul_pow]
    norm_num
  have hPoint (x : ℝ) (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
      (pairedFeatureMatrix (fun i : Fin (r+l+1) ↦
        deBruijnBorderFeature B t (rawOddPolynomial (r+l)) (Fin.last (r+l),1)
          (Fin.cons (α := fun _ ↦ (((ℝ × ℝ) ⊕ ℂ) ⊕ ℝ)) (Sum.inr x)
            (fun j ↦ Sum.inl
              (Fin.append (fun a ↦ Sum.inl (xy a)) (fun a ↦ Sum.inr (z a)) j)) i))).det =
        c * H (Fin.cons x (realPairFlatten r xy),z) := by
    rw [deBruijn_odd_canonicalSourceDet_eq]
    dsimp only [c,H]
    ring
  calc
    _ = c * ∫ x : ℝ, ∫ xy : Fin r → ℝ × ℝ, ∫ z,
        H (Fin.cons x (realPairFlatten r xy),z) ∂ν := by
      simp_rw [hPoint,integral_const_mul]
      rfl
    _ = c * ∫ u : Fin (2*r+1) → ℝ, ∫ z, H (u,z) ∂ν := congrArg (fun a : ℂ ↦ c*a) hFlat
    _ = c * ∫ z, (∫ u : Fin (2*r+1) → ℝ, H (u,z)) ∂ν :=
      congrArg (fun a : ℂ ↦ c*a) (integral_integral_swap hH)
    _ = c * (((2 : ℂ)^r*(r.factorial : ℂ)) * ∫ z,
        (∫ u in {u : Fin (2*r+1) → ℝ | Monotone u},
          weightedMixedVandermonde B t (2*r+1) l z u) ∂ν) := by
      simp_rw [hAvg,integral_const_mul]
    _ = c * (((2 : ℂ)^r*(r.factorial : ℂ))*J) := by rw [hJ]
    _ = (r.factorial : ℂ)*(2 : ℂ)^l*(Complex.I^l*J) := by
      dsimp only [c]
      rw [mul_pow]
      calc
        _ = ((1/2 : ℂ)^r*(2 : ℂ)^r) * (r.factorial : ℂ)*(2 : ℂ)^l*(Complex.I^l*J) := by ring
        _ = _ := by rw [hcancel,one_mul]
    _ = _ := by rw [hPhase]

end Paper.SkewOrthogonal
