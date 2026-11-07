/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnCanonicalRoots
public import GinoeClt.SkewOrthogonal.MixedCountBochner
public import GinoeClt.MeasureTheory.CanonicalMixedProduct
@[expose] public section
noncomputable section
open MeasureTheory Set Equiv
open scoped BigOperators ComplexConjugate NNReal Classical
namespace Paper.SkewOrthogonal
open Paper.Spectral

/-- The ACTUAL canonical even source sector integrates to r! 2^l times its
nonnegative spectral mass. All transports and every Fubini step are justified. -/
theorem deBruijn_even_sector_integral (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (r l : ℕ) :
    (∫ y : Fin (r+l) → ((ℝ × ℝ) ⊕ ℂ),
      (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t (pairedPolynomial (r+l)) (y i))).det
      ∂Measure.pi (fun i : Fin (r+l) ↦
        if i ∈ lastMixedMask (r+l) ⟨l,by omega⟩ then
          ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
        else (volume : Measure (ℝ × ℝ)).map Sum.inl)) =
      (r.factorial : ℂ)*(2 : ℂ)^l * Complex.ofReal (mixedCountIntegral B t (2*r) l).toReal := by
  let μR : Measure ((ℝ × ℝ) ⊕ ℂ) := (volume : Measure (ℝ × ℝ)).map Sum.inl
  let μC : Measure ((ℝ × ℝ) ⊕ ℂ) :=
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
  have eR : MeasurableEmbedding (@Sum.inl (ℝ × ℝ) ℂ) :=
    ⟨Sum.inl_injective,measurable_inl,fun _ hs ↦ hs.inl_image⟩
  have eC : MeasurableEmbedding (@Sum.inr (ℝ × ℝ) ℂ) :=
    ⟨Sum.inr_injective,measurable_inr,fun _ hs ↦ hs.inr_image⟩
  have : SigmaFinite μR := eR.sigmaFinite_map
  have : SigmaFinite μC := eC.sigmaFinite_map
  let ν : Measure (Fin l → ℂ) := Measure.pi
    (fun _ : Fin l ↦ (volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})
  let F : (Fin (r+l) → ((ℝ × ℝ) ⊕ ℂ)) → ℂ :=
    fun y ↦ (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t (pairedPolynomial (r+l)) (y i))).det
  let H : (Fin (2*r) → ℝ) × (Fin l → ℂ) → ℂ := fun p ↦
    weightedMixedVandermonde B t (2*r) l p.2 p.1 *
      realPairSign (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
        (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) p.1
  let c : ℂ := (1/2 : ℂ)^r*(2*Complex.I)^l
  let J : ℂ := ∫ u in {u : Fin (2*r) → ℝ | Monotone u},
    (∫ z, weightedMixedVandermonde B t (2*r) l z u ∂ν)
      ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ))
  have hF : Integrable F (Measure.pi (fun _ : Fin (r+l) ↦ μR+μC)) :=
    integrable_pairedFeatureMatrix deBruijnPairMeasure (deBruijnPairFeature B t (pairedPolynomial (r+l)))
      (integrable_deBruijnPairFeature_product B hB t (pairedPolynomial (r+l)))
  have hS := (integrable_pi_add_iff μR μC F).mp hF (lastMixedMask (r+l) ⟨l,by omega⟩)
  have ht := lastMixedMask_inl_inr_transport (volume : Measure (ℝ × ℝ))
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}) r l (r+l) rfl F hS
  have hD := integrable_mixedVandermonde B hB t (2*r) l
  have hG : Measurable (fun p : (Fin (2*r) → ℝ) × (Fin l → ℂ) ↦
      realPairSign (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,0))
        (fun a ↦ PfaffianMinor.pairColumnEquiv r (a,1)) p.1) :=
    (measurable_realPairSign _ _).comp measurable_fst
  have hH : Integrable H ((Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ))).prod ν) :=
    hD.mul_bdd hG.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ norm_realPairSign_le_one _ _ p.1)
  have hOrd := integrable_ordered_weightedMixedVandermonde B hB t (2*r) l
  have hpt (xy : Fin r → ℝ × ℝ) (z : Fin l → ℂ) :
      F (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j))) =
        c * H (realPairFlatten r xy,z) := by
    dsimp only [F]
    rw [deBruijn_canonicalSourceDet_eq]
    dsimp only [c,H]
    ring
  have hflat :
      (∫ xy : Fin r → ℝ × ℝ, (∫ z, H (realPairFlatten r xy,z) ∂ν)
        ∂Measure.pi (fun _ : Fin r ↦ (volume : Measure (ℝ × ℝ)))) =
      ∫ u : Fin (2*r) → ℝ, (∫ z, H (u,z) ∂ν)
        ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ)) := by
    simpa only [volume_pi] using! integral_realPairFlatten r (fun u ↦ ∫ z, H (u,z) ∂ν)
  have hAvg (z : Fin l → ℂ) :
      (∫ u : Fin (2*r) → ℝ, H (u,z)
        ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ))) =
      ((2 : ℂ)^r*(r.factorial : ℂ)) *
        ∫ u in {u : Fin (2*r) → ℝ | Monotone u},
          weightedMixedVandermonde B t (2*r) l z u
          ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ)) := by
    simpa only [H,volume_pi] using! integral_weightedMixedVandermonde_even B t r l z
  have hJ :
      (∫ z, (∫ u in {u : Fin (2*r) → ℝ | Monotone u},
        weightedMixedVandermonde B t (2*r) l z u
          ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ))) ∂ν) = J := by
    exact (integral_integral_swap hOrd).symm
  have hPhase : Complex.I^l*J = Complex.ofReal (mixedCountIntegral B t (2*r) l).toReal := by
    simpa only [J,ν,volume_pi] using! (mixedCountIntegral_toReal_eq_bochner B hB t (2*r) l).symm
  have hcancel : (1/2 : ℂ)^r*(2 : ℂ)^r = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ∫ xy : Fin r → ℝ × ℝ, (∫ z : Fin l → ℂ,
        F (Fin.append (fun j ↦ Sum.inl (xy j)) (fun j ↦ Sum.inr (z j))) ∂ν)
          ∂Measure.pi (fun _ : Fin r ↦ (volume : Measure (ℝ × ℝ))) := by
      simpa only [F,Fin.cast_eq_self] using! ht.2
    _ = c * ∫ xy : Fin r → ℝ × ℝ, (∫ z, H (realPairFlatten r xy,z) ∂ν)
        ∂Measure.pi (fun _ : Fin r ↦ (volume : Measure (ℝ × ℝ))) := by
      simp_rw [hpt,integral_const_mul]
    _ = c * ∫ u : Fin (2*r) → ℝ, (∫ z, H (u,z) ∂ν)
        ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ)) := congrArg (fun a : ℂ ↦ c*a) hflat
    _ = c * ∫ z, (∫ u : Fin (2*r) → ℝ, H (u,z)
        ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ))) ∂ν :=
      congrArg (fun a : ℂ ↦ c*a) (integral_integral_swap hH)
    _ = c * (((2 : ℂ)^r*(r.factorial : ℂ)) * ∫ z,
        (∫ u in {u : Fin (2*r) → ℝ | Monotone u},
          weightedMixedVandermonde B t (2*r) l z u
            ∂Measure.pi (fun _ : Fin (2*r) ↦ (volume : Measure ℝ))) ∂ν) := by
      simp_rw [hAvg,integral_const_mul]
    _ = c * (((2 : ℂ)^r*(r.factorial : ℂ))*J) := by rw [hJ]
    _ = (r.factorial : ℂ)*(2 : ℂ)^l*(Complex.I^l*J) := by
      dsimp only [c]
      rw [mul_pow]
      calc
        _ = ((1/2 : ℂ)^r*(2 : ℂ)^r) * (r.factorial : ℂ)*(2 : ℂ)^l*(Complex.I^l*J) := by ring
        _ = _ := by rw [hcancel,one_mul]
    _ = _ := by rw [hPhase]

/-- Natural-index wrapper for the selected l-complex-pair sector of m pairs. -/
theorem deBruijn_even_sector_integral_of_le (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m l : ℕ) (hl : l ≤ m) :
    (∫ y : Fin m → ((ℝ × ℝ) ⊕ ℂ),
      (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t (pairedPolynomial m) (y i))).det
      ∂Measure.pi (fun i : Fin m ↦
        if i ∈ lastMixedMask m ⟨l,Nat.lt_succ_of_le hl⟩ then
          ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
        else (volume : Measure (ℝ × ℝ)).map Sum.inl)) =
      ((m-l).factorial : ℂ)*(2 : ℂ)^l *
        Complex.ofReal (mixedCountIntegral B t (2*(m-l)) l).toReal := by
  obtain ⟨r,rfl⟩ : ∃ r, m = r+l := ⟨m-l,(Nat.sub_add_cancel hl).symm⟩
  simpa using! deBruijn_even_sector_integral B hB t r l

end Paper.SkewOrthogonal
