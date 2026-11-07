/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnOddSingletonReduction
public import GinoeClt.SkewOrthogonal.DeBruijnOddCanonicalIntegral
public import GinoeClt.MeasureTheory.CanonicalMixedProduct
@[expose] public section
noncomputable section
open MeasureTheory Equiv
open scoped BigOperators ComplexConjugate NNReal Classical
namespace Paper.SkewOrthogonal
open Paper.Spectral
local notation "Y" => ((ℝ × ℝ) ⊕ ℂ)
local notation "W" => (Y ⊕ ℝ)

/-- The surviving first-singleton determinant, with ordinary coordinates. -/
def firstOddSourceDeterminant (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (x : ℝ) (s : Fin m → Y) : ℂ :=
  rawOddSourceDeterminant B t m
    (Fin.cons (α := fun _ ↦ W) (Sum.inr x) (fun j ↦ Sum.inl (s j)))

theorem integrable_firstOddSourceDeterminant (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m : ℕ) :
    Integrable (fun p : ℝ × (Fin m → Y) ↦ firstOddSourceDeterminant B t m p.1 p.2)
      ((volume : Measure ℝ).prod (Measure.pi (fun _ : Fin m ↦ deBruijnPairMeasure))) := by
  let μP : Measure W := deBruijnPairMeasure.map Sum.inl
  let μS : Measure W := (volume : Measure ℝ).map Sum.inr
  have ep : MeasurableEmbedding (@Sum.inl Y ℝ) :=
    ⟨Sum.inl_injective,measurable_inl,fun _ hs ↦ hs.inl_image⟩
  have es : MeasurableEmbedding (@Sum.inr Y ℝ) :=
    ⟨Sum.inr_injective,measurable_inr,fun _ hs ↦ hs.inr_image⟩
  have : SigmaFinite μP := ep.sigmaFinite_map
  have : SigmaFinite μS := es.sigmaFinite_map
  have hF : Integrable (rawOddSourceDeterminant B t m)
      (Measure.pi (fun _ : Fin (m+1) ↦ μP+μS)) :=
    integrable_rawOddSourceDeterminant B hB t m
  have hS := (integrable_pi_add_iff μP μS _).mp hF ({0} : Finset (Fin (m+1)))
  exact (measurePreserving_firstBorderCons m).integrable_comp_of_integrable hS

theorem firstOddSourceDeterminant_perm (B : Set ℂ) (t : ℝ≥0) (m : ℕ)
    (σ : Perm (Fin m)) (x : ℝ) (s : Fin m → Y) :
    firstOddSourceDeterminant B t m x (s ∘ σ) = firstOddSourceDeterminant B t m x s := by
  let τ : Perm (Fin (m+1)) :=
    { toFun := Fin.cases 0 (fun i ↦ (σ i).succ)
      invFun := Fin.cases 0 (fun i ↦ (σ.symm i).succ)
      left_inv := by intro i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      right_inv := by intro i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }
  have he :
      Fin.cons (α := fun _ ↦ W) (Sum.inr x) (fun j ↦ Sum.inl ((s ∘ σ) j)) =
        (Fin.cons (α := fun _ ↦ W) (Sum.inr x) (fun j ↦ Sum.inl (s j))) ∘ τ := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  dsimp only [firstOddSourceDeterminant]
  rw [he]
  exact rawOddSourceDeterminant_perm B t m τ
    (Fin.cons (α := fun _ ↦ W) (Sum.inr x) (fun j ↦ Sum.inl (s j)))

/-- Every selected ordinary-pair sector, AFTER integration in the singleton,
has the exact canonical odd mixed mass. -/
theorem deBruijn_odd_selected_sector_integral (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (r l : ℕ) :
    (∫ s : Fin (r+l) → Y, (∫ x : ℝ, firstOddSourceDeterminant B t (r+l) x s)
      ∂Measure.pi (fun i : Fin (r+l) ↦
        if i ∈ lastMixedMask (r+l) ⟨l,by omega⟩ then
          ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
        else (volume : Measure (ℝ × ℝ)).map Sum.inl)) =
      (r.factorial : ℂ)*(2 : ℂ)^l *
        Complex.ofReal (mixedCountIntegral B t (2*r+1) l).toReal := by
  let μR : Measure Y := (volume : Measure (ℝ × ℝ)).map Sum.inl
  let μC : Measure Y := ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
  have er : MeasurableEmbedding (@Sum.inl (ℝ × ℝ) ℂ) :=
    ⟨Sum.inl_injective,measurable_inl,fun _ hs ↦ hs.inl_image⟩
  have ec : MeasurableEmbedding (@Sum.inr (ℝ × ℝ) ℂ) :=
    ⟨Sum.inr_injective,measurable_inr,fun _ hs ↦ hs.inr_image⟩
  have : SigmaFinite μR := er.sigmaFinite_map
  have : SigmaFinite μC := ec.sigmaFinite_map
  let S := lastMixedMask (r+l) ⟨l,by omega⟩
  let ρ : Measure (Fin (r+l) → Y) :=
    Measure.pi (fun i ↦ if i ∈ S then μC else μR)
  let ν : Measure (Fin l → ℂ) :=
    Measure.pi (fun _ ↦ (volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})
  have : ∀ i : Fin (r+l), SigmaFinite (if i ∈ S then μC else μR) := by
    intro i
    split <;> infer_instance
  have : SigmaFinite ρ := by dsimp only [ρ]; infer_instance
  let D : ℝ × (Fin (r+l) → Y) → ℂ :=
    fun p ↦ firstOddSourceDeterminant B t (r+l) p.1 p.2
  let F : (Fin (r+l) → Y) → ℂ := fun s ↦ ∫ x : ℝ, D (x,s)
  have hD : Integrable D ((volume : Measure ℝ).prod
      (Measure.pi (fun _ : Fin (r+l) ↦ μR+μC))) :=
    integrable_firstOddSourceDeterminant B hB t (r+l)
  have hρ : ρ ≤ Measure.pi (fun _ : Fin (r+l) ↦ μR+μC) := by
    rw [pi_add_eq_sum_selected μR μC]
    exact Finset.single_le_sum (fun T _ ↦ (bot_le :
      (0 : Measure (Fin (r+l) → Y)) ≤ Measure.pi (fun i ↦ if i ∈ T then μC else μR)))
        (Finset.mem_univ S)
  have hDS : Integrable D ((volume : Measure ℝ).prod ρ) :=
    hD.mono_measure (Measure.prod_mono le_rfl hρ)
  have hF : Integrable F ρ := hDS.integral_prod_right
  have ht := lastMixedMask_inl_inr_transport (volume : Measure (ℝ × ℝ))
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}) r l (r+l) rfl F hF
  let Ψ : (Fin r → ℝ × ℝ) × (Fin l → ℂ) → (Fin (r+l) → Y) :=
    fun p ↦ Fin.append (Sum.inl ∘ p.1) (Sum.inr ∘ p.2)
  have hm : MeasurePreserving Ψ
      ((volume : Measure (Fin r → ℝ × ℝ)).prod ν) ρ := by
    simpa only [Ψ,ρ,S,μR,μC,ν,appendMappedCoordinates,volume_pi,
      lastMixedMask,Finset.mem_filter,Finset.mem_univ,true_and,Nat.add_sub_cancel_right] using!
      measurePreserving_appendMappedCoordinates (volume : Measure (ℝ × ℝ))
        ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}) Sum.inl Sum.inr
        measurable_inl measurable_inr r l
  have hTarget : Integrable
      (fun p : ℝ × ((Fin r → ℝ × ℝ) × (Fin l → ℂ)) ↦ D (p.1,Ψ p.2))
      ((volume : Measure ℝ).prod ((volume : Measure (Fin r → ℝ × ℝ)).prod ν)) := by
    exact ((MeasurePreserving.id (volume : Measure ℝ)).prod hm).integrable_comp_of_integrable hDS
  have hSwap :
      (∫ xy : Fin r → ℝ × ℝ, ∫ z : Fin l → ℂ,
        (∫ x : ℝ, D (x,Ψ (xy,z))) ∂ν) =
      ∫ x : ℝ, ∫ xy : Fin r → ℝ × ℝ, ∫ z : Fin l → ℂ, D (x,Ψ (xy,z)) ∂ν := by
    calc
      _ = ∫ p : (Fin r → ℝ × ℝ) × (Fin l → ℂ), (∫ x : ℝ,
          D (x,Ψ p)) ∂((volume : Measure (Fin r → ℝ × ℝ)).prod ν) :=
        (integral_prod _ hTarget.integral_prod_right).symm
      _ = ∫ x : ℝ, ∫ p : (Fin r → ℝ × ℝ) × (Fin l → ℂ),
          D (x,Ψ p) ∂((volume : Measure (Fin r → ℝ × ℝ)).prod ν) :=
        (integral_integral_swap hTarget).symm
      _ = _ := integral_congr_ae (hTarget.prod_right_ae.mono fun x hx ↦ integral_prod _ hx)
  calc
    _ = ∫ xy : Fin r → ℝ × ℝ, ∫ z : Fin l → ℂ, F (Ψ (xy,z)) ∂ν := by
      simpa only [F,Ψ,D,ν,Fin.cast_eq_self,volume_pi] using! ht.2
    _ = ∫ x : ℝ, ∫ xy : Fin r → ℝ × ℝ, ∫ z : Fin l → ℂ, D (x,Ψ (xy,z)) ∂ν := hSwap
    _ = _ := by
      simpa only [D,Ψ,ν,firstOddSourceDeterminant,rawOddSourceDeterminant,Function.comp_def] using!
        deBruijn_odd_canonical_integral B hB t r l

end Paper.SkewOrthogonal
