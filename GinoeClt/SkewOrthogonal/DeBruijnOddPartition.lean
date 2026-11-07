/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnOddPairSector
public import GinoeClt.SkewOrthogonal.OddCountGram
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal ENNReal Classical
namespace Paper.SkewOrthogonal
open Paper.Spectral
local notation "Y" => ((ℝ × ℝ) ⊕ ℂ)

private theorem odd_selected_sector_of_le (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m l : ℕ) (hl : l ≤ m) :
    (∫ s : Fin m → Y, (∫ x : ℝ, firstOddSourceDeterminant B t m x s)
      ∂Measure.pi (fun i : Fin m ↦
        if i ∈ lastMixedMask m ⟨l,Nat.lt_succ_of_le hl⟩ then
          ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
        else (volume : Measure (ℝ × ℝ)).map Sum.inl)) =
      ((m-l).factorial : ℂ)*(2 : ℂ)^l *
        Complex.ofReal (mixedCountIntegral B t (2*(m-l)+1) l).toReal := by
  obtain ⟨r,rfl⟩ : ∃ r, m = r+l := ⟨m-l,(Nat.sub_add_cancel hl).symm⟩
  simpa using! deBruijn_odd_selected_sector_integral B hB t r l

theorem mixedCountPartition_odd_toReal (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m : ℕ) :
    Complex.ofReal (mixedCountPartition B t (2*m+1)).toReal =
      ∑ l : Fin (m+1), ((2 : ℂ)^l.val/(l.val.factorial : ℂ)) *
        Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal := by
  have hfinite (l : Fin (m+1)) :
      (((2^l.val : ℕ) : ℝ≥0∞)*(l.val.factorial : ℝ≥0∞)⁻¹) *
        mixedCountIntegral B t (2*m+1-2*l.val) l.val ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · apply ENNReal.inv_ne_top.mpr
        exact_mod_cast Nat.factorial_ne_zero l.val
    · exact (mixedCountIntegral_lt_top B hB t _ _).ne
  unfold mixedCountPartition
  rw [show (2*m+1)/2 = m by omega,ENNReal.toReal_sum (fun l _ ↦ hfinite l),Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hk : 2*m+1-2*l.val = 2*(m-l.val)+1 := by have h := l.isLt; omega
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,div_eq_mul_inv,hk]

/-- The ACTUAL raw odd Gram Pfaffian equals the full spectral partition, with
the original Gaussian border, exact 2^l/l! coefficients, and every m including zero. -/
theorem pfaffian_rawOddCountGram_eq_mixedPartition (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0) (m : ℕ) :
    pfaffian (rawOddCountGram m B (t : ℂ)) =
      Complex.ofReal (mixedCountPartition B t (2*m+1)).toReal := by
  let μR : Measure Y := (volume : Measure (ℝ × ℝ)).map Sum.inl
  let μC : Measure Y := ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
  have er : MeasurableEmbedding (@Sum.inl (ℝ × ℝ) ℂ) :=
    ⟨Sum.inl_injective,measurable_inl,fun _ hs ↦ hs.inl_image⟩
  have ec : MeasurableEmbedding (@Sum.inr (ℝ × ℝ) ℂ) :=
    ⟨Sum.inr_injective,measurable_inr,fun _ hs ↦ hs.inr_image⟩
  have : SigmaFinite μR := er.sigmaFinite_map
  have : SigmaFinite μC := ec.sigmaFinite_map
  let F : (Fin m → Y) → ℂ := fun s ↦ ∫ x : ℝ, firstOddSourceDeterminant B t m x s
  have hJoint := integrable_firstOddSourceDeterminant B hB t m
  have hF : Integrable F (Measure.pi (fun _ : Fin m ↦ μR+μC)) := hJoint.integral_prod_right
  have hSym : ∀ (σ : Equiv.Perm (Fin m)) y, F (y ∘ σ) = F y := by
    intro σ y
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
      firstOddSourceDeterminant_perm B t m σ x y)
  have hSec (l : Fin (m+1)) :
      (∫ y, F y ∂Measure.pi (fun i : Fin m ↦ if i ∈ lastMixedMask m l then μC else μR)) =
        ((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal := by
    exact odd_selected_sector_of_le B hB t m l.val (Nat.le_of_lt_succ l.isLt)
  have hSum : (∫ s, F s ∂Measure.pi (fun _ : Fin m ↦ μR+μC)) =
      ∑ l : Fin (m+1), (m.choose l.val : ℂ) *
        (((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal) := by
    rw [integral_pi_add_eq_choose_lastMixedMask μR μC m F hF hSym]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hSec]
  have hGram : (∫ y, rawOddSourceDeterminant B t m y
      ∂Measure.pi (fun _ : Fin (m+1) ↦ deBruijnBorderMeasure)) =
      ((m+1).factorial : ℂ)*pfaffian (rawOddCountGram m B (t : ℂ)) := by
    have h := integral_pairedFeatureMatrix deBruijnBorderMeasure
      (deBruijnBorderFeature B t (rawOddPolynomial m) (Fin.last m,1))
      (integrable_deBruijnBorderFeature_product B hB t (rawOddPolynomial m) (Fin.last m,1))
    simp_rw [integral_rawOddBorderFeature_wedge B hB hupper t m] at h
    exact h
  have hD : ((m+1).factorial : ℂ)*pfaffian (rawOddCountGram m B (t : ℂ)) =
      (m+1 : ℂ)*(∫ s, F s ∂Measure.pi (fun _ : Fin m ↦ μR+μC)) := by
    calc
      _ = ∫ y, rawOddSourceDeterminant B t m y
          ∂Measure.pi (fun _ : Fin (m+1) ↦ deBruijnBorderMeasure) := hGram.symm
      _ = (m+1 : ℂ)*(∫ x : ℝ, ∫ s : Fin m → Y,
          firstOddSourceDeterminant B t m x s ∂Measure.pi (fun _ : Fin m ↦ deBruijnPairMeasure)) :=
        integral_rawOddSourceDeterminant_singleton_reduction B hB t m
      _ = _ := congrArg (fun c : ℂ ↦ (m+1)*c) (integral_integral_swap hJoint)
  have hS : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hEq : (m.factorial : ℂ)*pfaffian (rawOddCountGram m B (t : ℂ)) =
      ∑ l : Fin (m+1), (m.choose l.val : ℂ) *
        (((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal) := by
    apply mul_left_cancel₀ hS
    calc
      _ = ((m+1).factorial : ℂ)*pfaffian (rawOddCountGram m B (t : ℂ)) := by
        rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
        ring
      _ = _ := hD.trans (congrArg (fun c : ℂ ↦ (m+1)*c) hSum)
  have hM : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  calc
    _ = (m.factorial : ℂ)⁻¹*((m.factorial : ℂ)*pfaffian (rawOddCountGram m B (t : ℂ))) := by
      rw [← mul_assoc,inv_mul_cancel₀ hM,one_mul]
    _ = (m.factorial : ℂ)⁻¹*∑ l : Fin (m+1), (m.choose l.val : ℂ) *
        (((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal) :=
      congrArg (fun c : ℂ ↦ (m.factorial : ℂ)⁻¹*c) hEq
    _ = ∑ l : Fin (m+1), ((2 : ℂ)^l.val/(l.val.factorial : ℂ)) *
        Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hc := inv_factorial_choose_mul m l.val (Nat.le_of_lt_succ l.isLt)
      calc
        _ = ((m.factorial : ℂ)⁻¹*(m.choose l.val : ℂ)*((m-l.val).factorial : ℂ)) *
            ((2 : ℂ)^l.val*Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)+1) l.val).toReal) := by ring
        _ = _ := by rw [hc]; ring
    _ = _ := (mixedCountPartition_odd_toReal B hB t m).symm

/-- The ACTUAL finite odd Gaussian count generating integral, including N=1. -/
theorem countGeneratingIntegral_odd_pfaffian (A : Set ℂ) (hA : IsOpen A)
    (n m : ℕ) (hN : n+1 = 2*m+1) (hupper : ∀ a ∈ A, 0 < a.im) (t : ℝ≥0) :
    (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n) ≠ ∞ ∧
    Complex.ofReal (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n).toReal =
      pfaffian (rawOddCountGram m (scaledCountDomain n A) (t : ℂ)) /
        pfaffian (rawOddCountGram m (scaledCountDomain n A) 0) := by
  constructor
  · rw [← lintegral_gaussianCountWeight A hA n t]
    exact lintegral_gaussianCountWeight_ne_top A hA n t
  · have hB : MeasurableSet (scaledCountDomain n A) :=
      (isOpen_scaledCountDomain A hA n).measurableSet
    have hBu : scaledCountDomain n A ⊆ {z : ℂ | 0 < z.im} := scaledCountDomain_upper A n hupper
    rw [countGeneratingIntegral_eq_mixedCountPartition_ratio A hA n hupper t,hN,
      ENNReal.toReal_div,Complex.ofReal_div,
      ← pfaffian_rawOddCountGram_eq_mixedPartition _ hB hBu t m,
      ← pfaffian_rawOddCountGram_eq_mixedPartition _ hB hBu 0 m]
    simp

end Paper.SkewOrthogonal
