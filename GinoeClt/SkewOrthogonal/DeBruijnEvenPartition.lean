/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.DeBruijnEvenSector
public import GinoeClt.SkewOrthogonal.GramNormalization
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NNReal ENNReal Classical
namespace Paper.SkewOrthogonal
open Paper.Spectral

/-- The actual original paired skew-Gram matrix with its complex count update. -/
def evenCountGram (m : ℕ) (B : Set ℂ) (s : ℂ) :
    Matrix (PairedIndex m) (PairedIndex m) ℂ :=
  fun p q ↦ skewForm (pairedPolynomial m p) (pairedPolynomial m q) + s *
    ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
      ((pairedPolynomial m p).eval z*(pairedPolynomial m q).eval (conj z) -
        (pairedPolynomial m q).eval z*(pairedPolynomial m p).eval (conj z))

theorem evenCountGram_zero (m : ℕ) (B : Set ℂ) : evenCountGram m B 0 = pairedGram m := by
  ext p q
  simp [evenCountGram,pairedGram]

theorem pfaffian_evenCountGram_zero_ne_zero (m : ℕ) (B : Set ℂ) :
    pfaffian (evenCountGram m B 0) ≠ 0 := by
  rw [evenCountGram_zero]
  exact pfaffian_pairedGram_ne_zero m

theorem inv_factorial_choose_mul (m l : ℕ) (hl : l ≤ m) :
    (m.factorial : ℂ)⁻¹*(m.choose l : ℂ)*((m-l).factorial : ℂ) = (l.factorial : ℂ)⁻¹ := by
  have hM : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hL : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  have hf : (m.choose l : ℂ)*(l.factorial : ℂ)*((m-l).factorial : ℂ) = (m.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hl
  have hc : (m.choose l : ℂ)*((m-l).factorial : ℂ) = (m.factorial : ℂ)/(l.factorial : ℂ) := by
    apply (eq_div_iff hL).mpr
    calc
      _ = (m.choose l : ℂ)*(l.factorial : ℂ)*((m-l).factorial : ℂ) := by ring
      _ = _ := hf
  calc
    _ = (m.factorial : ℂ)⁻¹*((m.factorial : ℂ)/(l.factorial : ℂ)) := by rw [mul_assoc,hc]
    _ = _ := by rw [div_eq_mul_inv,← mul_assoc,inv_mul_cancel₀ hM,one_mul]

/-- Convert the actual finite nonnegative even partition to its exact complex sum. -/
theorem mixedCountPartition_even_toReal (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (m : ℕ) :
    Complex.ofReal (mixedCountPartition B t (2*m)).toReal =
      ∑ l : Fin (m+1), ((2 : ℂ)^l.val/(l.val.factorial : ℂ)) *
        Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)) l.val).toReal := by
  have hfinite (l : Fin (m+1)) :
      (((2^l.val : ℕ) : ℝ≥0∞)*(l.val.factorial : ℝ≥0∞)⁻¹) *
        mixedCountIntegral B t (2*m-2*l.val) l.val ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · apply ENNReal.inv_ne_top.mpr
        exact_mod_cast Nat.factorial_ne_zero l.val
    · exact (mixedCountIntegral_lt_top B hB t _ _).ne
  unfold mixedCountPartition
  rw [show (2*m)/2 = m by omega,ENNReal.toReal_sum (fun l _ ↦ hfinite l),Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hk : 2*m-2*l.val = 2*(m-l.val) := by have h := l.isLt; omega
  simp [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,div_eq_mul_inv,hk]

/-- The EVEN actual skew-Gram Pfaffian is the complete spectral partition,
with its original relative 2^l/l! coefficients and ordinary volumes. -/
theorem pfaffian_evenCountGram_eq_mixedPartition (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : B ⊆ {z : ℂ | 0 < z.im}) (t : ℝ≥0) (m : ℕ) :
    pfaffian (evenCountGram m B (t : ℂ)) =
      Complex.ofReal (mixedCountPartition B t (2*m)).toReal := by
  let μR : Measure ((ℝ × ℝ) ⊕ ℂ) := (volume : Measure (ℝ × ℝ)).map Sum.inl
  let μC : Measure ((ℝ × ℝ) ⊕ ℂ) :=
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
  have eR : MeasurableEmbedding (@Sum.inl (ℝ × ℝ) ℂ) :=
    ⟨Sum.inl_injective,measurable_inl,fun _ hs ↦ hs.inl_image⟩
  have eC : MeasurableEmbedding (@Sum.inr (ℝ × ℝ) ℂ) :=
    ⟨Sum.inr_injective,measurable_inr,fun _ hs ↦ hs.inr_image⟩
  have : SigmaFinite μR := eR.sigmaFinite_map
  have : SigmaFinite μC := eC.sigmaFinite_map
  let F : (Fin m → ((ℝ × ℝ) ⊕ ℂ)) → ℂ := fun y ↦
    (pairedFeatureMatrix (fun i ↦ deBruijnPairFeature B t (pairedPolynomial m) (y i))).det
  have hF : Integrable F (Measure.pi (fun _ : Fin m ↦ μR+μC)) :=
    integrable_pairedFeatureMatrix deBruijnPairMeasure (deBruijnPairFeature B t (pairedPolynomial m))
      (integrable_deBruijnPairFeature_product B hB t (pairedPolynomial m))
  have hSym : ∀ (σ : Equiv.Perm (Fin m)) y, F (y ∘ σ) = F y := by
    intro σ y
    simpa only [F,Function.comp_def] using!
      pairedFeatureMatrix_det_perm (deBruijnPairFeature B t (pairedPolynomial m)) y σ
  have hGram : (∫ y, F y ∂Measure.pi (fun _ : Fin m ↦ μR+μC)) =
      (m.factorial : ℂ)*pfaffian (evenCountGram m B (t : ℂ)) := by
    simpa only [F,μR,μC,deBruijnPairMeasure,evenCountGram] using!
      integral_deBruijnPairFeature_determinant B hB hupper t m (pairedPolynomial m)
  have hSec (l : Fin (m+1)) :
      (∫ y, F y ∂Measure.pi (fun i : Fin m ↦ if i ∈ lastMixedMask m l then μC else μR)) =
        ((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)) l.val).toReal := by
    simpa only [F,μR,μC] using!
      deBruijn_even_sector_integral_of_le B hB t m l.val (Nat.le_of_lt_succ l.isLt)
  have hEq : (m.factorial : ℂ)*pfaffian (evenCountGram m B (t : ℂ)) =
      ∑ l : Fin (m+1), (m.choose l.val : ℂ) *
        (((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)) l.val).toReal) := by
    calc
      _ = ∫ y, F y ∂Measure.pi (fun _ : Fin m ↦ μR+μC) := hGram.symm
      _ = ∑ l : Fin (m+1), (m.choose l.val : ℂ) *
          ∫ y, F y ∂Measure.pi (fun i : Fin m ↦ if i ∈ lastMixedMask m l then μC else μR) :=
        integral_pi_add_eq_choose_lastMixedMask μR μC m F hF hSym
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hSec]
  have hM : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  calc
    _ = (m.factorial : ℂ)⁻¹*((m.factorial : ℂ)*pfaffian (evenCountGram m B (t : ℂ))) := by
      rw [← mul_assoc,inv_mul_cancel₀ hM,one_mul]
    _ = (m.factorial : ℂ)⁻¹*∑ l : Fin (m+1), (m.choose l.val : ℂ) *
        (((m-l.val).factorial : ℂ)*(2 : ℂ)^l.val *
          Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)) l.val).toReal) :=
      congrArg (fun c : ℂ ↦ (m.factorial : ℂ)⁻¹*c) hEq
    _ = ∑ l : Fin (m+1), ((2 : ℂ)^l.val/(l.val.factorial : ℂ)) *
        Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)) l.val).toReal := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hc := inv_factorial_choose_mul m l.val (Nat.le_of_lt_succ l.isLt)
      calc
        _ = ((m.factorial : ℂ)⁻¹*(m.choose l.val : ℂ)*((m-l.val).factorial : ℂ)) *
            ((2 : ℂ)^l.val*Complex.ofReal (mixedCountIntegral B t (2*(m-l.val)) l.val).toReal) := by ring
        _ = _ := by rw [hc]; ring
    _ = _ := (mixedCountPartition_even_toReal B hB t m).symm

/-- The ACTUAL finite even Gaussian count generating integral and its Pfaffian
ratio. Finiteness uses the existing pointwise count bound, not a uniform moment premise. -/
theorem countGeneratingIntegral_even_pfaffian (A : Set ℂ) (hA : IsOpen A)
    (n m : ℕ) (hN : n+1 = 2*m) (hupper : ∀ a ∈ A, 0 < a.im) (t : ℝ≥0) :
    (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n) ≠ ∞ ∧
    Complex.ofReal (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n).toReal =
      pfaffian (evenCountGram m (scaledCountDomain n A) (t : ℂ)) /
        pfaffian (evenCountGram m (scaledCountDomain n A) 0) := by
  constructor
  · rw [← lintegral_gaussianCountWeight A hA n t]
    exact lintegral_gaussianCountWeight_ne_top A hA n t
  · have hB : MeasurableSet (scaledCountDomain n A) :=
      (isOpen_scaledCountDomain A hA n).measurableSet
    have hBu : scaledCountDomain n A ⊆ {z : ℂ | 0 < z.im} := scaledCountDomain_upper A n hupper
    rw [countGeneratingIntegral_eq_mixedCountPartition_ratio A hA n hupper t,hN,
      ENNReal.toReal_div,Complex.ofReal_div,
      ← pfaffian_evenCountGram_eq_mixedPartition _ hB hBu t m,
      ← pfaffian_evenCountGram_eq_mixedPartition _ hB hBu 0 m]
    simp

end Paper.SkewOrthogonal
