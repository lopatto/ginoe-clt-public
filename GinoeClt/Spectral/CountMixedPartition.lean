/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurComplexOrderingIntegral
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal NNReal Classical BigOperators
namespace Paper.Spectral

/-- Upper-domain count tests leave every real representative unweighted. -/
theorem canonical_headCountProduct_upper (B : Set ℂ) (hupper : ∀ a ∈ B, 0 < a.im)
    (t : ℝ≥0) (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ) :
    schurHeadCountProduct B t (schurCanonicalHeads k l x z) = schurHeadCountProduct B t z := by
  have hr (r : ℝ) : (r : ℂ) ∉ B := by
    intro h
    have hh := hupper (r : ℂ) h
    have hzero : (0 : ℝ) < 0 := by simpa only [Complex.ofReal_im] using hh
    exact (lt_irrefl (0 : ℝ)) hzero
  rw [schurHeadCountProduct_eq_list,ofFn_schurCanonicalHeads,
    List.map_append,List.prod_append,List.map_map]
  have hf : (fun a : ℂ => if a ∈ B then 1+(t : ℝ≥0∞) else 1) ∘ Complex.ofReal =
      (fun _ : ℝ => (1 : ℝ≥0∞)) := by
    funext r
    exact ite_eq_right (hr r)
  rw [hf]
  have hone : ((List.ofFn x).map (fun _ => (1 : ℝ≥0∞))).prod = 1 := by
    rw [List.map_ofFn,List.prod_ofFn]
    change (∏ _i : Fin k, (1 : ℝ≥0∞)) = 1
    exact Finset.prod_const_one
  rw [hone,one_mul]
  exact (schurHeadCountProduct_eq_list B t z).symm

/-- Ordinary mixed real/complex sector integral. ONLY real weak ordering
remains; complex coordinates use unrestricted product of upper-plane AREA. -/
def mixedCountIntegral (B : Set ℂ) (t : ℝ≥0) (k l : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in {x : Fin k → ℝ | Monotone x},
    (∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/2))) *
      ∫⁻ z : Fin l → ℂ,
        (∏ i, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight (z i))) *
          (ENNReal.ofReal (schurHeadVandermondeNorm (schurCanonicalWord k l)
            (schurCanonicalHeads k l x z)) * schurHeadCountProduct B t z)
        ∂Measure.pi (fun _ : Fin l => (volume : Measure ℂ).restrict {a : ℂ | 0 < a.im})

theorem schurSpectralIntegral_canonical_eq_mixed (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : ∀ a ∈ B, 0 < a.im) (t : ℝ≥0) (k l : ℕ) :
    schurSpectralIntegral (schurCanonicalWord k l) (schurHeadCountTest B t (schurCanonicalWord k l)) =
      (l.factorial : ℝ≥0∞)⁻¹ * mixedCountIntegral B t k l := by
  rw [schurSpectralIntegral_canonical_countTest B hB t k l]
  simp only [mixedCountIntegral,schurUnorderedComplexWeight,
    canonical_headCountProduct_upper B hupper t]

/-- Explicit mixed partition in the ordered-real convention of de Bruijn:
the exact relative coefficient is 2^l/l!. -/
def mixedCountPartition (B : Set ℂ) (t : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  ∑ l : Fin (N/2+1), (((2^l.val : ℕ) : ℝ≥0∞) * (l.val.factorial : ℝ≥0∞)⁻¹) *
    mixedCountIntegral B t (N-2*l.val) l.val

theorem countSectorPartition_eq_mixed (B : Set ℂ) (hB : MeasurableSet B)
    (hupper : ∀ a ∈ B, 0 < a.im) (t : ℝ≥0) (N : ℕ) :
    countSectorPartition B t N = mixedCountPartition B t N := by
  unfold countSectorPartition mixedCountPartition
  apply Finset.sum_congr rfl
  intro l _
  change ((2^l.val : ℕ) : ℝ≥0∞) *
      schurSpectralIntegral (schurCanonicalWord (N-2*l.val) l.val)
        (schurHeadCountTest B t (schurCanonicalWord (N-2*l.val) l.val)) = _
  rw [schurSpectralIntegral_canonical_eq_mixed B hB hupper t (N-2*l.val) l.val]
  exact (mul_assoc _ _ _).symm

/-- The ACTUAL count generating integral equals the completely explicit mixed
spectral partition ratio, both parities, with no external density premise. -/
theorem countGeneratingIntegral_eq_mixedCountPartition_ratio (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ a ∈ A, 0 < a.im) (t : ℝ≥0) :
    (∫⁻ M : SampleSpace n, (1+(t : ℝ≥0∞))^count A n M ∂matrixLaw n) =
      mixedCountPartition (scaledCountDomain n A) t (n+1) /
        mixedCountPartition (scaledCountDomain n A) 0 (n+1) := by
  rw [countGeneratingIntegral_eq_sectorPartition_ratio A hA n hupper t,
    countSectorPartition_eq_mixed _ (isOpen_scaledCountDomain A hA n).measurableSet
      (scaledCountDomain_upper A n hupper),
    countSectorPartition_eq_mixed _ (isOpen_scaledCountDomain A hA n).measurableSet
      (scaledCountDomain_upper A n hupper)]

theorem mixedCountPartition_zero_ne_zero (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ a ∈ A, 0 < a.im) :
    mixedCountPartition (scaledCountDomain n A) 0 (n+1) ≠ 0 := by
  rw [← countSectorPartition_eq_mixed _ (isOpen_scaledCountDomain A hA n).measurableSet
    (scaledCountDomain_upper A n hupper)]
  exact countSectorPartition_zero_ne_zero A hA n hupper

theorem mixedCountPartition_zero_ne_top (A : Set ℂ) (hA : IsOpen A)
    (n : ℕ) (hupper : ∀ a ∈ A, 0 < a.im) :
    mixedCountPartition (scaledCountDomain n A) 0 (n+1) ≠ ∞ := by
  rw [← countSectorPartition_eq_mixed _ (isOpen_scaledCountDomain A hA n).measurableSet
    (scaledCountDomain_upper A n hupper)]
  exact countSectorPartition_zero_ne_top A hA n hupper

end Paper.Spectral
