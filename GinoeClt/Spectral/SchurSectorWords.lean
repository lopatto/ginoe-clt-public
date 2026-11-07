/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.CountSpectralPartition
public import GinoeClt.Spectral.SchurCanonicalProductIntegral
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Classical BigOperators
namespace Paper.Spectral

theorem schurCanonicalWord_count_false (k l : ℕ) :
    (schurCanonicalWord k l).count false = k := by simp [schurCanonicalWord,List.count_replicate]
theorem schurCanonicalWord_count_true (k l : ℕ) :
    (schurCanonicalWord k l).count true = l := by simp [schurCanonicalWord,List.count_replicate]
theorem schurCanonicalWord_size (k l : ℕ) :
    schurWordSize (schurCanonicalWord k l) = k+2*l := by
  rw [schurWordSize_eq_counts,schurCanonicalWord_count_false,schurCanonicalWord_count_true]

/-- The actual exact-size canonical word with l complex pairs and N-2l real roots. -/
def sectorSchurWord (N : ℕ) (l : Fin (N/2+1)) : SchurWordsOfSize N :=
  ⟨schurCanonicalWord (N-2*l.val) l.val,by
    rw [schurCanonicalWord_size]
    have hl := l.isLt
    omega⟩

theorem sectorSchurWord_injective (N : ℕ) : Function.Injective (sectorSchurWord N) := by
  intro l r h
  apply Fin.ext
  have hc := congrArg (fun w : SchurWordsOfSize N => w.val.count true) h
  simpa only [sectorSchurWord,schurCanonicalWord_count_true] using hc

theorem mem_range_sectorSchurWord (N : ℕ) (w : SchurWordsOfSize N) :
    w ∈ Set.range (sectorSchurWord N) ↔
      w.val = schurCanonicalWord (w.val.count false) (w.val.count true) := by
  constructor
  · rintro ⟨l,rfl⟩
    simp only [sectorSchurWord,schurCanonicalWord_count_false,schurCanonicalWord_count_true]
  · intro hw
    have hs := schurWordSize_eq_counts w.val
    rw [w.property] at hs
    have hl : w.val.count true < N/2+1 := by omega
    refine ⟨⟨w.val.count true,hl⟩,?_⟩
    apply Subtype.ext
    change schurCanonicalWord (N-2*w.val.count true) (w.val.count true) = w.val
    have hk : N-2*w.val.count true = w.val.count false := by omega
    rw [hk]
    exact hw.symm

theorem sectorSchurWord_length (N : ℕ) (l : Fin (N/2+1)) :
    (sectorSchurWord N l).val.length = N-l.val := by
  change (schurCanonicalWord (N-2*l.val) l.val).length = _
  simp only [schurCanonicalWord,List.length_append,List.length_replicate]
  have hl := l.isLt
  omega

/-- Exact finite sum reindexing; the explicit zero hypothesis discards only
noncanonical words, without a parity restriction or an a.e. replacement. -/
theorem sum_schurWords_eq_sectors (N : ℕ) (f : SchurWordsOfSize N → ℝ≥0∞)
    (hf : ∀ w, w.val ≠ schurCanonicalWord (w.val.count false) (w.val.count true) → f w = 0) :
    (∑ w, f w) = ∑ l : Fin (N/2+1), f (sectorSchurWord N l) := by
  have hz (w : SchurWordsOfSize N) (hw : w ∉ Finset.univ.image (sectorSchurWord N)) :
      f w = 0 := by
    apply hf
    intro hc
    obtain ⟨l,hl⟩ := (mem_range_sectorSchurWord N w).mpr hc
    exact hw (Finset.mem_image.mpr ⟨l,Finset.mem_univ _,hl⟩)
  have hs : (∑ w ∈ Finset.univ.image (sectorSchurWord N), f w) = ∑ w, f w := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ hw
    exact hz w hw
  rw [← hs]
  exact Finset.sum_image (sectorSchurWord_injective N).injOn

theorem countSpectralPartition_eq_sectors (B : Set ℂ) (hB : MeasurableSet B)
    (t : ℝ≥0) (N : ℕ) :
    countSpectralPartition B t N =
      ∑ l : Fin (N/2+1),
        (((2^(N-l.val) : ℕ) : ℝ≥0∞))⁻¹ *
          schurSpectralIntegral (sectorSchurWord N l).val
            (schurHeadCountTest B t (sectorSchurWord N l).val) := by
  unfold countSpectralPartition
  rw [sum_schurWords_eq_sectors N _ (by
    intro w hw
    rw [schurSpectralIntegral_headCountTest_eq_zero_of_not_canonical B hB t w.val hw,mul_zero])]
  apply Finset.sum_congr rfl
  intro l _
  rw [sectorSchurWord_length]

end Paper.Spectral
