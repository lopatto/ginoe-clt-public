/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurGaugeFoundations
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate
namespace Paper.Spectral

/-- An ordered positive word with strict pair gaps and distinct actual full roots is regular.
This does not assert that every simple-spectrum matrix avoids the pair-gap boundary. -/
theorem schurWord_regular_of_pairGaps_nodup (w : List Bool) :
    ∀ (p : SchurWordCells w), SchurWordPositive w p → SchurWordOrdered w p →
      SchurWordPairGaps w p → (schurWordRoots w p).Nodup →
        LinearMap.det (schurWordDifferential w p) ≠ 0 := by
  induction w with
  | nil =>
    intro p _ _ _ _
    rw [det_schurWordDifferential_nil p]
    exact one_ne_zero
  | cons tag w ih =>
    cases tag <;> intro p hp ho hg hn
    · let x := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      have hpt : SchurWordPositive w t := hp
      have hgt : SchurWordPairGaps w t := hg
      have hot : SchurWordOrdered w t := by
        change (((h (0,0) : ℝ) : ℂ) :: schurWordHeadRoots w t).Pairwise _ at ho
        exact (List.pairwise_cons.mp ho).2
      have hnt : (schurWordRoots w t).Nodup :=
        (Multiset.nodup_cons.mp
          (show (((h (0,0) : ℝ) : ℂ) ::ₘ schurWordRoots w t).Nodup from hn)).2
      have hs := scalar_word_cross_separation w p p hp hp ho ho rfl hn
      rw [det_schurWordDifferential_false w p]
      exact mul_ne_zero hs (ih t hpt hot hgt hnt)
    · let x := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let h := schurHeadInput x
      let t := schurTailInput x
      let z := schurRoot (h (0,0)) (h (0,1)) (h (1,0))
      have hpt : SchurWordPositive w t := hp.2.2
      have hgt : SchurWordPairGaps w t := hg.2
      have hot : SchurWordOrdered w t := by
        change (z :: schurWordHeadRoots w t).Pairwise _ at ho
        exact (List.pairwise_cons.mp ho).2
      have hnt : (schurWordRoots w t).Nodup :=
        (Multiset.nodup_cons.mp
          ((Multiset.nodup_cons.mp
            (show (z ::ₘ conj z ::ₘ schurWordRoots w t).Nodup from hn)).2)).2
      have hs := pair_word_cross_separation w p p hp hp ho ho rfl hn
      have hgap : 2 * (h (0,1)-h (1,0)) ≠ 0 :=
        (mul_pos (by norm_num : (0:ℝ) < 2) (sub_pos.mpr hg.1)).ne'
      rw [det_schurWordDifferential_true w p]
      exact mul_ne_zero (mul_ne_zero hs hgap) (ih t hpt hot hgt hnt)

end Paper.Spectral
