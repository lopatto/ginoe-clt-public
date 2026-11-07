/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurGaugeFoundations
public import GinoeClt.Spectral.SchurGaugeFrames
@[expose] public section
noncomputable section
open scoped Matrix ComplexConjugate
namespace Paper.Spectral

/-- The actual orthogonal intertwiners of ordered strict words lie in the finite
block-sign family. This is a classification, not a chartwise fiber count. -/
theorem orthogonal_ordered_word_intertwiner_gauge (w : List Bool) :
    ∀ (p q : SchurWordCells w), SchurWordPositive w p → SchurWordPositive w q →
      SchurWordOrdered w p → SchurWordOrdered w q →
      SchurWordPairGaps w p → SchurWordPairGaps w q → (schurWordRoots w p).Nodup →
      ∀ Q : Matrix.orthogonalGroup (Fin (schurWordSize w)) ℝ,
        schurWordParameter w p * (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) =
          (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) * schurWordParameter w q →
        (Q : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ) ∈ schurWordGaugeFrames w := by
  classical
  induction w with
  | nil =>
    intro p q hp hq hop hoq hgp hgq hn Q hT
    change Matrix.orthogonalGroup (Fin 0) ℝ at Q
    change (Q : Matrix (Fin 0) (Fin 0) ℝ) ∈ ({1} : Finset (Matrix (Fin 0) (Fin 0) ℝ))
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  | cons tag w ih =>
    cases tag <;> intro p q hp hq hop hoq hgp hgq hn Q hT
    · change Matrix.orthogonalGroup (Fin (1+schurWordSize w)) ℝ at Q
      let xp := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) p
      let xq := schurCellCoordinateEquiv ℝ 1 (schurWordSize w) q
      let tp := schurTailInput xp
      let tq := schurTailInput xq
      let H := schurHeadInput xp
      let H' := schurHeadInput xq
      let D := schurWordParameter w tp
      let D' := schurWordParameter w tq
      let U := schurUpperInput xp
      let U' := schurUpperInput xq
      let B := scalarBlock (H (0,0))
      let B' := scalarBlock (H' (0,0))
      have hKp : schurWordParameter (false::w) p = upperBlockMatrix B U D :=
        schurParameterPhysical_eq scalarHeadParameter (schurWordParameter w) p
      have hKq : schurWordParameter (false::w) q = upperBlockMatrix B' U' D' :=
        schurParameterPhysical_eq scalarHeadParameter (schurWordParameter w) q
      have hr := schurWordRoots_eq_of_intertwiner (false::w) p q hp hq Q hT
      have hsep := scalar_word_cross_separation w p q hp hq hop hoq hr hn
      have hTu : upperBlockMatrix B U D *
          (Q : Matrix (Fin (1+schurWordSize w)) (Fin (1+schurWordSize w)) ℝ) =
          (Q : Matrix (Fin (1+schurWordSize w)) (Fin (1+schurWordSize w)) ℝ) *
            upperBlockMatrix B' U' D' := by
        rw [← hKp, ← hKq]
        exact hT
      let Qs := schurOrthogonalReindex finSumFinEquiv.symm Q
      have hTs := schur_physical_intertwiner_to_sum B B' D D' U U' Q hTu
      have hpT : SchurWordPositive w tp := hp
      have hqT : SchurWordPositive w tq := hq
      have hgpT : SchurWordPairGaps w tp := hgp
      have hgqT : SchurWordPairGaps w tq := hgq
      have hopT : SchurWordOrdered w tp := by
        change (((H (0,0) : ℝ) : ℂ) :: schurWordHeadRoots w tp).Pairwise _ at hop
        exact (List.pairwise_cons.mp hop).2
      have hoqT : SchurWordOrdered w tq := by
        change (((H' (0,0) : ℝ) : ℂ) :: schurWordHeadRoots w tq).Pairwise _ at hoq
        exact (List.pairwise_cons.mp hoq).2
      have hnT : (schurWordRoots w tp).Nodup :=
        (Multiset.nodup_cons.mp
          (show ((((H (0,0) : ℝ) : ℂ)) ::ₘ schurWordRoots w tp).Nodup from hn)).2
      obtain ⟨R,hDR,hSign⟩ := scalar_head_intertwiner_frames (H (0,0)) (H' (0,0))
        D D' U U' Qs hsep hTs
      have hRmem := ih tp tq hpT hqT hopT hoqT hgpT hgqT hnT R hDR
      let ρ := Matrix.reindexRingEquiv ℝ
        (finSumFinEquiv : Fin 1 ⊕ Fin (schurWordSize w) ≃ Fin (1+schurWordSize w))
      have hQmap : ρ (Qs : Matrix (Fin 1 ⊕ Fin (schurWordSize w))
          (Fin 1 ⊕ Fin (schurWordSize w)) ℝ) = Q := by
        ext i j
        simp [ρ, Qs, schurOrthogonalReindex, Matrix.reindex_apply]
      change (Q : Matrix (Fin (1+schurWordSize w)) (Fin (1+schurWordSize w)) ℝ) ∈
        (Finset.univ ×ˢ schurWordGaugeFrames w).image (schurGaugeExtension 1 (schurWordSize w))
      apply Finset.mem_image.mpr
      rcases hSign with hplus | hminus
      · refine ⟨(false,(R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)),
          Finset.mem_product.mpr ⟨Finset.mem_univ _,hRmem⟩,?_⟩
        change ρ (Matrix.fromBlocks 1 0 0 (R : Matrix (Fin (schurWordSize w))
          (Fin (schurWordSize w)) ℝ)) = Q
        rw [← hplus]
        exact hQmap
      · refine ⟨(true,(R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)),
          Finset.mem_product.mpr ⟨Finset.mem_univ _,hRmem⟩,?_⟩
        change ρ (Matrix.fromBlocks (-1) 0 0 (R : Matrix (Fin (schurWordSize w))
          (Fin (schurWordSize w)) ℝ)) = Q
        rw [← hminus]
        exact hQmap
    · change Matrix.orthogonalGroup (Fin (2+schurWordSize w)) ℝ at Q
      let xp := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) p
      let xq := schurCellCoordinateEquiv ℝ 2 (schurWordSize w) q
      let tp := schurTailInput xp
      let tq := schurTailInput xq
      let H := schurHeadInput xp
      let H' := schurHeadInput xq
      let D := schurWordParameter w tp
      let D' := schurWordParameter w tq
      let U := schurUpperInput xp
      let U' := schurUpperInput xq
      let B := schurBlock (H (0,0)) (H (0,1)) (H (1,0))
      let B' := schurBlock (H' (0,0)) (H' (0,1)) (H' (1,0))
      let zp := schurRoot (H (0,0)) (H (0,1)) (H (1,0))
      let zq := schurRoot (H' (0,0)) (H' (0,1)) (H' (1,0))
      have hKp : schurWordParameter (true::w) p = upperBlockMatrix B U D :=
        schurParameterPhysical_eq pairHeadParameter (schurWordParameter w) p
      have hKq : schurWordParameter (true::w) q = upperBlockMatrix B' U' D' :=
        schurParameterPhysical_eq pairHeadParameter (schurWordParameter w) q
      have hr := schurWordRoots_eq_of_intertwiner (true::w) p q hp hq Q hT
      have hsep := pair_word_cross_separation w p q hp hq hop hoq hr hn
      have hTu : upperBlockMatrix B U D *
          (Q : Matrix (Fin (2+schurWordSize w)) (Fin (2+schurWordSize w)) ℝ) =
          (Q : Matrix (Fin (2+schurWordSize w)) (Fin (2+schurWordSize w)) ℝ) *
            upperBlockMatrix B' U' D' := by
        rw [← hKp, ← hKq]
        exact hT
      let Qs := schurOrthogonalReindex finSumFinEquiv.symm Q
      have hTs := schur_physical_intertwiner_to_sum B B' D D' U U' Q hTu
      change 0 < H (1,0) ∧ H (1,0) ≤ H (0,1) ∧ SchurWordPositive w tp at hp
      change 0 < H' (1,0) ∧ H' (1,0) ≤ H' (0,1) ∧ SchurWordPositive w tq at hq
      change H (1,0) < H (0,1) ∧ SchurWordPairGaps w tp at hgp
      change H' (1,0) < H' (0,1) ∧ SchurWordPairGaps w tq at hgq
      have hpT := hp.2.2
      have hqT := hq.2.2
      have hgpT := hgp.2
      have hgqT := hgq.2
      have hopT : SchurWordOrdered w tp := by
        change (zp :: schurWordHeadRoots w tp).Pairwise _ at hop
        exact (List.pairwise_cons.mp hop).2
      have hoqT : SchurWordOrdered w tq := by
        change (zq :: schurWordHeadRoots w tq).Pairwise _ at hoq
        exact (List.pairwise_cons.mp hoq).2
      have hnT : (schurWordRoots w tp).Nodup :=
        (Multiset.nodup_cons.mp (Multiset.nodup_cons.mp
          (show (zp ::ₘ conj zp ::ₘ schurWordRoots w tp).Nodup from hn)).2).2
      obtain ⟨R,hDR,hSign⟩ := pair_head_intertwiner_frames
        (H (0,0)) (H (0,1)) (H (1,0)) (H' (0,0)) (H' (0,1)) (H' (1,0))
        hp.1 hgp.1 hq.1 hgq.1 D D' U U' Qs hsep hTs
      have hRmem := ih tp tq hpT hqT hopT hoqT hgpT hgqT hnT R hDR
      let ρ := Matrix.reindexRingEquiv ℝ
        (finSumFinEquiv : Fin 2 ⊕ Fin (schurWordSize w) ≃ Fin (2+schurWordSize w))
      have hQmap : ρ (Qs : Matrix (Fin 2 ⊕ Fin (schurWordSize w))
          (Fin 2 ⊕ Fin (schurWordSize w)) ℝ) = Q := by
        ext i j
        simp [ρ, Qs, schurOrthogonalReindex, Matrix.reindex_apply]
      change (Q : Matrix (Fin (2+schurWordSize w)) (Fin (2+schurWordSize w)) ℝ) ∈
        (Finset.univ ×ˢ schurWordGaugeFrames w).image (schurGaugeExtension 2 (schurWordSize w))
      apply Finset.mem_image.mpr
      rcases hSign with hplus | hminus
      · refine ⟨(false,(R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)),
          Finset.mem_product.mpr ⟨Finset.mem_univ _,hRmem⟩,?_⟩
        change ρ (Matrix.fromBlocks 1 0 0 (R : Matrix (Fin (schurWordSize w))
          (Fin (schurWordSize w)) ℝ)) = Q
        rw [← hplus]
        exact hQmap
      · refine ⟨(true,(R : Matrix (Fin (schurWordSize w)) (Fin (schurWordSize w)) ℝ)),
          Finset.mem_product.mpr ⟨Finset.mem_univ _,hRmem⟩,?_⟩
        change ρ (Matrix.fromBlocks (-1) 0 0 (R : Matrix (Fin (schurWordSize w))
          (Fin (schurWordSize w)) ℝ)) = Q
        rw [← hminus]
        exact hQmap

end Paper.Spectral
