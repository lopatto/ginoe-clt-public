/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFreePairRecursion
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Matrix
namespace Paper.Spectral

lemma schurWordSize_choose_false (w : List Bool) :
    (schurWordSize (false::w)).choose 2 =
      schurWordSize w + (schurWordSize w).choose 2 := by
  change (1+schurWordSize w).choose 2 = _
  rw [Nat.add_comm 1]
  simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (schurWordSize w) 1

lemma schurWordSize_choose_true (w : List Bool) :
    (schurWordSize (true::w)).choose 2 =
      2*schurWordSize w+1+(schurWordSize w).choose 2 := by
  change (2+schurWordSize w).choose 2 = _
  have h (n : ℕ) : (n+1).choose 2 = n+n.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' n 1
  rw [show 2+schurWordSize w = (schurWordSize w+1)+1 by omega,h,h]
  omega

/-- Complete free Gaussian reduction for EVERY word, retaining the actual
matrix, original Pos and within-pair physical ratio. The common scalar depends
only on physical N=wordSize, including N=0. No ensemble law is assumed. -/
theorem schurFreeSpectralIntegral_eq (w : List Bool) :
    ∀ (F : (Fin w.length → ℂ) → ℝ≥0∞), Measurable F →
      schurFreeSpectralIntegral w F =
        ENNReal.ofReal (Real.sqrt (2*Real.pi)^((schurWordSize w).choose 2)) *
          schurSpectralIntegral w F := by
  induction w with
  | nil =>
    intro F hF
    let : IsEmpty (SchurWordFreeIndex []) := ⟨fun x => Fin.elim0 x.val.1⟩
    have hg (u : SchurWordFreeIndex [] → ℝ) :
        schurUpperGaussian (Matrix.vec (schurWordParameter [] (schurWordFreeCells [] u))) = 1 := by
      change schurUpperGaussian (ι := Fin 0 × Fin 0) _ = 1
      simp only [schurUpperGaussian,Fintype.sum_empty,neg_zero,zero_div,Real.exp_zero]
    have hs : schurFreePositiveSet [] = Set.univ := by
      ext u
      change True ↔ u ∈ Set.univ
      simp
    have hv : (volume : Measure (SchurWordFreeIndex [] → ℝ)) Set.univ = 1 := by
      have hh := congrArg (fun μ : Measure (SchurWordFreeIndex [] → ℝ) => μ Set.univ)
        (Measure.volume_pi_eq_dirac (fun _ : SchurWordFreeIndex [] => (0 : ℝ)))
      simpa only [measure_univ] using hh
    unfold schurFreeSpectralIntegral
    rw [hs,Measure.restrict_univ]
    simp only [schurWordPairRatio,schurWordHeadRootAt,ENNReal.ofReal_one,one_mul,
      schurWordSize,Nat.choose_zero_succ,pow_zero,schurSpectralIntegral]
    calc
      _ = ∫⁻ _u : SchurWordFreeIndex [] → ℝ, F Fin.elim0 := by
        apply lintegral_congr
        intro u
        simpa only [ENNReal.ofReal_one,one_mul,mul_one] using!
          congrArg (fun r : ℝ => ENNReal.ofReal r * F Fin.elim0) (hg u)
      _ = _ := by simp only [lintegral_const,hv,mul_one]
  | cons tag w ih =>
    intro F hF
    have ht (z : ℂ) :
        schurFreeSpectralIntegral w (fun v => F (Fin.cons z v)) =
          ENNReal.ofReal (Real.sqrt (2*Real.pi)^((schurWordSize w).choose 2)) *
            schurSpectralIntegral w (fun v => F (Fin.cons z v)) :=
      ih _ (hF.comp (measurable_finCons _ measurable_const _ measurable_id))
    have hp (r s : ℝ≥0∞) :
        r * (ENNReal.ofReal (Real.sqrt (2*Real.pi)^((schurWordSize w).choose 2))*s) =
          ENNReal.ofReal (Real.sqrt (2*Real.pi)^((schurWordSize w).choose 2))*(r*s) :=
      mul_left_comm _ _ _
    cases tag
    · rw [schurFreeSpectralIntegral_false w F hF]
      simp_rw [ht,hp]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity),← pow_add,schurWordSize_choose_false]
      rfl
    · rw [schurFreeSpectralIntegral_true w F hF]
      simp_rw [ht,hp]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity),← pow_add,schurWordSize_choose_true]
      rfl

end Paper.Spectral
