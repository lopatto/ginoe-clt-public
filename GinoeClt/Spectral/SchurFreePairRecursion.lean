/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFreeSpectralRecursion
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal Classical
namespace Paper.Spectral

theorem schurRoot_cartesian (a b c : ℝ) :
    schurRoot a b c = (a : ℂ)+(Real.sqrt (b*c) : ℂ)*Complex.I := by
  apply Complex.ext <;> simp [schurRoot]

/-- Actual pair-word raw integral after eliminating only its upper U cells.
The remaining head domain is exactly original b≥c>0. -/
theorem schurFreeSpectralIntegral_true_head (w : List Bool)
    (F : (Fin (true::w).length → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    schurFreeSpectralIntegral (true::w) F =
      ENNReal.ofReal (Real.sqrt (2*Real.pi)^(2*schurWordSize w)) *
        ∫⁻ a in pairHeadDomain,
          ENNReal.ofReal ((a 1-a 2)/Real.sqrt (a 1*a 2) *
            Real.exp (-(2*(a 0)^2+(a 1)^2+(a 2)^2)/2)) *
              schurFreeSpectralIntegral w
                (fun v => F (Fin.cons (schurRoot (a 0) (a 1) (a 2)) v)) := by
  let H : (Fin 3 → ℝ) × (SchurWordFreeIndex w → ℝ) → ℝ≥0∞ := fun p =>
    if p.1 ∈ pairHeadDomain ∧ SchurWordPositive w (schurWordFreeCells w p.2) then
      ENNReal.ofReal ((p.1 1-p.1 2)/Real.sqrt (p.1 1*p.1 2)) *
        ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w p.2)) *
          F (Fin.cons (schurRoot (p.1 0) (p.1 1) (p.1 2))
            (schurWordHeadRootAt w (schurWordFreeCells w p.2)))
    else 0
  have hroot : Measurable (fun u : SchurWordFreeIndex w → ℝ =>
      schurWordHeadRootAt w (schurWordFreeCells w u)) :=
    ((continuous_schurWordHeadRootVector w).comp (continuous_schurWordFreeCells w)).measurable
  have hr : Measurable (fun u : SchurWordFreeIndex w → ℝ =>
      ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w u))) :=
    ((measurable_schurWordPairRatio w).comp
      (continuous_schurWordFreeCells w).measurable).ennreal_ofReal
  have hh : Measurable H := by
    have hz : Measurable (fun p : (Fin 3 → ℝ) × (SchurWordFreeIndex w → ℝ) =>
        schurRoot (p.1 0) (p.1 1) (p.1 2)) := by
      simp_rw [schurRoot_cartesian]
      fun_prop
    have hq : Measurable (fun p : (Fin 3 → ℝ) × (SchurWordFreeIndex w → ℝ) =>
        ENNReal.ofReal ((p.1 1-p.1 2)/Real.sqrt (p.1 1*p.1 2))) := by fun_prop
    have hi := (hq.mul (hr.comp measurable_snd)).mul
      (hF.comp (measurable_finCons _ hz _ (hroot.comp measurable_snd)))
    exact hi.ite (((measurableSet_pairHeadDomain).preimage measurable_fst).inter
      ((measurableSet_schurFreePositiveSet w).preimage measurable_snd)) measurable_const
  have he (y : SchurWordFreeIndex (true::w) → ℝ) :
      (schurFreePositiveSet (true::w)).indicator (fun u =>
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter (true::w) (schurWordFreeCells (true::w) u)))) *
            ENNReal.ofReal (schurWordPairRatio (true::w) (schurWordFreeCells (true::w) u)) *
              F (schurWordHeadRootAt (true::w) (schurWordFreeCells (true::w) u))) y =
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter (true::w) (schurWordFreeCells (true::w) y)))) *
            H ((pairFreeSplit w y).1,(pairFreeSplit w y).2.2) := by
    by_cases hp : y ∈ schurFreePositiveSet (true::w)
    · have ht := (pairFree_positive_iff w y).mp hp
      have hhead : (pairFreeSplit w y).1 ∈ pairHeadDomain := ⟨ht.1,ht.2.1⟩
      have hn : 0 ≤ ((pairFreeSplit w y).1 1-(pairFreeSplit w y).1 2)/
          Real.sqrt ((pairFreeSplit w y).1 1*(pairFreeSplit w y).1 2) :=
        div_nonneg (sub_nonneg.mpr ht.2.1) (Real.sqrt_nonneg _)
      rw [Set.indicator_of_mem hp,pairFree_pairRatio,pairFree_headRootAt,
        ENNReal.ofReal_mul hn]
      have hcond : (pairFreeSplit w y).1 ∈ pairHeadDomain ∧
          SchurWordPositive w (schurWordFreeCells w (pairFreeSplit w y).2.2) :=
        ⟨hhead,ht.2.2⟩
      simp only [H,ite_eq_left hcond]
      ac_rfl
    · have ht : ¬ ((pairFreeSplit w y).1 ∈ pairHeadDomain ∧
          SchurWordPositive w (schurWordFreeCells w (pairFreeSplit w y).2.2)) := by
        rintro ⟨hh,ht⟩
        exact hp ((pairFree_positive_iff w y).mpr ⟨hh.1,hh.2,ht⟩)
      rw [Set.indicator_of_notMem hp]
      simp only [H,ite_eq_right ht,mul_zero]
  have hinner (a : Fin 3 → ℝ) (ha : a ∈ pairHeadDomain) :
      (∫⁻ t : SchurWordFreeIndex w → ℝ,
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter w (schurWordFreeCells w t)))) * H (a,t)) =
      ENNReal.ofReal ((a 1-a 2)/Real.sqrt (a 1*a 2)) *
        schurFreeSpectralIntegral w
          (fun v => F (Fin.cons (schurRoot (a 0) (a 1) (a 2)) v)) := by
    unfold schurFreeSpectralIntegral
    rw [← lintegral_indicator (measurableSet_schurFreePositiveSet w),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ schurFreePositiveSet w
    · rw [Set.indicator_of_mem ht]
      have ht' : SchurWordPositive w (schurWordFreeCells w t) := ht
      have hcond : a ∈ pairHeadDomain ∧ SchurWordPositive w (schurWordFreeCells w t) :=
        ⟨ha,ht'⟩
      simp only [H,ite_eq_left hcond]
      ac_rfl
    · rw [Set.indicator_of_notMem ht]
      have ht' : ¬ SchurWordPositive w (schurWordFreeCells w t) := ht
      simp [H,ht',mul_zero]
  calc
    _ = ∫⁻ y : SchurWordFreeIndex (true::w) → ℝ,
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter (true::w) (schurWordFreeCells (true::w) y)))) *
            H ((pairFreeSplit w y).1,(pairFreeSplit w y).2.2) := by
      unfold schurFreeSpectralIntegral
      rw [← lintegral_indicator (measurableSet_schurFreePositiveSet (true::w))]
      exact lintegral_congr he
    _ = _ := by
      rw [lintegral_pairFreeGaussian w H hh]
      congr 1
      rw [← lintegral_indicator measurableSet_pairHeadDomain]
      apply lintegral_congr
      intro a
      by_cases ha : a ∈ pairHeadDomain
      · rw [Set.indicator_of_mem ha]
        simp_rw [mul_assoc]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hinner a ha,← mul_assoc]
        rw [mul_comm (ENNReal.ofReal (Real.exp (-(2*(a 0)^2+(a 1)^2+(a 2)^2)/2))) _,
          ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      · rw [Set.indicator_of_notMem ha]
        have hz (t : SchurWordFreeIndex w → ℝ) : H (a,t) = 0 := by simp [H,ha]
        simp_rw [hz,mul_zero,lintegral_zero]

/-- The pair-head step after the proved ordinary spectral-pair COV. Its extra
sqrt(2*pi) is the exact local gap integration, not an assumed sector scalar. -/
theorem schurFreeSpectralIntegral_true (w : List Bool)
    (F : (Fin (true::w).length → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    schurFreeSpectralIntegral (true::w) F =
      ENNReal.ofReal (Real.sqrt (2*Real.pi)^(2*schurWordSize w+1)) *
        ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight z) *
          schurFreeSpectralIntegral w (fun v => F (Fin.cons z v)) := by
  let H : ℂ → ℝ≥0∞ := fun z => schurFreeSpectralIntegral w (fun v => F (Fin.cons z v))
  have hH : Measurable H := by
    exact measurable_schurFreeSpectralIntegral w
      (fun p : ℂ × (Fin w.length → ℂ) => F (Fin.cons p.1 p.2))
      (hF.comp (measurable_finCons _ measurable_fst _ measurable_snd))
  rw [schurFreeSpectralIntegral_true_head w F hF]
  have hh := lintegral_pairHead_gaussian_ratio H hH
  simp_rw [← schurRoot_cartesian] at hh
  rw [hh]
  have hw (z : ℂ) :
      ENNReal.ofReal (Real.sqrt (2*Real.pi)*Real.exp (z.im^2-z.re^2)*
        Paper.Kernel.erfc (Real.sqrt 2*z.im)) * H z =
      ENNReal.ofReal (Real.sqrt (2*Real.pi)) *
        (ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight z) * H z) := by
    rw [complexWeight_cartesian,mul_assoc,ENNReal.ofReal_mul (Real.sqrt_nonneg _),mul_assoc]
  simp_rw [hw]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity),← pow_succ]

end Paper.Spectral
