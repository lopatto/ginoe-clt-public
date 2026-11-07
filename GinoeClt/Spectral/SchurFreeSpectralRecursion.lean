/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurFreeSpectralSemantics
public import GinoeClt.Spectral.SchurSpectralIntegral
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal Classical
namespace Paper.Spectral

/-- Precisely the original positive raw free parameters. -/
def schurFreePositiveSet (w : List Bool) : Set (SchurWordFreeIndex w → ℝ) :=
  {u | SchurWordPositive w (schurWordFreeCells w u)}

theorem measurableSet_schurFreePositiveSet (w : List Bool) :
    MeasurableSet (schurFreePositiveSet w) :=
  (measurableSet_schurWordPositive w).preimage (continuous_schurWordFreeCells w).measurable

/-- The actual free Gaussian and physical within-pair ratio, with a test
function of the actual representative vector. No ordering has been removed:
an ordering indicator may be included in F. -/
def schurFreeSpectralIntegral (w : List Bool)
    (F : (Fin w.length → ℂ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ u in schurFreePositiveSet w,
    ENNReal.ofReal (schurUpperGaussian (Matrix.vec
      (schurWordParameter w (schurWordFreeCells w u)))) *
      ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w u)) *
        F (schurWordHeadRootAt w (schurWordFreeCells w u))

theorem measurable_schurFreeSpectralIntegral (w : List Bool)
    {X : Type*} [MeasurableSpace X]
    (F : X × (Fin w.length → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun x => schurFreeSpectralIntegral w (fun v => F (x,v))) := by
  have hroot : Measurable (fun u : SchurWordFreeIndex w → ℝ =>
      schurWordHeadRootAt w (schurWordFreeCells w u)) :=
    ((continuous_schurWordHeadRootVector w).comp (continuous_schurWordFreeCells w)).measurable
  have hr : Measurable (fun u : SchurWordFreeIndex w → ℝ =>
      ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w u))) :=
    ((measurable_schurWordPairRatio w).comp
      (continuous_schurWordFreeCells w).measurable).ennreal_ofReal
  have hi : Measurable (fun p : X × (SchurWordFreeIndex w → ℝ) =>
      ENNReal.ofReal (schurUpperGaussian (Matrix.vec
        (schurWordParameter w (schurWordFreeCells w p.2)))) *
        ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w p.2)) *
          F (p.1,schurWordHeadRootAt w (schurWordFreeCells w p.2))) :=
    (((measurable_freeParameterGaussian w).comp measurable_snd).mul
      (hr.comp measurable_snd)).mul
      (hF.comp (measurable_fst.prodMk (hroot.comp measurable_snd)))
  exact hi.lintegral_prod_right'
    (ν := (volume : Measure (SchurWordFreeIndex w → ℝ)).restrict (schurFreePositiveSet w))

/-- Scalar-head step of the genuine raw free integral. -/
theorem schurFreeSpectralIntegral_false (w : List Bool)
    (F : (Fin (false::w).length → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    schurFreeSpectralIntegral (false::w) F =
      ENNReal.ofReal (Real.sqrt (2*Real.pi)^schurWordSize w) *
        ∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (-a^2/2)) *
          schurFreeSpectralIntegral w (fun v => F (Fin.cons (a : ℂ) v)) := by
  let H : (Fin 1 → ℝ) × (SchurWordFreeIndex w → ℝ) → ℝ≥0∞ := fun p =>
    if SchurWordPositive w (schurWordFreeCells w p.2) then
      ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w p.2)) *
        F (Fin.cons (p.1 0 : ℂ) (schurWordHeadRootAt w (schurWordFreeCells w p.2)))
    else 0
  have hroot : Measurable (fun u : SchurWordFreeIndex w → ℝ =>
      schurWordHeadRootAt w (schurWordFreeCells w u)) :=
    ((continuous_schurWordHeadRootVector w).comp (continuous_schurWordFreeCells w)).measurable
  have hr : Measurable (fun u : SchurWordFreeIndex w → ℝ =>
      ENNReal.ofReal (schurWordPairRatio w (schurWordFreeCells w u))) :=
    ((measurable_schurWordPairRatio w).comp
      (continuous_schurWordFreeCells w).measurable).ennreal_ofReal
  have hh : Measurable H := by
    have hi := (hr.comp measurable_snd).mul
      (hF.comp (measurable_finCons
        (fun p : (Fin 1 → ℝ) × (SchurWordFreeIndex w → ℝ) => (p.1 0 : ℂ))
        (by fun_prop) _ (hroot.comp measurable_snd)))
    exact hi.ite ((measurableSet_schurFreePositiveSet w).preimage measurable_snd) measurable_const
  have he (y : SchurWordFreeIndex (false::w) → ℝ) :
      (schurFreePositiveSet (false::w)).indicator (fun u =>
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter (false::w) (schurWordFreeCells (false::w) u)))) *
            ENNReal.ofReal (schurWordPairRatio (false::w) (schurWordFreeCells (false::w) u)) *
              F (schurWordHeadRootAt (false::w) (schurWordFreeCells (false::w) u))) y =
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter (false::w) (schurWordFreeCells (false::w) y)))) *
            H ((scalarFreeSplit w y).1,(scalarFreeSplit w y).2.2) := by
    by_cases ht : SchurWordPositive w (schurWordFreeCells w (scalarFreeSplit w y).2.2)
    · have hp : y ∈ schurFreePositiveSet (false::w) := (scalarFree_positive_iff w y).mpr ht
      rw [Set.indicator_of_mem hp,scalarFree_pairRatio,scalarFree_headRootAt]
      simp only [H,ite_eq_left ht]
      exact mul_assoc _ _ _
    · have hp : y ∉ schurFreePositiveSet (false::w) := by
        intro hp
        exact ht ((scalarFree_positive_iff w y).mp hp)
      rw [Set.indicator_of_notMem hp]
      simp only [H,ite_eq_right ht,mul_zero]
  have hinner (a : Fin 1 → ℝ) :
      (∫⁻ t : SchurWordFreeIndex w → ℝ,
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter w (schurWordFreeCells w t)))) * H (a,t)) =
      schurFreeSpectralIntegral w (fun v => F (Fin.cons (a 0 : ℂ) v)) := by
    unfold schurFreeSpectralIntegral
    rw [← lintegral_indicator (measurableSet_schurFreePositiveSet w)]
    apply lintegral_congr
    intro t
    by_cases ht : SchurWordPositive w (schurWordFreeCells w t)
    · have ht' : t ∈ schurFreePositiveSet w := ht
      rw [Set.indicator_of_mem ht']
      simp only [H,ite_eq_left ht]
      exact (mul_assoc _ _ _).symm
    · have ht' : t ∉ schurFreePositiveSet w := ht
      rw [Set.indicator_of_notMem ht']
      simp only [H,ite_eq_right ht,mul_zero]
  calc
    _ = ∫⁻ y : SchurWordFreeIndex (false::w) → ℝ,
        ENNReal.ofReal (schurUpperGaussian (Matrix.vec
          (schurWordParameter (false::w) (schurWordFreeCells (false::w) y)))) *
            H ((scalarFreeSplit w y).1,(scalarFreeSplit w y).2.2) := by
      unfold schurFreeSpectralIntegral
      rw [← lintegral_indicator (measurableSet_schurFreePositiveSet (false::w))]
      exact lintegral_congr he
    _ = ENNReal.ofReal (Real.sqrt (2*Real.pi)^schurWordSize w) *
        ∫⁻ a : Fin 1 → ℝ, ENNReal.ofReal (Real.exp (-(a 0)^2/2)) *
          schurFreeSpectralIntegral w (fun v => F (Fin.cons (a 0 : ℂ) v)) := by
      rw [lintegral_scalarFreeGaussian w H hh]
      congr 1
      apply lintegral_congr
      intro a
      simp_rw [mul_assoc]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hinner]
    _ = _ := by
      congr 1
      have hm : Measurable (fun a : ℝ =>
          ENNReal.ofReal (Real.exp (-a^2/2)) *
            schurFreeSpectralIntegral w (fun v => F (Fin.cons (a : ℂ) v))) := by
        have ht := measurable_schurFreeSpectralIntegral w
          (fun p : ℝ × (Fin w.length → ℂ) => F (Fin.cons (p.1 : ℂ) p.2))
          (hF.comp (measurable_finCons _ (by fun_prop) _ measurable_snd))
        exact (by fun_prop : Measurable (fun a : ℝ => ENNReal.ofReal (Real.exp (-a^2/2)))).mul ht
      exact (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).lintegral_comp hm

end Paper.Spectral
