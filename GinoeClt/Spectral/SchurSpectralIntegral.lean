/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurPairRatioIntegration
public import GinoeClt.SkewOrthogonal.Weight
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper.Spectral

/-- The existing complex skew weight in ordinary Cartesian coordinates. -/
theorem complexWeight_cartesian (z : ℂ) :
    Paper.SkewOrthogonal.complexWeight z =
      Real.exp (z.im^2-z.re^2) * Paper.Kernel.erfc (Real.sqrt 2*z.im) := by
  unfold Paper.SkewOrthogonal.complexWeight
  congr 1
  congr 1
  simp [pow_two,Complex.mul_re]

/-- Ordinary iterated spectral-head integration. Real heads use real Lebesgue
measure; pair heads use ordinary upper complex area. The type of F is the
standard finite coordinate function space, in the original word order. -/
def schurSpectralIntegral : (w : List Bool) → ((Fin w.length → ℂ) → ℝ≥0∞) → ℝ≥0∞
  | [], F => F Fin.elim0
  | false::w, F => ∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (-a^2/2)) *
      schurSpectralIntegral w (fun v => F (Fin.cons (a : ℂ) v))
  | true::w, F => ∫⁻ z in {z : ℂ | 0 < z.im},
      ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight z) *
        schurSpectralIntegral w (fun v => F (Fin.cons z v))

lemma measurable_finCons {X : Type*} [MeasurableSpace X] {n : ℕ}
    (a : X → ℂ) (ha : Measurable a) (v : X → (Fin n → ℂ)) (hv : Measurable v) :
    Measurable (fun x => (Fin.cons (a x) (v x) : Fin (n+1) → ℂ)) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using ha
  · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp hv

/-- Joint Borel parameter measurability, before using spectral integration in
Tonelli or a later induction. No density law is assumed in this definition. -/
theorem measurable_schurSpectralIntegral (w : List Bool) :
    ∀ {X : Type*} [MeasurableSpace X]
      (F : X × (Fin w.length → ℂ) → ℝ≥0∞), Measurable F →
      Measurable (fun x => schurSpectralIntegral w (fun v => F (x,v))) := by
  induction w with
  | nil =>
    intro X _ F hF
    exact hF.comp (measurable_id.prodMk measurable_const)
  | cons tag w ih =>
    cases tag
    · intro X _ F hF
      have hc : Measurable (fun q : (X × ℝ) × (Fin w.length → ℂ) =>
          (q.1.1,(Fin.cons (q.1.2 : ℂ) q.2 : Fin (w.length+1) → ℂ))) :=
        (measurable_fst.comp measurable_fst).prodMk
          (measurable_finCons _ (by fun_prop) _ measurable_snd)
      have ht := ih (X := X × ℝ)
        (fun q => F (q.1.1,(Fin.cons (q.1.2 : ℂ) q.2 : Fin (w.length+1) → ℂ))) (hF.comp hc)
      have hi : Measurable (fun p : X × ℝ =>
          ENNReal.ofReal (Real.exp (-p.2^2/2)) *
            schurSpectralIntegral w (fun v => F (p.1,Fin.cons (p.2 : ℂ) v))) :=
        (by fun_prop : Measurable (fun p : X × ℝ =>
          ENNReal.ofReal (Real.exp (-p.2^2/2)))).mul ht
      exact hi.lintegral_prod_right'
    · intro X _ F hF
      have hc : Measurable (fun q : (X × ℂ) × (Fin w.length → ℂ) =>
          (q.1.1,(Fin.cons q.1.2 q.2 : Fin (w.length+1) → ℂ))) :=
        (measurable_fst.comp measurable_fst).prodMk
          (measurable_finCons _ (measurable_snd.comp measurable_fst) _ measurable_snd)
      have ht := ih (X := X × ℂ)
        (fun q => F (q.1.1,(Fin.cons q.1.2 q.2 : Fin (w.length+1) → ℂ))) (hF.comp hc)
      have hw : Measurable (fun p : X × ℂ =>
          ENNReal.ofReal (Paper.SkewOrthogonal.complexWeight p.2)) :=
        (Paper.SkewOrthogonal.continuous_complexWeight.measurable.comp
          measurable_snd).ennreal_ofReal
      exact (hw.mul ht).lintegral_prod_right'
        (ν := (volume : Measure ℂ).restrict {z | 0 < z.im})

/-- Finite scalar extraction is valid even when the remaining integral is
infinite. No nonzero or finiteness premise is imposed on F. -/
theorem schurSpectralIntegral_const_mul (w : List Bool) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    ∀ F : (Fin w.length → ℂ) → ℝ≥0∞,
      schurSpectralIntegral w (fun v => c*F v) = c*schurSpectralIntegral w F := by
  induction w with
  | nil => intro F; rfl
  | cons tag w ih =>
    cases tag <;> intro F <;>
      simp only [schurSpectralIntegral,ih]
    · simp_rw [← mul_assoc,mul_comm _ c,mul_assoc]
      exact lintegral_const_mul' c _ hc
    · simp_rw [← mul_assoc,mul_comm _ c,mul_assoc]
      exact lintegral_const_mul' c _ hc

end Paper.Spectral
