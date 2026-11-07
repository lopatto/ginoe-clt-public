/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.RealSignAntisymmetry
public import GinoeClt.Spectral.SchurOrderingIntegral
public import GinoeClt.SkewOrthogonal.Weight
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section
noncomputable section
open Equiv Set MeasureTheory
open scoped BigOperators
namespace Paper.Spectral

/-- The full finite coordinate orbit sum is unchanged by a further permutation. -/
theorem sum_coordinate_orbit {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (τ : Perm (Fin n)) :
    (∑ σ : Perm (Fin n), F ((x ∘ τ) ∘ σ)) = ∑ σ : Perm (Fin n), F (x ∘ σ) := by
  simpa only [Equiv.coe_mulLeft,Perm.coe_mul,Function.comp_def] using
    Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Perm (Fin n) => F (x ∘ σ))

/-- Exact orbit averaging, with actual ZERO on repeated coordinates. The sign-sum
premise is a local finite lemma, discharged below for BOTH literal pair kernels. -/
theorem sum_alternating_pairSign_orbit (n : ℕ) (D G : (Fin n → ℝ) → ℂ) (c : ℂ)
    (halt : ∀ (σ : Perm (Fin n)) x, D (x ∘ σ) = permutationSign σ * D x)
    (hzero : ∀ x, ¬ Function.Injective x → D x = 0)
    (hGsum : ∀ x, StrictMono x →
      (∑ σ : Perm (Fin n), permutationSign σ * G (x ∘ σ)) = c)
    (x : Fin n → ℝ) :
    (∑ σ : Perm (Fin n), D (x ∘ σ) * G (x ∘ σ)) =
      c * ∑ σ : Perm (Fin n), (orderingChamber n id).indicator D (x ∘ σ) := by
  classical
  have hsorted (y : Fin n → ℝ) (hy : Function.Injective y) (hm : Monotone y) :
      (∑ σ : Perm (Fin n), D (y ∘ σ) * G (y ∘ σ)) =
        c * ∑ σ : Perm (Fin n), (orderingChamber n id).indicator D (y ∘ σ) := by
    obtain ⟨τ,hτ,hu⟩ := existsUnique_sorted_coordinate_perm n id Function.injective_id y hy
    have h1 : Monotone (fun i => id (y ((1 : Perm (Fin n)) i))) := by simpa using hm
    have hτ1 : (1 : Perm (Fin n)) = τ := hu 1 h1
    have huniq : ∀ σ : Perm (Fin n), Monotone (y ∘ σ) → σ = 1 := by
      intro σ hσ
      exact (hu σ hσ).trans hτ1.symm
    have hS : (∑ σ : Perm (Fin n), (orderingChamber n id).indicator D (y ∘ σ)) = D y := by
      calc
        _ = (orderingChamber n id).indicator D (y ∘ (1 : Perm (Fin n))) := by
          apply Finset.sum_eq_single 1
          · intro σ hσ hne
            have hn : y ∘ σ ∉ orderingChamber n id := fun h => hne (huniq σ h)
            simp only [Set.indicator_apply,ite_eq_right hn]
          · simp
        _ = D y := by
          have hm1 : y ∘ (1 : Perm (Fin n)) ∈ orderingChamber n id := by simpa [orderingChamber] using hm
          rw [Set.indicator_apply,ite_eq_left hm1]
          rfl
    rw [hS]
    calc
      _ = D y * ∑ σ : Perm (Fin n), permutationSign σ * G (y ∘ σ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [halt σ y]
        ring
      _ = _ := by rw [hGsum y (hm.strictMono_of_injective hy)]; ring
  by_cases hx : Function.Injective x
  · obtain ⟨τ,hτ,hu⟩ := existsUnique_sorted_coordinate_perm n id Function.injective_id x hx
    have hs := hsorted (x ∘ τ) (hx.comp τ.injective) hτ
    have hL := sum_coordinate_orbit (fun y => D y * G y) x τ
    have hR := sum_coordinate_orbit ((orderingChamber n id).indicator D) x τ
    exact hL.symm.trans (hs.trans (congrArg (fun z : ℂ => c*z) hR))
  · have hz : ∀ σ : Perm (Fin n), D (x ∘ σ) = 0 := by
      intro σ
      rw [halt σ x,hzero x hx,mul_zero]
    have hi : ∀ σ : Perm (Fin n), (orderingChamber n id).indicator D (x ∘ σ) = 0 := by
      intro σ
      by_cases hm : x ∘ σ ∈ orderingChamber n id
      · rw [Set.indicator_apply,ite_eq_left hm,hz σ]
      · simp only [Set.indicator_apply,ite_eq_right hm]
    simp only [hz,zero_mul,Finset.sum_const_zero,hi,mul_zero]

/-- Product-measure integral transport under the literal x∘σ map. -/
theorem integral_coordinatePerm (μ : Measure ℝ) [SigmaFinite μ] (n : ℕ)
    (F : (Fin n → ℝ) → ℂ) (σ : Perm (Fin n)) :
    (∫ x, F (x ∘ σ) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => μ) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have he : e = (fun x : Fin n → ℝ => x ∘ σ) := by
    funext x i
    have h := MeasurableEquiv.piCongrLeft_apply_apply σ.symm
      (β := fun _ : Fin n => ℝ) x (σ i)
    simpa only [e,Equiv.symm_apply_apply,Function.comp_def] using h
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => μ) σ.symm).integral_comp' F
  change (∫ x, F (e x) ∂Measure.pi (fun _ : Fin n => μ)) = _ at h
  simpa only [he] using h

/-- Complex-valued real averaging, with genuine L1 for every finite-sum term.
No diagonal-null premise, smoothness, or unproved sign identity is inserted. -/
theorem integral_alternating_pairSign (μ : Measure ℝ) [SigmaFinite μ]
    (n : ℕ) (D G : (Fin n → ℝ) → ℂ) (c : ℂ)
    (hD : Integrable D (Measure.pi (fun _ : Fin n => μ)))
    (hG : Measurable G) (hGb : ∀ x, ‖G x‖ ≤ 1)
    (halt : ∀ (σ : Perm (Fin n)) x, D (x ∘ σ) = permutationSign σ * D x)
    (hzero : ∀ x, ¬ Function.Injective x → D x = 0)
    (hGsum : ∀ x, StrictMono x →
      (∑ σ : Perm (Fin n), permutationSign σ * G (x ∘ σ)) = c) :
    (∫ x, D x * G x ∂Measure.pi (fun _ : Fin n => μ)) =
      c * ∫ x in orderingChamber n id, D x ∂Measure.pi (fun _ : Fin n => μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let S := orderingChamber n (id : ℝ → ℝ)
  have hS : MeasurableSet S := measurableSet_orderingChamber n id
    (by simpa only [id_eq] using measurableSet_le measurable_fst measurable_snd)
  have hDG : Integrable (fun x => D x * G x) ν :=
    hD.mul_bdd hG.aestronglyMeasurable (Filter.Eventually.of_forall hGb)
  have hSD : Integrable (S.indicator D) ν := hD.indicator hS
  have hIp (σ : Perm (Fin n)) : Integrable (fun x => D (x ∘ σ)*G (x ∘ σ)) ν :=
    (measurePreserving_coordinatePerm μ n σ).integrable_comp_of_integrable hDG
  have hIs (σ : Perm (Fin n)) : Integrable (fun x => S.indicator D (x ∘ σ)) ν :=
    (measurePreserving_coordinatePerm μ n σ).integrable_comp_of_integrable hSD
  have hIpint (σ : Perm (Fin n)) : (∫ x, D (x ∘ σ)*G (x ∘ σ) ∂ν) =
      ∫ x, D x*G x ∂ν := integral_coordinatePerm μ n (fun x => D x*G x) σ
  have hIsint (σ : Perm (Fin n)) : (∫ x, S.indicator D (x ∘ σ) ∂ν) =
      ∫ x, S.indicator D x ∂ν := integral_coordinatePerm μ n (S.indicator D) σ
  have hEq : (n.factorial : ℂ) * (∫ x, D x*G x ∂ν) =
      (n.factorial : ℂ) * (c * ∫ x in S, D x ∂ν) := by
    calc
      _ = ∑ σ : Perm (Fin n), ∫ x, D (x ∘ σ)*G (x ∘ σ) ∂ν := by
        simp only [hIpint,Finset.sum_const,
          Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
      _ = ∫ x, ∑ σ : Perm (Fin n), D (x ∘ σ)*G (x ∘ σ) ∂ν :=
        (integral_finsetSum Finset.univ (fun σ hσ => hIp σ)).symm
      _ = ∫ x, c * ∑ σ : Perm (Fin n), S.indicator D (x ∘ σ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sum_alternating_pairSign_orbit n D G c halt hzero hGsum x
      _ = c * ∑ σ : Perm (Fin n), ∫ x, S.indicator D (x ∘ σ) ∂ν := by
        rw [integral_const_mul,integral_finsetSum Finset.univ (fun σ hσ => hIs σ)]
      _ = _ := by
        simp only [hIsint,integral_indicator hS,
          Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
        ring
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  exact mul_left_cancel₀ hn hEq

/-- Literal product of sign differences for any explicitly specified real pairs. -/
def realPairSign {n r : ℕ} (p q : Fin r → Fin n) (x : Fin n → ℝ) : ℂ :=
  ∏ a : Fin r, (SignType.sign (x (q a)-x (p a)) : ℂ)

theorem measurable_realPairSign {n r : ℕ} (p q : Fin r → Fin n) :
    Measurable (realPairSign p q) := by
  apply Finset.measurable_prod
  intro a ha
  exact Paper.SkewOrthogonal.measurable_complex_sign.comp
    ((measurable_pi_apply (q a)).sub (measurable_pi_apply (p a)))

theorem norm_realPairSign_le_one {n r : ℕ} (p q : Fin r → Fin n) (x : Fin n → ℝ) :
    ‖realPairSign p q x‖ ≤ 1 := by
  rw [realPairSign,norm_prod]
  apply Finset.prod_le_one₀ (fun a ha => norm_nonneg _)
  intro a ha
  cases SignType.sign (x (q a)-x (p a)) <;> norm_num

/-- EVEN actual real-pair sign integration. -/
theorem integral_even_realPairSign (μ : Measure ℝ) [SigmaFinite μ] (r : ℕ)
    (D : (Fin (2*r) → ℝ) → ℂ)
    (hD : Integrable D (Measure.pi (fun _ : Fin (2*r) => μ)))
    (halt : ∀ (σ : Perm (Fin (2*r))) x, D (x ∘ σ) = permutationSign σ * D x)
    (hzero : ∀ x, ¬ Function.Injective x → D x = 0) :
    (∫ x, D x * realPairSign (fun a => PfaffianMinor.pairColumnEquiv r (a,0))
      (fun a => PfaffianMinor.pairColumnEquiv r (a,1)) x ∂Measure.pi (fun _ : Fin (2*r) => μ)) =
    ((2 : ℂ)^r * (r.factorial : ℂ)) *
      ∫ x in orderingChamber (2*r) id, D x ∂Measure.pi (fun _ : Fin (2*r) => μ) := by
  apply integral_alternating_pairSign μ (2*r) D _ _ hD
    (measurable_realPairSign _ _) (norm_realPairSign_le_one _ _) halt hzero
  intro x hx
  simpa only [realPairSign,Function.comp_def] using even_real_sign_antisymmetrization r x hx

/-- ODD actual real-pair sign integration, with the FIRST coordinate unpaired. -/
theorem integral_odd_realPairSign (μ : Measure ℝ) [SigmaFinite μ] (r : ℕ)
    (D : (Fin (2*r+1) → ℝ) → ℂ)
    (hD : Integrable D (Measure.pi (fun _ : Fin (2*r+1) => μ)))
    (halt : ∀ (σ : Perm (Fin (2*r+1))) x, D (x ∘ σ) = permutationSign σ * D x)
    (hzero : ∀ x, ¬ Function.Injective x → D x = 0) :
    (∫ x, D x * realPairSign (fun a => (PfaffianMinor.pairColumnEquiv r (a,0)).succ)
      (fun a => (PfaffianMinor.pairColumnEquiv r (a,1)).succ) x
        ∂Measure.pi (fun _ : Fin (2*r+1) => μ)) =
    ((2 : ℂ)^r * (r.factorial : ℂ)) *
      ∫ x in orderingChamber (2*r+1) id, D x ∂Measure.pi (fun _ : Fin (2*r+1) => μ) := by
  apply integral_alternating_pairSign μ (2*r+1) D _ _ hD
    (measurable_realPairSign _ _) (norm_realPairSign_le_one _ _) halt hzero
  intro x hx
  simpa only [realPairSign,Function.comp_def] using odd_real_sign_antisymmetrization_expanded r x hx

end Paper.Spectral
