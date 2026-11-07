/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.MeasureTheory.PiAdd
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Order.Interval.Finset.Fin
@[expose] public section
noncomputable section
open Set Equiv MeasureTheory
open scoped BigOperators
namespace MeasureTheory

/-- Extend two native equal-cardinality subtype equivalences to the whole finite
coordinate set. The permutation sends membership in T to membership in S. -/
theorem exists_perm_membership_of_card_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) (hc : S.card = T.card) :
    ∃ σ : Perm ι, ∀ i, σ i ∈ S ↔ i ∈ T := by
  classical
  have hc0 : Fintype.card {i : ι // i ∈ T} = Fintype.card {i : ι // i ∈ S} := by
    simpa only [Fintype.card_coe] using hc.symm
  let e0 : {i : ι // i ∈ T} ≃ {i : ι // i ∈ S} := Fintype.equivOfCardEq hc0
  let e1 : {i : ι // i ∉ T} ≃ {i : ι // i ∉ S} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_compl,hc0])
  let σ : Perm ι := ((Equiv.sumCompl (fun i => i ∈ T)).symm.trans
    (e0.sumCongr e1)).trans (Equiv.sumCompl (fun i => i ∈ S))
  refine ⟨σ,?_⟩
  intro i
  by_cases hi : i ∈ T
  · have he : σ i = (e0 ⟨i,hi⟩).val := by
      simp only [σ,Equiv.trans_apply,Equiv.sumCompl_symm_apply_of_pos hi,
        Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumCompl_apply_inl]
    simp only [he,(e0 ⟨i,hi⟩).property,hi]
  · have he : σ i = (e1 ⟨i,hi⟩).val := by
      simp only [σ,Equiv.trans_apply,Equiv.sumCompl_symm_apply_of_neg hi,
        Equiv.sumCongr_apply,Sum.map_inr,Equiv.sumCompl_apply_inr]
    simp only [he,(e1 ⟨i,hi⟩).property,hi]

/-- Symmetric complex-valued integrands have identical integrals in every sector
of the same cardinality. This is a bijective measure change, even for totalized
nonintegrable Bochner integrals; actual L1 is supplied separately by PiAdd. -/
theorem integral_selected_eq_of_card_eq {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → X) → ℂ) (hsym : ∀ (σ : Perm ι) x, F (x ∘ σ) = F x)
    (S T : Finset ι) (hc : S.card = T.card) :
    (∫ x, F x ∂Measure.pi (fun i : ι => if i ∈ S then ν else μ)) =
      ∫ x, F x ∂Measure.pi (fun i : ι => if i ∈ T then ν else μ) := by
  classical
  obtain ⟨σ,hσ⟩ := exists_perm_membership_of_card_eq S T hc
  let ρ : ι → Measure X := fun i => if i ∈ S then ν else μ
  have : ∀ i, SigmaFinite (ρ i) := fun i => by dsimp only [ρ]; split <;> infer_instance
  have hρ : (fun i => ρ (σ i)) = (fun i : ι => if i ∈ T then ν else μ) := by
    funext i
    simp only [ρ,hσ i]
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ
  have he : e = (fun x : ι → X => x ∘ σ.symm) := by
    funext x i
    have h := MeasurableEquiv.piCongrLeft_apply_apply σ
      (β := fun _ : ι => X) x (σ.symm i)
    simpa only [e,Equiv.apply_symm_apply,Function.comp_def] using h
  have hp := (measurePreserving_piCongrLeft ρ σ).integral_comp' F
  change (∫ x, F (e x) ∂Measure.pi (fun i => ρ (σ i))) = ∫ x, F x ∂Measure.pi ρ at hp
  rw [hρ] at hp
  simpa only [he,hsym,ρ] using hp.symm

/-- Canonical sector: the LAST l of m coordinates carry the complex measure. -/
def lastMixedMask (m : ℕ) (l : Fin (m+1)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => m-l.val ≤ i.val)

theorem card_lastMixedMask (m : ℕ) (l : Fin (m+1)) : (lastMixedMask m l).card = l.val := by
  classical
  by_cases hl : l.val = 0
  · rw [hl]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hm := (Finset.mem_filter.mp hi).2
    have hil := i.isLt
    simp only [hl,Nat.sub_zero] at hm
    omega
  · let a : Fin m := ⟨m-l.val,by have hlm := l.isLt; omega⟩
    have he : lastMixedMask m l = Finset.Ici a := by
      ext i
      simp only [lastMixedMask,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ici]
      rfl
    rw [he,Fin.card_Ici]
    dsimp only [a]
    have hlm := l.isLt
    omega

/-- Pure finite regrouping by cardinality, with exact binomial coefficients. -/
theorem sum_finset_eq_choose_lastMixedMask (m : ℕ) (H : Finset (Fin m) → ℂ)
    (hcard : ∀ S T, S.card = T.card → H S = H T) :
    (∑ S : Finset (Fin m), H S) =
      ∑ l : Fin (m+1), (m.choose l.val : ℂ) * H (lastMixedMask m l) := by
  classical
  let idx (S : Finset (Fin m)) : Fin (m+1) := ⟨S.card,by
    have h := Finset.card_le_univ S
    simpa only [Fintype.card_fin,Nat.lt_succ_iff] using h⟩
  have hgroup :
      (∑ l : Fin (m+1), ∑ S ∈ Finset.univ.filter (fun S => idx S = l), H S) =
        ∑ S : Finset (Fin m), H S :=
    Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := idx) (fun S hS => Finset.mem_univ (idx S)) H
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro l hl
  have hf : Finset.univ.filter (fun S : Finset (Fin m) => idx S = l) =
      Finset.univ.powersetCard l.val := by
    ext S
    simp [idx,Fin.ext_iff]
  rw [hf]
  calc
    _ = ∑ S ∈ Finset.univ.powersetCard l.val, H (lastMixedMask m l) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hcard S (lastMixedMask m l)
        ((Finset.mem_powersetCard.mp hS).2.trans (card_lastMixedMask m l).symm)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_powersetCard,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]

/-- The subset expansion grouped by the number of ν coordinates; all dimensions,
zero measures and endpoint sectors are included. -/
theorem integral_pi_add_eq_choose_lastMixedMask {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (m : ℕ)
    (F : (Fin m → X) → ℂ) (hF : Integrable F (Measure.pi (fun _ : Fin m => μ+ν)))
    (hsym : ∀ (σ : Perm (Fin m)) x, F (x ∘ σ) = F x) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin m => μ+ν)) =
      ∑ l : Fin (m+1), (m.choose l.val : ℂ) *
        ∫ x, F x ∂Measure.pi (fun i : Fin m => if i ∈ lastMixedMask m l then ν else μ) := by
  rw [integral_pi_add_eq_sum_selected μ ν F hF]
  apply sum_finset_eq_choose_lastMixedMask
  intro S T hc
  exact integral_selected_eq_of_card_eq μ ν F hsym S T hc

end MeasureTheory
