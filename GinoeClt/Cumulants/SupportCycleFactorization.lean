/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.KernelCycleIntegrals
public import Mathlib.GroupTheory.Perm.Fin

/-! # Factorization of actual permutation integrals by support -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal Classical

namespace Paper.KernelIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem permutationIntegral_reindex (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (e : ι ≃ κ) (σ : Equiv.Perm ι) :
    permutationIntegral μ K (e.permCongr σ) = permutationIntegral μ K σ := by
  have hp (x : κ → Ω) :
      permutationIntegrand K (e.permCongr σ) x =
        permutationIntegrand K σ ((MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e.symm) x) := by
    have he (i : ι) :
        (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) e.symm) x i = x (e i) := by
      simpa using MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : ι => Ω) e.symm x (e i)
    simp only [permutationIntegrand, he]
    symm
    calc
      (∏ i, K (x (e i)) (x (e (σ i)))) =
          ∏ i, K (x (e i)) (x (e.permCongr σ (e i))) := by
        simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      _ = ∏ i, K (x i) (x (e.permCongr σ i)) :=
        Equiv.prod_comp e (fun i => K (x i) (x (e.permCongr σ i)))
  unfold permutationIntegral
  simp_rw [hp]
  exact (measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm).integral_comp' _

theorem permutationIntegral_split (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) (p : ι → Prop) [DecidablePred p]
    (hp : ∀ i, p (σ i) ↔ p i) :
    permutationIntegral μ K σ =
      permutationIntegral μ K (σ.subtypePerm hp) *
        permutationIntegral μ K (σ.subtypePerm (p := fun i => ¬ p i) (fun i => not_congr (hp i))) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) p
  have hi (x : ι → Ω) :
      permutationIntegrand K σ x =
        permutationIntegrand K (σ.subtypePerm hp) (e x).1 *
          permutationIntegrand K (σ.subtypePerm (p := fun i => ¬ p i) (fun i => not_congr (hp i))) (e x).2 := by
    change (∏ i, K (x i) (x (σ i))) =
      (∏ i : {i // p i}, K (x i) (x (σ i))) *
        ∏ i : {i // ¬ p i}, K (x i) (x (σ i))
    exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => K (x i) (x (σ i)))).symm
  unfold permutationIntegral
  simp_rw [hi]
  calc
    _ = ∫ z, permutationIntegrand K (σ.subtypePerm hp) z.1 *
        permutationIntegrand K (σ.subtypePerm (p := fun i => ¬ p i)
          (fun i => not_congr (hp i))) z.2
        ∂(Measure.pi (fun _ : {i // p i} => μ)).prod
          (Measure.pi (fun _ : {i // ¬ p i} => μ)) :=
      (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) p).integral_comp' _
    _ = _ := integral_prod_mul _ _

variable [DecidableEq ι]

/-- The integral over precisely the moved coordinates. -/
def supportIntegral (μ : Measure Ω) (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) : ℂ :=
  permutationIntegral μ K σ.subtypePermOfSupport

theorem permutationIntegral_eq_supportIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) :
    permutationIntegral μ K σ =
      supportIntegral μ K σ *
        (cycleIntegral μ K 1) ^ (Fintype.card ι - σ.support.card) := by
  rw [permutationIntegral_split μ K σ (fun i => i ∈ σ.support)
    (fun _ => Equiv.Perm.apply_mem_support)]
  have hf : σ.subtypePerm (p := fun i => i ∉ σ.support) (fun i => not_congr
      (Equiv.Perm.apply_mem_support (f := σ) (x := i))) = 1 := by
    ext i
    exact Equiv.Perm.notMem_support.mp i.property
  rw [hf, permutationIntegral_one, cycleIntegral_one,
    Fintype.card_subtype_compl, Fintype.card_coe]
  congr 1
  unfold supportIntegral Equiv.Perm.subtypePermOfSupport
  congr 1
  exact Subsingleton.elim _ _

@[simp] theorem supportIntegral_one (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) : supportIntegral μ K (1 : Equiv.Perm ι) = 1 := by
  unfold supportIntegral
  have h : (1 : Equiv.Perm ι).subtypePermOfSupport = 1 := by
    ext i
    rfl
  rw [h, permutationIntegral_one]
  simp


omit [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq ι] in
theorem isCycle_permCongr (e : ι ≃ κ) (σ : Equiv.Perm ι) (hσ : σ.IsCycle) :
    (e.permCongr σ).IsCycle := by
  obtain ⟨a, ha, h⟩ := hσ
  refine ⟨e a, ?_, fun b hb => ?_⟩
  · simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, ne_eq,
      Equiv.apply_eq_iff_eq] using ha
  · have hb' : σ (e.symm b) ≠ e.symm b := by
      intro hh
      apply hb
      simp only [Equiv.permCongr_apply, hh, Equiv.apply_symm_apply]
    obtain ⟨n, hn⟩ := h hb'
    refine ⟨n, ?_⟩
    have hz := (map_zpow e.permCongrHom σ n).symm
    change ((e.permCongr σ) ^ n) (e a) = b
    change (e.permCongr σ) ^ n = e.permCongr (σ ^ n) at hz
    rw [hz]
    simp only [Equiv.permCongr_apply,
      Equiv.symm_apply_apply, hn, Equiv.apply_symm_apply]

theorem supportIntegral_of_isCycle (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) (hσ : σ.IsCycle) :
    supportIntegral μ K σ = cycleIntegral μ K σ.support.card := by
  let e := Fintype.equivFin σ.support
  have hc : σ.subtypePermOfSupport.IsCycle := by
    have hh : σ.IsCycleOn (σ.support : Set ι) := by
      simpa only [Equiv.Perm.coe_support_eq_set_support] using hσ.isCycleOn
    exact hh.isCycle_subtypePerm
      (Finset.one_lt_card_iff_nontrivial.mp hσ.two_le_card_support)
  have hec : (e.permCongr σ.subtypePermOfSupport).IsCycle :=
    isCycle_permCongr e _ hc
  have hs : (e.permCongr σ.subtypePermOfSupport).support = Finset.univ := by
    ext i
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true,
      Equiv.permCongr_apply, ne_eq]
    intro h
    have hi := congrArg e.symm h
    have hx := (e.symm i).property
    apply Equiv.Perm.mem_support.mp hx
    simpa only [Equiv.symm_apply_apply, Equiv.Perm.subtypePermOfSupport,
      Equiv.Perm.subtypePerm_apply, Subtype.ext_iff] using hi
  have hm : 2 ≤ Fintype.card σ.support := by
    simpa only [Fintype.card_coe] using hσ.two_le_card_support
  have ht : (e.permCongr σ.subtypePermOfSupport).cycleType =
      (finRotate (Fintype.card σ.support)).cycleType := by
    rw [hec.cycleType, hs, Finset.card_univ, Fintype.card_fin,
      cycleType_finRotate_of_le hm]
  obtain ⟨τ, hτ⟩ := _root_.isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq ht)
  unfold supportIntegral
  rw [← permutationIntegral_reindex μ K e]
  have hr : cycleIntegral μ K σ.support.card =
      permutationIntegral μ K (finRotate (Fintype.card σ.support)) := by
    rw [cycleIntegral,
      ite_eq_right (by have := hσ.two_le_card_support; omega : σ.support.card ≠ 0),
      Fintype.card_coe]
  rw [hr, ← hτ, permutationIntegral_conj]


omit [DecidableEq ι] in
theorem permutationIntegral_equiv (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (e : ι ≃ κ) (σ : Equiv.Perm ι) (τ : Equiv.Perm κ)
    (h : ∀ i, e (σ i) = τ (e i)) :
    permutationIntegral μ K σ = permutationIntegral μ K τ := by
  have he : e.permCongr σ = τ := by
    ext i
    simpa only [Equiv.permCongr_apply, Equiv.apply_symm_apply] using h (e.symm i)
  rw [← he, permutationIntegral_reindex]

theorem supportIntegral_mul_of_disjoint (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ τ : Equiv.Perm ι) (hd : Equiv.Perm.Disjoint σ τ) :
    supportIntegral μ K (σ * τ) = supportIntegral μ K σ * supportIntegral μ K τ := by
  let p : (σ * τ).support → Prop := fun x => (x : ι) ∈ σ.support
  have hp : ∀ x, p ((σ * τ).subtypePermOfSupport x) ↔ p x := by
    intro x
    change (σ * τ) (x : ι) ∈ σ.support ↔ (x : ι) ∈ σ.support
    rw [Equiv.Perm.mul_apply, Equiv.Perm.apply_mem_support]
    exact Equiv.Perm.mem_support_iff_of_commute hd.commute.symm _
  let eL : {x : (σ * τ).support // p x} ≃ σ.support :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, by rw [hd.support_mul]; exact Finset.mem_union_left _ x.property⟩,
        x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  let eR : {x : (σ * τ).support // ¬ p x} ≃ τ.support :=
    { toFun := fun x => ⟨x.val.val, by
        have hx := x.val.property
        have hu : x.val.val ∈ σ.support ∨ x.val.val ∈ τ.support := by
          simpa only [hd.support_mul, Finset.mem_union] using hx
        exact hu.resolve_left x.property⟩
      invFun := fun x => ⟨⟨x.val, by rw [hd.support_mul]; exact Finset.mem_union_right _ x.property⟩,
        hd.symm.mem_imp x.property⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  unfold supportIntegral
  rw [permutationIntegral_split μ K _ p hp]
  congr 1
  · apply permutationIntegral_equiv μ K eL
    intro x
    apply Subtype.ext
    change σ (τ x.val.val) = σ x.val.val
    rw [Equiv.Perm.notMem_support.mp (hd.mem_imp x.property)]
  · apply permutationIntegral_equiv μ K eR
    intro x
    apply Subtype.ext
    change σ (τ x.val.val) = τ x.val.val
    exact Equiv.Perm.notMem_support.mp
      (hd.symm.mem_imp (Equiv.Perm.apply_mem_support.mpr (eR x).property))

theorem supportIntegral_eq_cycleType (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) :
    supportIntegral μ K σ =
      (σ.cycleType.map (fun m => cycleIntegral μ K m)).prod := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simp [Equiv.Perm.cycleType_one]
  | base_cycles σ hσ =>
    rw [supportIntegral_of_isCycle μ K σ hσ, hσ.cycleType,
      Multiset.map_singleton, Multiset.prod_singleton]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [supportIntegral_mul_of_disjoint μ K σ τ hd, hd.cycleType_mul,
      Multiset.map_add, Multiset.prod_add, hσ, hτ]

/-- Actual permutation integrals factor over every cycle, including fixed points.
No trace is divided out, so the identity includes kernels with zero diagonal integral. -/
theorem permutationIntegral_eq_cycleType (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) :
    permutationIntegral μ K σ =
      (cycleIntegral μ K 1) ^ (Fintype.card ι - σ.cycleType.sum) *
        (σ.cycleType.map (fun m => cycleIntegral μ K m)).prod := by
  rw [permutationIntegral_eq_supportIntegral, supportIntegral_eq_cycleType,
    Equiv.Perm.sum_cycleType, mul_comm]

theorem determinantIntegral_eq_cycleType_sum (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0) (hbound : ∀ x y, ‖K x y‖ ≤ C) (k : ℕ) :
    determinantIntegral μ K k =
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ((cycleIntegral μ K 1) ^ (k - σ.cycleType.sum) *
          (σ.cycleType.map (fun m => cycleIntegral μ K m)).prod) := by
  rw [determinantIntegral_eq_sum μ K hK C hbound k]
  apply Finset.sum_congr rfl
  intro σ _
  rw [permutationIntegral_eq_cycleType, Fintype.card_fin]

end Paper.KernelIntegrals
