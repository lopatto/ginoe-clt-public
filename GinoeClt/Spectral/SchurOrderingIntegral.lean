/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace Paper.Spectral

/-- Weakly ordered chamber for an arbitrary injective ordering key. -/
def orderingChamber {α β : Type*} [Preorder β] (k : ℕ) (key : α → β) : Set (Fin k → α) :=
  {x | Monotone (key ∘ x)}

/-- A genuine finite sorting permutation, unique when all coordinates are distinct.
The construction sorts the actual finite image, without any choice of ordering on α. -/
theorem existsUnique_sorted_coordinate_perm {α β : Type*} [LinearOrder β]
    (k : ℕ) (key : α → β) (hkey : Function.Injective key)
    (x : Fin k → α) (hx : Function.Injective x) :
    ∃! σ : Equiv.Perm (Fin k), Monotone (fun i => key (x (σ i))) := by
  classical
  let f : Fin k → β := key ∘ x
  have hf : Function.Injective f := hkey.comp hx
  let s : Finset β := Finset.univ.image f
  have hc : s.card = k := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  let e : Fin k ≃ s := Equiv.ofBijective
    (fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨(fun i j h => hf (congrArg Subtype.val h)),by
      rintro ⟨b,hb⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hb
      exact ⟨i,Subtype.ext hi⟩⟩
  let o : Fin k ≃o s := s.orderIsoOfFin hc
  let σ : Equiv.Perm (Fin k) := o.toEquiv.trans e.symm
  have hσ (i : Fin k) : f (σ i) = (o i).val :=
    congrArg Subtype.val (e.apply_symm_apply (o i))
  have hm : Monotone (fun i => key (x (σ i))) := by
    intro i j hij
    change f (σ i) ≤ f (σ j)
    rw [hσ i,hσ j]
    exact o.monotone hij
  refine ⟨σ,hm,?_⟩
  intro τ hτ
  have hstrict : StrictMono (fun i => f (τ i)) :=
    hτ.strictMono_of_injective (hf.comp τ.injective)
  have heq : (fun i => f (τ i)) = s.orderEmbOfFin hc :=
    Finset.orderEmbOfFin_unique hc
      (fun i => Finset.mem_image.mpr ⟨τ i,Finset.mem_univ _,rfl⟩) hstrict
  apply Equiv.ext
  intro i
  apply hf
  exact (congrFun heq i).trans (hσ i).symm

/-- Exact POINTWISE sorted-permutation count, including the empty coordinate family. -/
theorem card_sorted_coordinate_perms {α β : Type*} [LinearOrder β]
    (k : ℕ) (key : α → β) (hkey : Function.Injective key)
    (x : Fin k → α) (hx : Function.Injective x) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) =>
      Monotone (fun i => key (x (σ i))))).card = 1 := by
  classical
  obtain ⟨σ,hσ,hu⟩ := existsUnique_sorted_coordinate_perm k key hkey x hx
  have he : Finset.univ.filter (fun τ : Equiv.Perm (Fin k) =>
      Monotone (fun i => key (x (τ i)))) = {σ} := by
    ext τ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨hu τ,fun h => h.symm ▸ hσ⟩
  rw [he,Finset.card_singleton]

/-- Only measurability of the BINARY ordering relation is required.
In particular this does not impose the order topology on Lex(ℝ×ℝ). -/
theorem measurableSet_orderingChamber {α β : Type*} [MeasurableSpace α] [Preorder β]
    (k : ℕ) (key : α → β)
    (hrel : MeasurableSet {z : α × α | key z.1 ≤ key z.2}) :
    MeasurableSet (orderingChamber k key) := by
  have he : orderingChamber k key =
      ⋂ i : Fin k, ⋂ j : Fin k, ⋂ (_h : i ≤ j), {x | key (x i) ≤ key (x j)} := by
    ext x
    simp only [orderingChamber,Monotone,Set.mem_ofPred_eq,Set.mem_iInter,Function.comp_def]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact hrel.preimage (show Measurable (fun x : Fin k → α => (x i,x j)) from by fun_prop)

/-- Unique sorting supplies one term; on repeated inputs every term is genuinely
zero by the explicit zero-weight hypothesis, even if F is infinite elsewhere. -/
theorem sum_orderingChamber_indicator {α β : Type*} [LinearOrder β]
    (k : ℕ) (key : α → β) (hkey : Function.Injective key)
    (F : (Fin k → α) → ℝ≥0∞)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬ Function.Injective x → F x = 0) (x : Fin k → α) :
    (∑ σ : Equiv.Perm (Fin k), (orderingChamber k key).indicator F (x ∘ σ)) = F x := by
  classical
  by_cases hx : Function.Injective x
  · obtain ⟨σ,hσ,hu⟩ := existsUnique_sorted_coordinate_perm k key hkey x hx
    calc
      _ = (orderingChamber k key).indicator F (x ∘ σ) := by
        apply Finset.sum_eq_single σ
        · intro τ _ hne
          have hn : x ∘ τ ∉ orderingChamber k key := fun h => hne (hu τ h)
          simp only [Set.indicator_apply,ite_eq_right hn]
        · simp
      _ = F x := by
        have hm : x ∘ σ ∈ orderingChamber k key := hσ
        rw [Set.indicator_apply,ite_eq_left hm]
        exact hsym σ x
  · have hz := hzero x hx
    calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro σ _
        by_cases hm : x ∘ σ ∈ orderingChamber k key
        · rw [Set.indicator_apply,ite_eq_left hm]
          exact (hsym σ x).trans hz
        · simp only [Set.indicator_apply,ite_eq_right hm]
      _ = F x := hz.symm

/-- Product measure is invariant under the literal coordinate permutation x∘σ. -/
theorem measurePreserving_coordinatePerm {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    MeasurePreserving (fun x : Fin k → α => x ∘ σ)
      (Measure.pi (fun _ : Fin k => μ)) (Measure.pi (fun _ : Fin k => μ)) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin k => μ) σ.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin k => α) σ.symm) =
      (fun x : Fin k → α => x ∘ σ) := by
    funext x i
    have h := MeasurableEquiv.piCongrLeft_apply_apply σ.symm
      (β := fun _ : Fin k => α) x (σ i)
    simpa only [Equiv.symm_apply_apply,Function.comp_def] using h
  simpa only [he] using h

/-- Symmetric nonnegative Borel integration over one ordered chamber.
No atomless/diagonal-null premise or finite-integral premise is used. -/
theorem lintegral_symmetric_eq_factorial_orderingChamber {α β : Type*}
    [MeasurableSpace α] [LinearOrder β] (μ : Measure α) [SigmaFinite μ]
    (k : ℕ) (key : α → β) (hkey : Function.Injective key)
    (hrel : MeasurableSet {z : α × α | key z.1 ≤ key z.2})
    (F : (Fin k → α) → ℝ≥0∞) (hF : Measurable F)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬ Function.Injective x → F x = 0) :
    (∫⁻ x, F x ∂Measure.pi (fun _ : Fin k => μ)) =
      (k.factorial : ℝ≥0∞) *
        ∫⁻ x in orderingChamber k key, F x ∂Measure.pi (fun _ : Fin k => μ) := by
  classical
  have hS := measurableSet_orderingChamber k key hrel
  have hI : Measurable ((orderingChamber k key).indicator F) := hF.indicator hS
  have hi (σ : Equiv.Perm (Fin k)) :
      (∫⁻ x, (orderingChamber k key).indicator F (x ∘ σ)
        ∂Measure.pi (fun _ : Fin k => μ)) =
      ∫⁻ x in orderingChamber k key, F x ∂Measure.pi (fun _ : Fin k => μ) := by
    rw [← lintegral_indicator hS]
    exact (measurePreserving_coordinatePerm μ k σ).lintegral_comp hI
  calc
    _ = ∫⁻ x, ∑ σ : Equiv.Perm (Fin k), (orderingChamber k key).indicator F (x ∘ σ)
        ∂Measure.pi (fun _ : Fin k => μ) :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun x =>
        (sum_orderingChamber_indicator k key hkey F hsym hzero x).symm)
    _ = ∑ σ : Equiv.Perm (Fin k), ∫⁻ x, (orderingChamber k key).indicator F (x ∘ σ)
        ∂Measure.pi (fun _ : Fin k => μ) :=
      lintegral_finsetSum Finset.univ (fun σ _ => hI.comp (by fun_prop))
    _ = _ := by
      simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]

end Paper.Spectral
