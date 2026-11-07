/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.MeasureTheory.SymmetricMixedSectors
public import GinoeClt.SkewOrthogonal.DeBruijnPairMeasure
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MeasureTheory

/-- Literal first-real/last-complex coordinate concatenation; no root or pair reordering. -/
def appendMappedCoordinates {A B Y : Type*} (r l : ℕ) (f : A → Y) (g : B → Y)
    (p : (Fin r → A) × (Fin l → B)) : Fin (r+l) → Y :=
  Fin.append (f ∘ p.1) (g ∘ p.2)

/-- A direct rectangle calculation gives scalar ONE for ordinary product measures. -/
theorem measurePreserving_appendMappedCoordinates {A B Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (f : A → Y) (g : B → Y) (hf : Measurable f) (hg : Measurable g)
    [SigmaFinite (μ.map f)] [SigmaFinite (ν.map g)] (r l : ℕ) :
    MeasurePreserving (appendMappedCoordinates r l f g)
      ((Measure.pi (fun _ : Fin r => μ)).prod (Measure.pi (fun _ : Fin l => ν)))
      (Measure.pi (fun i : Fin (r+l) => if r ≤ i.val then ν.map g else μ.map f)) := by
  have hC : Measurable (appendMappedCoordinates r l f g) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [appendMappedCoordinates,Fin.append_left,Function.comp_def] using
        hf.comp ((measurable_pi_apply a).comp measurable_fst)
    · simpa only [appendMappedCoordinates,Fin.append_right,Function.comp_def] using
        hg.comp ((measurable_pi_apply b).comp measurable_snd)
  have : ∀ i : Fin (r+l), SigmaFinite (if r ≤ i.val then ν.map g else μ.map f) := fun i => by
    split <;> infer_instance
  refine ⟨hC,?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have he : (appendMappedCoordinates r l f g) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (fun a : Fin r => f ⁻¹' s (Fin.castAdd l a))) ×ˢ
      (Set.pi Set.univ (fun b : Fin l => g ⁻¹' s (Fin.natAdd r b))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_univ_pi,Set.mem_prod]
    constructor
    · intro hp
      constructor
      · intro a
        simpa only [appendMappedCoordinates,Fin.append_left,Function.comp_def] using hp (Fin.castAdd l a)
      · intro b
        simpa only [appendMappedCoordinates,Fin.append_right,Function.comp_def] using hp (Fin.natAdd r b)
    · rintro ⟨ha,hb⟩ i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · simpa only [appendMappedCoordinates,Fin.append_left,Function.comp_def] using ha a
      · simpa only [appendMappedCoordinates,Fin.append_right,Function.comp_def] using hb b
  rw [Measure.map_apply hC (MeasurableSet.univ_pi hs),he,Measure.prod_prod,
    Measure.pi_pi,Measure.pi_pi,Fin.prod_univ_add]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro a ha
    have hcut : ¬ r ≤ (Fin.castAdd l a).val := not_le_of_gt a.isLt
    rw [ite_eq_right hcut,Measure.map_apply hf (hs (Fin.castAdd l a))]
  · apply Finset.prod_congr rfl
    intro b hb
    have hcut : r ≤ (Fin.natAdd r b).val := by change r ≤ r+b.val; omega
    rw [ite_eq_left hcut,Measure.map_apply hg (hs (Fin.natAdd r b))]

/-- Genuine L1 transport, established before using Fubini. -/
theorem integrable_appendMappedCoordinates {A B Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (f : A → Y) (g : B → Y) (hf : Measurable f) (hg : Measurable g)
    [SigmaFinite (μ.map f)] [SigmaFinite (ν.map g)] (r l : ℕ)
    (F : (Fin (r+l) → Y) → ℂ)
    (hF : Integrable F (Measure.pi (fun i : Fin (r+l) => if r ≤ i.val then ν.map g else μ.map f))) :
    Integrable (fun p => F (appendMappedCoordinates r l f g p))
      ((Measure.pi (fun _ : Fin r => μ)).prod (Measure.pi (fun _ : Fin l => ν))) :=
  (measurePreserving_appendMappedCoordinates μ ν f g hf hg r l).integrable_comp_of_integrable hF

/-- Canonical mapped-sector integral equals the ordinary separate product integral.
No extra measurability of F is required: its actual L1 supplies AE strong measurability. -/
theorem integral_appendMappedCoordinates {A B Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (f : A → Y) (g : B → Y) (hf : Measurable f) (hg : Measurable g)
    [SigmaFinite (μ.map f)] [SigmaFinite (ν.map g)] (r l : ℕ)
    (F : (Fin (r+l) → Y) → ℂ)
    (hF : Integrable F (Measure.pi (fun i : Fin (r+l) => if r ≤ i.val then ν.map g else μ.map f))) :
    (∫ x, F x ∂Measure.pi (fun i : Fin (r+l) => if r ≤ i.val then ν.map g else μ.map f)) =
      ∫ a : Fin r → A, ∫ b : Fin l → B,
        F (Fin.append (f ∘ a) (g ∘ b)) ∂Measure.pi (fun _ : Fin l => ν)
          ∂Measure.pi (fun _ : Fin r => μ) := by
  have hm := measurePreserving_appendMappedCoordinates μ ν f g hf hg r l
  have hL1 := integrable_appendMappedCoordinates μ ν f g hf hg r l F hF
  have hFM : AEStronglyMeasurable F
      (((Measure.pi (fun _ : Fin r => μ)).prod (Measure.pi (fun _ : Fin l => ν))).map
        (appendMappedCoordinates r l f g)) := by
    rw [hm.map_eq]
    exact hF.aestronglyMeasurable
  calc
    _ = ∫ p, F (appendMappedCoordinates r l f g p)
        ∂((Measure.pi (fun _ : Fin r => μ)).prod (Measure.pi (fun _ : Fin l => ν))) := by
      rw [← hm.map_eq]
      exact integral_map hm.measurable.aemeasurable hFM
    _ = _ := integral_prod _ hL1

/-- Exact LAST-l mask, including its dimension cast. The source is the ordinary
A^r × B^l product and r+l=m; no symmetry is required of the integrand. -/
theorem lastMixedMask_inl_inr_transport {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (r l m : ℕ) (h : r+l=m) (F : (Fin m → A ⊕ B) → ℂ)
    (hF : Integrable F (Measure.pi (fun i : Fin m =>
      if i ∈ lastMixedMask m ⟨l,by omega⟩ then ν.map Sum.inr else μ.map Sum.inl))) :
    Integrable (fun p : (Fin r → A) × (Fin l → B) => F (fun i : Fin m =>
      Fin.append (Sum.inl ∘ p.1) (Sum.inr ∘ p.2) (Fin.cast h.symm i)))
        ((Measure.pi (fun _ : Fin r => μ)).prod (Measure.pi (fun _ : Fin l => ν))) ∧
    (∫ x, F x ∂Measure.pi (fun i : Fin m =>
      if i ∈ lastMixedMask m ⟨l,by omega⟩ then ν.map Sum.inr else μ.map Sum.inl)) =
      ∫ a : Fin r → A, ∫ b : Fin l → B, F (fun i : Fin m =>
        Fin.append (Sum.inl ∘ a) (Sum.inr ∘ b) (Fin.cast h.symm i))
          ∂Measure.pi (fun _ : Fin l => ν) ∂Measure.pi (fun _ : Fin r => μ) := by
  classical
  have hf : MeasurableEmbedding (@Sum.inl A B) :=
    ⟨Sum.inl_injective,measurable_inl,fun s hs => hs.inl_image⟩
  have hg : MeasurableEmbedding (@Sum.inr A B) :=
    ⟨Sum.inr_injective,measurable_inr,fun s hs => hs.inr_image⟩
  have : SigmaFinite (μ.map (@Sum.inl A B)) := hf.sigmaFinite_map
  have : SigmaFinite (ν.map (@Sum.inr A B)) := hg.sigmaFinite_map
  subst m
  have hmask : (fun i : Fin (r+l) => if i ∈ lastMixedMask (r+l) ⟨l,by omega⟩
      then ν.map (@Sum.inr A B) else μ.map (@Sum.inl A B)) =
      (fun i : Fin (r+l) => if r ≤ i.val then ν.map Sum.inr else μ.map Sum.inl) := by
    funext i
    simp [lastMixedMask]
  rw [hmask] at hF ⊢
  constructor
  · simpa only [appendMappedCoordinates,Fin.cast_eq_self] using
      integrable_appendMappedCoordinates μ ν Sum.inl Sum.inr hf.measurable hg.measurable r l F hF
  · simpa only [Fin.cast_eq_self] using
      integral_appendMappedCoordinates μ ν Sum.inl Sum.inr hf.measurable hg.measurable r l F hF

end MeasureTheory

namespace Paper.SkewOrthogonal

/-- The ACTUAL real-pair/upper-area sector transport, with ordinary volumes. -/
theorem deBruijn_lastMixedMask_transport (m : ℕ) (l : Fin (m+1))
    (F : (Fin m → ((ℝ × ℝ) ⊕ ℂ)) → ℂ)
    (hF : Integrable F (Measure.pi (fun i : Fin m =>
      if i ∈ lastMixedMask m l then
        ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
      else (volume : Measure (ℝ × ℝ)).map Sum.inl))) :
    Integrable (fun p : (Fin (m-l.val) → ℝ × ℝ) × (Fin l.val → ℂ) =>
      F (fun i : Fin m => Fin.append (Sum.inl ∘ p.1) (Sum.inr ∘ p.2)
        (Fin.cast (Nat.sub_add_cancel (Nat.le_of_lt_succ l.isLt)).symm i)))
      ((Measure.pi (fun _ : Fin (m-l.val) => (volume : Measure (ℝ × ℝ)))).prod
        (Measure.pi (fun _ : Fin l.val => (volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}))) ∧
    (∫ x, F x ∂Measure.pi (fun i : Fin m =>
      if i ∈ lastMixedMask m l then
        ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).map Sum.inr
      else (volume : Measure (ℝ × ℝ)).map Sum.inl)) =
      ∫ a : Fin (m-l.val) → ℝ × ℝ, ∫ b : Fin l.val → ℂ,
        F (fun i : Fin m => Fin.append (Sum.inl ∘ a) (Sum.inr ∘ b)
          (Fin.cast (Nat.sub_add_cancel (Nat.le_of_lt_succ l.isLt)).symm i))
        ∂Measure.pi (fun _ : Fin l.val => (volume : Measure ℂ).restrict {z : ℂ | 0 < z.im})
          ∂Measure.pi (fun _ : Fin (m-l.val) => (volume : Measure (ℝ × ℝ))) :=
  lastMixedMask_inl_inr_transport volume (volume.restrict {z : ℂ | 0 < z.im})
    (m-l.val) l.val m (Nat.sub_add_cancel (Nat.le_of_lt_succ l.isLt)) F hF

end Paper.SkewOrthogonal
