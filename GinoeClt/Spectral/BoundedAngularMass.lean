/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.BoundedOrthogonalCharts
public import GinoeClt.Spectral.CayleyAngular
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
namespace Paper.Spectral

/-- Actual native angular coordinates in the bounded ambient relative chart. -/
def boundedAngularSource (N : ℕ) : Set (SkewIndex N → ℝ) :=
  (fun a => (skewFromCoordinates N a : Matrix (Fin N) (Fin N) ℝ)) ⁻¹'
    (boundedCayleyLocalHomeomorph N).source

theorem isOpen_boundedAngularSource (N : ℕ) : IsOpen (boundedAngularSource N) :=
  (boundedCayleyLocalHomeomorph N).open_source.preimage
    (continuous_skewFromCoordinates_matrix N)

theorem zero_mem_boundedAngularSource (N : ℕ) : (0 : SkewIndex N → ℝ) ∈ boundedAngularSource N := by
  have hz : skewFromCoordinates N (0 : SkewIndex N → ℝ) = 0 :=
    (skewCoordinateEquiv N).map_zero
  change (skewFromCoordinates N (0 : SkewIndex N → ℝ) : Matrix (Fin N) (Fin N) ℝ) ∈
    (boundedCayleyLocalHomeomorph N).source
  rw [hz]
  exact zero_mem_boundedCayleyLocalHomeomorph_source N

/-- Every actual angle is a lower matrix entry bounded by the ambient unit-ball norm.
This is an ordinary norm bound, not a volume normalization. -/
theorem isBounded_boundedAngularSource (N : ℕ) : Bornology.IsBounded (boundedAngularSource N) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1,?_⟩
  intro a ha
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro p
  have hΩ : ‖(skewFromCoordinates N a : Matrix (Fin N) (Fin N) ℝ)‖ < 1 :=
    boundedCayley_source_norm_lt_one N _ ha
  have hr := congrFun (skewCoordinates_fromCoordinates N a) p
  change (skewFromCoordinates N a : Matrix (Fin N) (Fin N) ℝ) p.val.2 p.val.1 = a p at hr
  rw [←hr]
  exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans hΩ.le

/-- Continuous densities are genuinely integrable on bounded finite-dimensional sets. -/
theorem integrableOn_bounded_pi_of_continuous {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (S : Set (ι → ℝ))
    (hS : Bornology.IsBounded S) : IntegrableOn f S volume := by
  have hc : IsCompact (closure S) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hS.closure
  exact (ContinuousOn.integrableOn_compact hc hf.continuousOn).mono_set subset_closure

/-- A globally positive integrable density has positive integral on a nonempty open set. -/
theorem setIntegral_pos_pi_of_positive {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (S : Set (ι → ℝ)) (hS : IsOpen S) (hne : S.Nonempty)
    (hf : ∀ x, 0 < f x) (hi : IntegrableOn f S volume) : 0 < ∫ x in S, f x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hf x).le) hi).mpr
  have hs : Function.support f = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hf x).ne'
  rw [hs, Measure.restrict_apply_univ]
  exact IsOpen.measure_pos volume hS hne

theorem integrableOn_boundedAngularJacobian (N : ℕ) :
    IntegrableOn (fun a : SkewIndex N → ℝ => cayleyAngularJacobian N (skewFromCoordinates N a))
      (boundedAngularSource N) volume :=
  integrableOn_bounded_pi_of_continuous _ (continuous_cayleyAngularJacobian_coordinates N) _
    (isBounded_boundedAngularSource N)

/-- The mass of one actual bounded relative angular chart. -/
def boundedAngularMass (N : ℕ) : ℝ :=
  ∫ a in boundedAngularSource N, cayleyAngularJacobian N (skewFromCoordinates N a)

theorem boundedAngularMass_pos (N : ℕ) : 0 < boundedAngularMass N :=
  setIntegral_pos_pi_of_positive _ _ (isOpen_boundedAngularSource N)
    ⟨0,zero_mem_boundedAngularSource N⟩
    (fun a => cayleyAngularJacobian_pos N (skewFromCoordinates N a))
    (integrableOn_boundedAngularJacobian N)

end Paper.Spectral
