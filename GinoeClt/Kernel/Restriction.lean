/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.KernelCycleCumulants

/-! # Pointwise masking and normalization of actual kernel integrals -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal Classical

namespace Paper.Kernel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι]

/-- Mask in both variables. Its bounds include all diagonal points. -/
def maskKernel (A : Set Ω) (K : Ω → Ω → ℂ) (x y : Ω) : ℂ :=
  if x ∈ A ∧ y ∈ A then K x y else 0

omit [MeasurableSpace Ω] in
theorem maskKernel_eq_of_mem (A : Set Ω) (K : Ω → Ω → ℂ) {x y : Ω}
    (hx : x ∈ A) (hy : y ∈ A) : maskKernel A K x y = K x y := by
  simp only [maskKernel, hx, hy, and_self, ite_true]

theorem measurable_maskKernel (A : Set Ω) (hA : MeasurableSet A)
    (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (maskKernel A K)) := by
  have he : Function.uncurry (maskKernel A K) =
      (A ×ˢ A).indicator (Function.uncurry K) := by
    funext x
    simp only [Function.uncurry, maskKernel, Set.indicator, Set.mem_prod_eq]
    split_ifs with h <;> simp [h]
  rw [he]
  exact hK.indicator (hA.prod hA)

omit [MeasurableSpace Ω] in
theorem norm_maskKernel_le (A : Set Ω) (K : Ω → Ω → ℂ) (C : ℝ≥0)
    (hK : ∀ x ∈ A, ∀ y ∈ A, ‖K x y‖ ≤ C) (x y : Ω) :
    ‖maskKernel A K x y‖ ≤ C := by
  by_cases h : x ∈ A ∧ y ∈ A
  · rw [maskKernel, ite_eq_left h]
    exact hK x h.1 y h.2
  · rw [maskKernel, ite_eq_right h, norm_zero]
    exact C.coe_nonneg

theorem ae_coords_mem (μ : Measure Ω) [SigmaFinite μ] (A : Set Ω) (hA : MeasurableSet A) :
    ∀ᵐ x : ι → Ω ∂Measure.pi (fun _ : ι => μ.restrict A), ∀ i, x i ∈ A :=
  Filter.eventually_all.mpr fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => μ.restrict A) (i := i)).eventually
      (ae_restrict_mem hA)

theorem permutationIntegral_mask (μ : Measure Ω) [SigmaFinite μ]
    (A : Set Ω) (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) :
    KernelIntegrals.permutationIntegral (μ.restrict A) (maskKernel A K) σ =
      KernelIntegrals.permutationIntegral (μ.restrict A) K σ := by
  unfold KernelIntegrals.permutationIntegral
  apply integral_congr_ae
  filter_upwards [ae_coords_mem (ι := ι) μ A hA] with x hx
  unfold KernelIntegrals.permutationIntegrand
  apply Finset.prod_congr rfl
  intro i _
  exact maskKernel_eq_of_mem A K (hx i) (hx (σ i))

theorem determinantIntegral_mask (μ : Measure Ω) [SigmaFinite μ]
    (A : Set Ω) (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (k : ℕ) :
    KernelIntegrals.determinantIntegral (μ.restrict A) (maskKernel A K) k =
      KernelIntegrals.determinantIntegral (μ.restrict A) K k := by
  unfold KernelIntegrals.determinantIntegral
  apply integral_congr_ae
  filter_upwards [ae_coords_mem (ι := Fin k) μ A hA] with x hx
  congr 1
  ext i j
  exact maskKernel_eq_of_mem A K (hx i) (hx j)

theorem cycleIntegral_mask (μ : Measure Ω) [SigmaFinite μ]
    (A : Set Ω) (hA : MeasurableSet A) (K : Ω → Ω → ℂ) (m : ℕ) :
    KernelIntegrals.cycleIntegral (μ.restrict A) (maskKernel A K) m =
      KernelIntegrals.cycleIntegral (μ.restrict A) K m := by
  unfold KernelIntegrals.cycleIntegral
  split_ifs
  · rfl
  · exact permutationIntegral_mask μ A hA K _

theorem permutationIntegral_const_mul (μ : Measure Ω) (K : Ω → Ω → ℂ)
    (c : ℂ) (σ : Equiv.Perm ι) :
    KernelIntegrals.permutationIntegral μ (fun x y => c * K x y) σ =
      c ^ Fintype.card ι * KernelIntegrals.permutationIntegral μ K σ := by
  unfold KernelIntegrals.permutationIntegral KernelIntegrals.permutationIntegrand
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  exact integral_const_mul _ _

theorem determinantIntegral_const_mul (μ : Measure Ω) (K : Ω → Ω → ℂ)
    (c : ℂ) (k : ℕ) :
    KernelIntegrals.determinantIntegral μ (fun x y => c * K x y) k =
      c ^ k * KernelIntegrals.determinantIntegral μ K k := by
  have hm (x : Fin k → Ω) : KernelIntegrals.kernelMatrix (fun z w => c * K z w) x =
      c • KernelIntegrals.kernelMatrix K x := by
    ext i j
    rfl
  unfold KernelIntegrals.determinantIntegral
  simp_rw [hm, Matrix.det_smul, Fintype.card_fin]
  exact integral_const_mul _ _

theorem cycleIntegral_const_mul (μ : Measure Ω) (K : Ω → Ω → ℂ)
    (c : ℂ) (m : ℕ) :
    KernelIntegrals.cycleIntegral μ (fun x y => c * K x y) m =
      c ^ m * KernelIntegrals.cycleIntegral μ K m := by
  unfold KernelIntegrals.cycleIntegral
  split_ifs
  · simp
  · simpa only [Fintype.card_fin] using permutationIntegral_const_mul μ K c (finRotate m)

end Paper.Kernel
