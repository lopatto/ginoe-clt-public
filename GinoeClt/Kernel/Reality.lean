/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Kernel.Restriction

/-! # Reality of actual Hermitian-kernel determinant and cycle integrals -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace Paper.Kernel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace Ω] in
theorem conj_det_kernelMatrix (K : Ω → Ω → ℂ)
    (hHerm : ∀ x y, K y x = conj (K x y)) (x : ι → Ω) :
    conj (Matrix.det (KernelIntegrals.kernelMatrix K x)) =
      Matrix.det (KernelIntegrals.kernelMatrix K x) := by
  have hm : (KernelIntegrals.kernelMatrix K x).conjTranspose =
      KernelIntegrals.kernelMatrix K x := by
    ext i j
    exact (hHerm (x j) (x i)).symm
  have hh := Matrix.det_conjTranspose (KernelIntegrals.kernelMatrix K x)
  rw [hm] at hh
  exact hh.symm

theorem conj_determinantIntegral (μ : Measure Ω) (K : Ω → Ω → ℂ)
    (hHerm : ∀ x y, K y x = conj (K x y)) (k : ℕ) :
    conj (KernelIntegrals.determinantIntegral μ K k) =
      KernelIntegrals.determinantIntegral μ K k := by
  unfold KernelIntegrals.determinantIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ (conj_det_kernelMatrix K hHerm)

omit [MeasurableSpace Ω] [DecidableEq ι] in
theorem conj_permutationIntegrand (K : Ω → Ω → ℂ)
    (hHerm : ∀ x y, K y x = conj (K x y)) (σ : Equiv.Perm ι) (x : ι → Ω) :
    conj (KernelIntegrals.permutationIntegrand K σ x) =
      KernelIntegrals.permutationIntegrand K σ⁻¹ x := by
  unfold KernelIntegrals.permutationIntegrand
  rw [map_prod]
  calc
    _ = ∏ i, K (x (σ i)) (x i) :=
      Finset.prod_congr rfl fun i _ => (hHerm (x i) (x (σ i))).symm
    _ = ∏ i, K (x i) (x (σ⁻¹ i)) := by
      simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        Equiv.prod_comp (σ : ι ≃ ι) (fun i => K (x i) (x (σ⁻¹ i)))

theorem conj_permutationIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (hHerm : ∀ x y, K y x = conj (K x y)) (σ : Equiv.Perm ι) :
    conj (KernelIntegrals.permutationIntegral μ K σ) =
      KernelIntegrals.permutationIntegral μ K σ := by
  unfold KernelIntegrals.permutationIntegral
  rw [← integral_conj]
  simp_rw [conj_permutationIntegrand K hHerm]
  change KernelIntegrals.permutationIntegral μ K σ⁻¹ =
    KernelIntegrals.permutationIntegral μ K σ
  rw [KernelIntegrals.permutationIntegral_eq_cycleType μ K σ⁻¹,
    KernelIntegrals.permutationIntegral_eq_cycleType μ K σ, Equiv.Perm.cycleType_inv]

theorem conj_cycleIntegral (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (hHerm : ∀ x y, K y x = conj (K x y)) (m : ℕ) :
    conj (KernelIntegrals.cycleIntegral μ K m) = KernelIntegrals.cycleIntegral μ K m := by
  unfold KernelIntegrals.cycleIntegral
  split_ifs
  · exact map_zero _
  · exact conj_permutationIntegral μ K hHerm _

theorem im_eq_zero_of_conj_eq {z : ℂ} (hz : conj z = z) : z.im = 0 := by
  have hh := congrArg Complex.im hz
  simp only [Complex.conj_im] at hh
  linarith

end Paper.Kernel
