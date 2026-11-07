/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Actual kernel determinant and cycle integrals

These are integrals of the stated kernel, rather than definitions by a cycle
formula. The kernel can be complex and need not define a point process.
Pointwise bounds include the diagonal; an almost-everywhere bound for the
two-variable product measure alone would not suffice for one-cycles.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal Classical
namespace Paper.KernelIntegrals

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def kernelMatrix (K : Ω → Ω → ℂ) (x : ι → Ω) : Matrix ι ι ℂ :=
  fun i j => K (x i) (x j)

omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in
@[simp] theorem kernelMatrix_apply (K : Ω → Ω → ℂ) (x : ι → Ω) (i j : ι) :
    kernelMatrix K x i j = K (x i) (x j) := rfl

def permutationIntegrand (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) (x : ι → Ω) : ℂ :=
  ∏ i, K (x i) (x (σ i))

def permutationIntegral (μ : Measure Ω) (K : Ω → Ω → ℂ) (σ : Equiv.Perm ι) : ℂ :=
  ∫ x : ι → Ω, permutationIntegrand K σ x ∂Measure.pi (fun _ : ι => μ)

def determinantIntegral (μ : Measure Ω) (K : Ω → Ω → ℂ) (k : ℕ) : ℂ :=
  ∫ x : Fin k → Ω, Matrix.det (kernelMatrix K x)
    ∂Measure.pi (fun _ : Fin k => μ)

/-- The positive-order cyclic integral uses the canonical rotation. The value
at zero is an explicit internal extension and is never a zero-length cycle. -/
def cycleIntegral (μ : Measure Ω) (K : Ω → Ω → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else permutationIntegral μ K (finRotate m)

omit [DecidableEq ι] in
theorem measurable_permutationIntegrand (K : Ω → Ω → ℂ)
    (hK : Measurable (Function.uncurry K)) (σ : Equiv.Perm ι) :
    Measurable (permutationIntegrand K σ) := by
  unfold permutationIntegrand
  apply Finset.measurable_fun_prod
  intro i _
  have hp : Measurable (fun x : ι → Ω => (x i, x (σ i))) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (σ i))
  exact hK.comp hp

omit [MeasurableSpace Ω] [DecidableEq ι] in
theorem norm_permutationIntegrand_le (K : Ω → Ω → ℂ) (C : ℝ≥0)
    (hK : ∀ x y, ‖K x y‖ ≤ C) (σ : Equiv.Perm ι) (x : ι → Ω) :
    ‖permutationIntegrand K σ x‖ ≤ (C : ℝ) ^ Fintype.card ι := by
  unfold permutationIntegrand
  calc
    ‖∏ i, K (x i) (x (σ i))‖ ≤ ∏ i, ‖K (x i) (x (σ i))‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _i : ι, (C : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hK _ _)
    _ = (C : ℝ) ^ Fintype.card ι := by simp

omit [DecidableEq ι] in
theorem integrable_permutationIntegrand (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0) (hbound : ∀ x y, ‖K x y‖ ≤ C) (σ : Equiv.Perm ι) :
    Integrable (permutationIntegrand K σ) (Measure.pi (fun _ : ι => μ)) := by
  apply (integrable_const ((C : ℝ) ^ Fintype.card ι)).mono'
    (measurable_permutationIntegrand K hK σ).aestronglyMeasurable
  exact ae_of_all _ (norm_permutationIntegrand_le K C hbound σ)

omit [MeasurableSpace Ω] in
theorem determinant_integrand_eq (K : Ω → Ω → ℂ) (x : ι → Ω) :
    Matrix.det (kernelMatrix K x) =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * permutationIntegrand K σ x := by
  rw [← Matrix.det_transpose (kernelMatrix K x), Matrix.det_apply']
  rfl

theorem integrable_determinantIntegrand (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0) (hbound : ∀ x y, ‖K x y‖ ≤ C) :
    Integrable (fun x : ι → Ω => Matrix.det (kernelMatrix K x))
      (Measure.pi (fun _ : ι => μ)) := by
  simp_rw [determinant_integrand_eq]
  apply integrable_finsetSum
  intro σ _
  exact (integrable_permutationIntegrand μ K hK C hbound σ).const_mul _

theorem determinantIntegral_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0) (hbound : ∀ x y, ‖K x y‖ ≤ C) (k : ℕ) :
    determinantIntegral μ K k =
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℂ) * permutationIntegral μ K σ := by
  unfold determinantIntegral
  simp_rw [determinant_integrand_eq]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, permutationIntegral]
  · intro σ _
    exact (integrable_permutationIntegrand μ K hK C hbound σ).const_mul _

@[simp] theorem determinantIntegral_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) : determinantIntegral μ K 0 = 1 := by
  simp [determinantIntegral, Matrix.det_fin_zero, measureReal_def]

omit [DecidableEq ι] in
theorem permutationIntegral_one (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ) :
    permutationIntegral μ K (1 : Equiv.Perm ι) = (∫ x, K x x ∂μ) ^ Fintype.card ι := by
  simpa only [permutationIntegral, permutationIntegrand, Equiv.Perm.one_apply] using
    (integral_fintype_prod_eq_pow (ι := ι) (μ := μ) (fun x => K x x))

@[simp] theorem cycleIntegral_one (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ) :
    cycleIntegral μ K 1 = ∫ x, K x x ∂μ := by
  rw [cycleIntegral, ite_eq_right (by decide), finRotate_one]
  change permutationIntegral μ K (1 : Equiv.Perm (Fin 1)) = _
  simpa using permutationIntegral_one (ι := Fin 1) μ K

theorem determinantIntegral_one (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Ω → ℂ) :
    determinantIntegral μ K 1 = cycleIntegral μ K 1 := by
  unfold determinantIntegral
  simp only [Matrix.det_fin_one, kernelMatrix_apply]
  rw [cycleIntegral_one]
  simpa only [Fintype.prod_unique, Fintype.card_fin, pow_one,
    show (default : Fin 1) = 0 from Subsingleton.elim _ _] using
    (integral_fintype_prod_eq_pow (ι := Fin 1) (μ := μ) (fun x => K x x))

omit [DecidableEq ι] in
theorem permutationIntegral_conj (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Ω → ℂ) (σ τ : Equiv.Perm ι) :
    permutationIntegral μ K (τ * σ * τ⁻¹) = permutationIntegral μ K σ := by
  have hp (x : ι → Ω) :
      permutationIntegrand K (τ * σ * τ⁻¹) x =
        permutationIntegrand K σ ((MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) τ.symm) x) := by
    have he (i : ι) : (MeasurableEquiv.piCongrLeft (fun _ : ι => Ω) τ.symm) x i = x (τ i) := by
      simpa using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => Ω) τ.symm x (τ i)
    simp only [permutationIntegrand, he]
    symm
    calc
      (∏ i, K (x (τ i)) (x (τ (σ i)))) =
          ∏ i, K (x (τ i)) (x ((τ * σ * τ⁻¹) (τ i))) := by
        simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      _ = ∏ i, K (x i) (x ((τ * σ * τ⁻¹) i)) :=
        Equiv.prod_comp (τ : ι ≃ ι) (fun i => K (x i) (x ((τ * σ * τ⁻¹) i)))
  unfold permutationIntegral
  simp_rw [hp]
  exact (measurePreserving_piCongrLeft (fun _ : ι => μ) τ.symm).integral_comp' _

end Paper.KernelIntegrals
