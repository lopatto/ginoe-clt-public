/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurWordFamily
public import GinoeClt.Spectral.SchurAngularFactorization
public import GinoeClt.Spectral.SchurRegularSpectrum
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Matrix ENNReal BigOperators
namespace Paper.Spectral

/-- Actual sector-volume identity with common angular mass and the whole-atlas
multiplicity. The word-dependent raw free integral is displayed completely. -/
theorem schurAtlasImageOfSize_lintegral_factor {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (g : ((Fin N × Fin N) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin N) ℝ)
      (M : Matrix (Fin N) (Fin N) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M))
    (w : SchurWordsOfSize N) :
    ((2^w.val.length : ℕ) : ℝ≥0∞) *
      (∫⁻ y in schurAtlasImageOfSize centers w, g y) =
    ENNReal.ofReal (boundedAtlasAngularMass centers) *
      ∫⁻ u in schurWordFreeSource w.val,
        ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val
          (schurWordFreeCells w.val u))| *
        g (schurCellsCast w.property
          (Matrix.vec (schurWordParameter w.val (schurWordFreeCells w.val u)))) := by
  rcases w with ⟨w,h⟩
  subst N
  change ((2^w.length : ℕ) : ℝ≥0∞) *
      (∫⁻ y in id '' ⋃ i, (fun x => schurAtlasCells w centers (i,x)) ''
        {x | schurAtlasSimpleSource w centers (i,x)}, g y) =
    ENNReal.ofReal (boundedAtlasAngularMass centers) *
      ∫⁻ u in schurWordFreeSource w,
        ENNReal.ofReal |LinearMap.det (schurWordDifferential w (schurWordFreeCells w u))| *
        g (Matrix.vec (schurWordParameter w (schurWordFreeCells w u)))
  rw [Set.image_id]
  exact (schurAtlasSimpleSource_lintegral w centers hcover g hg).symm.trans
    (sum_schurAtlasSimpleSource_lintegral_factor w centers g hg hginv)

/-- Divide only by the explicit finite nonzero gauge count, never by an
uncomputed angular/Haar normalization. Zero or infinite free integrals are allowed. -/
theorem lintegral_schurAtlasImageOfSize_eq {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (g : ((Fin N × Fin N) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin N) ℝ)
      (M : Matrix (Fin N) (Fin N) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M))
    (w : SchurWordsOfSize N) :
    (∫⁻ y in schurAtlasImageOfSize centers w, g y) =
    (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ *
      (ENNReal.ofReal (boundedAtlasAngularMass centers) *
        ∫⁻ u in schurWordFreeSource w.val,
          ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val
            (schurWordFreeCells w.val u))| *
          g (schurCellsCast w.property
            (Matrix.vec (schurWordParameter w.val (schurWordFreeCells w.val u))))) := by
  have hd : ((2^w.val.length : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (pow_ne_zero w.val.length (by norm_num : (2 : ℕ) ≠ 0))
  have ht : ((2^w.val.length : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [← schurAtlasImageOfSize_lintegral_factor centers hcover g hg hginv w,
    ← mul_assoc, ENNReal.inv_mul_cancel hd ht, one_mul]

/-- Complete geometric Schur integration for invariant nonnegative weights:
one ordinary matrix integral, one finite family of genuine free-cell integrals,
and one actual finite positive angular factor shared by every word. -/
theorem lintegral_eq_angularMass_mul_sum_schurFree {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (g : ((Fin N × Fin N) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin N) ℝ)
      (M : Matrix (Fin N) (Fin N) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M)) :
    (∫⁻ y, g y) =
      ENNReal.ofReal (boundedAtlasAngularMass centers) *
        ∑ w : SchurWordsOfSize N,
          (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ *
          ∫⁻ u in schurWordFreeSource w.val,
            ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val
              (schurWordFreeCells w.val u))| *
            g (schurCellsCast w.property
              (Matrix.vec (schurWordParameter w.val (schurWordFreeCells w.val u)))) := by
  rw [lintegral_eq_sum_schurAtlasImageOfSize centers hcover]
  simp_rw [lintegral_schurAtlasImageOfSize_eq centers hcover g hg hginv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact mul_left_comm _ _ _

/-- Geometric Schur formula over ORIGINAL positivity and ordering alone.
Regularity and simplicity masks are removed by their proved zero determinant weight. -/
theorem lintegral_eq_angularMass_mul_sum_schurPositive {N m : ℕ}
    (centers : Fin (m+1) → Matrix.orthogonalGroup (Fin N) ℝ)
    (hcover : ∀ M : Matrix (Fin N) (Fin N) ℝ, M * Mᵀ = 1 →
      M ∈ ⋃ i, boundedOrthogonalCayleyNeighborhood N (centers i))
    (g : ((Fin N × Fin N) → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (Q : Matrix.orthogonalGroup (Fin N) ℝ)
      (M : Matrix (Fin N) (Fin N) ℝ),
      g (Matrix.vec ((Q : Matrix _ _ ℝ) * M * (Q : Matrix _ _ ℝ)ᵀ)) = g (Matrix.vec M)) :
    (∫⁻ y, g y) =
      ENNReal.ofReal (boundedAtlasAngularMass centers) *
        ∑ w : SchurWordsOfSize N,
          (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ *
          ∫⁻ u in {v | SchurWordPositive w.val (schurWordFreeCells w.val v) ∧
              SchurWordOrdered w.val (schurWordFreeCells w.val v)},
            ENNReal.ofReal |LinearMap.det (schurWordDifferential w.val
              (schurWordFreeCells w.val u))| *
            g (schurCellsCast w.property
              (Matrix.vec (schurWordParameter w.val (schurWordFreeCells w.val u)))) := by
  rw [lintegral_eq_angularMass_mul_sum_schurFree centers hcover g hg hginv]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  exact congrArg (fun z : ℝ≥0∞ => (((2^w.val.length : ℕ) : ℝ≥0∞))⁻¹ * z)
    (lintegral_schurWordFreeSource_eq_positive_ordered w.val
      (fun x => g (schurCellsCast w.property x)))

end Paper.Spectral
