/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Spectral.Continuity
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurability of multiplicity counts

Continuous symmetric spectral sums are continuous even at eigenvalue collisions.
Approximating an open-set indicator by continuous functions therefore gives
measurability of the actual root-multiset count, without a simplicity assumption.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators NNReal Classical
namespace Paper.Spectral

def spectralSum (n : ℕ) (f : ℂ → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, f (matrixAllEigenvalues n M i)

theorem continuous_spectralSum (n : ℕ) (f : ℂ → ℝ) (hf : Continuous f) :
    Continuous (spectralSum n f) := by
  apply continuous_matrixFullSymmetricSpectralLift n
    (fun z : Fin n → ℂ => ∑ i, f (z i))
  · exact continuous_finsetSum _ fun i _ => hf.comp (continuous_apply i)
  · intro e z
    exact e.sum_comp (fun i => f (z i))

theorem count_roots_eq_sum (A : Set ℂ) (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((M.charpoly.roots.filter (· ∈ A)).card : ℝ) =
      ∑ i : Fin n, if matrixAllEigenvalues n M i ∈ A then (1 : ℝ) else 0 := by
  classical
  rw [← matrix_full_roots_configuration_multiset M (matrixAllEigenvalues n M)
    (matrixAllEigenvalues_charpoly n M)]
  rw [Multiset.filter_map, Multiset.card_map, ← Finset.filter_val]
  change (((Finset.univ.filter fun i => matrixAllEigenvalues n M i ∈ A).card : ℕ) : ℝ) = _
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem measurable_count_roots_of_isOpen (A : Set ℂ) (hA : IsOpen A) (n : ℕ) :
    Measurable (fun M : Matrix (Fin n) (Fin n) ℂ =>
      ((M.charpoly.roots.filter (· ∈ A)).card : ℝ)) := by
  classical
  let f : ℕ → ℂ → ℝ := fun m z =>
    1 - ((hA.isClosed_compl.apprSeq m z : ℝ≥0) : ℝ)
  have hf (m : ℕ) : Continuous (f m) :=
    continuous_const.sub (NNReal.continuous_coe.comp
      (hA.isClosed_compl.apprSeq m).continuous)
  have hlim (z : ℂ) :
      Tendsto (fun m => f m z) atTop (𝓝 (if z ∈ A then (1 : ℝ) else 0)) := by
    have hc := tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq
      hA.isClosed_compl) z
    have hr := NNReal.continuous_coe.continuousAt.tendsto.comp hc
    by_cases hz : z ∈ A <;>
      simpa [f, Set.indicator, hz] using (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  apply measurable_of_tendsto_metrizable
    (fun m => (continuous_spectralSum n (f m) (hf m)).measurable)
  rw [tendsto_pi_nhds]
  intro M
  rw [count_roots_eq_sum A n M]
  exact tendsto_finsetSum _ fun i _ => hlim (matrixAllEigenvalues n M i)

end Paper.Spectral

namespace Paper

/-- The actual algebraic-multiplicity count is measurable on every open domain,
including matrices with repeated eigenvalues. -/
theorem countMeasurable_of_isOpen (A : Set ℂ) (hA : IsOpen A) :
    CountMeasurable A := by
  intro n
  have hc : Continuous (fun M : SampleSpace n =>
      (scaledMatrix n M).map Complex.ofRealHom) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun M : SampleSpace n =>
      Complex.ofReal ((Real.sqrt (n + 1 : ℝ))⁻¹ * M i j))
    exact Complex.continuous_ofReal.comp
      (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
  have hm := (Spectral.measurable_count_roots_of_isOpen A hA (n + 1)).comp hc.measurable
  simpa only [Function.comp_def, Matrix.charpoly_map, count, eigenvalues] using hm

end Paper
