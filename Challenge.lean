/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Main CLT statement

Source: the local manuscript associated with arXiv:2306.10243, Theorem 1.3.
The model and hypotheses are complete. This independent statement file imports
only canonical Mathlib modules; its single deliberate proof hole is compared
with the proved Paper.principalTheorem in Solution.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Paper

def LipschitzBoundaryChart (A : Set ℂ) (p : ℂ) : Prop :=
  ∃ (c : ℂ) (r h : ℝ) (K : ℝ≥0) (f : ℝ → ℝ),
    ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧
    LipschitzOnWith K f (Set.Ioo (-r) r) ∧ f 0 = 0 ∧
    (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ,
      |(c * (w - p)).re| < r →
      |(c * (w - p)).im| < h →
      (w ∈ A ↔ f (c * (w - p)).re < (c * (w - p)).im)

/-- IsConnected includes nonemptiness. No simple-connectivity requirement. -/
def IsAdmissibleLipschitzDomain (A : Set ℂ) : Prop :=
  IsOpen A ∧ IsConnected A ∧
    closure A ⊆ {z : ℂ | ‖z‖ < 1 ∧ 0 < z.im} ∧
    ∀ p ∈ frontier A, LipschitzBoundaryChart A p

/-- Physical matrix size is N=n+1, covering every positive integer. -/
abbrev SampleSpace (n : ℕ) := Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ

def matrixLaw (n : ℕ) : Measure (SampleSpace n) :=
  Measure.pi fun _ : Fin (n + 1) ↦
    Measure.pi fun _ : Fin (n + 1) ↦ ProbabilityTheory.gaussianReal 0 1

instance matrixLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (matrixLaw n) := by
  unfold matrixLaw
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin (n + 1) ↦
      Measure.pi (fun _ : Fin (n + 1) ↦ ProbabilityTheory.gaussianReal 0 1)) :
      Measure (Fin (n + 1) → Fin (n + 1) → ℝ))
  infer_instance

def scaledMatrix (n : ℕ) (M : SampleSpace n) : SampleSpace n :=
  (Real.sqrt (n + 1 : ℝ))⁻¹ • M

/-- Algebraic multiplicities are retained; no eigenvalue ordering is chosen. -/
def eigenvalues (n : ℕ) (M : SampleSpace n) : Multiset ℂ :=
  ((scaledMatrix n M).charpoly.map Complex.ofRealHom).roots

def count (A : Set ℂ) (n : ℕ) (M : SampleSpace n) : ℕ := by
  classical
  exact ((eigenvalues n M).filter (· ∈ A)).card

def meanCount (A : Set ℂ) (n : ℕ) : ℝ :=
  ∫ M, (count A n M : ℝ) ∂matrixLaw n

def statistic (A : Set ℂ) (n : ℕ) (M : SampleSpace n) : ℝ :=
  ((count A n M : ℝ) - meanCount A n) / (n + 1 : ℝ) ^ (1 / 4 : ℝ)

/-- Euclidean, length-normalized Hausdorff measure on the complex plane. -/
def boundaryMeasure (A : Set ℂ) : ℝ≥0∞ :=
  (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A)

def varianceOfLength (ell : ℝ≥0) : ℝ≥0 :=
  ell / (2 * Real.pi ^ (3 / 2 : ℝ)).toNNReal

/-- Geometric conclusion: finite positive length, not an extra domain
hypothesis. The measure equality fixes ell uniquely. -/
def BoundaryLengthRegular (A : Set ℂ) : Prop :=
  ∃ ell : ℝ≥0, (ell : ℝ≥0∞) = boundaryMeasure A ∧ 0 < ell

/-- Including finite positive length prevents an infinite-measure-to-zero
conversion from hiding a degenerate Gaussian. -/
def MainConclusion (A : Set ℂ) : Prop :=
  ∃ ell : ℝ≥0, (ell : ℝ≥0∞) = boundaryMeasure A ∧ 0 < ell ∧
    TendstoInDistribution (statistic A) atTop (fun x : ℝ ↦ x) matrixLaw
      (ProbabilityTheory.gaussianReal 0 (varianceOfLength ell))

/-- The main CLT proposition. -/
def PrincipalStatement : Prop :=
  ∀ A : Set ℂ, IsAdmissibleLipschitzDomain A → MainConclusion A

/-- Main CLT for admissible Lipschitz domains, through every positive matrix size. -/
theorem principalTheorem : PrincipalStatement := by
  sorry

end Paper
