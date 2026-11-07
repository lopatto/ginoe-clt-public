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
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Matrix model, domain definition and CLT interfaces

These definitions specify the real Gaussian ensemble, admissible Lipschitz
domains and main conclusion. The proof of PrincipalStatement is provided by
Paper.principalTheorem in SkewOrthogonal.CountPfaffianIdentity.

The local rectangular graph presentation follows the standard planar Lipschitz
definition. Compare Quanyu Tang, RequestProject/Defs.lean at
f07f1c7051862ba146429db6eda5dc4e8b020f74 (Apache-2.0); here Lipschitz continuity
is required only on the chart interval.
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

/-- The main CLT proposition, proved by Paper.principalTheorem. -/
def PrincipalStatement : Prop :=
  ∀ A : Set ℂ, IsAdmissibleLipschitzDomain A → MainConclusion A

def moment (A : Set ℂ) (n r : ℕ) : ℝ :=
  ∫ M, statistic A n M ^ r ∂matrixLaw n

/-- Analytic cumulants are derivatives of log MGF at zero. -/
def cumulant (A : Set ℂ) (n r : ℕ) : ℝ :=
  iteratedDeriv r (ProbabilityTheory.cgf (statistic A n) (matrixLaw n)) 0

/-- Set-partition moment polynomial; the empty partition has product one. -/
def momentPolynomial (r : ℕ) (kappa : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ P : Finpartition (Finset.univ : Finset (Fin r)),
    ∏ B ∈ P.parts, kappa B.card

def pairCumulant (v : ℝ≥0) (r : ℕ) : ℝ :=
  if r = 2 then (v : ℝ) else 0

/-- Measurability interface: measurable real-valued multiplicity count. -/
def CountMeasurable (A : Set ℂ) : Prop :=
  ∀ n, Measurable (fun M : SampleSpace n ↦ (count A n M : ℝ))

/-- Moment interface: normalized-count moments are genuinely integrable. -/
def AllMoments (A : Set ℂ) : Prop :=
  ∀ n r, Integrable (fun M : SampleSpace n ↦ statistic A n M ^ r) (matrixLaw n)

/-- Moment-cumulant interface: analytic cumulants satisfy the finite partition identity. -/
def MomentCumulantIdentity (A : Set ℂ) : Prop :=
  ∀ n r, moment A n r = momentPolynomial r (cumulant A n)

/-- Cumulant-limit interface for the manuscript's determinant,
pseudo-cumulant and trace arguments. -/
def CumulantLimits (A : Set ℂ) (ell : ℝ≥0) : Prop :=
  ∀ r, 1 ≤ r →
    Tendsto (fun n ↦ cumulant A n r) atTop
      (𝓝 (pairCumulant (varianceOfLength ell) r))

/-- Gaussian moment interface: Gaussian moments in pair-partition form. -/
def GaussianPartitionMoments : Prop :=
  ∀ (v : ℝ≥0) (r : ℕ),
    (∫ x : ℝ, x ^ r ∂ProbabilityTheory.gaussianReal 0 v) =
      momentPolynomial r (pairCumulant v)

/-- Gaussian convergence criterion: a general criterion for arbitrary real random variables on
arbitrary indexed probability spaces. This is not a claim about GinOE counts.
Compare Billingsley (1995), Thms30.1-30.2. Not an approved external assumption. -/
def GaussianMomentCriterion : Prop :=
  ∀ (Ω : ℕ → Type) [_mΩ : ∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [_hP : ∀ n, IsProbabilityMeasure (P n)]
    (X : (n : ℕ) → Ω n → ℝ) (v : ℝ≥0),
    0 < v →
    (∀ n, AEMeasurable (X n) (P n)) →
    (∀ n r, Integrable (fun x ↦ X n x ^ r) (P n)) →
    (∀ r, Tendsto (fun n ↦ ∫ x, X n x ^ r ∂P n) atTop
      (𝓝 (∫ x : ℝ, x ^ r ∂ProbabilityTheory.gaussianReal 0 v))) →
    TendstoInDistribution X atTop (fun x : ℝ ↦ x) P
      (ProbabilityTheory.gaussianReal 0 v)

end Paper
