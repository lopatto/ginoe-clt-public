/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

import Solution

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-! Independent principal-type and essential-definition contract checks. -/

example :
    Paper.PrincipalStatement ↔
      ∀ A : Set ℂ, Paper.IsAdmissibleLipschitzDomain A →
        ∃ ell : ℝ≥0,
          (ell : ℝ≥0∞) =
            (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) ∧
          0 < ell ∧
          TendstoInDistribution (Paper.statistic A) atTop (fun x : ℝ ↦ x)
            Paper.matrixLaw
            (ProbabilityTheory.gaussianReal 0
              (ell / (2 * Real.pi ^ (3 / 2 : ℝ)).toNNReal)) := by
  simp only [Paper.PrincipalStatement, Paper.MainConclusion, Paper.boundaryMeasure,
    Paper.varianceOfLength]

example (A : Set ℂ) :
    Paper.IsAdmissibleLipschitzDomain A ↔
      IsOpen A ∧ IsConnected A ∧
        closure A ⊆ {z : ℂ | ‖z‖ < 1 ∧ 0 < z.im} ∧
        ∀ p ∈ frontier A, Paper.LipschitzBoundaryChart A p := by
  simp only [Paper.IsAdmissibleLipschitzDomain]

example (A : Set ℂ) (p : ℂ) :
    Paper.LipschitzBoundaryChart A p ↔
      ∃ (c : ℂ) (r h : ℝ) (K : ℝ≥0) (f : ℝ → ℝ),
        ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧
        LipschitzOnWith K f (Set.Ioo (-r) r) ∧ f 0 = 0 ∧
        (∀ x : ℝ, |x| < r → |f x| < h) ∧
        ∀ w : ℂ,
          |(c * (w - p)).re| < r →
          |(c * (w - p)).im| < h →
          (w ∈ A ↔ f (c * (w - p)).re < (c * (w - p)).im) := by
  simp only [Paper.LipschitzBoundaryChart]

example (n : ℕ) :
    Paper.matrixLaw n =
      (Measure.pi (fun _ : Fin (n + 1) ↦
        Measure.pi (fun _ : Fin (n + 1) ↦ ProbabilityTheory.gaussianReal 0 1)) :
        Measure (Paper.SampleSpace n)) := by
  simp only [Paper.matrixLaw]
  congr 1

example (n : ℕ) (M : Paper.SampleSpace n) (i j : Fin (n + 1)) :
    Paper.scaledMatrix n M i j = M i j / Real.sqrt (n + 1 : ℝ) := by
  simp [Paper.scaledMatrix, div_eq_mul_inv, mul_comm]

example (A : Set ℂ) (n : ℕ) (M : Paper.SampleSpace n) :
    Paper.count A n M =
      (by
        classical
        exact ((((Real.sqrt (n + 1 : ℝ))⁻¹ • M).charpoly.map
          Complex.ofRealHom).roots.filter (· ∈ A)).card) := by
  classical
  simp only [Paper.count, Paper.eigenvalues, Paper.scaledMatrix]

example (A : Set ℂ) (n : ℕ) :
    Paper.meanCount A n =
      ∫ M, (Paper.count A n M : ℝ) ∂Paper.matrixLaw n := by
  simp only [Paper.meanCount]


example (A : Set ℂ) (n : ℕ) (M : Paper.SampleSpace n) :
    Paper.statistic A n M =
      ((Paper.count A n M : ℝ) -
        ∫ X : Paper.SampleSpace n, (Paper.count A n X : ℝ) ∂Paper.matrixLaw n) /
          (n+1 : ℝ) ^ (1/4 : ℝ) := by
  simp only [Paper.statistic,Paper.meanCount]

example (A : Set ℂ) :
    Paper.boundaryMeasure A =
      (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) := rfl

example (ell : ℝ≥0) :
    (Paper.varianceOfLength ell : ℝ) =
      (ell : ℝ) / (2 * Real.pi ^ (3/2 : ℝ)) :=
  Paper.varianceOfLength_coe ell

-- Independent, explicit expected principal type: no intermediate-law hypothesis.
example :
    ∀ A : Set ℂ,
      (IsOpen A ∧ IsConnected A ∧
        closure A ⊆ {z : ℂ | ‖z‖ < 1 ∧ 0 < z.im} ∧
        ∀ p ∈ frontier A, Paper.LipschitzBoundaryChart A p) →
      ∃ ell : ℝ≥0,
        (ell : ℝ≥0∞) =
          (Measure.hausdorffMeasure 1 : Measure ℂ) (frontier A) ∧
        0 < ell ∧
        TendstoInDistribution (Paper.statistic A) atTop (fun x : ℝ ↦ x)
          Paper.matrixLaw
          (ProbabilityTheory.gaussianReal 0
            (ell / (2 * Real.pi ^ (3 / 2 : ℝ)).toNNReal)) :=
  @Paper.mainTheorem_unconditional

example : Paper.PrincipalStatement := Paper.principalTheorem

#print axioms Paper.principalTheorem
