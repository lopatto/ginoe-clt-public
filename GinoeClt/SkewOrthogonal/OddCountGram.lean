/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.SkewOrthogonal.RawOddBorderSpecialization
public import GinoeClt.SkewOrthogonal.SourceIntegrability
public import GinoeClt.SkewOrthogonal.DeBruijnEvenPartition
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate Matrix
namespace Paper.SkewOrthogonal

/-- The OLD raw bordered Gaussian Gram plus its literal continuous complex-count update. -/
def rawOddCountGram (m : ℕ) (B : Set ℂ) (s : ℂ) :
    Matrix (PairedIndex (m+1)) (PairedIndex (m+1)) ℂ :=
  fun p q => rawOddAugmentedGram m p q + s *
    ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
      (rawOddEvaluation m z p * rawOddEvaluation m (conj z) q -
        rawOddEvaluation m z q * rawOddEvaluation m (conj z) p)

/-- The SAME continuous update in the EXISTING border-adjusted polynomial basis. -/
def adjustedOddCountGram (m : ℕ) (B : Set ℂ) (s : ℂ) :
    Matrix (PairedIndex (m+1)) (PairedIndex (m+1)) ℂ :=
  fun p q => oddAugmentedGram m p q + s *
    ∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
      (adjustedOddEvaluation m z p * adjustedOddEvaluation m (conj z) q -
        adjustedOddEvaluation m z q * adjustedOddEvaluation m (conj z) p)

@[simp] theorem rawOddCountGram_zero (m : ℕ) (B : Set ℂ) :
    rawOddCountGram m B 0 = rawOddAugmentedGram m := by ext p q; simp [rawOddCountGram]
@[simp] theorem adjustedOddCountGram_zero (m : ℕ) (B : Set ℂ) :
    adjustedOddCountGram m B 0 = oddAugmentedGram m := by ext p q; simp [adjustedOddCountGram]

theorem pfaffian_rawOddCountGram_zero_ne_zero (m : ℕ) (B : Set ℂ) :
    pfaffian (rawOddCountGram m B 0) ≠ 0 := by
  rw [rawOddCountGram_zero]
  exact pfaffian_rawOddAugmentedGram_ne_zero m

/-- Commute one FIXED finite matrix through entrywise integrals. Every finite
summand is genuinely L1 before the two finite sum/integral interchanges. -/
theorem matrix_entry_integral_congruence {κ X : Type*} [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) (C : Matrix κ κ ℂ) (K : X → Matrix κ κ ℂ)
    (hK : ∀ i j, Integrable (fun z => K z i j) μ) :
    C * Matrix.of (fun i j => ∫ z, K z i j ∂μ) * C.transpose =
      Matrix.of (fun p q => ∫ z, (C * K z * C.transpose) p q ∂μ) := by
  classical
  ext p q
  simp only [Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun j hj =>
    integrable_finsetSum Finset.univ (fun i hi => ((hK i j).const_mul (C p i)).mul_const (C q j)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum Finset.univ (fun i hi => ((hK i j).const_mul (C p i)).mul_const (C q j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_mul_const,integral_const_mul]

/-- The SAME reviewed determinant-one row basis carries the ACTUAL continuous
update, without assuming any weighted radical property of the last even polynomial. -/
theorem oddRowBasis_count_congruence (m : ℕ) (B : Set ℂ) (_hBm : MeasurableSet B)
    (hB : B ⊆ {z : ℂ | 0 < z.im}) (s : ℂ) :
    oddRowBasis m * rawOddCountGram m B s * (oddRowBasis m).transpose = adjustedOddCountGram m B s := by
  let c : ℂ → ℂ := fun z => (2*Complex.I)*(complexWeight z : ℂ)
  let K : ℂ → Matrix (PairedIndex (m+1)) (PairedIndex (m+1)) ℂ := fun z =>
    c z • (Matrix.vecMulVec (rawOddEvaluation m z) (rawOddEvaluation m (conj z)) -
      Matrix.vecMulVec (rawOddEvaluation m (conj z)) (rawOddEvaluation m z))
  let L : ℂ → Matrix (PairedIndex (m+1)) (PairedIndex (m+1)) ℂ := fun z =>
    c z • (Matrix.vecMulVec (adjustedOddEvaluation m z) (adjustedOddEvaluation m (conj z)) -
      Matrix.vecMulVec (adjustedOddEvaluation m (conj z)) (adjustedOddEvaluation m z))
  have hK (p q : PairedIndex (m+1)) : Integrable (fun z => K z p q) (volume.restrict B) := by
    have h := integrableOn_sourcePolynomialWedge (rawOddPolynomial m) B hB p q
    simp_rw [rawOddPolynomial_eval] at h
    exact h
  have hpoint (z : ℂ) : oddRowBasis m * K z * (oddRowBasis m).transpose = L z := by
    dsimp only [K,L]
    rw [Matrix.mul_smul,Matrix.smul_mul,matrix_evaluation_wedge_congruence,
      oddRowBasis_mulVec_evaluation,oddRowBasis_mulVec_evaluation]
  have hraw : rawOddCountGram m B s = rawOddAugmentedGram m + s •
      Matrix.of (fun p q => ∫ z in B, K z p q) := by
    ext p q
    change rawOddAugmentedGram m p q + s * _ = rawOddAugmentedGram m p q + s * _
    apply congrArg (fun a : ℂ => rawOddAugmentedGram m p q+s*a)
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [K,c,Matrix.vecMulVec]
    ring
  have hadj : adjustedOddCountGram m B s = oddAugmentedGram m + s •
      Matrix.of (fun p q => ∫ z in B, L z p q) := by
    ext p q
    change oddAugmentedGram m p q + s * _ = oddAugmentedGram m p q + s * _
    apply congrArg (fun a : ℂ => oddAugmentedGram m p q+s*a)
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [L,c,Matrix.vecMulVec]
    ring
  rw [hraw,hadj,Matrix.mul_add,Matrix.add_mul,oddRowBasis_congruence,
    Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  congr 1
  rw [matrix_entry_integral_congruence (volume.restrict B) (oddRowBasis m) K hK]
  simp_rw [hpoint]

theorem rawOddCountGram_skew (m : ℕ) (B : Set ℂ) (s : ℂ) (p q : PairedIndex (m+1)) :
    rawOddCountGram m B s q p = -rawOddCountGram m B s p q := by
  have hb : rawOddAugmentedGram m q p = -rawOddAugmentedGram m p q :=
    borderedGram_skew m (pairedPolynomial m) (evenPolynomial m) p q
  have hi : (∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
      (rawOddEvaluation m z q*rawOddEvaluation m (conj z) p -
        rawOddEvaluation m z p*rawOddEvaluation m (conj z) q)) =
      -(∫ z in B, (2*Complex.I)*(complexWeight z : ℂ) *
        (rawOddEvaluation m z p*rawOddEvaluation m (conj z) q -
          rawOddEvaluation m z q*rawOddEvaluation m (conj z) p)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  simp only [rawOddCountGram]
  rw [hb,hi]
  ring

theorem pfaffian_rawOddCountGram_eq (m : ℕ) (B : Set ℂ) (hBm : MeasurableSet B)
    (hB : B ⊆ {z : ℂ | 0 < z.im}) (s : ℂ) :
    pfaffian (rawOddCountGram m B s) = pfaffian (adjustedOddCountGram m B s) := by
  have h := pfaffian_congruence (rawOddCountGram m B s) (oddRowBasis m)
    (rawOddCountGram_skew m B s)
  rw [oddRowBasis_count_congruence m B hBm hB s,oddRowBasis_det,one_mul] at h
  exact h.symm

theorem pfaffian_rawOddCountGram_ratio (m : ℕ) (B : Set ℂ) (hBm : MeasurableSet B)
    (hB : B ⊆ {z : ℂ | 0 < z.im}) (s : ℂ) :
    pfaffian (rawOddCountGram m B s) / pfaffian (rawOddCountGram m B 0) =
      pfaffian (adjustedOddCountGram m B s) / pfaffian (adjustedOddCountGram m B 0) := by
  rw [pfaffian_rawOddCountGram_eq m B hBm hB s,rawOddCountGram_zero,adjustedOddCountGram_zero,
    pfaffian_rawOddAugmentedGram_eq]

/-- Pointwise equality only ON the genuine upper half-plane. Reflection changes
polynomial arguments and never conjugates their coefficients. -/
theorem rankTwo_pointBalancedFeatures_upper {m : ℕ} (E : ℂ → PairedIndex m → ℂ)
    (z : ℂ) (hz : 0 ≤ z.im) (p q : PairedIndex m) :
    rankTwoEntry (pointBalancedFeatures E) z p q = (2*Complex.I)*(complexWeight z : ℂ) *
      (E z p * E (conj z) q - E z q * E (conj z) p) := by
  have h := balancedFeatures_wedge E (fun _ : Fin 1 => z) (fun _ => hz) (0 : Fin 1) p q
  calc
    _ = (2*Complex.I)*(complexWeight z : ℂ) *
        (E z p * E (conj z) q - E (conj z) p * E z q) := by
      simpa only [rankTwoEntry,pointBalancedFeatures] using h
    _ = _ := by ring

/-- The EXISTING continuous generating polynomial evaluates to the ACTUAL raw odd
Gram ratio. This is a proved polynomial/matrix bridge, not an assumed ensemble law. -/
theorem eval_continuousAtomicGeneratingPolynomial_rawOddCountGram (m : ℕ) (B : Set ℂ)
    (hBm : MeasurableSet B) (hB : B ⊆ {z : ℂ | 0 < z.im}) (s : ℂ) :
    (continuousAtomicGeneratingPolynomial (volume.restrict B) (oddNormWeight m)
      (pointBalancedFeatures (adjustedOddEvaluation m))).eval s =
      pfaffian (rawOddCountGram m B s) / pfaffian (rawOddCountGram m B 0) := by
  have hAff : (fun p q => interlacedMatrix (Matrix.diagonal (oddNormWeight m)) p q + s *
      ∫ z in B, rankTwoEntry (pointBalancedFeatures (adjustedOddEvaluation m)) z p q) =
      adjustedOddCountGram m B s := by
    rw [← oddAugmentedGram_eq_interlaced]
    funext p q
    apply congrArg (fun a : ℂ => oddAugmentedGram m p q+s*a)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hBm] with z hz
    exact rankTwo_pointBalancedFeatures_upper _ z (hB hz).le p q
  rw [eval_continuousAtomicGeneratingPolynomial,hAff,← oddAugmentedGram_eq_interlaced]
  simpa only [rawOddCountGram_zero,adjustedOddCountGram_zero] using
    (pfaffian_rawOddCountGram_ratio m B hBm hB s).symm

/-- The SAME existing polynomial evaluation bridge for the already-defined EVEN
count Gram. No duplicate definition or new stochastic interpretation is introduced. -/
theorem eval_continuousAtomicGeneratingPolynomial_evenCountGram (m : ℕ) (B : Set ℂ)
    (hBm : MeasurableSet B) (hB : B ⊆ {z : ℂ | 0 < z.im}) (s : ℂ) :
    (continuousAtomicGeneratingPolynomial (volume.restrict B) (fun i : Fin m => skewNorm i.val)
      (pointBalancedFeatures (fun z p => (pairedPolynomial m p).eval z))).eval s =
      pfaffian (evenCountGram m B s) / pfaffian (evenCountGram m B 0) := by
  have hAff : (fun p q => interlacedMatrix (Matrix.diagonal (fun i : Fin m => skewNorm i.val)) p q + s *
      ∫ z in B, rankTwoEntry (pointBalancedFeatures (fun z p => (pairedPolynomial m p).eval z)) z p q) =
      evenCountGram m B s := by
    rw [← pairedGram_eq_interlaced]
    funext p q
    change pairedGram m p q+s*_ = skewForm (pairedPolynomial m p) (pairedPolynomial m q)+s*_
    apply congrArg (fun a : ℂ => pairedGram m p q+s*a)
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hBm] with z hz
    exact rankTwo_pointBalancedFeatures_upper _ z (hB hz).le p q
  rw [eval_continuousAtomicGeneratingPolynomial,hAff,← pairedGram_eq_interlaced,evenCountGram_zero]

end Paper.SkewOrthogonal
