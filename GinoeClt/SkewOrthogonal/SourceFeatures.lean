/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.SkewOrthogonal.AtomicExpansion
public import GinoeClt.SkewOrthogonal.OddAtomicUpdate
public import GinoeClt.Kernel.SkewSymmetry

/-! # Actual polynomial features for both parities of the source complex kernel

Forrester–Nagao0806.0055v1(4.41)/(4.42), Mays1202.1218v1(148),
Definition4.16/(169)/Definition4.26. Raw entry identities are proved first.
The frozen pfaffianKernelMatrix includes rescale N; its exact matrix bridge
therefore evaluates the features AT rescale N(z_i). No N prefactor is hidden.
-/
@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexConjugate

namespace Paper.SkewOrthogonal

/-- Balanced source columns. The reflection acts on the polynomial argument,
with no conjugation of its coefficients. -/
def balancedFeatures {κ : Type*} {r : ℕ} (E : ℂ → κ → ℂ) (z : Fin r → ℂ) :
    Fin r → κ → Fin 2 → ℂ :=
  fun i p a ↦ if a = 0 then (Real.sqrt 2 : ℂ) * polynomialWeight (z i) * E (z i) p
    else Complex.I * (Real.sqrt 2 : ℂ) * polynomialWeight (conj (z i)) * E (conj (z i)) p

/-- Literal unweighted evaluation contraction. -/
def evaluationPrekernel {m : ℕ} (w : Fin m → ℂ) (E : ℂ → PairedIndex m → ℂ)
    (z v : ℂ) : ℂ :=
  ∑ i : Fin m, (w i)⁻¹ * (E z (i,0) * E v (i,1) - E z (i,1) * E v (i,0))

theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

theorem atomicFeatureKernel_skew {m r : ℕ} (w : Fin m → ℂ)
    (A : Fin r → PairedIndex m → Fin 2 → ℂ) (p q : PairedIndex r) :
    atomicFeatureKernel w A q p = -atomicFeatureKernel w A p q := by
  rw [atomicFeatureKernel, atomicFeatureKernel, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem balancedKernel_00 {m r : ℕ} (w : Fin m → ℂ) (E : ℂ → PairedIndex m → ℂ)
    (z : Fin r → ℂ) (i j : Fin r) :
    atomicFeatureKernel w (balancedFeatures E z) (i,0) (j,0) =
      2 * polynomialWeight (z i) * polynomialWeight (z j) * evaluationPrekernel w E (z i) (z j) := by
  simp only [atomicFeatureKernel, balancedFeatures, ite_true, evaluationPrekernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring_nf
  rw [sqrt_two_complex_sq]
  ring

theorem balancedKernel_01 {m r : ℕ} (w : Fin m → ℂ) (E : ℂ → PairedIndex m → ℂ)
    (z : Fin r → ℂ) (i j : Fin r) :
    atomicFeatureKernel w (balancedFeatures E z) (i,0) (j,1) =
      2 * Complex.I * polynomialWeight (z i) * polynomialWeight (conj (z j)) *
        evaluationPrekernel w E (z i) (conj (z j)) := by
  simp only [atomicFeatureKernel, balancedFeatures, ite_true, one_ne_zero, ite_false, evaluationPrekernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring_nf
  rw [sqrt_two_complex_sq]
  ring

theorem balancedKernel_11 {m r : ℕ} (w : Fin m → ℂ) (E : ℂ → PairedIndex m → ℂ)
    (z : Fin r → ℂ) (i j : Fin r) :
    atomicFeatureKernel w (balancedFeatures E z) (i,1) (j,1) =
      -2 * polynomialWeight (conj (z i)) * polynomialWeight (conj (z j)) *
        evaluationPrekernel w E (conj (z i)) (conj (z j)) := by
  simp only [atomicFeatureKernel, balancedFeatures, one_ne_zero, ite_false, evaluationPrekernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  ring_nf
  rw [sqrt_two_complex_sq, Complex.I_sq]
  ring

theorem evaluationPrekernel_even (m : ℕ) (z v : ℂ) :
    evaluationPrekernel (fun i : Fin m ↦ skewNorm i.val)
      (fun u p ↦ (pairedPolynomial m p).eval u) z v = pairedPrekernel m z v := by
  rw [pairedPrekernel_eq_basis_sum]
  unfold evaluationPrekernel
  apply Finset.sum_congr rfl
  intro i hi
  rw [div_eq_mul_inv]
  ring

theorem evaluationPrekernel_odd (m : ℕ) (z v : ℂ) :
    evaluationPrekernel (oddNormWeight m) (adjustedOddEvaluation m) z v = oddPrekernel m z v := by
  have he (u : ℂ) (i : Fin m) (a : Fin 2) :
      adjustedOddEvaluation m u (i.castSucc,a) = (oddBasisPolynomial m (some (i,a))).eval u := by
    simpa only [splitLastPair_symm_inl, oddBasisPolynomial] using adjustedOddEvaluation_inl m u (i,a)
  have hb (u : ℂ) : adjustedOddEvaluation m u (Fin.last m,1) = 0 := by
    simp [adjustedOddEvaluation, isBorderIndex]
  rw [oddPrekernel_eq_basis_sum]
  unfold evaluationPrekernel
  rw [Fin.sum_univ_castSucc]
  simp only [oddNormWeight, Fin.lastCases_castSucc, Fin.lastCases_last, he, hb,
    mul_zero, zero_mul, sub_self, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [div_eq_mul_inv]
  ring

theorem oddNormWeight_ne_zero (m : ℕ) (i : Fin (m+1)) : oddNormWeight m i ≠ 0 := by
  induction i using Fin.lastCases
  · simpa only [oddNormWeight, Fin.lastCases_last] using realBorder_even_ne_zero m
  · rename_i j
    simpa only [oddNormWeight, Fin.lastCases_castSucc] using skewNorm_ne_zero j.val

/-- Raw D/S/I entries, with genuine even polynomial features. -/
theorem balancedEvenKernel_raw {r : ℕ} (m : ℕ) (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im)
    (p q : PairedIndex r) :
    atomicFeatureKernel (fun i : Fin m ↦ skewNorm i.val)
      (balancedFeatures (fun u a ↦ (pairedPolynomial m a).eval u) z) p q =
      if p.2 = 0 then (if q.2 = 0 then Kernel.D (2*m) (z p.1) (z q.1)
        else Kernel.S (2*m) (z p.1) (z q.1))
      else if q.2 = 0 then -Kernel.S (2*m) (z q.1) (z p.1)
        else Kernel.I (2*m) (z p.1) (z q.1) := by
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  fin_cases a <;> fin_cases b
  · change atomicFeatureKernel (fun t : Fin m => skewNorm t.val) (balancedFeatures (fun u a => (pairedPolynomial m a).eval u) z)
      (i,0) (j,0) = Kernel.D (2*m) (z i) (z j)
    rw [balancedKernel_00, evaluationPrekernel_even]
    exact weighted_pairedPrekernel_D m (z i) (z j) (hz i) (hz j)
  · change atomicFeatureKernel (fun t : Fin m => skewNorm t.val) (balancedFeatures (fun u a => (pairedPolynomial m a).eval u) z)
      (i,0) (j,1) = Kernel.S (2*m) (z i) (z j)
    rw [balancedKernel_01, evaluationPrekernel_even]
    exact weighted_pairedPrekernel_S m (z i) (z j) (hz i) (hz j)
  · change atomicFeatureKernel (fun t : Fin m => skewNorm t.val) (balancedFeatures (fun u a => (pairedPolynomial m a).eval u) z)
      (i,1) (j,0) = -Kernel.S (2*m) (z j) (z i)
    rw [atomicFeatureKernel_skew, balancedKernel_01, evaluationPrekernel_even,
      weighted_pairedPrekernel_S m (z j) (z i) (hz j) (hz i)]
  · change atomicFeatureKernel (fun t : Fin m => skewNorm t.val) (balancedFeatures (fun u a => (pairedPolynomial m a).eval u) z)
      (i,1) (j,1) = Kernel.I (2*m) (z i) (z j)
    rw [balancedKernel_11, evaluationPrekernel_even]
    exact weighted_pairedPrekernel_I m (z i) (z j) (hz i) (hz j)

/-- Raw D/S/I entries, including the genuine odd final pair and zero border feature. -/
theorem balancedOddKernel_raw {r : ℕ} (m : ℕ) (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im)
    (p q : PairedIndex r) :
    atomicFeatureKernel (oddNormWeight m) (balancedFeatures (adjustedOddEvaluation m) z) p q =
      if p.2 = 0 then (if q.2 = 0 then Kernel.D (2*m+1) (z p.1) (z q.1)
        else Kernel.S (2*m+1) (z p.1) (z q.1))
      else if q.2 = 0 then -Kernel.S (2*m+1) (z q.1) (z p.1)
        else Kernel.I (2*m+1) (z p.1) (z q.1) := by
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  fin_cases a <;> fin_cases b
  · change atomicFeatureKernel (oddNormWeight m) (balancedFeatures (adjustedOddEvaluation m) z)
      (i,0) (j,0) = Kernel.D (2*m+1) (z i) (z j)
    rw [balancedKernel_00, evaluationPrekernel_odd]
    exact weighted_oddPrekernel_D m (z i) (z j) (hz i) (hz j)
  · change atomicFeatureKernel (oddNormWeight m) (balancedFeatures (adjustedOddEvaluation m) z)
      (i,0) (j,1) = Kernel.S (2*m+1) (z i) (z j)
    rw [balancedKernel_01, evaluationPrekernel_odd]
    exact weighted_oddPrekernel_S m (z i) (z j) (hz i) (hz j)
  · change atomicFeatureKernel (oddNormWeight m) (balancedFeatures (adjustedOddEvaluation m) z)
      (i,1) (j,0) = -Kernel.S (2*m+1) (z j) (z i)
    rw [atomicFeatureKernel_skew, balancedKernel_01, evaluationPrekernel_odd,
      weighted_oddPrekernel_S m (z j) (z i) (hz j) (hz i)]
  · change atomicFeatureKernel (oddNormWeight m) (balancedFeatures (adjustedOddEvaluation m) z)
      (i,1) (j,1) = Kernel.I (2*m+1) (z i) (z j)
    rw [balancedKernel_11, evaluationPrekernel_odd]
    exact weighted_oddPrekernel_I m (z i) (z j) (hz i) (hz j)

theorem rescale_im_nonneg (N : ℕ) (z : ℂ) (hz : 0 ≤ z.im) : 0 ≤ (Kernel.rescale N z).im := by
  simpa [Kernel.rescale, Complex.mul_im] using mul_nonneg (Real.sqrt_nonneg (N : ℝ)) hz

/-- EXACT frozen matrix: the rescaling belongs in the feature arguments. -/
theorem balancedEvenKernel_eq_frozen {r : ℕ} (m : ℕ) (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im) :
    atomicFeatureKernel (fun i : Fin m ↦ skewNorm i.val)
      (balancedFeatures (fun u a ↦ (pairedPolynomial m a).eval u)
        (fun i ↦ Kernel.rescale (2*m) (z i))) = Kernel.pfaffianKernelMatrix (2*m) z := by
  ext p q
  simpa only [Kernel.pfaffianKernelMatrix] using balancedEvenKernel_raw m
    (fun i ↦ Kernel.rescale (2*m) (z i)) (fun i ↦ rescale_im_nonneg _ _ (hz i)) p q

theorem balancedOddKernel_eq_frozen {r : ℕ} (m : ℕ) (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im) :
    atomicFeatureKernel (oddNormWeight m)
      (balancedFeatures (adjustedOddEvaluation m) (fun i ↦ Kernel.rescale (2*m+1) (z i))) =
        Kernel.pfaffianKernelMatrix (2*m+1) z := by
  ext p q
  simpa only [Kernel.pfaffianKernelMatrix] using balancedOddKernel_raw m
    (fun i ↦ Kernel.rescale (2*m+1) (z i)) (fun i ↦ rescale_im_nonneg _ _ (hz i)) p q

/-- The balanced feature wedge is the actual complex source atom 2iW. -/
theorem balancedFeatures_wedge {κ : Type*} {r : ℕ} (E : ℂ → κ → ℂ)
    (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im) (i : Fin r) (p q : κ) :
    balancedFeatures E z i p 0 * balancedFeatures E z i q 1 -
      balancedFeatures E z i p 1 * balancedFeatures E z i q 0 =
        (2*Complex.I)*(complexWeight (z i) : ℂ) *
          (E (z i) p * E (conj (z i)) q - E (conj (z i)) p * E (z i) q) := by
  rw [complexWeight_eq_polynomialWeight_product (z i) (hz i)]
  simp only [balancedFeatures, ite_true, one_ne_zero, ite_false]
  ring_nf
  rw [sqrt_two_complex_sq]
  ring

/-- The actual finite odd source update is exactly the balanced-feature Gram update. -/
theorem finiteAtomicGram_balanced_odd {r : ℕ} (m : ℕ) (c : Fin r → ℂ)
    (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im) :
    finiteAtomicGram (oddNormWeight m) c (balancedFeatures (adjustedOddEvaluation m) z) =
      adjustedOddAtomicGram m Finset.univ c z := by
  ext p q
  change interlacedMatrix (Matrix.diagonal (oddNormWeight m)) p q + _ = _
  rw [← oddAugmentedGram_eq_interlaced]
  simp only [adjustedOddAtomicGram, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change c i * (balancedFeatures (adjustedOddEvaluation m) z i p 0 *
      balancedFeatures (adjustedOddEvaluation m) z i q 1 -
    balancedFeatures (adjustedOddEvaluation m) z i p 1 * balancedFeatures (adjustedOddEvaluation m) z i q 0) =
      (c i * (2*Complex.I)*(complexWeight (z i) : ℂ)) *
        (adjustedOddEvaluation m (z i) p * adjustedOddEvaluation m (conj (z i)) q -
          adjustedOddEvaluation m (conj (z i)) p * adjustedOddEvaluation m (z i) q)
  rw [balancedFeatures_wedge _ _ hz]
  ring

/-- The actual finite even source update, with the unmodified paired Gaussian Gram. -/
theorem finiteAtomicGram_balanced_even {r : ℕ} (m : ℕ) (c : Fin r → ℂ)
    (z : Fin r → ℂ) (hz : ∀ i, 0 ≤ (z i).im) :
    finiteAtomicGram (fun i : Fin m ↦ skewNorm i.val) c
      (balancedFeatures (fun u p ↦ (pairedPolynomial m p).eval u) z) =
      (fun p q ↦ pairedGram m p q + ∑ i : Fin r,
        (c i*(2*Complex.I)*(complexWeight (z i) : ℂ)) *
          ((pairedPolynomial m p).eval (z i) * (pairedPolynomial m q).eval (conj (z i)) -
            (pairedPolynomial m p).eval (conj (z i)) * (pairedPolynomial m q).eval (z i))) := by
  ext p q
  change interlacedMatrix (Matrix.diagonal (fun i : Fin m ↦ skewNorm i.val)) p q + _ = _
  rw [← pairedGram_eq_interlaced]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [balancedFeatures_wedge _ _ hz]
  ring

end Paper.SkewOrthogonal
