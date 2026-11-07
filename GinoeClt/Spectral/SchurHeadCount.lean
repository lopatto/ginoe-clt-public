/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.GaussianCountWeight
public import GinoeClt.Spectral.Scaling
public import GinoeClt.Spectral.SchurRootOrder
@[expose] public section
noncomputable section
open Set
open scoped Matrix ENNReal NNReal Classical
namespace Paper.Spectral

/-- The exact RAW domain corresponding to the frozen inverse-square-root scaling. -/
def scaledCountDomain (n : ℕ) (A : Set ℂ) : Set ℂ :=
  (fun z : ℂ => (Real.sqrt (n+1 : ℝ) : ℂ) * z) '' A

theorem scaledCountDomain_upper (A : Set ℂ) (n : ℕ)
    (hA : ∀ z ∈ A, 0 < z.im) : ∀ z ∈ scaledCountDomain n A, 0 < z.im := by
  rintro z ⟨a,ha,rfl⟩
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (hA a ha)

/-- Filtering by an upper-half-plane set keeps exactly the genuine head LIST,
with every multiplicity; no support-set conversion is used. -/
theorem schurWordRoots_filter_upper_eq_heads (B : Set ℂ)
    (hB : ∀ z ∈ B, 0 < z.im) (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p) :
    (schurWordRoots w p).filter (fun z => z ∈ B) =
      (schurWordHeadRoots w p : Multiset ℂ).filter (fun z => z ∈ B) := by
  rw [schurWordHeadRoots_eq_filter w p hp,Multiset.filter_filter]
  apply Multiset.filter_congr
  intro z _
  constructor
  · intro hz
    exact ⟨hz,(hB z hz).le⟩
  · exact And.left

/-- The actual scaled count in a transported physical word matrix equals the
length of the raw-domain filter on the original head list. -/
theorem count_schurWord_cast_eq_headFilter (A : Set ℂ) (n : ℕ)
    (hA : ∀ z ∈ A, 0 < z.im) (w : SchurWordsOfSize (n+1))
    (p : SchurWordCells w.val) (hp : SchurWordPositive w.val p) :
    count A n (Matrix.of (fun i j =>
      schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p)) (j,i))) =
      ((schurWordHeadRoots w.val p).filter (fun z => z ∈ scaledCountDomain n A)).length := by
  have hM : (Matrix.of (fun i j =>
      schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p)) (j,i)) : SampleSpace n) =
      (schurWordParameter w.val p).reindex (finCongr w.property) (finCongr w.property) := by
    rw [schurCellsCast_vec]
    rfl
  rw [hM,count_eq_raw_count_scaled_domain,Matrix.charpoly_reindex,
    schurWordParameter_roots w.val p hp]
  change ((schurWordRoots w.val p).filter (fun z => z ∈ scaledCountDomain n A)).card = _
  rw [schurWordRoots_filter_upper_eq_heads (scaledCountDomain n A)
    (scaledCountDomain_upper A n hA) w.val p hp]
  simp only [Multiset.filter_coe,Multiset.coe_card]

/-- A finite product of identical indicator weights is the corresponding
generating power, counting every occurrence in a list. -/
theorem list_prod_indicator_base {α β : Type*} [Monoid β] (l : List α)
    (p : α → Prop) [DecidablePred p] (b : β) :
    (l.map (fun a => if p a then b else 1)).prod = b ^ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a
    · simp [ha,ih,pow_succ']
    · simp [ha,ih]

theorem countGeneratingWeight_schurWord_cast (A : Set ℂ) (n : ℕ)
    (hA : ∀ z ∈ A, 0 < z.im) (w : SchurWordsOfSize (n+1))
    (p : SchurWordCells w.val) (hp : SchurWordPositive w.val p) (t : ℝ≥0) :
    (1 + (t : ℝ≥0∞)) ^ count A n (Matrix.of (fun i j =>
      schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p)) (j,i))) =
    ((schurWordHeadRoots w.val p).map
      (fun z => if z ∈ scaledCountDomain n A then 1 + (t : ℝ≥0∞) else 1)).prod := by
  rw [count_schurWord_cast_eq_headFilter A n hA w p hp]
  exact (list_prod_indicator_base (schurWordHeadRoots w.val p)
    (fun z => z ∈ scaledCountDomain n A) (1 + (t : ℝ≥0∞))).symm

/-- Equality transport preserves the literal sum of squared real entries. -/
theorem sum_sq_finCongr {M N : ℕ} (h : M = N)
    (K : Matrix (Fin M) (Fin M) ℝ) :
    (∑ i : Fin N, ∑ j : Fin N,
      (K.reindex (finCongr h) (finCongr h)) i j ^ 2) =
      ∑ i : Fin M, ∑ j : Fin M, K i j ^ 2 := by
  subst N
  rfl

/-- The actual Gaussian normalization is unchanged by the same dimension cast. -/
theorem matrixGaussianDensity_schurWord_cast (n : ℕ) (w : SchurWordsOfSize (n+1))
    (p : SchurWordCells w.val) :
    matrixGaussianDensity n (Matrix.of (fun i j =>
      schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p)) (j,i))) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ ((n+1)^2) *
        Real.exp (-(∑ i : Fin (schurWordSize w.val), ∑ j : Fin (schurWordSize w.val),
          schurWordParameter w.val p i j ^ 2) / 2) := by
  rw [schurCellsCast_vec]
  change matrixGaussianDensity n
    ((schurWordParameter w.val p).reindex (finCongr w.property) (finCongr w.property)) = _
  rw [matrixGaussianDensity_eq,sum_sq_finCongr]

/-- Complete actual Gaussian/count integrand in raw word variables.
All normalization, matrix scaling and root multiplicities remain explicit. -/
theorem gaussianCountWeight_schurWord_cast (A : Set ℂ) (n : ℕ)
    (hA : ∀ z ∈ A, 0 < z.im) (w : SchurWordsOfSize (n+1))
    (p : SchurWordCells w.val) (hp : SchurWordPositive w.val p) (t : ℝ≥0) :
    gaussianCountWeight A n t (schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p))) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ ((n+1)^2) *
        Real.exp (-(∑ i : Fin (schurWordSize w.val), ∑ j : Fin (schurWordSize w.val),
          schurWordParameter w.val p i j ^ 2) / 2)) *
      ((schurWordHeadRoots w.val p).map
        (fun z => if z ∈ scaledCountDomain n A then 1 + (t : ℝ≥0∞) else 1)).prod := by
  change ENNReal.ofReal (matrixGaussianDensity n (Matrix.of (fun i j =>
      schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p)) (j,i)))) *
    (1 + (t : ℝ≥0∞)) ^ count A n (Matrix.of (fun i j =>
      schurCellsCast w.property (Matrix.vec (schurWordParameter w.val p)) (j,i))) = _
  rw [matrixGaussianDensity_schurWord_cast,
    countGeneratingWeight_schurWord_cast A n hA w p hp t]

/-- A real head has weight exactly one in the nonreal-count generating product. -/
theorem scaledCountDomain_real_notMem (A : Set ℂ) (n : ℕ)
    (hA : ∀ z ∈ A, 0 < z.im) (a : ℝ) :
    (a : ℂ) ∉ scaledCountDomain n A := by
  intro ha
  have h := scaledCountDomain_upper A n hA (a : ℂ) ha
  simp only [Complex.ofReal_im,lt_self_iff_false] at h

end Paper.Spectral
