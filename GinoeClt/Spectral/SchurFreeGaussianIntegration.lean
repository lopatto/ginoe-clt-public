/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurUpperGaussian
public import GinoeClt.Spectral.SchurAngularFactorization
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Matrix ENNReal BigOperators
namespace Paper.Spectral

/-- Eliminate a genuinely independent middle block in a literal ordinary index
permutation. All values are ENNReal, so zero/infinite residual integrals are retained. -/
theorem lintegral_literalTripleRead_separate {A U T F : Type*}
    [Fintype A] [Fintype U] [Fintype T] [Fintype F]
    (e : A ⊕ (U ⊕ T) ≃ F) (B : (U → ℝ) → ℝ≥0∞) (hB : Measurable B)
    (H : (A → ℝ) × (T → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ y : F → ℝ, B (literalTripleRead e y).2.1 *
      H ((literalTripleRead e y).1,(literalTripleRead e y).2.2)) =
      (∫⁻ u, B u) * ∫⁻ a, ∫⁻ t, H (a,t) := by
  let c : U ⊕ (A ⊕ T) ≃ A ⊕ (U ⊕ T) :=
    (Equiv.sumAssoc U A T).symm.trans
      (((Equiv.sumComm U A).sumCongr (Equiv.refl T)).trans (Equiv.sumAssoc A U T))
  let e' : U ⊕ (A ⊕ T) ≃ F := c.trans e
  have hF : Measurable (fun z : (U → ℝ) × ((A → ℝ) × (T → ℝ)) =>
      B z.1 * H z.2) := (hB.comp measurable_fst).mul (hH.comp measurable_snd)
  calc
    _ = ∫⁻ y : F → ℝ, B (literalTripleRead e' y).1 *
        H (literalTripleRead e' y).2 := rfl
    _ = ∫⁻ z : (U → ℝ) × ((A → ℝ) × (T → ℝ)), B z.1 * H z.2 :=
      (volume_preserving_literalTripleRead e').lintegral_comp hF
    _ = (∫⁻ u, B u) * ∫⁻ z : (A → ℝ) × (T → ℝ), H z :=
      lintegral_prod_mul hB.aemeasurable hH.aemeasurable
    _ = _ := congrArg (fun q => (∫⁻ u, B u) * q) (lintegral_prod H hH.aemeasurable)

theorem continuous_schurUpperGaussian {ι : Type*} [Fintype ι] :
    Continuous (schurUpperGaussian (ι := ι)) := by
  unfold schurUpperGaussian
  fun_prop

theorem measurable_freeParameterGaussian (w : List Bool) :
    Measurable (fun t : SchurWordFreeIndex w → ℝ =>
      ENNReal.ofReal (schurUpperGaussian
        (Matrix.vec (schurWordParameter w (schurWordFreeCells w t))))) :=
  (continuous_schurUpperGaussian.comp (continuous_vec_schurWordFreeParameter w)).measurable.ennreal_ofReal

/-- Exact actual K Gaussian, with the literal U cells and no Jacobian surrogate. -/
theorem scalarFreeGaussian_eq (w : List Bool) (y : SchurWordFreeIndex (false::w) → ℝ) :
    schurUpperGaussian (Matrix.vec (schurWordParameter (false::w)
      (schurWordFreeCells (false::w) y))) =
      Real.exp (-((scalarFreeSplit w y).1 0)^2/2) *
        schurUpperGaussian (scalarFreeSplit w y).2.1 *
        schurUpperGaussian (Matrix.vec
          (schurWordParameter w (schurWordFreeCells w (scalarFreeSplit w y).2.2))) := by
  have h := congrArg (fun M : Matrix (Fin (1+schurWordSize w)) (Fin (1+schurWordSize w)) ℝ =>
      schurUpperGaussian (Matrix.vec M)) (scalarFreeParameter_eq w y)
  refine h.trans ?_
  simpa only [schurUpperGaussian_vec_scalarBlock] using!
    schurUpperGaussian_vec_upperBlockMatrix (scalarBlock ((scalarFreeSplit w y).1 0))
      (fun i j => (scalarFreeSplit w y).2.1 (j,i))
      (schurWordParameter w (schurWordFreeCells w (scalarFreeSplit w y).2.2))

theorem pairFreeGaussian_eq (w : List Bool) (y : SchurWordFreeIndex (true::w) → ℝ) :
    schurUpperGaussian (Matrix.vec (schurWordParameter (true::w)
      (schurWordFreeCells (true::w) y))) =
      Real.exp (-(2*((pairFreeSplit w y).1 0)^2+((pairFreeSplit w y).1 1)^2+
        ((pairFreeSplit w y).1 2)^2)/2) *
        schurUpperGaussian (pairFreeSplit w y).2.1 *
        schurUpperGaussian (Matrix.vec
          (schurWordParameter w (schurWordFreeCells w (pairFreeSplit w y).2.2))) := by
  have h := congrArg (fun M : Matrix (Fin (2+schurWordSize w)) (Fin (2+schurWordSize w)) ℝ =>
      schurUpperGaussian (Matrix.vec M)) (pairFreeParameter_eq w y)
  refine h.trans ?_
  simpa only [schurUpperGaussian_vec_schurBlock] using!
    schurUpperGaussian_vec_upperBlockMatrix
      (schurBlock ((pairFreeSplit w y).1 0) ((pairFreeSplit w y).1 1) ((pairFreeSplit w y).1 2))
      (fun i j => (pairFreeSplit w y).2.1 (j,i))
      (schurWordParameter w (schurWordFreeCells w (pairFreeSplit w y).2.2))

/-- Eliminate actual scalar-word upper cells against ANY nonnegative Borel
head/tail weight. This generic intermediate has no ensemble/count assumption. -/
theorem lintegral_scalarFreeGaussian (w : List Bool)
    (H : (Fin 1 → ℝ) × (SchurWordFreeIndex w → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ y : SchurWordFreeIndex (false::w) → ℝ,
      ENNReal.ofReal (schurUpperGaussian (Matrix.vec (schurWordParameter (false::w)
        (schurWordFreeCells (false::w) y)))) *
          H ((scalarFreeSplit w y).1,(scalarFreeSplit w y).2.2)) =
      ENNReal.ofReal (Real.sqrt (2*Real.pi) ^ schurWordSize w) *
        ∫⁻ a : Fin 1 → ℝ, ∫⁻ t : SchurWordFreeIndex w → ℝ,
          ENNReal.ofReal (Real.exp (-(a 0)^2/2)) *
            ENNReal.ofReal (schurUpperGaussian
              (Matrix.vec (schurWordParameter w (schurWordFreeCells w t)))) * H (a,t) := by
  let B : (Fin (schurWordSize w) × Fin 1 → ℝ) → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (schurUpperGaussian u)
  let F : (Fin 1 → ℝ) × (SchurWordFreeIndex w → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(z.1 0)^2/2)) *
      ENNReal.ofReal (schurUpperGaussian
        (Matrix.vec (schurWordParameter w (schurWordFreeCells w z.2)))) * H z
  have hB : Measurable B := continuous_schurUpperGaussian.measurable.ennreal_ofReal
  have ha : Measurable (fun a : Fin 1 → ℝ => ENNReal.ofReal (Real.exp (-(a 0)^2/2))) := by fun_prop
  have hF : Measurable F := ((ha.comp measurable_fst).mul
    ((measurable_freeParameterGaussian w).comp measurable_snd)).mul hH
  have he (y : SchurWordFreeIndex (false::w) → ℝ) :
      ENNReal.ofReal (schurUpperGaussian (Matrix.vec (schurWordParameter (false::w)
        (schurWordFreeCells (false::w) y)))) * H ((scalarFreeSplit w y).1,(scalarFreeSplit w y).2.2) =
      B (scalarFreeSplit w y).2.1 * F ((scalarFreeSplit w y).1,(scalarFreeSplit w y).2.2) := by
    rw [scalarFreeGaussian_eq,
      ENNReal.ofReal_mul' (show 0 ≤ schurUpperGaussian _ from (Real.exp_pos _).le),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    dsimp only [B,F]
    ac_rfl
  calc
    _ = ∫⁻ y, B (scalarFreeSplit w y).2.1 * F ((scalarFreeSplit w y).1,(scalarFreeSplit w y).2.2) :=
      lintegral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by
      have h := lintegral_literalTripleRead_separate (scalarFreeIndexEquiv w) B hB F hF
      simpa only [scalarFreeSplit,B,lintegral_schurUpperGaussian,Nat.mul_one,F] using! h

/-- The pair-word version has EXACT head exponent 2a²+b²+c² and coefficient-one U. -/
theorem lintegral_pairFreeGaussian (w : List Bool)
    (H : (Fin 3 → ℝ) × (SchurWordFreeIndex w → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ y : SchurWordFreeIndex (true::w) → ℝ,
      ENNReal.ofReal (schurUpperGaussian (Matrix.vec (schurWordParameter (true::w)
        (schurWordFreeCells (true::w) y)))) * H ((pairFreeSplit w y).1,(pairFreeSplit w y).2.2)) =
      ENNReal.ofReal (Real.sqrt (2*Real.pi) ^ (2*schurWordSize w)) *
        ∫⁻ a : Fin 3 → ℝ, ∫⁻ t : SchurWordFreeIndex w → ℝ,
          ENNReal.ofReal (Real.exp (-(2*(a 0)^2+(a 1)^2+(a 2)^2)/2)) *
            ENNReal.ofReal (schurUpperGaussian
              (Matrix.vec (schurWordParameter w (schurWordFreeCells w t)))) * H (a,t) := by
  let B : (Fin (schurWordSize w) × Fin 2 → ℝ) → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (schurUpperGaussian u)
  let F : (Fin 3 → ℝ) × (SchurWordFreeIndex w → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(2*(z.1 0)^2+(z.1 1)^2+(z.1 2)^2)/2)) *
      ENNReal.ofReal (schurUpperGaussian
        (Matrix.vec (schurWordParameter w (schurWordFreeCells w z.2)))) * H z
  have hB : Measurable B := continuous_schurUpperGaussian.measurable.ennreal_ofReal
  have ha : Measurable (fun a : Fin 3 → ℝ =>
      ENNReal.ofReal (Real.exp (-(2*(a 0)^2+(a 1)^2+(a 2)^2)/2))) := by fun_prop
  have hF : Measurable F := ((ha.comp measurable_fst).mul
    ((measurable_freeParameterGaussian w).comp measurable_snd)).mul hH
  have he (y : SchurWordFreeIndex (true::w) → ℝ) :
      ENNReal.ofReal (schurUpperGaussian (Matrix.vec (schurWordParameter (true::w)
        (schurWordFreeCells (true::w) y)))) * H ((pairFreeSplit w y).1,(pairFreeSplit w y).2.2) =
      B (pairFreeSplit w y).2.1 * F ((pairFreeSplit w y).1,(pairFreeSplit w y).2.2) := by
    rw [pairFreeGaussian_eq,
      ENNReal.ofReal_mul' (show 0 ≤ schurUpperGaussian _ from (Real.exp_pos _).le),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    dsimp only [B,F]
    ac_rfl
  calc
    _ = ∫⁻ y, B (pairFreeSplit w y).2.1 * F ((pairFreeSplit w y).1,(pairFreeSplit w y).2.2) :=
      lintegral_congr_ae (Filter.Eventually.of_forall he)
    _ = _ := by
      have h := lintegral_literalTripleRead_separate (pairFreeIndexEquiv w) B hB F hF
      simpa only [pairFreeSplit,B,lintegral_schurUpperGaussian,Nat.mul_comm,F] using! h

/-- Source positivity is independent of the between-block upper entries. -/
theorem scalarStepFree_positive_iff (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ) :
    SchurWordPositive (false::w) (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U) ↔
      SchurWordPositive w t := by
  simp only [SchurWordPositive,schurStepFreeCells_coordinates,schurTailInput_free]

theorem pairStepFree_positive_iff (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ) :
    SchurWordPositive (true::w) (schurStepFreeCells (pairFreeInput a b c) t U) ↔
      0 < c ∧ c ≤ b ∧ SchurWordPositive w t := by
  simp [SchurWordPositive,schurStepFreeCells_coordinates,schurHeadInput_free,
    schurTailInput_free,pairFreeInput,Function.flip_def]

/-- The actual representative list, retaining multiplicity, has no U dependence. -/
theorem scalarStepFree_headRoots (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ) :
    schurWordHeadRoots (false::w) (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U) =
      (a : ℂ) :: schurWordHeadRoots w t := by
  simp only [schurWordHeadRoots,schurStepFreeCells_coordinates,schurHeadInput_free,schurTailInput_free]

theorem pairStepFree_headRoots (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ) :
    schurWordHeadRoots (true::w) (schurStepFreeCells (pairFreeInput a b c) t U) =
      schurRoot a b c :: schurWordHeadRoots w t := by
  simp [schurWordHeadRoots,schurStepFreeCells_coordinates,schurHeadInput_free,
    schurTailInput_free,pairFreeInput,Function.flip_def]

/-- The ACTUAL signed Jacobian is U-independent, with exact Sylvester factors. -/
theorem scalarStepFree_det (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ) :
    LinearMap.det (schurWordDifferential (false::w)
      (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U)) =
      (sylvesterMatrix (schurWordParameter w t) (scalarBlock a)).det *
        LinearMap.det (schurWordDifferential w t) := by
  simpa only [schurStepFreeCells_coordinates,schurHeadInput_free,schurTailInput_free] using!
    det_schurWordDifferential_false w (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U)

theorem pairStepFree_det (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ) :
    LinearMap.det (schurWordDifferential (true::w)
      (schurStepFreeCells (pairFreeInput a b c) t U)) =
      (sylvesterMatrix (schurWordParameter w t) (schurBlock a b c)).det *
        (2*(b-c)) * LinearMap.det (schurWordDifferential w t) := by
  simpa [schurStepFreeCells_coordinates,schurHeadInput_free,schurTailInput_free,
    pairFreeInput,Matrix.vec,Function.flip_def] using!
    det_schurWordDifferential_true w (schurStepFreeCells (pairFreeInput a b c) t U)

/-- Full original order predicate, via the unchanged actual representative list. -/
theorem scalarStepFree_ordered_iff (w : List Bool) (a : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 1) (Fin (schurWordSize w)) ℝ) :
    SchurWordOrdered (false::w) (schurStepFreeCells (fun _ : Fin 1 × Fin 1 => a) t U) ↔
      ((a : ℂ) :: schurWordHeadRoots w t).Pairwise
        (fun z v => schurRootKey z ≤ schurRootKey v) := by
  exact (congrArg (fun l : List ℂ => l.Pairwise (fun z v => schurRootKey z ≤ schurRootKey v))
    (scalarStepFree_headRoots w a t U)).to_iff

theorem pairStepFree_ordered_iff (w : List Bool) (a b c : ℝ) (t : SchurWordCells w)
    (U : Matrix (Fin 2) (Fin (schurWordSize w)) ℝ) :
    SchurWordOrdered (true::w) (schurStepFreeCells (pairFreeInput a b c) t U) ↔
      (schurRoot a b c :: schurWordHeadRoots w t).Pairwise
        (fun z v => schurRootKey z ≤ schurRootKey v) := by
  exact (congrArg (fun l : List ℂ => l.Pairwise (fun z v => schurRootKey z ≤ schurRootKey v))
    (pairStepFree_headRoots w a b c t U)).to_iff

end Paper.Spectral
