/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurPairWeight
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Matrix ENNReal
namespace Paper.Spectral

/-- Spectral pair coordinates retain the zero-gap boundary. -/
def pairSpectralDomain : Set (Fin 2 → ℝ) := {x | 0 < x 0 ∧ 0 ≤ x 1}

/-- The actual original normalized pair domain in the raw free cells (b,c). -/
def pairRawDomain : Set (Fin 2 → ℝ) := {x | 0 < x 1 ∧ x 1 ≤ x 0}

def pairSpectralCoordinates (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.sqrt (x 0 * x 1), x 0 - x 1]

lemma pair_vector_eta (x : Fin 2 → ℝ) : ![x 0,x 1] = x := by
  ext i
  fin_cases i <;> rfl

theorem pairSpectralCoordinates_left_inv {x : Fin 2 → ℝ} (hx : 0 < x 0) :
    pairSpectralCoordinates (pairOffDiagonal x) = x := by
  have h := pairOffDiagonal_spectral (delta := x 1) hx
  rw [pair_vector_eta] at h
  ext i
  fin_cases i
  · exact h.1
  · exact h.2

theorem pairOffDiagonal_right_inv {x : Fin 2 → ℝ}
    (hx : x ∈ pairRawDomain) :
    pairOffDiagonal (pairSpectralCoordinates x) = x := by
  have hb : 0 < x 0 := lt_of_lt_of_le hx.1 hx.2
  simpa only [pairSpectralCoordinates,pair_vector_eta] using
    pairOffDiagonal_inverse hb hx.1

theorem pairOffDiagonal_mapsTo :
    MapsTo pairOffDiagonal pairSpectralDomain pairRawDomain := by
  intro x hx
  have hp := pairOffDiagonal_pos (delta := x 1) hx.1
  have ho := (pairOffDiagonal_order_iff (x 0) (x 1)).mpr hx.2
  rw [pair_vector_eta] at hp ho
  exact ⟨hp.2,ho⟩

theorem pairSpectralCoordinates_mapsTo :
    MapsTo pairSpectralCoordinates pairRawDomain pairSpectralDomain := by
  intro x hx
  change 0 < Real.sqrt (x 0 * x 1) ∧ 0 ≤ x 0 - x 1
  exact ⟨Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hx.1 hx.2) hx.1),
    sub_nonneg.mpr hx.2⟩

theorem pairOffDiagonal_image :
    pairOffDiagonal '' pairSpectralDomain = pairRawDomain := by
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact pairOffDiagonal_mapsTo hx
  · intro x hx
    exact ⟨pairSpectralCoordinates x,pairSpectralCoordinates_mapsTo hx,
      pairOffDiagonal_right_inv hx⟩

theorem pairOffDiagonal_injOn :
    InjOn pairOffDiagonal pairSpectralDomain := by
  intro x hx y hy h
  have hh := congrArg pairSpectralCoordinates h
  rwa [pairSpectralCoordinates_left_inv hx.1,pairSpectralCoordinates_left_inv hy.1] at hh

theorem measurableSet_pairSpectralDomain : MeasurableSet pairSpectralDomain := by
  exact (isOpen_lt continuous_const (continuous_apply 0)).measurableSet.inter
    (isClosed_le continuous_const (continuous_apply 1)).measurableSet

theorem measurableSet_pairRawDomain : MeasurableSet pairRawDomain := by
  exact (isOpen_lt continuous_const (continuous_apply 1)).measurableSet.inter
    (isClosed_le (continuous_apply 1) (continuous_apply 0)).measurableSet

lemma pairOffDiagonalJacobianCLM_det (y delta : ℝ) :
    (pairOffDiagonalJacobianCLM y delta).det = -(2*y/pairRadius y delta) := by
  change LinearMap.det (Matrix.toLin' (pairOffDiagonalJacobian y delta)) = _
  rw [← LinearMap.det_toMatrix',LinearMap.toMatrix'_toLin',det_pairOffDiagonalJacobian]

/-- Genuine injective change of ordinary two-dimensional volume from the
original b≥c>0 source to y>0, delta≥0, including its boundary. -/
theorem lintegral_pairRawDomain (g : (Fin 2 → ℝ) → ℝ≥0∞) :
    (∫⁻ b in pairRawDomain, g b) =
      ∫⁻ x in pairSpectralDomain,
        ENNReal.ofReal (2*x 0/pairRadius (x 0) (x 1)) * g (pairOffDiagonal x) := by
  have hd : ∀ x ∈ pairSpectralDomain,
      HasFDerivWithinAt pairOffDiagonal
        (pairOffDiagonalJacobianCLM (x 0) (x 1)) pairSpectralDomain x := by
    intro x hx
    have hh := (hasFDerivAt_pairOffDiagonal (delta := x 1) hx.1).hasFDerivWithinAt
      (s := pairSpectralDomain)
    simpa only [pair_vector_eta] using hh
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (Fin 2 → ℝ)) measurableSet_pairSpectralDomain hd
      pairOffDiagonal_injOn g
  rw [pairOffDiagonal_image] at h
  refine h.trans (setLIntegral_congr_fun measurableSet_pairSpectralDomain ?_)
  intro x hx
  change ENNReal.ofReal |(pairOffDiagonalJacobianCLM (x 0) (x 1)).det| * g (pairOffDiagonal x) = _
  rw [pairOffDiagonalJacobianCLM_det,abs_neg,abs_of_pos
    (div_pos (mul_pos (by norm_num) hx.1) (pairRadius_pos hx.1))]

/-- Ordinary coordinate volume in spectral pair cells, with the exact y>0,
delta≥0 domain and no integrability assumption for the nonnegative weight. -/
theorem lintegral_pairSpectralDomain (f : (Fin 2 → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x in pairSpectralDomain, f x) =
      ∫⁻ y in Ioi (0 : ℝ), ∫⁻ delta in Ici (0 : ℝ), f ![y,delta] := by
  have h := (volume_preserving_finTwoArrow ℝ).symm
    MeasurableEquiv.finTwoArrow |>.setLIntegral_comp_preimage
      measurableSet_pairSpectralDomain hf
  have hpre : MeasurableEquiv.finTwoArrow.symm ⁻¹' pairSpectralDomain =
      Ioi (0 : ℝ) ×ˢ Ici (0 : ℝ) := by
    ext x
    rfl
  rw [hpre] at h
  rw [← h]
  exact setLIntegral_prod (fun p : ℝ × ℝ => f ![p.1,p.2])
    ((hf.comp MeasurableEquiv.finTwoArrow.symm.measurable).aemeasurable)

/-- Nonnegative delta integral obtained from the already checked genuine
Bochner pair-weight integral. The boundary delta=0 is restored by nullity. -/
theorem lintegral_pairCoordinate_weight {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫⁻ delta in Ici (0 : ℝ), ENNReal.ofReal
      (4*y*delta/pairRadius y delta * Real.exp (-(a^2+y^2+delta^2/2)))) =
      ENNReal.ofReal (2*Real.sqrt (2*Real.pi)*y*Real.exp (y^2-a^2)*
        Paper.Kernel.erfc (Real.sqrt 2*y)) := by
  have hp := pairCoordinate_weight_integral hy a
  rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rw [← ofReal_integral_eq_lintegral_ofReal hp.1.integrableOn ?_,hp.2]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with delta hd
  have hr := pairRadius_pos (delta := delta) hy
  have hd' : 0 < delta := hd
  change (0 : ℝ) ≤ 4*y*delta/pairRadius y delta * Real.exp (-(a^2+y^2+delta^2/2))
  positivity

lemma pairOffDiagonal_gaussian_weight (a : ℝ) (H : ℝ → ℝ≥0∞)
    {x : Fin 2 → ℝ} (hx : 0 < x 0) :
    ENNReal.ofReal (2*x 0/pairRadius (x 0) (x 1)) *
        (ENNReal.ofReal (2*((pairOffDiagonal x) 0-(pairOffDiagonal x) 1) *
          Real.exp (-(2*a^2+(pairOffDiagonal x) 0^2+(pairOffDiagonal x) 1^2)/2)) *
          H (Real.sqrt ((pairOffDiagonal x) 0*(pairOffDiagonal x) 1))) =
      ENNReal.ofReal (4*x 0*x 1/pairRadius (x 0) (x 1) *
        Real.exp (-(a^2+x 0^2+x 1^2/2))) * H (x 0) := by
  have hs := pairOffDiagonal_spectral (delta := x 1) hx
  have hq := pairOffDiagonal_sq_sum (x 0) (x 1)
  rw [pair_vector_eta] at hs hq
  have ha : -(2*a^2+(pairOffDiagonal x) 0^2+(pairOffDiagonal x) 1^2)/2 =
      -(a^2+x 0^2+x 1^2/2) := by nlinarith only [hq]
  have he : (2*x 0/pairRadius (x 0) (x 1)) *
        (2*((pairOffDiagonal x) 0-(pairOffDiagonal x) 1) *
          Real.exp (-(2*a^2+(pairOffDiagonal x) 0^2+(pairOffDiagonal x) 1^2)/2)) =
      4*x 0*x 1/pairRadius (x 0) (x 1) *
        Real.exp (-(a^2+x 0^2+x 1^2/2)) := by
    rw [hs.2,ha]
    ring
  rw [hs.1,← mul_assoc,← ENNReal.ofReal_mul (by
    exact (div_pos (mul_pos (by norm_num) hx) (pairRadius_pos hx)).le),he]

/-- Integration over the original b≥c>0 free head, with its ACTUAL local
word determinant 2(b-c), leaves the exact complex-pair weight. The Borel
remaining factor may be infinite and is assumed to depend only on y=√(bc). -/
theorem lintegral_pairRaw_gaussian (a : ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ b in pairRawDomain,
      ENNReal.ofReal (2*(b 0-b 1)*Real.exp (-(2*a^2+b 0^2+b 1^2)/2)) *
        H (Real.sqrt (b 0*b 1))) =
      ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (2*Real.sqrt (2*Real.pi)*y*Real.exp (y^2-a^2)*
          Paper.Kernel.erfc (Real.sqrt 2*y)) * H y := by
  rw [lintegral_pairRawDomain]
  calc
    _ = ∫⁻ x in pairSpectralDomain,
        ENNReal.ofReal (4*x 0*x 1/pairRadius (x 0) (x 1) *
          Real.exp (-(a^2+x 0^2+x 1^2/2))) * H (x 0) := by
      apply setLIntegral_congr_fun measurableSet_pairSpectralDomain
      intro x hx
      exact pairOffDiagonal_gaussian_weight a H hx.1
    _ = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ delta in Ici (0 : ℝ),
        ENNReal.ofReal (4*y*delta/pairRadius y delta *
          Real.exp (-(a^2+y^2+delta^2/2))) * H y := by
      exact lintegral_pairSpectralDomain _ (by unfold pairRadius; fun_prop)
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change (∫⁻ delta in Ici (0 : ℝ), ENNReal.ofReal
        (4*y*delta/pairRadius y delta * Real.exp (-(a^2+y^2+delta^2/2))) * H y) = _
      rw [lintegral_mul_const _ (by unfold pairRadius; fun_prop),
        lintegral_pairCoordinate_weight hy a]

/-- The exact actual pair-head free domain, with field order (a,b,c). -/
def pairHeadDomain : Set (Fin 3 → ℝ) := {h | 0 < h 2 ∧ h 2 ≤ h 1}

theorem measurableSet_pairHeadDomain : MeasurableSet pairHeadDomain := by
  exact (isOpen_lt continuous_const (continuous_apply 2)).measurableSet.inter
    (isClosed_le (continuous_apply 2) (continuous_apply 1)).measurableSet

lemma pairHeadSplit_inverse (p : ℝ × (Fin 2 → ℝ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm p =
      ![p.1,p.2 0,p.2 1] := by
  ext i
  fin_cases i <;> rfl

/-- Literal head product-volume separation; no Jacobian scalar is hidden. -/
theorem lintegral_pairHeadDomain (g : (Fin 3 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ h in pairHeadDomain, g h) =
      ∫⁻ a : ℝ, ∫⁻ b in pairRawDomain, g ![a,b 0,b 1] := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm e
  have h := hmp.setLIntegral_comp_preimage measurableSet_pairHeadDomain hg
  have hp : e.symm ⁻¹' pairHeadDomain = Set.univ ×ˢ pairRawDomain := by
    ext p
    change (0 < p.2 1 ∧ p.2 1 ≤ p.2 0) ↔ (True ∧ (0 < p.2 1 ∧ p.2 1 ≤ p.2 0))
    simp
  rw [hp] at h
  rw [← h]
  have hg' : Measurable (fun p : ℝ × (Fin 2 → ℝ) => g ![p.1,p.2 0,p.2 1]) := by
    fun_prop
  change (∫⁻ p in Set.univ ×ˢ pairRawDomain,
    g ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm p)
      ∂(volume.prod volume)) = _
  simp_rw [pairHeadSplit_inverse]
  simpa only [setLIntegral_univ] using
    (setLIntegral_prod (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Fin 2 → ℝ))) (s := Set.univ) (t := pairRawDomain)
      (fun p : ℝ × (Fin 2 → ℝ) => g ![p.1,p.2 0,p.2 1]) hg'.aemeasurable)

/-- Actual free pair-head Gaussian/Jacobian integration in ordinary product
volume. H uses precisely (a,√(bc)), with no c≤b restriction lost. -/
theorem lintegral_pairHead_gaussian (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ h in pairHeadDomain,
      ENNReal.ofReal (2*(h 1-h 2)*Real.exp (-(2*h 0^2+h 1^2+h 2^2)/2)) *
        H (h 0,Real.sqrt (h 1*h 2))) =
      ∫⁻ a : ℝ, ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (2*Real.sqrt (2*Real.pi)*y*Real.exp (y^2-a^2)*
          Paper.Kernel.erfc (Real.sqrt 2*y)) * H (a,y) := by
  rw [lintegral_pairHeadDomain _ (by fun_prop)]
  apply lintegral_congr
  intro a
  exact lintegral_pairRaw_gaussian a (fun y => H (a,y))
    (hH.comp (measurable_const.prodMk measurable_id))

/-- Ordinary Euclidean complex area is the product of real and imaginary
coordinates, with no normalization scalar. -/
theorem lintegral_complex_upper (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in {z : ℂ | 0 < z.im}, f z) =
      ∫⁻ a : ℝ, ∫⁻ y in Ioi (0 : ℝ), f ((a : ℂ)+(y : ℂ)*Complex.I) := by
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd
  have h := hmp.setLIntegral_comp_preimage (s := {z : ℂ | 0 < z.im})
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet hf
  have hp : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | 0 < z.im} =
      Set.univ ×ˢ Ioi (0 : ℝ) := by
    ext p
    change 0 < p.2 ↔ (True ∧ 0 < p.2)
    simp
  rw [hp] at h
  rw [← h]
  have he (p : ℝ × ℝ) :
      Complex.measurableEquivRealProd.symm p = (p.1 : ℂ)+(p.2 : ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  simp_rw [he]
  have hf' : Measurable (fun p : ℝ × ℝ => f ((p.1 : ℂ)+(p.2 : ℂ)*Complex.I)) := by
    fun_prop
  simpa only [Measure.volume_eq_prod,setLIntegral_univ] using
    (setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Set.univ) (t := Ioi (0 : ℝ))
      (fun p : ℝ × ℝ => f ((p.1 : ℂ)+(p.2 : ℂ)*Complex.I)) hf'.aemeasurable)

/-- Actual pair-head Gaussian/Jacobian reduction directly to ordinary upper
complex area and a test weight on the raw upper eigenvalue. -/
theorem lintegral_pairHead_gaussian_complex (H : ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ h in pairHeadDomain,
      ENNReal.ofReal (2*(h 1-h 2)*Real.exp (-(2*h 0^2+h 1^2+h 2^2)/2)) *
        H ((h 0 : ℂ)+(Real.sqrt (h 1*h 2) : ℂ)*Complex.I)) =
      ∫⁻ z in {z : ℂ | 0 < z.im},
        ENNReal.ofReal (2*Real.sqrt (2*Real.pi)*z.im*Real.exp (z.im^2-z.re^2)*
          Paper.Kernel.erfc (Real.sqrt 2*z.im)) * H z := by
  have herfc : Measurable Paper.Kernel.erfc := Paper.Kernel.continuous_erfc.measurable
  rw [lintegral_complex_upper _ (by fun_prop)]
  simpa only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
    zero_mul,add_zero,zero_add,sub_zero] using
    lintegral_pairHead_gaussian (fun p : ℝ × ℝ =>
      H ((p.1 : ℂ)+(p.2 : ℂ)*Complex.I)) (by fun_prop)

end Paper.Spectral
