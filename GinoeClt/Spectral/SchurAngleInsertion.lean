/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurParameterSemantics
@[expose] public section
noncomputable section
namespace Paper.Spectral

/-- The actual word differential depends on the parameter matrix K, not raw angles. -/
theorem schurWordDifferential_congr_parameter (w : List Bool)
    (p q : SchurWordCells w) (h : schurWordParameter w p = schurWordParameter w q) :
    schurWordDifferential w p = schurWordDifferential w q := by
  exact congrArg (fun M => schurDiagonalLinearMap M
    (schurWordOmega w) (schurWordParameter w)) h

/-- Any angular vector can be inserted while keeping the SAME actual parameter matrix. -/
theorem exists_schurWord_angle_parameter (w : List Bool) (p : SchurWordCells w)
    (a : SchurWordAngles w) :
    ∃ q : SchurWordCells w,
      schurWordAngleMap w q = a ∧ schurWordParameter w q = schurWordParameter w p := by
  refine ⟨schurWordAngleSection w a +
    (p-schurWordAngleSection w (schurWordAngleMap w p)),?_,?_⟩
  · rw [map_add,map_sub,schurWordAngleMap_section,schurWordAngleMap_section,sub_self,add_zero]
  · rw [map_add,map_sub,schurWordParameter_angleSection,
      schurWordParameter_angleSection,zero_add,sub_zero]

/-- At an actual regular point, a chosen angle and actual parameter K determine UNIQUE raw cells. -/
theorem existsUnique_schurWord_angle_parameter (w : List Bool) (p : SchurWordCells w)
    (hd : LinearMap.det (schurWordDifferential w p) ≠ 0) (a : SchurWordAngles w) :
    ∃! q : SchurWordCells w,
      schurWordAngleMap w q = a ∧ schurWordParameter w q = schurWordParameter w p := by
  obtain ⟨q,hq⟩ := exists_schurWord_angle_parameter w p a
  refine ⟨q,hq,?_⟩
  intro r hr
  apply schurWord_joint_injective w p hd
  apply Prod.ext
  · have ha := hr.1.trans hq.1.symm
    change (skewCoordinateEquiv (schurWordSize w)).symm (schurWordOmegaSkew w r) =
      (skewCoordinateEquiv (schurWordSize w)).symm (schurWordOmegaSkew w q) at ha
    have hs := (skewCoordinateEquiv (schurWordSize w)).symm.injective ha
    exact congrArg Subtype.val hs
  · exact hr.2.trans hq.2.symm

/-- All physical source conditions are retained after angle insertion. -/
theorem schurWord_source_congr_parameter (w : List Bool) (p q : SchurWordCells w)
    (h : schurWordParameter w p = schurWordParameter w q) :
    (SchurWordPositive w p ↔ SchurWordPositive w q) ∧
      (SchurWordOrdered w p ↔ SchurWordOrdered w q) ∧
      (SchurWordPairGaps w p ↔ SchurWordPairGaps w q) ∧
      (LinearMap.det (schurWordDifferential w p) ≠ 0 ↔
        LinearMap.det (schurWordDifferential w q) ≠ 0) := by
  have hs := schurWordParameter_semantics_eq w p q h
  refine ⟨hs.1,schurWordOrdered_congr_parameter w p q h,hs.2.1,?_⟩
  rw [schurWordDifferential_congr_parameter w p q h]

end Paper.Spectral
