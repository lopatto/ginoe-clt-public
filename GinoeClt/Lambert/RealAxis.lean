/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Lambert.Domain
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue

/-! # Exact real-axis component of the complex principal inverse -/

@[expose] public section
noncomputable section
open Set

namespace Paper.Lambert

def realExpMul (u : ℝ) : ℝ := u * Real.exp u

theorem continuous_realExpMul : Continuous realExpMul :=
  continuous_id.mul Real.continuous_exp

theorem hasDerivAt_realExpMul (u : ℝ) :
    HasDerivAt realExpMul (Real.exp u * (1 + u)) u := by
  have hh := (hasDerivAt_id u).mul (Real.hasDerivAt_exp u)
  have hc : (1 : ℝ) * Real.exp u + u * Real.exp u = Real.exp u * (1 + u) := by ring
  have h := hh.congr_deriv hc
  unfold realExpMul
  simpa only [Pi.mul_def, id_eq] using h

theorem strictMonoOn_realExpMul : StrictMonoOn realExpMul (Set.Ioi (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _) continuous_realExpMul.continuousOn
  intro u hu
  rw [(hasDerivAt_realExpMul u).deriv]
  have hh : -1 < u := by simpa only [interior_Ioi, Set.mem_Ioi] using hu
  exact mul_pos (Real.exp_pos _) (by linarith)

theorem existsUnique_realExpMul {r : ℝ} (hr : -Real.exp (-1) < r) :
    ∃! u : ℝ, -1 < u ∧ realExpMul u = r := by
  let b := max 1 (r + 1)
  have hb : 0 ≤ b := le_trans (by norm_num) (le_max_left _ _)
  have hrb : r < b := by have := le_max_right 1 (r + 1); linarith
  have hfb : r < realExpMul b := by
    have he : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
    exact hrb.trans_le (by simpa only [realExpMul, mul_one] using mul_le_mul_of_nonneg_left he hb)
  have hfa : realExpMul (-1) < r := by simpa [realExpMul] using hr
  obtain ⟨u, hu, he⟩ := intermediate_value_Ioo (a := (-1 : ℝ)) (b := b)
    (by linarith) continuous_realExpMul.continuousOn ⟨hfa, hfb⟩
  refine ⟨u, ⟨hu.1, he⟩, ?_⟩
  rintro v ⟨hv, hvf⟩
  exact strictMonoOn_realExpMul.injOn hv hu.1 (hvf.trans he.symm)

/-- A real point of the slit plane has exactly one preimage in the proposed
complex principal domain. Nonreal preimages there are ruled out by the sign identity. -/
theorem existsUnique_expMul_real {r : ℝ} (hr : -Real.exp (-1) < r) :
    ∃! w : ℂ, w ∈ principalDomain ∧ expMul w = (r : ℂ) := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_realExpMul hr
  refine ⟨(u : ℂ), ⟨(ofReal_mem_principalDomain u).mpr hu.1, ?_⟩, ?_⟩
  · rw [expMul_ofReal]
    exact congrArg (fun t : ℝ => (t : ℂ)) hu.2
  · rintro w ⟨hw, hfw⟩
    have hi : w.im = 0 := (expMul_im_eq_zero_iff hw).mp (by rw [hfw]; rfl)
    have hew : w = (w.re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact hi
    have hwr : -1 < w.re := (ofReal_mem_principalDomain w.re).mp (hew ▸ hw)
    have hf : realExpMul w.re = r := by
      apply Complex.ofReal_injective
      change ((w.re * Real.exp w.re : ℝ) : ℂ) = (r : ℂ)
      rw [← expMul_ofReal, ← hew]
      exact hfw
    have he : w.re = u := huniq w.re ⟨hwr, hf⟩
    rw [hew, he]

end Paper.Lambert
