/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.OrderedSchurCoverage
@[expose] public section
noncomputable section
namespace Paper.Spectral

/-- Key comparison preserves the order of imaginary parts. -/
theorem schurRootKey_im_le {z u : ℂ} (h : schurRootKey z ≤ schurRootKey u) : z.im ≤ u.im := by
  rcases (schurRootKey_le_iff z u).mp h with hlt | ⟨heq,hre⟩
  · exact hlt.le
  · exact heq.le

/-- Upper tags are monotone in the key order. -/
theorem schurRootKey_upper_tag_le {z u : ℂ} (h : schurRootKey z ≤ schurRootKey u) :
    decide (0 < z.im) ≤ decide (0 < u.im) := by
  by_cases hz : 0 < z.im
  · have hu : 0 < u.im := lt_of_lt_of_le hz (schurRootKey_im_le h)
    simp [hz,hu]
  · simp [hz]

/-- A nondecreasing Boolean list consists of its false tags followed by its true tags. -/
theorem bool_list_eq_canonical (w : List Bool) (hs : w.Pairwise (· ≤ ·)) :
    w = List.replicate (w.count false) false ++ List.replicate (w.count true) true := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have ht := List.pairwise_cons.mp hs
    cases b
    · calc
        false :: w = false :: (List.replicate (w.count false) false ++
          List.replicate (w.count true) true) := congrArg (List.cons false) (ih ht.2)
        _ = _ := by simp [List.replicate_succ, List.cons_append]
    · have hall : ∀ b ∈ w, b = true := by
        intro b hb
        have h := ht.1 b hb
        cases b with
        | false => exact False.elim ((by decide : ¬(true ≤ false)) h)
        | true => rfl
      have hw := List.eq_replicate_of_mem hall
      rw [hw]
      simp [List.count_replicate, List.replicate_succ]

/-- Ordered normalized representatives force precisely the standard real/pair sector word. -/
theorem ordered_schurWord_eq_canonical (w : List Bool) (p : SchurWordCells w)
    (hp : SchurWordPositive w p) (ho : SchurWordOrdered w p) :
    w = List.replicate (w.count false) false ++ List.replicate (w.count true) true := by
  have htags : ((schurWordHeadRoots w p).map (fun z : ℂ => decide (0 < z.im))).Pairwise (· ≤ ·) :=
    ho.map _ (fun z u h => schurRootKey_upper_tag_le h)
  rw [map_upper_schurWordHeadRoots w p hp] at htags
  exact bool_list_eq_canonical w htags

end Paper.Spectral
