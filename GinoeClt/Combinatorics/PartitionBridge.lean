/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Sort

/-!
# The canonical bridge between the two finite partition representations

Mathlib's ordered partitions put the blocks in increasing order of their
greatest elements and enumerate each block increasingly. Forgetting these
canonical enumerations gives an ordinary finite set partition.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Classical
open Set Function
namespace Paper.PartitionBridge

def block {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) : Finset (Fin n) :=
  Finset.univ.image (c.emb i)

@[simp] theorem mem_block {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length)
    (x : Fin n) : x ∈ block c i ↔ ∃ r, c.emb i r = x := by
  simp [block]

theorem coe_block {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    (block c i : Set (Fin n)) = Set.range (c.emb i) := by
  ext x
  simp [block]

@[simp] theorem card_block {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    (block c i).card = c.partSize i := by
  simp [block, Finset.card_image_of_injective _ (c.emb_strictMono i).injective]

theorem block_nonempty {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    (block c i).Nonempty :=
  ⟨c.emb i ⟨0, c.partSize_pos i⟩, (mem_block c i _).mpr ⟨_, rfl⟩⟩

theorem block_injective {n : ℕ} (c : OrderedFinpartition n) :
    Injective (block c) := by
  intro i j h
  let r : Fin (c.partSize i) := ⟨0, c.partSize_pos i⟩
  have hx : c.emb i r ∈ block c j := h ▸ (mem_block c i _).mpr ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := (mem_block c j _).mp hx
  exact congrArg Sigma.fst (c.emb_injective (a₁ := ⟨j, s⟩) (a₂ := ⟨i, r⟩) hs) |>.symm

def toFinpartition {n : ℕ} (c : OrderedFinpartition n) :
    Finpartition (Finset.univ : Finset (Fin n)) :=
  Finpartition.ofExistsUnique (Finset.univ.image (block c))
    (fun _ _ => Finset.subset_univ _)
    (by
      intro x _
      obtain ⟨⟨i, r⟩, hr⟩ := c.exists_inverse x
      refine ⟨block c i, ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
        (mem_block c i x).mpr ⟨r, hr⟩⟩, ?_⟩
      rintro B ⟨hB, hx⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨s, hs⟩ := (mem_block c j x).mp hx
      have hji : j = i := congrArg Sigma.fst
        (c.emb_injective (a₁ := ⟨j, s⟩) (a₂ := ⟨i, r⟩) (hs.trans hr.symm))
      exact congrArg (block c) hji)
    (by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact (block_nonempty c i).ne_empty hi)

@[simp] theorem toFinpartition_parts {n : ℕ} (c : OrderedFinpartition n) :
    (toFinpartition c).parts = Finset.univ.image (block c) := rfl

@[simp] theorem card_toFinpartition_parts {n : ℕ} (c : OrderedFinpartition n) :
    (toFinpartition c).parts.card = c.length := by
  simp [toFinpartition_parts, Finset.card_image_of_injective _ (block_injective c)]

def partMax {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n)))
    (B : P.parts) : Fin n :=
  B.val.max' (P.nonempty_of_mem_parts B.property)

theorem partMax_injective {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Injective (partMax P) := by
  intro B C h
  apply Subtype.ext
  apply P.eq_of_mem_parts B.property C.property
    (Finset.max'_mem _ _)
  change partMax P B ∈ (C : Finset (Fin n))
  rw [h]
  exact Finset.max'_mem _ _

def sortedParts {n : ℕ} (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Fin P.parts.card ≃ P.parts := by
  letI : LinearOrder P.parts := LinearOrder.lift' (partMax P) (partMax_injective P)
  exact (Fintype.orderIsoFinOfCardEq P.parts (k := P.parts.card) (by simp)).toEquiv

theorem sortedParts_max_strictMono {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    StrictMono (fun i => partMax P (sortedParts P i)) := by
  let : LinearOrder P.parts := LinearOrder.lift' (partMax P) (partMax_injective P)
  intro i j hij
  exact lt_of_le_of_ne
    ((Fintype.orderIsoFinOfCardEq P.parts (k := P.parts.card) (by simp)).map_rel_iff'.mpr hij.le)
    (by intro h; exact hij.ne ((sortedParts P).injective (partMax_injective P h)))

def toOrderedFinpartition {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : OrderedFinpartition n where
  length := P.parts.card
  partSize i := (sortedParts P i).val.card
  partSize_pos i := Finset.card_pos.mpr (P.nonempty_of_mem_parts (sortedParts P i).property)
  emb i := (sortedParts P i).val.orderEmbOfFin rfl
  emb_strictMono i := ((sortedParts P i).val.orderEmbOfFin rfl).strictMono
  parts_strictMono := by
    intro i j hij
    dsimp only
    rw [Finset.orderEmbOfFin_last rfl
      (Finset.card_pos.mpr (P.nonempty_of_mem_parts (sortedParts P i).property)),
      Finset.orderEmbOfFin_last rfl
      (Finset.card_pos.mpr (P.nonempty_of_mem_parts (sortedParts P j).property))]
    exact sortedParts_max_strictMono P hij
  disjoint := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin]
    apply Finset.disjoint_coe.mpr
    apply P.disjoint (sortedParts P i).property (sortedParts P j).property
    intro h
    exact hij ((sortedParts P).injective (Subtype.ext h))
  cover x := by
    obtain ⟨B, hB, hx⟩ := P.exists_mem (Finset.mem_univ x)
    refine ⟨(sortedParts P).symm ⟨B, hB⟩, ?_⟩
    rw [Finset.range_orderEmbOfFin]
    simpa using hx

@[simp] theorem block_toOrderedFinpartition {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) (i : Fin P.parts.card) :
    block (toOrderedFinpartition P) i = (sortedParts P i).val := by
  change Finset.univ.image ((sortedParts P i).val.orderEmbOfFin rfl) = (sortedParts P i).val
  exact Finset.image_orderEmbOfFin_univ _ _

@[simp] theorem toFinpartition_toOrderedFinpartition {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    toFinpartition (toOrderedFinpartition P) = P := by
  ext B
  simp only [toFinpartition_parts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [block_toOrderedFinpartition P i]
    exact (sortedParts P i).property
  · intro hB
    exact ⟨(sortedParts P).symm ⟨B, hB⟩, by simp⟩

/-- The canonical greatest element used in the ordering of blocks. -/
def greatest {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) : Fin n :=
  c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩

theorem greatest_mem_block {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    greatest c i ∈ block c i :=
  (mem_block c i _).mpr ⟨_, rfl⟩

theorem max'_block_eq_greatest {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    (block c i).max' (block_nonempty c i) = greatest c i := by
  apply (Finset.max'_eq_iff (block c i) (block_nonempty c i) _).mpr
  refine ⟨greatest_mem_block c i, ?_⟩
  intro b hb
  obtain ⟨r, rfl⟩ := (mem_block c i b).mp hb
  apply (c.emb_strictMono i).monotone
  change r.val ≤ c.partSize i - 1
  omega

theorem greatest_eq_of_block_eq {n : ℕ} (c d : OrderedFinpartition n)
    (i : Fin c.length) (j : Fin d.length) (h : block c i = block d j) :
    greatest c i = greatest d j := by
  calc
    greatest c i = (block c i).max' (block_nonempty c i) := (max'_block_eq_greatest c i).symm
    _ = (block d j).max' (block_nonempty d j) := by congr 1
    _ = greatest d j := max'_block_eq_greatest d j

theorem eq_of_blocks {n : ℕ} (c d : OrderedFinpartition n) (hl : c.length = d.length)
    (hb : ∀ i : Fin c.length, block c i = block d (Fin.cast hl i)) : c = d := by
  rcases c with ⟨cl, cp, hcp, ce, hce, hcs, hcd, hcc⟩
  rcases d with ⟨dl, dp, hdp, de, hde, hds, hdd, hdc⟩
  dsimp only at hl
  subst dl
  have hp : cp = dp := by
    funext i
    have hi := congrArg Finset.card (hb i)
    simpa only [card_block, Fin.cast_refl, id_eq] using hi
  subst dp
  have he : ce = de := by
    funext i
    apply ((hce i).range_inj_of_wellFoundedLT (hde i)).mp
    have hi := congrArg (fun B : Finset (Fin n) => (B : Set (Fin n))) (hb i)
    simpa only [coe_block, Fin.cast_refl, id_eq] using hi
  subst de
  rfl

theorem greatest_range_subset {n : ℕ} (c d : OrderedFinpartition n)
    (h : toFinpartition c = toFinpartition d) :
    Set.range (greatest c) ⊆ Set.range (greatest d) := by
  rintro z ⟨i, rfl⟩
  have hi : block c i ∈ (toFinpartition d).parts := by
    rw [← h]
    simp [toFinpartition_parts]
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  exact ⟨j, greatest_eq_of_block_eq d c j i hj⟩

theorem toFinpartition_injective {n : ℕ} :
    Injective (toFinpartition (n := n)) := by
  intro c d h
  have hl : c.length = d.length := by
    rw [← card_toFinpartition_parts c, ← card_toFinpartition_parts d, h]
  have hrange : Set.range (greatest c) = Set.range (greatest d) :=
    Set.Subset.antisymm (greatest_range_subset c d h) (greatest_range_subset d c h.symm)
  have hcast : Set.range (fun i : Fin c.length => greatest d (Fin.cast hl i)) =
      Set.range (greatest d) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast hl.symm j, by simp⟩
  have hm : greatest c = (fun i => greatest d (Fin.cast hl i)) :=
    (c.parts_strictMono.range_inj_of_wellFoundedLT
      (d.parts_strictMono.comp (Fin.cast_strictMono hl))).mp (hrange.trans hcast.symm)
  apply eq_of_blocks c d hl
  intro i
  apply (toFinpartition c).eq_of_mem_parts
  · simp [toFinpartition_parts]
  · rw [h]
    simp [toFinpartition_parts]
  · exact greatest_mem_block c i
  · rw [congrFun hm i]
    exact greatest_mem_block d _

@[simp] theorem toOrderedFinpartition_toFinpartition {n : ℕ}
    (c : OrderedFinpartition n) : toOrderedFinpartition (toFinpartition c) = c := by
  apply toFinpartition_injective
  exact toFinpartition_toOrderedFinpartition (toFinpartition c)

/-- Canonical finite partitions and ordinary set partitions have identical
mathematical blocks; no multiplicity factor is introduced by ordering. -/
def equiv (n : ℕ) :
    OrderedFinpartition n ≃ Finpartition (Finset.univ : Finset (Fin n)) where
  toFun := toFinpartition
  invFun := toOrderedFinpartition
  left_inv := toOrderedFinpartition_toFinpartition
  right_inv := toFinpartition_toOrderedFinpartition

/-- Every commutative product depending only on block sizes is preserved. -/
theorem prod_partSize_eq {n : ℕ} {R : Type*} [CommMonoid R]
    (c : OrderedFinpartition n) (w : ℕ → R) :
    (∏ i : Fin c.length, w (c.partSize i)) =
      ∏ B ∈ (equiv n c).parts, w B.card := by
  change _ = ∏ B ∈ Finset.univ.image (block c), w B.card
  rw [Finset.prod_image]
  · simp only [card_block]
  · exact (block_injective c).injOn

/-- The sum of every block-size product can be reindexed without changing its
coefficient, including the empty partition. -/
theorem sum_prod_partSize_eq {n : ℕ} {R : Type*} [CommSemiring R] (w : ℕ → R) :
    (∑ c : OrderedFinpartition n, ∏ i : Fin c.length, w (c.partSize i)) =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)), ∏ B ∈ P.parts, w B.card := by
  rw [← (equiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  exact prod_partSize_eq c w

end Paper.PartitionBridge
