/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module

public import GinoeClt.Cumulants.FormalStirlingEGF
public import Mathlib.GroupTheory.Perm.Centralizer

/-! # Finite permutation cycle index and its formal generating function -/

@[expose] public section
noncomputable section
open scoped BigOperators Classical

namespace Paper.Cumulants

/-- Factorial symmetry of a multiset of cycle lengths. -/
def cycleSymmetry (l : Multiset ℕ) : ℕ :=
  ∏ m ∈ l.toFinset, Nat.factorial (l.count m)

/-- The standard denominator for permutations with the given cycle lengths. -/
def cycleDenominator (l : Multiset ℕ) : ℕ := l.prod * cycleSymmetry l

@[simp] theorem cycleSymmetry_zero : cycleSymmetry 0 = 1 := by
  simp [cycleSymmetry]

@[simp] theorem cycleDenominator_zero : cycleDenominator 0 = 1 := by
  simp [cycleDenominator]

theorem cycleSymmetry_cons (a : ℕ) (l : Multiset ℕ) :
    cycleSymmetry (a ::ₘ l) = (l.count a + 1) * cycleSymmetry l := by
  have hi : cycleSymmetry l = ∏ m ∈ insert a l.toFinset, Nat.factorial (l.count m) := by
    by_cases ha : a ∈ l.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      rfl
    · rw [Finset.prod_insert ha]
      simp only [cycleSymmetry, Multiset.count_eq_zero_of_notMem
        (fun h => ha (Multiset.mem_toFinset.mpr h)), Nat.factorial_zero, one_mul]
  unfold cycleSymmetry at hi ⊢
  rw [Multiset.toFinset_cons, ← Finset.mul_prod_erase _ _ (by simp : a ∈ insert a l.toFinset)]
  rw [Multiset.count_cons_self, Nat.factorial_succ, hi,
    ← Finset.mul_prod_erase _ (fun m => Nat.factorial (l.count m)) (by simp : a ∈ insert a l.toFinset)]
  rw [mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro m hm
  rw [Multiset.count_cons_of_ne (Finset.mem_erase.mp hm).1]

theorem cycleDenominator_cons (a : ℕ) (l : Multiset ℕ) :
    cycleDenominator (a ::ₘ l) = a * (l.count a + 1) * cycleDenominator l := by
  simp only [cycleDenominator, Multiset.prod_cons, cycleSymmetry_cons]
  ring

theorem cycleDenominator_pos (l : Multiset ℕ) (h : ∀ a ∈ l, 0 < a) :
    0 < cycleDenominator l := by
  unfold cycleDenominator cycleSymmetry
  apply Nat.mul_pos
  · exact Multiset.prod_pos h
  · exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- Separate the one-cycles from the nontrivial cycle lengths of a partition. -/
theorem partition_parts_split {n : ℕ} (p : n.Partition) :
    p.parts = p.parts.filter (fun m => 2 ≤ m) + Multiset.replicate (p.parts.count 1) 1 := by
  calc
    p.parts = p.parts.filter (fun m => 2 ≤ m) +
        p.parts.filter (fun m => ¬ 2 ≤ m) :=
      (Multiset.filter_add_not (fun m => 2 ≤ m) p.parts).symm
    _ = _ := by
      rw [← Multiset.filter_eq' p.parts 1]
      congr 1
      apply Multiset.filter_congr
      intro m hm
      have hp := p.parts_pos hm
      omega

theorem partition_cycle_sum {n : ℕ} (p : n.Partition) :
    (p.parts.filter (fun m => 2 ≤ m)).sum + p.parts.count 1 = n := by
  have hh := congrArg Multiset.sum (partition_parts_split p)
  simpa only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.mul_one, Nat.cast_id, p.parts_sum] using hh.symm


theorem cycleSymmetry_add_ones (l : Multiset ℕ) (h1 : 1 ∉ l) (c : ℕ) :
    cycleSymmetry (l + Multiset.replicate c 1) = Nat.factorial c * cycleSymmetry l := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Multiset.replicate_succ, Multiset.add_cons, cycleSymmetry_cons,
      Multiset.count_add, Multiset.count_eq_zero_of_notMem h1,
      Multiset.count_replicate_self, zero_add, ih, Nat.factorial_succ]
    ring

theorem cycleDenominator_add_ones (l : Multiset ℕ) (h1 : 1 ∉ l) (c : ℕ) :
    cycleDenominator (l + Multiset.replicate c 1) =
      Nat.factorial c * l.prod * cycleSymmetry l := by
  simp only [cycleDenominator, Multiset.prod_add, Multiset.prod_replicate,
    one_pow, mul_one, cycleSymmetry_add_ones l h1 c]
  ring

theorem partition_cycleDenominator {n : ℕ} (p : n.Partition) :
    cycleDenominator p.parts =
      Nat.factorial (n - (p.parts.filter (fun m => 2 ≤ m)).sum) *
        (p.parts.filter (fun m => 2 ≤ m)).prod *
          cycleSymmetry (p.parts.filter (fun m => 2 ≤ m)) := by
  have h1 : 1 ∉ p.parts.filter (fun m => 2 ≤ m) := by simp
  have hc := partition_cycle_sum p
  have hd : p.parts.count 1 = n - (p.parts.filter (fun m => 2 ≤ m)).sum := by omega
  conv_lhs => rw [partition_parts_split p]
  rw [cycleDenominator_add_ones _ h1, hd]

/-- Native permutation partition with the cardinality of Fin simplified. -/
def finPermPartition {n : ℕ} (σ : Equiv.Perm (Fin n)) : n.Partition where
  parts := σ.partition.parts
  parts_pos := σ.partition.parts_pos
  parts_sum := by simpa only [Fintype.card_fin] using σ.partition.parts_sum

@[simp] theorem finPermPartition_parts {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (finPermPartition σ).parts = σ.partition.parts := rfl

theorem filter_finPermPartition {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((finPermPartition σ).parts.filter (fun m => 2 ≤ m)) = σ.cycleType :=
  Equiv.Perm.filter_parts_partition_eq_cycleType

theorem finPermPartition_eq_of_isConj {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : IsConj σ τ) : finPermPartition σ = finPermPartition τ :=
  Nat.Partition.ext (congrArg (fun p : (Fintype.card (Fin n)).Partition => p.parts)
    (Equiv.Perm.partition_eq_of_isConj.mp h))

theorem exists_perm_partition {n : ℕ} (p : n.Partition) :
    ∃ σ : Equiv.Perm (Fin n), finPermPartition σ = p := by
  let l := p.parts.filter (fun m => 2 ≤ m)
  have hs := partition_cycle_sum p
  change l.sum + p.parts.count 1 = n at hs
  have hl : l.sum ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using Nat.le.intro hs
  have hp : ∀ a ∈ l, 2 ≤ a := fun a ha => (Multiset.mem_filter.mp ha).2
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin n)).mpr ⟨hl, hp⟩
  refine ⟨σ, Nat.Partition.ext ?_⟩
  rw [finPermPartition_parts, Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType,
    hσ, Fintype.card_fin]
  have hc : n - l.sum = p.parts.count 1 := by omega
  rw [hc]
  exact (partition_parts_split p).symm

/-- Full cycle-partition counting, with one-cycles included. This is a direct
consequence of Mathlib's centralizer count, with fixed-point multiplicity restored. -/
theorem card_perm_partition_mul {n : ℕ} (p : n.Partition) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => finPermPartition σ = p)).card *
      cycleDenominator p.parts = Nat.factorial n := by
  let l := p.parts.filter (fun m => 2 ≤ m)
  obtain ⟨σ, hσ⟩ := exists_perm_partition p
  have hσl : σ.cycleType = l := by
    rw [← filter_finPermPartition, hσ]
  have hf : (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => finPermPartition τ = p)) =
      Finset.univ.filter (fun τ => τ.cycleType = l) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hh
      rw [← filter_finPermPartition, hh]
    · intro hh
      exact (finPermPartition_eq_of_isConj
        (Equiv.Perm.isConj_of_cycleType_eq (hh.trans hσl.symm))).trans hσ
  have hs := partition_cycle_sum p
  have hh := Equiv.Perm.card_of_cycleType_mul_eq (Fin n) l
  have hc : l.sum ≤ Fintype.card (Fin n) ∧ ∀ a ∈ l, 2 ≤ a := by
    refine ⟨?_, fun a ha => (Multiset.mem_filter.mp ha).2⟩
    simpa only [Fintype.card_fin] using Nat.le.intro hs
  rw [ite_eq_left hc, Fintype.card_fin] at hh
  rw [hf, partition_cycleDenominator]
  exact hh


section Weights
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A finite cycle weight, divided only by its positive integer symmetry factor. -/
def multisetCycleWeight (r : ℕ → R) (l : Multiset ℕ) : R :=
  algebraMap ℚ R ((cycleDenominator l : ℚ)⁻¹) * (l.map r).prod

def partitionCycleWeight (r : ℕ → R) {n : ℕ} (p : n.Partition) : R :=
  multisetCycleWeight r p.parts

@[simp] theorem multisetCycleWeight_zero (r : ℕ → R) :
    multisetCycleWeight r 0 = 1 := by simp [multisetCycleWeight]

theorem multisetCycleWeight_cons (r : ℕ → R) (a : ℕ) (ha : 0 < a)
    (l : Multiset ℕ) (hl : ∀ b ∈ l, 0 < b) :
    (a : R) * (l.count a + 1 : ℕ) * multisetCycleWeight r (a ::ₘ l) =
      r a * multisetCycleWeight r l := by
  have hd : (cycleDenominator l : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (cycleDenominator_pos l hl).ne'
  have ha' : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  have hc : ((l.count a + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hq : (a : ℚ) * (l.count a + 1 : ℕ) *
      (cycleDenominator (a ::ₘ l) : ℚ)⁻¹ = (cycleDenominator l : ℚ)⁻¹ := by
    rw [cycleDenominator_cons]
    push_cast
    field_simp
  have hr := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_natCast] at hr
  simp only [multisetCycleWeight, Multiset.map_cons, Multiset.prod_cons]
  calc
    _ = ((a : R) * (l.count a + 1 : ℕ) *
        algebraMap ℚ R ((cycleDenominator (a ::ₘ l) : ℚ)⁻¹)) *
          (r a * (l.map r).prod) := by ring
    _ = _ := by rw [hr]; ring


theorem sum_partitionCycleWeight_marked (r : ℕ → R) {n m : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ n) :
    (∑ p : n.Partition, (m : R) * (p.parts.count m : ℕ) * partitionCycleWeight r p) =
      r m * ∑ q : (n - m).Partition, partitionCycleWeight r q := by
  let e := Nat.Partition.partitionWithPartEquiv hm1 hm
  have hsub :
      (∑ p : {p : n.Partition // m ∈ p.parts},
        (m : R) * (p.val.parts.count m : ℕ) * partitionCycleWeight r p.val) =
      ∑ p : n.Partition, (m : R) * (p.parts.count m : ℕ) * partitionCycleWeight r p := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro p hp
      have hh : m ∉ p.parts := fun hh => hp ⟨⟨p, hh⟩, rfl⟩
      simp only [Multiset.count_eq_zero_of_notMem hh, Nat.cast_zero, mul_zero, zero_mul]
    · intro p
      rfl
  rw [← hsub]
  calc
    _ = ∑ p : {p : n.Partition // m ∈ p.parts},
        r m * partitionCycleWeight r (e p) := by
      apply Finset.sum_congr rfl
      intro p _
      have hp : p.val.parts = m ::ₘ (e p).parts := by
        simpa only [e, Nat.Partition.partitionWithPartEquiv_apply_parts] using
          (Multiset.cons_erase p.property).symm
      unfold partitionCycleWeight
      rw [hp, Multiset.count_cons_self]
      exact multisetCycleWeight_cons r m hm1 _ (fun b hb => (e p).parts_pos hb)
    _ = ∑ q : (n - m).Partition, r m * partitionCycleWeight r q :=
      Equiv.sum_comp e (fun q : (n - m).Partition => r m * partitionCycleWeight r q)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem partitionCycleWeight_degree (r : ℕ → R) {n : ℕ} (p : n.Partition) :
    (n : R) * partitionCycleWeight r p =
      ∑ m ∈ Finset.Icc 1 n,
        (m : R) * (p.parts.count m : ℕ) * partitionCycleWeight r p := by
  have hs : p.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨p.parts_pos (Multiset.mem_toFinset.mp hm),
      p.le_of_mem_parts (Multiset.mem_toFinset.mp hm)⟩
  have hn := Finset.sum_multiset_count_of_subset p.parts (Finset.Icc 1 n) hs
  have hc : (n : R) = ∑ m ∈ Finset.Icc 1 n, (m : R) * (p.parts.count m : ℕ) := by
    have hnat : n = ∑ m ∈ Finset.Icc 1 n, m * p.parts.count m := by
      calc
        n = p.parts.sum := p.parts_sum.symm
        _ = _ := by simpa only [nsmul_eq_mul, Nat.mul_comm, Nat.cast_id] using hn
    simpa only [Nat.cast_sum, Nat.cast_mul] using congrArg (Nat.cast : ℕ → R) hnat
  rw [hc, Finset.sum_mul]

/-- The finite cycle recurrence underlying the exponential formula. -/
theorem sum_partitionCycleWeight_recursion (r : ℕ → R) (n : ℕ) :
    (n : R) * (∑ p : n.Partition, partitionCycleWeight r p) =
      ∑ m ∈ Finset.Icc 1 n,
        r m * ∑ q : (n - m).Partition, partitionCycleWeight r q := by
  rw [Finset.mul_sum]
  calc
    _ = ∑ p : n.Partition, ∑ m ∈ Finset.Icc 1 n,
        (m : R) * (p.parts.count m : ℕ) * partitionCycleWeight r p :=
      Finset.sum_congr rfl fun p _ => partitionCycleWeight_degree r p
    _ = ∑ m ∈ Finset.Icc 1 n, ∑ p : n.Partition,
        (m : R) * (p.parts.count m : ℕ) * partitionCycleWeight r p :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact sum_partitionCycleWeight_marked r (Finset.mem_Icc.mp hm).1
        (Finset.mem_Icc.mp hm).2


open scoped PowerSeries

def cyclePartitionSeries (r : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (fun n => ∑ p : n.Partition, partitionCycleWeight r p)

def cycleLogSeries (r : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (fun n => if n = 0 then 0
    else algebraMap ℚ R ((n : ℚ)⁻¹) * r n)

@[simp] theorem constantCoeff_cyclePartitionSeries (r : ℕ → R) :
    PowerSeries.constantCoeff (cyclePartitionSeries r) = 1 := by
  simp [cyclePartitionSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    partitionCycleWeight]

@[simp] theorem constantCoeff_cycleLogSeries (r : ℕ → R) :
    PowerSeries.constantCoeff (cycleLogSeries r) = 0 := by
  simp [cycleLogSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_derivative_cycleLogSeries (r : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX (cycleLogSeries r)) = r (n + 1) := by
  have hq : ((n + 1 : ℕ) : ℚ)⁻¹ * (n + 1 : ℕ) = 1 := by
    apply inv_mul_cancel₀
    positivity
  have hr := congrArg (algebraMap ℚ R) hq
  simp only [map_mul, map_natCast, map_one] at hr
  rw [PowerSeries.coeff_derivative, cycleLogSeries, PowerSeries.coeff_mk,
    ite_eq_right (Nat.succ_ne_zero n)]
  calc
    _ = (algebraMap ℚ R (((n + 1 : ℕ) : ℚ)⁻¹) * (n + 1 : ℕ)) * r (n + 1) := by
      push_cast
      ring
    _ = _ := by rw [hr, one_mul]

theorem derivative_cyclePartitionSeries (r : ℕ → R) :
    d⁄dX (cyclePartitionSeries r) =
      d⁄dX (cycleLogSeries r) * cyclePartitionSeries r := by
  apply PowerSeries.ext
  intro n
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
        r (k + 1) * ∑ p : (n - k).Partition, partitionCycleWeight r p) =
      ∑ m ∈ Finset.Icc 1 (n + 1),
        r m * ∑ p : (n + 1 - m).Partition, partitionCycleWeight r p := by
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      exact Finset.mem_Icc.mpr ⟨by omega, by simpa using Finset.mem_range.mp hk⟩
    · intro k hk j hj he
      omega
    · intro m hm
      refine ⟨m - 1, ?_, ?_⟩
      · apply Finset.mem_range.mpr
        have := Finset.mem_Icc.mp hm
        omega
      · have := Finset.mem_Icc.mp hm
        omega
    · intro k hk
      have he : n - k = n + 1 - (k + 1) := by omega
      rw [he]
  calc
    _ = (n + 1 : R) * ∑ p : (n + 1).Partition, partitionCycleWeight r p := by
      rw [PowerSeries.coeff_derivative, cyclePartitionSeries, PowerSeries.coeff_mk]
      ring
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        sum_partitionCycleWeight_recursion r (n + 1)
    _ = _ := hsum.symm
    _ = _ := by
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_derivative_cycleLogSeries, cyclePartitionSeries,
        PowerSeries.coeff_mk, Nat.succ_eq_add_one]

theorem derivative_logOf_mul (F : PowerSeries R)
    (hF : PowerSeries.constantCoeff F = 1) :
    d⁄dX (PowerSeries.logOf F) * F = d⁄dX F := by
  have hs : PowerSeries.HasSubst (F - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hF])
  have hlog := congrArg (PowerSeries.substAlgHom hs)
    (PowerSeries.derivative_log_mul_one_add_X (A := R))
  simp only [map_mul, map_add, map_one, PowerSeries.substAlgHom_X] at hlog
  rw [PowerSeries.coe_substAlgHom hs] at hlog
  have hf : (1 : PowerSeries R) + (F - 1) = F := by ring
  rw [hf] at hlog
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst (hg := hs),
    map_sub, PowerSeries.derivative_one, sub_zero]
  calc
    _ = ((d⁄dX (PowerSeries.log R)).subst (F - 1) * F) * d⁄dX F := by ring
    _ = _ := by rw [hlog, one_mul]

theorem logOf_cyclePartitionSeries (r : ℕ → R) :
    PowerSeries.logOf (cyclePartitionSeries r) = cycleLogSeries r := by
  let : HasUniqueDiv R := HasUniqueDiv.of_module_rat R
  apply PowerSeries.derivative.ext
  · have hu : IsUnit (cyclePartitionSeries r) :=
      PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)
    apply hu.mul_right_cancel
    rw [derivative_logOf_mul _ (constantCoeff_cyclePartitionSeries r),
      derivative_cyclePartitionSeries]
  · rw [PowerSeries.constantCoeff_logOf (constantCoeff_cyclePartitionSeries r),
      constantCoeff_cycleLogSeries]


def permutationCycleSeries (r : ℕ → R) : PowerSeries R :=
  ordinaryEGF (fun n => ∑ σ : Equiv.Perm (Fin n),
    (((finPermPartition σ).parts).map r).prod)

theorem normalized_card_perm_partition {n : ℕ} (p : n.Partition) :
    algebraMap ℚ R ((Nat.factorial n : ℚ)⁻¹) *
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => finPermPartition σ = p)).card : R) =
      algebraMap ℚ R ((cycleDenominator p.parts : ℚ)⁻¹) := by
  have hd : (cycleDenominator p.parts : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (cycleDenominator_pos p.parts (fun b hb => p.parts_pos hb)).ne'
  have hf : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hh := congrArg (Nat.cast : ℕ → ℚ) (card_perm_partition_mul p)
  simp only [Nat.cast_mul] at hh
  have hq : (Nat.factorial n : ℚ)⁻¹ *
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => finPermPartition σ = p)).card : ℚ) =
      (cycleDenominator p.parts : ℚ)⁻¹ := by
    calc
      _ = (Nat.factorial n : ℚ)⁻¹ *
          ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => finPermPartition σ = p)).card : ℚ) *
          ((cycleDenominator p.parts : ℚ) * (cycleDenominator p.parts : ℚ)⁻¹) := by
        rw [mul_inv_cancel₀ hd, mul_one]
      _ = (Nat.factorial n : ℚ)⁻¹ *
          (((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => finPermPartition σ = p)).card : ℚ) *
            (cycleDenominator p.parts : ℚ)) * (cycleDenominator p.parts : ℚ)⁻¹ := by ring
      _ = _ := by rw [hh, inv_mul_cancel₀ hf, one_mul]
  simpa only [map_mul, map_natCast] using congrArg (algebraMap ℚ R) hq

/-- The normalized permutation sum equals the sum over full cycle partitions. -/
theorem permutationCycleSeries_eq_cyclePartitionSeries (r : ℕ → R) :
    permutationCycleSeries r = cyclePartitionSeries r := by
  apply PowerSeries.ext
  intro n
  have hs := Finset.sum_fiberwise_of_maps_to'
    (g := fun σ : Equiv.Perm (Fin n) => finPermPartition σ)
    (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) (fun p => (p.parts.map r).prod)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  rw [permutationCycleSeries, ordinaryEGF, cyclePartitionSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk, one_div, ← hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold partitionCycleWeight multisetCycleWeight
  rw [← mul_assoc, normalized_card_perm_partition]

theorem logOf_permutationCycleSeries (r : ℕ → R) :
    PowerSeries.logOf (permutationCycleSeries r) = cycleLogSeries r := by
  rw [permutationCycleSeries_eq_cyclePartitionSeries, logOf_cyclePartitionSeries]


/-- The multiplicative sign of a cycle, including the fixed-point value one. -/
def signedCycleTrace (trace : ℕ → R) (m : ℕ) : R :=
  -(-1 : R) ^ m * trace m

omit [Algebra ℚ R] in
theorem signedCycleTrace_eq (trace : ℕ → R) {m : ℕ} (hm : 1 ≤ m) :
    signedCycleTrace trace m = (-1 : R) ^ (m - 1) * trace m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  simp [signedCycleTrace, pow_succ]

omit [Algebra ℚ R] in
theorem sign_eq_cycleSign_prod {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : R) =
      (σ.cycleType.map (fun m => -(-1 : R) ^ m)).prod := by
  let f : ℤˣ →* R := (Int.castRingHom R).toMonoidHom.comp (Units.coeHom ℤ)
  have hh := congrArg f (Equiv.Perm.sign_of_cycleType' σ)
  simpa [f, map_multiset_prod, Multiset.map_map, Function.comp_def] using hh

omit [Algebra ℚ R] in
theorem signedCycleTrace_partition_product (trace : ℕ → R) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    ((finPermPartition σ).parts.map (signedCycleTrace trace)).prod =
      ((Equiv.Perm.sign σ : ℤ) : R) *
        (trace 1 ^ (n - σ.cycleType.sum) * (σ.cycleType.map trace).prod) := by
  rw [finPermPartition_parts, Equiv.Perm.parts_partition,
    Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
  rw [← Equiv.Perm.sum_cycleType, Fintype.card_fin]
  simp only [signedCycleTrace, pow_one, neg_neg, one_mul]
  change (σ.cycleType.map (fun m => -(-1 : R) ^ m * trace m)).prod *
    trace 1 ^ (n - σ.cycleType.sum) = _
  rw [Multiset.prod_map_mul, ← sign_eq_cycleSign_prod]
  ring

/-- The signed permutation sum, with fixed points and repeated cycle lengths. -/
def determinantCycleSequence (trace : ℕ → R) (n : ℕ) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
    (trace 1 ^ (n - σ.cycleType.sum) * (σ.cycleType.map trace).prod)

theorem ordinaryEGF_determinantCycleSequence (trace : ℕ → R) :
    ordinaryEGF (determinantCycleSequence trace) =
      permutationCycleSeries (signedCycleTrace trace) := by
  unfold permutationCycleSeries
  congr 1
  funext n
  unfold determinantCycleSequence
  exact Finset.sum_congr rfl fun σ _ => (signedCycleTrace_partition_product trace σ).symm

theorem logOf_determinantCycleSequence (trace : ℕ → R) :
    PowerSeries.logOf (ordinaryEGF (determinantCycleSequence trace)) =
      cycleLogSeries (signedCycleTrace trace) := by
  rw [ordinaryEGF_determinantCycleSequence, logOf_permutationCycleSeries]


theorem exp_subst_logOf (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = 1) :
    (PowerSeries.exp R).subst (PowerSeries.logOf F) = F := by
  have hs : PowerSeries.HasSubst (F - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hF])
  have hh := congrArg (PowerSeries.substAlgHom hs) (PowerSeries.subst_exp_log R)
  simp only [map_add, map_one, PowerSeries.substAlgHom_X] at hh
  rw [PowerSeries.coe_substAlgHom hs,
    PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.log hs (PowerSeries.exp R)] at hh
  have hf : (1 : PowerSeries R) + (F - 1) = F := by ring
  rw [hf] at hh
  exact hh

/-- The full exponential cycle-index identity, obtained by inverting the proved
formal logarithm rather than by an analytic interchange of integrals or series. -/
theorem determinantCycleSequence_exponential (trace : ℕ → R) :
    (PowerSeries.exp R).subst (cycleLogSeries (signedCycleTrace trace)) =
      ordinaryEGF (determinantCycleSequence trace) := by
  rw [← logOf_determinantCycleSequence]
  apply exp_subst_logOf
  rw [ordinaryEGF_determinantCycleSequence,
    permutationCycleSeries_eq_cyclePartitionSeries, constantCoeff_cyclePartitionSeries]

end Weights

end Paper.Cumulants
