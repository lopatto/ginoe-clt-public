/-
Copyright (c) 2026 Patrick Lopatto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lopatto
-/
module
public import GinoeClt.Spectral.SchurCanonicalSymmetry
@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Paper.Spectral

/-- LIST determinant, with the same multiplicities and order as the full roots. -/
def listVandermondeDet (s : List ℂ) : ℂ := (Matrix.vandermonde s.get).det

theorem listVandermondeDet_cons (a : ℂ) (s : List ℂ) :
    listVandermondeDet (a::s) =
      (s.map (fun z => z-a)).prod * listVandermondeDet s := by
  have hg : (a::s).get = Fin.cons a s.get := by
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  have hp : (∏ i : Fin s.length, (s.get i-a)) = (s.map (fun z => z-a)).prod := by
    have he : List.ofFn (fun i : Fin s.length => s.get i-a) = s.map (fun z => z-a) := by
      rw [List.ofFn_comp' s.get (fun z => z-a),List.ofFn_get]
    simpa only [List.prod_ofFn] using congrArg List.prod he
  rw [listVandermondeDet,hg,det_vandermonde_cons,hp]
  rfl

theorem listVandermondeDet_cons_two (a b : ℂ) (s : List ℂ) :
    listVandermondeDet (a::b::s) = (b-a) *
      ((s.map (fun z => z-a)).prod * (s.map (fun z => z-b)).prod) *
      listVandermondeDet s := by
  rw [listVandermondeDet_cons,listVandermondeDet_cons]
  simp only [List.map_cons,List.prod_cons]
  ring

theorem listVandermondeDet_ofFn {n : ℕ} (v : Fin n → ℂ) :
    listVandermondeDet (List.ofFn v) = (Matrix.vandermonde v).det := by
  have he : (List.ofFn v).get = fun i => v (Fin.cast (by simp) i) := by
    funext i
    exact List.get_ofFn v i
  rw [listVandermondeDet,he,det_vandermonde_finCast]

/-- A finite product of nonnegative REAL factors remains such a factor. -/
theorem list_prod_nonnegative_real {α : Type*} (s : List α) (f : α → ℂ)
    (hf : ∀ a ∈ s, ∃ r : ℝ, 0 ≤ r ∧ f a = (r : ℂ)) :
    ∃ r : ℝ, 0 ≤ r ∧ (s.map f).prod = (r : ℂ) := by
  induction s with
  | nil => exact ⟨1,zero_le_one,by simp⟩
  | cons a s ih =>
    obtain ⟨r,hr,he⟩ := hf a (by simp)
    obtain ⟨q,hq,hqe⟩ := ih (fun b hb => hf b (by simp [hb]))
    refine ⟨r*q,mul_nonneg hr hq,?_⟩
    simp only [List.map_cons,List.prod_cons,he,hqe,Complex.ofReal_mul]

theorem paired_list_product (s : List ℂ) (f : ℂ → ℂ) :
    ((s.flatMap (fun z => [z,conj z])).map f).prod =
      (s.map (fun z => f z * f (conj z))).prod := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,
      List.prod_cons,ih]
    ring

theorem conjugate_pair_cross_product (u a : ℂ) :
    ((u-a)*(conj u-a)) * ((u-conj a)*(conj u-conj a)) =
      ((‖u-a‖^2 * ‖u-conj a‖^2 : ℝ) : ℂ) := by
  calc
    _ = ((u-a)*conj (u-a)) * ((u-conj a)*conj (u-conj a)) := by
      simp only [map_sub,starRingEnd_self_apply]
      ring
    _ = _ := by
      rw [Complex.mul_conj',Complex.mul_conj']
      push_cast
      rfl

/-- Cross factors from TWO complete conjugate pairs are nonnegative real,
including all collisions; no distinctness or cancellation enters the proof. -/
theorem paired_cross_nonnegative_real (s : List ℂ) (a : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ((s.flatMap (fun z => [z,conj z])).map (fun u => u-a)).prod *
      ((s.flatMap (fun z => [z,conj z])).map (fun u => u-conj a)).prod = (r : ℂ) := by
  rw [paired_list_product,paired_list_product]
  have he :
      (s.map (fun u => (u-a)*(conj u-a))).prod *
      (s.map (fun u => (u-conj a)*(conj u-conj a))).prod =
      (s.map (fun u => ((u-a)*(conj u-a))*((u-conj a)*(conj u-conj a)))).prod := by
    induction s with
    | nil => simp
    | cons u s ih =>
      simp only [List.map_cons,List.prod_cons]
      rw [← ih]
      ring
  rw [he]
  apply list_prod_nonnegative_real
  intro u hu
  exact ⟨‖u-a‖^2 * ‖u-conj a‖^2,mul_nonneg (sq_nonneg _) (sq_nonneg _),
    conjugate_pair_cross_product u a⟩

theorem paired_real_cross_nonnegative_real (s : List ℂ) (a : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ((s.flatMap (fun z => [z,conj z])).map (fun u => u-(a : ℂ))).prod = (r : ℂ) := by
  rw [paired_list_product]
  apply list_prod_nonnegative_real
  intro u hu
  refine ⟨‖u-(a : ℂ)‖^2,sq_nonneg _,?_⟩
  simpa only [map_sub,Complex.conj_ofReal,Complex.ofReal_pow] using Complex.mul_conj' (u-(a : ℂ))

/-- Exact phase for a complete LIST of upper conjugate pairs. Non-strict upper
membership suffices internally, so boundary collisions remain covered. -/
theorem listVandermondeDet_pairs_nonnegative (s : List ℂ)
    (hs : ∀ z ∈ s, 0 ≤ z.im) :
    ∃ r : ℝ, 0 ≤ r ∧
      Complex.I^s.length * listVandermondeDet (s.flatMap (fun z => [z,conj z])) = (r : ℂ) := by
  induction s with
  | nil => exact ⟨1,zero_le_one,by simp [listVandermondeDet]⟩
  | cons z s ih =>
    obtain ⟨r,hr,he⟩ := ih (fun u hu => hs u (by simp [hu]))
    obtain ⟨q,hq,hqe⟩ := paired_cross_nonnegative_real s z
    have hz : 0 ≤ z.im := hs z (by simp)
    have hi : Complex.I * (conj z-z) = ((2*z.im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]; ring
    refine ⟨2*z.im*q*r,mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz) hq) hr,?_⟩
    simp only [List.length_cons,List.flatMap_cons,List.cons_append,List.nil_append]
    rw [listVandermondeDet_cons_two,hqe]
    calc
      _ = (Complex.I*(conj z-z))*(q : ℂ) *
          (Complex.I^s.length * listVandermondeDet (s.flatMap (fun u => [u,conj u]))) := by
        rw [pow_succ]
        ring
      _ = _ := by rw [hi,he]; push_cast; ring

/-- Weakly ordered real roots contribute only nonnegative factors. -/
theorem listVandermondeDet_real_pairs_nonnegative (x : List ℝ) (z : List ℂ)
    (hx : x.Pairwise (· ≤ ·)) (hz : ∀ u ∈ z, 0 ≤ u.im) :
    ∃ r : ℝ, 0 ≤ r ∧ Complex.I^z.length *
      listVandermondeDet (x.map Complex.ofReal ++ z.flatMap (fun u => [u,conj u])) = (r : ℂ) := by
  induction x with
  | nil => simpa using listVandermondeDet_pairs_nonnegative z hz
  | cons a x ih =>
    obtain ⟨ha,hxt⟩ := List.pairwise_cons.mp hx
    obtain ⟨r,hr,he⟩ := ih hxt
    obtain ⟨q,hq,hqe⟩ := list_prod_nonnegative_real x (fun b => (b : ℂ)-(a : ℂ))
      (fun b hb => ⟨b-a,sub_nonneg.mpr (ha b hb),by push_cast; rfl⟩)
    obtain ⟨v,hv,hve⟩ := paired_real_cross_nonnegative_real z a
    refine ⟨q*v*r,mul_nonneg (mul_nonneg hq hv) hr,?_⟩
    simp only [List.map_cons,List.cons_append]
    rw [listVandermondeDet_cons,List.map_append,List.prod_append,List.map_map]
    simp only [Function.comp_def]
    rw [hqe,hve]
    calc
      _ = (q : ℂ)*(v : ℂ)*(Complex.I^z.length *
        listVandermondeDet (x.map Complex.ofReal ++ z.flatMap (fun u => [u,conj u]))) := by ring
      _ = _ := by rw [he]; push_cast; ring

/-- The exact canonical FULL Vandermonde phase, in the original root order.
All collisions, weak real ordering, and zero-dimensional sectors are included. -/
theorem canonical_vandermonde_phase (k l : ℕ) (x : Fin k → ℝ) (z : Fin l → ℂ)
    (hx : Monotone x) (hz : ∀ i, 0 < (z i).im) :
    Complex.I^l * (Matrix.vandermonde (schurFullRootsFromHeads
      (schurCanonicalWord k l) (schurCanonicalHeads k l x z))).det =
      (schurHeadVandermondeNorm (schurCanonicalWord k l) (schurCanonicalHeads k l x z) : ℂ) := by
  have hxp : (List.ofFn x).Pairwise (· ≤ ·) := by
    simpa only [Function.comp_def,id_eq] using
      (monotone_key_iff_pairwise_ofFn id x).mp hx
  have hzp : ∀ u ∈ List.ofFn z, 0 ≤ u.im := by
    intro u hu
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
    exact (hz i).le
  obtain ⟨r,hr,he⟩ := listVandermondeDet_real_pairs_nonnegative
    (List.ofFn x) (List.ofFn z) hxp hzp
  rw [← fullRoots_canonical_list k l x z,listVandermondeDet_ofFn,List.length_ofFn] at he
  have hn : schurHeadVandermondeNorm (schurCanonicalWord k l)
      (schurCanonicalHeads k l x z) = r := by
    have h := congrArg norm he
    simpa only [norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hr,schurHeadVandermondeNorm] using h
  rw [hn]
  exact he

end Paper.Spectral
