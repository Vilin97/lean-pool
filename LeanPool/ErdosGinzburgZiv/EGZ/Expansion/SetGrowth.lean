/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Growth under translations

Translation boundaries are subadditive.  Averaging overlaps with a finite
set of translations supplies a large boundary, which can then be divided
among short words in a set of generators.  In particular this gives the
basis growth estimate needed in relative expansion without using
Loomis--Whitney.
-/

open scoped BigOperators
open Module

namespace EGZ.Expansion

section AddGroup

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translate a finite set by an element of its ambient group. -/
def translate (Y : Finset G) (a : G) : Finset G :=
  Y.map (Equiv.addRight a).toEmbedding

omit [DecidableEq G] in
@[simp] theorem mem_translate {Y : Finset G} {a x : G} :
    x ∈ translate Y a ↔ x - a ∈ Y := by
  simp [translate, Finset.mem_map_equiv, sub_eq_add_neg]

omit [DecidableEq G] in
@[simp] theorem card_translate (Y : Finset G) (a : G) :
    (translate Y a).card = Y.card := Finset.card_map _

omit [DecidableEq G] in
@[simp] theorem translate_zero (Y : Finset G) : translate Y 0 = Y := by
  ext x
  simp

omit [DecidableEq G] in
theorem translate_add (Y : Finset G) (a b : G) :
    translate Y (a + b) = translate (translate Y a) b := by
  ext x
  simp [sub_sub, add_comm]

theorem translate_sdiff (Y Z : Finset G) (a : G) :
    translate (Y \ Z) a = translate Y a \ translate Z a := by
  ext x
  simp

/-- The number of new points added by one translation. -/
def boundary (Y : Finset G) (a : G) : ℕ := (translate Y a \ Y).card

@[simp] theorem boundary_zero (Y : Finset G) : boundary Y 0 = 0 := by
  simp [boundary]

theorem boundary_add_card (Y : Finset G) (a : G) :
    boundary Y a + Y.card = (translate Y a ∪ Y).card :=
  Finset.card_sdiff_add_card _ _

theorem boundary_add_overlap (Y : Finset G) (a : G) :
    boundary Y a + (translate Y a ∩ Y).card = Y.card := by
  simpa [boundary] using Finset.card_sdiff_add_card_inter (translate Y a) Y

theorem boundary_le_card (Y : Finset G) (a : G) : boundary Y a ≤ Y.card := by
  have := boundary_add_overlap Y a
  omega

theorem boundary_add_le (Y : Finset G) (a b : G) :
    boundary Y (a + b) ≤ boundary Y a + boundary Y b := by
  have hsub : translate Y (a + b) \ Y ⊆
      (translate Y (a + b) \ translate Y b) ∪ (translate Y b \ Y) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    by_cases hb : x ∈ translate Y b
    · exact Or.inr ⟨hb, hx.2⟩
    · exact Or.inl ⟨hx.1, hb⟩
  calc
    boundary Y (a + b) ≤
        ((translate Y (a + b) \ translate Y b) ∪ (translate Y b \ Y)).card :=
      Finset.card_le_card hsub
    _ ≤ (translate Y (a + b) \ translate Y b).card + boundary Y b :=
      Finset.card_union_le _ _
    _ = boundary Y a + boundary Y b := by
      rw [translate_add, ← translate_sdiff, card_translate]
      rfl

theorem boundary_nsmul_le (Y : Finset G) (a : G) (n : ℕ) :
    boundary Y (n • a) ≤ n * boundary Y a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, Nat.succ_mul]
    exact (boundary_add_le Y (n • a) a).trans (Nat.add_le_add_right ih _)

theorem boundary_sum_le {ι : Type*} (I : Finset ι) (Y : Finset G) (a : ι → G) :
    boundary Y (∑ i ∈ I, a i) ≤ ∑ i ∈ I, boundary Y (a i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (boundary_add_le Y (a i) _).trans (Nat.add_le_add_left ih _)

/-- A translation cannot overlap a set at more positions than the set has. -/
theorem sum_overlap_le (Y B : Finset G) :
    (∑ b ∈ B, (translate Y b ∩ Y).card) ≤ Y.card * Y.card := by
  classical
  have hcard (b : G) : (translate Y b ∩ Y).card =
      ∑ y ∈ Y, if y - b ∈ Y then 1 else 0 := by
    have heq : translate Y b ∩ Y = Y.filter (fun y ↦ y - b ∈ Y) := by
      ext y
      simp [and_comm]
    rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  calc
    (∑ y ∈ Y, ∑ b ∈ B, if y - b ∈ Y then 1 else 0) ≤
        ∑ _y ∈ Y, Y.card := by
      apply Finset.sum_le_sum
      intro y _
      rw [← Finset.card_filter]
      exact Finset.card_le_card_of_injOn (fun b ↦ y - b)
        (fun b hb ↦ (Finset.mem_filter.mp hb).2)
        (fun a _ b _ h ↦ sub_right_injective h)
    _ = Y.card * Y.card := by simp

/-- Among at least twice as many distinct translations as points of `Y`,
one translation adds at least half the points of `Y`. -/
theorem exists_boundary_double_le (Y B : Finset G) (hB : B.Nonempty)
    (hlarge : 2 * Y.card ≤ B.card) :
    ∃ b ∈ B, Y.card ≤ 2 * boundary Y b := by
  by_contra! h
  have hsum : (∑ b ∈ B, 2 * boundary Y b) < B.card * Y.card := by
    calc
      (∑ b ∈ B, 2 * boundary Y b) < ∑ _b ∈ B, Y.card :=
        Finset.sum_lt_sum_of_nonempty hB (fun b hb ↦ h b hb)
      _ = B.card * Y.card := by simp
  have htotal : (∑ b ∈ B, boundary Y b) +
      (∑ b ∈ B, (translate Y b ∩ Y).card) = B.card * Y.card := by
    rw [← Finset.sum_add_distrib]
    simp only [boundary_add_overlap, Finset.sum_const, smul_eq_mul]
  have hover := sum_overlap_le Y B
  rw [← Finset.mul_sum] at hsum
  nlinarith

end AddGroup

section Basis

variable {p d : ℕ} [NeZero p] [Fact p.Prime]

/-- A box of short nonnegative words in a basis, before reduction wraps. -/
noncomputable def basisBox (E : Basis (Fin d) (ZMod p) (FpCoord p d)) (m : ℕ) :
    Finset (FpCoord p d) := by
  classical
  exact Finset.univ.image fun a : Fin d → Fin m ↦
    E.equivFun.symm (fun i ↦ (a i : ℕ))

omit [NeZero p] in
theorem basisBox_injective (E : Basis (Fin d) (ZMod p) (FpCoord p d))
    {m : ℕ} (hm : m ≤ p) : Function.Injective
      (fun a : Fin d → Fin m ↦ E.equivFun.symm (fun i ↦ (a i : ℕ))) := by
  intro a b hab
  have hh := congrArg E.equivFun hab
  simp only [LinearEquiv.apply_symm_apply] at hh
  funext i
  apply Fin.ext
  have hi := congrArg ZMod.val (congrFun hh i)
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ((a i).isLt.trans_le hm),
    Nat.mod_eq_of_lt ((b i).isLt.trans_le hm)] using hi

theorem card_basisBox (E : Basis (Fin d) (ZMod p) (FpCoord p d))
    {m : ℕ} (hm : m ≤ p) : (basisBox E m).card = m ^ d := by
  classical
  rw [basisBox, Finset.card_image_of_injective _ (basisBox_injective E hm)]
  simp

omit [NeZero p] in
theorem basisBox_nonempty (E : Basis (Fin d) (ZMod p) (FpCoord p d))
    {m : ℕ} (hm : 0 < m) : (basisBox E m).Nonempty := by
  classical
  let a : Fin d → Fin m := fun _ ↦ ⟨0, hm⟩
  exact ⟨_, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

omit [NeZero p] in
/-- A member of a basis box adds at most the sum of the boundaries of its
individual basis steps, counted with their multiplicities. -/
theorem boundary_basisBox_le (E : Basis (Fin d) (ZMod p) (FpCoord p d))
    (Y : Finset (FpCoord p d)) {m : ℕ} {b : FpCoord p d}
    (hb : b ∈ basisBox E m) :
    boundary Y b ≤ m * ∑ i : Fin d, boundary Y (E i) := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
  rw [Basis.equivFun_symm_apply]
  have heq (i : Fin d) : ((a i : ℕ) : ZMod p) • E i = (a i : ℕ) • E i := by
    ext j
    simp [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  calc
    boundary Y (∑ i, (a i : ZMod p) • E i) ≤
        ∑ i, boundary Y ((a i : ℕ) • E i) := by
      simp only [heq]
      exact boundary_sum_le Finset.univ Y (fun i ↦ (a i : ℕ) • E i)
    _ ≤ ∑ i, m * boundary Y (E i) := by
      apply Finset.sum_le_sum
      intro i _
      exact (boundary_nsmul_le Y (E i) (a i)).trans
        (Nat.mul_le_mul_right _ (a i).isLt.le)
    _ = m * ∑ i, boundary Y (E i) := (Finset.mul_sum _ _ _).symm

/-- Integer form of the basis growth estimate.  Taking
`m = ceil (2 * |Y|^(1/d))` yields the usual power-size increment. -/
theorem exists_basis_boundary (E : Basis (Fin d) (ZMod p) (FpCoord p d))
    (hd : 0 < d) (Y : Finset (FpCoord p d))
    {m : ℕ} (hmpos : 0 < m) (hmp : m ≤ p) (hsize : 2 * Y.card ≤ m ^ d) :
    ∃ i : Fin d, Y.card ≤ 2 * m * d * boundary Y (E i) := by
  classical
  obtain ⟨b, hb, hbd⟩ := exists_boundary_double_le Y (basisBox E m)
    (basisBox_nonempty E hmpos) (by rwa [card_basisBox E hmp])
  have hB := boundary_basisBox_le E Y hb
  have hnon : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, by simp⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ hnon (fun i ↦ boundary Y (E i))
  have hsum : (∑ j : Fin d, boundary Y (E j)) ≤ d * boundary Y (E i) := by
    calc
      (∑ j : Fin d, boundary Y (E j)) ≤ ∑ _j : Fin d, boundary Y (E i) := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.le_sup (f := fun i ↦ boundary Y (E i))
          (Finset.mem_univ j)).trans_eq hmax
      _ = d * boundary Y (E i) := by simp
  refine ⟨i, ?_⟩
  calc
    Y.card ≤ 2 * boundary Y b := hbd
    _ ≤ 2 * (m * (d * boundary Y (E i))) :=
      Nat.mul_le_mul_left _ (hB.trans (Nat.mul_le_mul_left _ hsum))
    _ = _ := by ring

end Basis

theorem exists_basis_boundary_real {p d : ℕ} [NeZero p] [Fact p.Prime]
    (E : Basis (Fin d) (ZMod p) (FpCoord p d)) (hd : 0 < d)
    (Y : Finset (FpCoord p d)) (x : ℝ) (hx : 1 ≤ x)
    (hcard : (Y.card : ℝ) = x ^ d) (hxp : 2 * x ≤ p) :
    ∃ i : Fin d, x ^ (d - 1) ≤ 6 * d * (boundary Y (E i) : ℝ) := by
  classical
  let m := ⌈2 * x⌉₊
  have hxpos : 0 < x := by linarith
  have hmlo : 2 * x ≤ (m : ℝ) := Nat.le_ceil _
  have hmhi : (m : ℝ) ≤ 3 * x := by
    have hh : (m : ℝ) < 2 * x + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hmpos : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    rw [this, Nat.cast_zero] at hmlo
    linarith
  have hmp : m ≤ p := Nat.ceil_le.mpr hxp
  have htwod : (2 : ℝ) ≤ 2 ^ d := by
    have heq : d = (d - 1) + 1 := by omega
    rw [heq, pow_succ]
    nlinarith [one_le_pow₀ (n := d - 1) (show (1 : ℝ) ≤ 2 by norm_num)]
  have hsize : 2 * Y.card ≤ m ^ d := by
    have hh : (2 : ℝ) * Y.card ≤ (m : ℝ) ^ d := calc
      2 * Y.card = 2 * x ^ d := by rw [hcard]
      _ ≤ (2 * x) ^ d := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right htwod (by positivity)
      _ ≤ (m : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hmlo d
    exact_mod_cast hh
  obtain ⟨i, hi⟩ := exists_basis_boundary E hd Y hmpos hmp hsize
  refine ⟨i, ?_⟩
  have hir : x ^ d ≤ 2 * (m : ℝ) * d * (boundary Y (E i) : ℝ) := by
    rw [← hcard]
    exact_mod_cast hi
  have hmul : 2 * (m : ℝ) * d * (boundary Y (E i) : ℝ) ≤
      6 * x * d * (boundary Y (E i) : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hmhi
      (show (0 : ℝ) ≤ 2 * d * (boundary Y (E i) : ℝ) by positivity)]
  have hpow : x ^ d = x * x ^ (d - 1) := by
    conv_lhs => rw [show d = 1 + (d - 1) by omega, pow_add]
    simp
  rw [hpow] at hir
  nlinarith [hir.trans hmul]

end EGZ.Expansion
