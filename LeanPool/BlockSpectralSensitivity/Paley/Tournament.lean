/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime

/-!
# The Paley tournament

This file formalizes Section 2 (`THE PALEY TOURNAMENT`) of `bs_lambda.txt`.  The abstract
interface `BSLambda.IsDRTournamentWith` lives in `BSLambda/Defs/Tournament.lean`; here we build
the concrete example.

* `BSLambda.paleyArc` orients the pair `{i, j}` of elements of `ZMod k` by `i → j` iff `j - i`
  is a nonzero quadratic residue.
* `BSLambda.paleyArc_isDRTournamentWith` shows that for a prime `k ≡ 3 mod 4` this is a doubly
  regular tournament with `2 * d + 1 = k` and `4 * t + 3 = k`; `BSLambda.paley_isDR` is the
  case `k = 14011`, `d = 7005`, `t = 3502` used by the construction.

The mathematical content is the character-sum calculation at the end of Section 2: the
Jacobsthal-type identity `∑ z, χ ((z - a) * (z - b)) = -1` for `a ≠ b`
(`sum_quadraticChar_mul_sub`), together with the two counting corollaries
`two_mul_card_quadraticChar_eq_one` and `four_mul_card_quadraticChar_sub_eq_one`.  Those
lemmas mention nothing from this development, so they live in the root namespace alongside
Mathlib's `quadraticChar` API rather than in `BSLambda`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

open Finset

section QuadraticCharSums

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character sums to zero over any translate of `F`.
(Section 2 of `bs_lambda.txt`.) -/
theorem sum_quadraticChar_sub (hF : ringChar F ≠ 2) (a : F) :
    ∑ z : F, quadraticChar F (z - a) = 0 := by
  rw [← quadraticChar_sum_zero hF]
  exact Fintype.sum_equiv (Equiv.subRight a) _ _ fun _ ↦ rfl

/-- The Jacobsthal-type identity `∑ z, χ ((z - a) * (z - b)) = -1` for `a ≠ b`.
This is the key identity of the character-sum calculation in Section 2 of `bs_lambda.txt`. -/
theorem sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ z : F, quadraticChar F ((z - a) * (z - b)) = -1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hza {z : F} (hz : z ∈ univ.erase a) : z - a ≠ 0 := sub_ne_zero.mpr (mem_erase.mp hz).1
  have hw1 {w : F} (hw : w ∈ univ.erase (1 : F)) : (1 : F) - w ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (mem_erase.mp hw).1)
  have hone {z : F} (h : z - a ≠ 0) : (1 : F) - (z - b) / (z - a) = (b - a) / (z - a) := by
    field_simp [h]
    ring
  have hsq {z : F} (h : z - a ≠ 0) : (z - a) * (z - b) = (z - a) ^ 2 * ((z - b) / (z - a)) := by
    field_simp [h]
  have hinva {w : F} (h : (1 : F) - w ≠ 0) : (b - w * a) / (1 - w) - a = (b - a) / (1 - w) := by
    field_simp [h]
    ring
  have hinvb {w : F} (h : (1 : F) - w ≠ 0) :
      (b - w * a) / (1 - w) - b = w * (b - a) / (1 - w) := by
    field_simp [h]
    ring
  have key : ∑ z ∈ univ.erase a, quadraticChar F ((z - a) * (z - b))
      = ∑ w ∈ univ.erase 1, quadraticChar F w := by
    refine sum_nbij' (fun z ↦ (z - b) / (z - a)) (fun w ↦ (b - w * a) / (1 - w))
      ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [mem_erase, mem_univ, and_true]
      rw [Ne, div_eq_one_iff_eq (hza hz)]
      intro h
      apply hab
      linear_combination h
    · intro w hw
      simp only [mem_erase, mem_univ, and_true]
      refine sub_ne_zero.mp ?_
      rw [hinva (hw1 hw)]
      exact div_ne_zero hba (hw1 hw)
    · intro z hz
      rw [hone (hza hz), div_eq_iff (div_ne_zero hba (hza hz))]
      field_simp [hza hz]
      ring
    · intro w hw
      rw [hinva (hw1 hw), hinvb (hw1 hw), div_div_div_cancel_right₀ (hw1 hw), mul_div_assoc,
        div_self hba, mul_one]
    · intro z hz
      rw [hsq (hza hz), map_mul, quadraticChar_sq_one' (hza hz), one_mul]
  have hleft : ∑ z ∈ univ.erase a, quadraticChar F ((z - a) * (z - b))
      = ∑ z : F, quadraticChar F ((z - a) * (z - b)) :=
    sum_erase _ (by simp)
  have hright : ∑ w ∈ univ.erase 1, quadraticChar F w = -1 := by
    have h := sum_erase_add (univ : Finset F) (fun w ↦ quadraticChar F w) (mem_univ (1 : F))
    rw [quadraticChar_sum_zero hF] at h
    simp only [MulChar.map_one] at h
    omega
  rw [← hleft, key, hright]

/-- Exactly half of the nonzero elements of `F` are quadratic residues; this gives the out-degree
`(k - 1) / 2` of the Paley tournament. (Section 2 of `bs_lambda.txt`.) -/
theorem two_mul_card_quadraticChar_eq_one (hF : ringChar F ≠ 2) :
    2 * (univ.filter fun a : F ↦ quadraticChar F a = 1).card + 1 = Fintype.card F := by
  have hval (a : F) : 1 + quadraticChar F a
      = (if a = 0 then 1 else 0) + 2 * if quadraticChar F a = 1 then (1 : ℤ) else 0 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rcases quadraticChar_dichotomy ha with h | h <;> simp [h, ha]
  have h : ∑ a : F, (1 + quadraticChar F a) = (Fintype.card F : ℤ) := by
    rw [sum_add_distrib, quadraticChar_sum_zero hF]
    simp
  rw [sum_congr rfl fun a _ ↦ hval a, sum_add_distrib, ← mul_sum, sum_boole, sum_boole] at h
  simp only [filter_eq', mem_univ, ite_true, card_singleton] at h
  omega

/-- When `-1` is a nonresidue, swapping the two arguments of a difference negates the quadratic
character. (Section 2 of `bs_lambda.txt`.) -/
theorem quadraticChar_sub_swap (hneg : quadraticChar F (-1) = -1) (a b : F) :
    quadraticChar F (a - b) = -quadraticChar F (b - a) := by
  rw [← neg_sub b a, ← neg_one_mul, map_mul, hneg, neg_one_mul]

/-- A residue shift is nonzero: `χ (z - a) = 1` forces `z ≠ a`. -/
private theorem ne_of_quadraticChar_sub_eq_one {a z : F} (h : quadraticChar F (z - a) = 1) :
    z ≠ a := by
  rintro rfl
  simp at h

/-- The expanded Jacobsthal sum over the complement of `{a, b}`: the products
`(1 + χ (z - a)) (1 + χ (z - b))` add up to `#F - 3`. (Section 2 of `bs_lambda.txt`.) -/
private theorem sum_one_add_quadraticChar_sub_mul (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    ∑ z ∈ (univ.erase a).erase b,
        (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = (Fintype.card F : ℤ) - 3 := by
  have hpt (z : F) : (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = 1 + quadraticChar F (z - a) + quadraticChar F (z - b)
        + quadraticChar F ((z - a) * (z - b)) := by
    rw [map_mul]
    ring
  have htot : ∑ z : F, (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = (Fintype.card F : ℤ) - 1 := by
    rw [sum_congr rfl fun z _ ↦ hpt z, sum_add_distrib, sum_add_distrib, sum_add_distrib,
      sum_quadraticChar_sub hF, sum_quadraticChar_sub hF, sum_quadraticChar_mul_sub hF hab]
    simp [sub_eq_add_neg]
  have hb := sum_erase_add ((univ : Finset F).erase a)
    (fun z ↦ (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b)))
    (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩)
  have ha := sum_erase_add (univ : Finset F)
    (fun z ↦ (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))) (mem_univ a)
  simp only [sub_self, quadraticChar_zero, add_zero, mul_one, one_mul] at hb ha
  rw [htot, quadraticChar_sub_swap hneg a b] at ha
  omega

/-- Away from `a` and `b`, the product `(1 + χ (z - a)) (1 + χ (z - b))` is `4` on the common
residue shifts and `0` elsewhere. (Section 2 of `bs_lambda.txt`.) -/
private theorem one_add_quadraticChar_sub_mul_eq_ite {a b z : F} (hz : z ≠ a) (hz' : z ≠ b) :
    (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = if quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1 then 4 else 0 := by
  by_cases hc : quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1
  · rw [ite_eq_left hc, hc.1, hc.2]
    norm_num only
  · rw [ite_eq_right hc]
    rcases not_and_or.mp hc with h' | h'
    · rw [(quadraticChar_eq_neg_one_iff_not_one (sub_ne_zero.mpr hz)).mpr h']
      ring
    · rw [(quadraticChar_eq_neg_one_iff_not_one (sub_ne_zero.mpr hz')).mpr h']
      ring

/-- For `a ≠ b`, exactly `(#F - 3) / 4` elements `z` satisfy `χ (z - a) = χ (z - b) = 1`.
This is the common-out-neighbour count of the Paley tournament.
(Section 2 of `bs_lambda.txt`.) -/
theorem four_mul_card_quadraticChar_sub_eq_one (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    4 * (univ.filter fun z : F ↦
        quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1).card + 3
      = Fintype.card F := by
  have hset : ((univ.erase a).erase b).filter
      (fun z : F ↦ quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1)
      = univ.filter fun z : F ↦ quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1 := by
    ext z
    simp only [mem_filter, mem_erase, mem_univ, true_and, and_true, and_iff_right_iff_imp]
    exact fun hz ↦ ⟨ne_of_quadraticChar_sub_eq_one hz.2, ne_of_quadraticChar_sub_eq_one hz.1⟩
  have h := sum_one_add_quadraticChar_sub_mul hF hneg hab
  rw [sum_congr rfl fun z hz ↦ one_add_quadraticChar_sub_mul_eq_ite
      (ne_of_mem_erase (mem_erase.mp hz).2) (ne_of_mem_erase hz), ← sum_filter, hset, sum_const,
    nsmul_eq_mul] at h
  omega

end QuadraticCharSums

namespace BSLambda

section Paley

/-- The Paley tournament on `F_k` for a prime `k ≡ 3 mod 4`: `i → j` iff `j - i` is a nonzero
quadratic residue. (Section 2 of `bs_lambda.txt`.) -/
def paleyArc (k : ℕ) [Fact (Nat.Prime k)] (i j : ZMod k) : Bool :=
  decide (quadraticChar (ZMod k) (j - i) = 1)

/-- `k = 14011` is prime. (Section 2 of `bs_lambda.txt`.) -/
theorem prime_14011 : Nat.Prime 14011 := by norm_num

instance factPrime14011 : Fact (Nat.Prime 14011) := ⟨prime_14011⟩

/-- The characteristic of `F_14011` is not `2`. (Section 2 of `bs_lambda.txt`.) -/
theorem ringChar_zmod14011 : ringChar (ZMod 14011) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  norm_num only

/-- Since `14011 ≡ 3 mod 4`, the element `-1` is a nonresidue in `F_14011`; this is what makes
the Paley orientation a tournament. (Section 2 of `bs_lambda.txt`.) -/
theorem quadraticChar_neg_one_zmod14011 : quadraticChar (ZMod 14011) (-1) = -1 := by
  rw [quadraticChar_neg_one ringChar_zmod14011, ZMod.card, ZMod.χ₄_nat_eq_if_mod_four]
  norm_num

/-- Two distinct elements of `F_k` have exactly `t` common quadratic-residue shifts, where
`4 * t + 3 = k`; this is the `t` of the Paley tournament. (Section 2 of `bs_lambda.txt`.) -/
private theorem card_filter_quadraticChar_sub_eq_one {k t : ℕ} [Fact (Nat.Prime k)]
    (hchar : ringChar (ZMod k) ≠ 2) (hneg : quadraticChar (ZMod k) (-1) = -1)
    (ht : 4 * t + 3 = k) {a b : ZMod k} (hab : a ≠ b) :
    (univ.filter fun z : ZMod k ↦
        quadraticChar (ZMod k) (z - a) = 1 ∧ quadraticChar (ZMod k) (z - b) = 1).card = t := by
  have h := four_mul_card_quadraticChar_sub_eq_one hchar hneg hab
  rw [ZMod.card] at h
  omega

/-- **The Paley tournament is doubly regular.**  If `F_k` has odd characteristic and `-1` is a
nonresidue in it — equivalently, `k ≡ 3 mod 4` — then the Paley orientation of `F_k` is a
doubly regular tournament with out-degree `d = (k - 1) / 2` and `t = (k - 3) / 4` common
neighbours. (Section 2 of `bs_lambda.txt`.) -/
theorem paleyArc_isDRTournamentWith {k d t : ℕ} [Fact (Nat.Prime k)]
    (hchar : ringChar (ZMod k) ≠ 2) (hneg : quadraticChar (ZMod k) (-1) = -1)
    (hd : 2 * d + 1 = k) (ht : 4 * t + 3 = k) : IsDRTournamentWith (paleyArc k) d t where
  arc_self i := by
    simp only [paleyArc, sub_self, quadraticChar_zero, decide_eq_false_iff_not]
    decide
  arc_eq_not_arc := fun {i j} hij ↦ by
    have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp only [paleyArc, quadraticChar_sub_swap hneg i j]
    rcases quadraticChar_dichotomy hji with h | h <;> rw [h] <;> decide
  card_outNbrs i := by
    have hcard : (outNbrs (paleyArc k) i).card
        = (univ.filter fun a : ZMod k ↦ quadraticChar (ZMod k) a = 1).card :=
      Finset.card_equiv (Equiv.subRight i) (by simp [paleyArc])
    have h := two_mul_card_quadraticChar_eq_one (F := ZMod k) hchar
    rw [ZMod.card] at h
    omega
  card_commonOut := fun {i j} hij ↦ by
    have hset : commonOut (paleyArc k) i j = univ.filter fun z : ZMod k ↦
        quadraticChar (ZMod k) (z - i) = 1 ∧ quadraticChar (ZMod k) (z - j) = 1 := by
      ext x
      simp [paleyArc]
    rw [hset]
    exact card_filter_quadraticChar_sub_eq_one hchar hneg ht hij
  card_commonIn := fun {i j} hij ↦ by
    have hcard : (commonIn (paleyArc k) i j).card
        = (univ.filter fun z : ZMod k ↦ quadraticChar (ZMod k) (z - -i) = 1
            ∧ quadraticChar (ZMod k) (z - -j) = 1).card := by
      refine Finset.card_equiv (Equiv.neg (ZMod k)) fun x ↦ ?_
      simp only [paleyArc, decide_eq_true_eq, mem_commonIn, mem_filter, mem_univ, true_and,
        Equiv.neg_apply, show ∀ u : ZMod k, -x - -u = u - x from fun u ↦ by ring]
    rw [hcard]
    exact card_filter_quadraticChar_sub_eq_one hchar hneg ht fun h ↦ hij (neg_injective h)

/-- **The Paley tournament on `F_14011` is doubly regular** with `d = 7005` and `t = 3502`.
(Section 2 of `bs_lambda.txt`.) -/
theorem paley_isDR : IsDRTournamentWith (paleyArc 14011) 7005 3502 :=
  paleyArc_isDRTournamentWith ringChar_zmod14011 quadraticChar_neg_one_zmod14011 rfl rfl

end Paley

end BSLambda
