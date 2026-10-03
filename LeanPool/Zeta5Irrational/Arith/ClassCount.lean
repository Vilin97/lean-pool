/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.ClassFrame
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

/-! # Class counting

For `p = 2m + 1` every residue `c` mod `p` is `≡ ±a` for a unique `a ∈ {0, …, m}` (`ccls c`).
We express the per-class counts `classCount` of the framework in terms of these classes.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- `μ(a, c) = [a ≡ c] + [a ≡ -c]`. -/
def mu (p : ℕ) (a : ℕ) (c : ZMod p) : ℕ :=
  (if ((a : ℤ) : ZMod p) = c then 1 else 0) + (if ((a : ℤ) : ZMod p) = -c then 1 else 0)

/-- The class of a residue. -/
@[expose] def ccls (hm : 2 * m + 1 = p) (c : ZMod p) : Fin (m + 1) :=
  if h : c.val ≤ m then ⟨c.val, by omega⟩ else ⟨p - c.val, by have := c.val_lt; omega⟩

lemma ccls_spec (hm : 2 * m + 1 = p) (c : ZMod p) :
    (((ccls hm c : ℕ) : ℤ) : ZMod p) = c ∨ (((ccls hm c : ℕ) : ℤ) : ZMod p) = -c := by
  have hp0 : NeZero p := ⟨hp.out.ne_zero⟩
  unfold ccls
  split_ifs with h
  · left; simp
  · right
    have hv := c.val_lt
    simp only []
    rw [show ((p - c.val : ℕ) : ℤ) = (p : ℤ) - (c.val : ℤ) by
        push_cast [Nat.cast_sub hv.le];
        ring]
    push_cast
    rw [ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]

lemma two_ne_zero_zmod (hm : 2 * m + 1 = p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  rcases (Nat.le_succ_iff.mp this) with h1 | h1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h2 | h2
    · exact hp.out.ne_zero h2
    · exact hp.out.ne_one h2
  · omega

/-- Uniqueness of the class. -/
lemma ccls_unique (hm : 2 * m + 1 = p) (c : ZMod p) (a : Fin (m + 1))
    (h : (((a : ℕ) : ℤ) : ZMod p) = c ∨ (((a : ℕ) : ℤ) : ZMod p) = -c) : a = ccls hm c := by
  have h1 := ccls_spec hm c
  apply sq_injective hm
  simp only
  have e : ∀ x : ZMod p, x = c ∨ x = -c → x ^ 2 = c ^ 2 := by rintro x (rfl | rfl) <;> ring
  have ha := e _ h
  have hc := e _ h1
  push_cast at ha hc
  rw [ha, hc]

lemma mu_eq (hm : 2 * m + 1 = p) (a : Fin (m + 1)) (c : ZMod p) :
    mu p a c = if a = ccls hm c then (if c = 0 then 2 else 1) else 0 := by
  unfold mu
  by_cases ha : a = ccls hm c
  · rw [ite_eq_left ha]
    have hs := ccls_spec hm c
    rw [← ha] at hs
    by_cases hc : c = 0
    · subst hc
      rw [ite_eq_left rfl]
      have : (((a : ℕ) : ℤ) : ZMod p) = 0 := by rcases hs with h | h <;> simpa using h
      rw [ite_eq_left this, ite_eq_left (by rw [this, neg_zero])]
    · rw [ite_eq_right hc]
      have hnot : ¬((((a : ℕ) : ℤ) : ZMod p) = c ∧ (((a : ℕ) : ℤ) : ZMod p) = -c) := by
        rintro ⟨h1, h2⟩
        apply hc
        have : (2 : ZMod p) * c = 0 := by have := h1.symm.trans h2; linear_combination this
        exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod hm)
      rcases hs with h | h
      · rw [ite_eq_left h, ite_eq_right (fun h' => hnot ⟨h, h'⟩)]
      · rw [ite_eq_right (fun h' => hnot ⟨h', h⟩), ite_eq_left h]
  · rw [ite_eq_right ha]
    rw [ite_eq_right (fun h => ha (ccls_unique hm c a (Or.inl h))),
      ite_eq_right (fun h => ha (ccls_unique hm c a (Or.inr h)))]

/-- `#{j ≤ X : j ≡ c} + #{j ≤ X : j ≡ -c}`. -/
@[expose] def SX (p X : ℕ) (c : ZMod p) : ℕ :=
  ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = c).card +
    ((Icc 1 X).filter fun j : ℕ => ((j : ℤ) : ZMod p) = -c).card

lemma SX_neg (X : ℕ) (c : ZMod p) : SX p X (-c) = SX p X c := by unfold SX; rw [neg_neg, add_comm]

lemma SX_ccls (hm : 2 * m + 1 = p) (X : ℕ) (c : ZMod p) :
    SX p X c = SX p X (((ccls hm c : ℕ) : ℤ) : ZMod p) := by
  rcases ccls_spec hm c with h | h <;> rw [h]
  rw [SX_neg]

/-- The class constant `5[a = 0] + 6 S_N(a) - S_K(a)`. -/
@[expose] noncomputable def Bse (p K N : ℕ) (a : ℕ) : ℚ :=
  (if a = 0 then 5 else 0) + 6 * (SX p N (((a : ℤ) : ZMod p)) : ℚ) - SX p K (((a : ℤ) : ZMod p))

/-- The vanishing order of the row `s = (a, i)` at the class `b`. -/
@[expose]
def nu {m : ℕ} (L : Fin (m + 1) → ℕ) (s : Σ a : Fin (m + 1), Fin (L a)) (b : Fin (m + 1)) : ℕ :=
  if b = s.1 then s.2 else L b

lemma card_filter_replicate (k : ℕ) (v : ℤ) (P : ℤ → Prop) [DecidablePred P] :
    ((Multiset.replicate k v).filter P).card = if P v then k else 0 := by
  split_ifs with h
  · rw [Multiset.filter_eq_self.mpr fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h]
    simp
  · rw [Multiset.filter_eq_nil.mpr fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h]
    simp

lemma card_filter_sum_replicate {α : Type*} (s : Finset α) (L : α → ℕ) (v : α → ℤ) (P : ℤ → Prop)
    [DecidablePred P] :
    ((∑ c ∈ s, Multiset.replicate (L c) (v c)).filter P).card =
      ∑ c ∈ s, if P (v c) then L c else 0 := by
  classical
    induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.card_add, ih, Finset.sum_insert ha,
      card_filter_replicate]

lemma count_classRoots (hm : 2 * m + 1 = p) (L : Fin (m + 1) → ℕ)
    (s : Σ a : Fin (m + 1), Fin (L a)) (c : ZMod p) :
    ((classRoots L s.1 s.2).filter fun γ : ℤ => (γ : ZMod p) = c).card +
        ((classRoots L s.1 s.2).filter fun γ : ℤ => (γ : ZMod p) = -c).card =
      (if c = 0 then 2 else 1) * nu L s (ccls hm c) := by
  unfold classRoots
  simp only [Multiset.filter_add, Multiset.card_add, card_filter_sum_replicate,
    card_filter_replicate]
  have key :
    ∀ b : Fin (m + 1),
      ∀ k : ℕ,
        ((if (((b : ℕ) : ℤ) : ZMod p) = c then k else 0) +
            (if (((b : ℕ) : ℤ) : ZMod p) = -c then k else 0)) =
          k * mu p b c :=
    by intro b k; unfold mu; split_ifs <;> ring
  have e :
    ∀ S : Finset (Fin (m + 1)),
      (∑ b ∈ S, if (((b : ℕ) : ℤ) : ZMod p) = c then L b else 0) +
          (∑ b ∈ S, if (((b : ℕ) : ℤ) : ZMod p) = -c then L b else 0) =
        ∑ b ∈ S, L b * mu p b c :=
    by intro S; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun b _ => key b (L b)
  have e2 := key s.1 s.2
  calc
    _ =
        ((∑ b ∈ Finset.univ.erase s.1, if (((b : ℕ) : ℤ) : ZMod p) = c then L b else 0) +
            (∑ b ∈ Finset.univ.erase s.1, if (((b : ℕ) : ℤ) : ZMod p) = -c then L b else 0)) +
          ((if (((s.1 : ℕ) : ℤ) : ZMod p) = c then (s.2 : ℕ) else 0) +
            (if (((s.1 : ℕ) : ℤ) : ZMod p) = -c then (s.2 : ℕ) else 0)) :=
      by ring
    _ = ∑ b ∈ Finset.univ.erase s.1, L b * mu p b c + s.2 * mu p s.1 c := by rw [e, e2]
    _ = _ := by
      simp_rw [mu_eq hm]
      unfold nu
      by_cases h : ccls hm c = s.1
      · rw [ite_eq_left h, ite_eq_left h.symm,
          Finset.sum_eq_zero fun b hb => by
            rw [ite_eq_right (fun h' => (Finset.mem_erase.mp hb).1 (h'.trans h)), mul_zero]]
        ring
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero, add_zero,
          Finset.sum_eq_single_of_mem (ccls hm c) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
            fun b _ hb => by rw [ite_eq_right hb, mul_zero]]
        rw [ite_eq_left rfl]; ring

lemma count_DN (N : ℕ) (c : ZMod p) :
    ((6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ))).filter fun γ : ℤ => (γ : ZMod p) = c).card +
        ((6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ))).filter fun γ : ℤ =>
            (γ : ZMod p) = -c).card =
      6 * SX p N c := by
  unfold SX
  simp only [Multiset.filter_nsmul, Multiset.card_nsmul, Multiset.filter_map, Multiset.card_map]
  rw [mul_add]
  rfl

lemma card_plc_PlK (K : ℕ) (c : ZMod p) : (plc p (PlK K) c).card = SX p K c := by
  unfold plc PlK SX
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (PlK_disjoint K)),
    Finset.filter_image, Finset.filter_image,
    Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Int.cast_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> [rw [← h2]; rw [h2]] <;> ring

lemma ccls_eq_zero_iff (hm : 2 * m + 1 = p) (c : ZMod p) : ccls hm c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hs := ccls_spec hm c
    rw [h] at hs
    simp only [Fin.val_zero, Nat.cast_zero, Int.cast_zero] at hs
    rcases hs with h1 | h1
    · exact h1.symm
    · exact neg_eq_zero.mp h1.symm
  · rintro rfl
    unfold ccls
    rw [dite_eq_left (by simp)]
    ext; simp

/-- **The class counts** in terms of `Bse` and the row vanishing orders. -/
theorem classCount_eq (hm : 2 * m + 1 = p) (K N : ℕ) (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (c : ZMod p) :
    classCount p K (entryRoots N L s t) c =
      Bse p K N (ccls hm c) +
        (if ccls hm c = 0 then 2 else 1) * ((nu L s (ccls hm c) : ℚ) + nu L t (ccls hm c)) := by
  unfold classCount entryRoots Bse
  simp only [Multiset.filter_add, Multiset.card_add]
  have h1 := count_DN (p := p) N c
  have h2 := count_classRoots hm L s c
  have h3 := count_classRoots hm L t c
  rw [card_plc_PlK, ← SX_ccls hm N c, ← SX_ccls hm K c]
  have hz : ((if c = 0 then 5 else 0 : ℕ) : ℚ) = if (ccls hm c : ℕ) = 0 then 5 else 0 := by
    by_cases hc : c = 0
    · rw [ite_eq_left hc, ite_eq_left (by rw [(ccls_eq_zero_iff hm c).mpr hc]; rfl)]; norm_num
    · have hne : (ccls hm c : ℕ) ≠ 0 := fun h => hc ((ccls_eq_zero_iff hm c).mp (Fin.ext h))
      simp [hc, hne]
  have hz2 : ((if c = 0 then 2 else 1 : ℕ) : ℚ) = if ccls hm c = 0 then 2 else 1 := by
    by_cases hc : c = 0
    · rw [ite_eq_left hc, ite_eq_left ((ccls_eq_zero_iff hm c).mpr hc)]; norm_num
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ((ccls_eq_zero_iff hm c).mp h))]; norm_num
  have h1' :
    (((Multiset.filter (fun γ : ℤ => (γ : ZMod p) = c)
                (6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)))).card :
            ℕ) :
          ℚ) +
        ((Multiset.filter (fun γ : ℤ => (γ : ZMod p) = -c)
              (6 • ((Icc 1 N).val.map fun j : ℕ => (j : ℤ)))).card :
          ℕ) =
      6 * (SX p N c : ℚ) :=
    by exact_mod_cast h1
  have h2' := congrArg (fun x : ℕ => (x : ℚ)) h2
  have h3' := congrArg (fun x : ℕ => (x : ℚ)) h3
  simp only [Nat.cast_add, Nat.cast_mul] at h2' h3'
  rw [hz2] at h2' h3'
  push_cast
  rw [← hz]
  push_cast
  linarith

end Zeta5Irrational
