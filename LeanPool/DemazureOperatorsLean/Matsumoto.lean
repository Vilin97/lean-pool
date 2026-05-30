/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/

import LeanPool.DemazureOperatorsLean.StrongExchange
import Init.Data.List.Erase

namespace CoxeterSystem
noncomputable section

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

instance : DecidableEq W := Classical.typeDecidableEq W

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "len" => cs.length

/-- Extra nondegeneracy assumptions used in the Matsumoto theorem development. -/
class MatsumotoCondition where
  one_le_M : ∀ i j : B, 1 ≤ M i j
  alternatingWords_ne_one :
    ∀ (i j : B) (_ : i ≠ j) (p : ℕ) (_ : 0 < p) (_ : p < M i j),
      (s i * s j) ^ p ≠ 1

/-- A nil move removes two adjacent equal simple reflections at a given offset. -/
structure NilMove (cs : CoxeterSystem M W) where
  /-- The simple reflection index used by the nil move. -/
  i : B
  /-- The offset where the nil move is applied. -/
  p : ℕ
/-- A braid move replaces a braid word by the opposite braid word at a given offset. -/
structure BraidMove (cs : CoxeterSystem M W) where
  /-- The first simple reflection index in the braid word. -/
  i : B
  /-- The second simple reflection index in the braid word. -/
  j : B
  /-- The offset where the braid move is applied. -/
  p : ℕ

/-- A Coxeter move is either a nil move or a braid move. -/
inductive CoxeterMove (cs : CoxeterSystem M W) where
| nil : cs.NilMove → cs.CoxeterMove
| braid : cs.BraidMove → cs.CoxeterMove

/-- Apply a nil move to a word. -/
def apply_nilMove (nm : cs.NilMove) (l : List B) : List B :=
  match nm with
  | NilMove.mk i p =>
    match p with
    | 0 =>
      if l.take 2 = [i, i] then
        l.drop 2
      else
        l
    | p + 1 =>
      match l with
      | [] => []
      | h::t => h :: apply_nilMove (NilMove.mk i p) t

/-- Apply a braid move to a word. -/
def apply_braidMove (bm : cs.BraidMove) (l : List B) : List B :=
  match bm with
  | BraidMove.mk i j p =>
    match p with
    | 0 =>
      if l.take (M i j) = braidWord M i j then
        braidWord M j i ++ l.drop (M i j)
      else
        l
    | p + 1 =>
      match l with
      | [] => []
      | h::t => h :: apply_braidMove (BraidMove.mk i j p) t

/-- Apply either kind of Coxeter move to a word. -/
def apply_coxeterMove (cm : cs.CoxeterMove) (l : List B) : List B :=
  match cm with
  | CoxeterMove.nil nm => cs.apply_nilMove nm l
  | CoxeterMove.braid bm => cs.apply_braidMove bm l

theorem nilMove_wordProd (nm : cs.NilMove) (l : List B) : π (cs.apply_nilMove nm l) = π l := by
  rcases nm with ⟨i, p⟩
  match p with
  | 0 =>
    rw[apply_nilMove]
    by_cases h : l.take 2 = [i, i]
    · rw [if_pos h]
      have h' : l = l.take 2 ++ l.drop 2 := by simp
      nth_rewrite 2 [h']
      rw[wordProd_append]
      rw[h]
      have h_pair : cs.wordProd [i, i] = 1 := by
        convert_to cs.wordProd ([i] ++ [i]) = 1
        rw[wordProd_append]
        simp
      rw [h_pair, one_mul]
    · rw [if_neg h]
  | p + 1 =>
    match l with
    | [] => simp[apply_nilMove]
    | h::t =>
      simp only [apply_nilMove, wordProd_cons]
      rw[nilMove_wordProd (NilMove.mk i p) t]

theorem braidMove_wordProd (bm : cs.BraidMove) (l : List B) :
    π (cs.apply_braidMove bm l) = π l := by
  rcases bm with ⟨i, j, p⟩
  match p with
    | 0 =>
      rw[apply_braidMove]
      by_cases h : List.take (M.M i j) l = braidWord M i j
      · rw [if_pos h]
        have h' : l = l.take (M.M i j) ++ l.drop (M.M i j) := by simp
        nth_rewrite 2 [h']
        repeat rw[wordProd_append]
        rw[h]
        simp[wordProd_braidWord_eq]
      · rw [if_neg h]
    | p + 1 =>
      match l with
      | [] => simp[apply_braidMove]
      | h::t =>
        simp only [apply_braidMove, wordProd_cons]
        rw[braidMove_wordProd (BraidMove.mk i j p) t]

theorem coxeterMove_wordProd (cm : cs.CoxeterMove) (l : List B) :
    π (cs.apply_coxeterMove cm l) = π l := by
  cases cm with
  | nil nm => exact cs.nilMove_wordProd nm l
  | braid bm => exact cs.braidMove_wordProd bm l

/-- Apply a list of Coxeter moves to a word from right to left. -/
def apply_coxeterMove_sequence (cms : List (cs.CoxeterMove)) (l : List B) : List B :=
  List.foldr (cs.apply_coxeterMove) l cms

example (nm : cs.NilMove) : cs.CoxeterMove := CoxeterMove.nil nm

/-- Apply a sequence of braid moves to a word. -/
def apply_braidMoveSequence (bms : List (cs.BraidMove)) (l : List B) : List B :=
  match bms with
  | [] => l
  | bm :: bms' => cs.apply_braidMove bm (apply_braidMoveSequence bms' l)

lemma apply_braidMoveSequence_cons (bm : cs.BraidMove) (bms : List (cs.BraidMove))
    (l : List B) :
    cs.apply_braidMoveSequence (bm :: bms) l =
      cs.apply_braidMove bm (cs.apply_braidMoveSequence bms l) := by
  simp[apply_braidMoveSequence]

lemma cons_of_length_succ {α : Type} (l : List α) {p : ℕ} (h : l.length = p + 1) :
  ∃ (a : α) (t : List α), l = a :: t ∧ t.length = p := by
  cases l with
  | nil =>
    simp at h
  | cons a t =>
    simp at h
    use a, t
/-- Shift a braid move one position to the right. -/
def shift_braidMove (bm : cs.BraidMove) : cs.BraidMove :=
  match bm with
  | BraidMove.mk i j p => BraidMove.mk i j (p + 1)

lemma braidMove_cons (bm : cs.BraidMove) (l : List B) (a : B) :
  a :: cs.apply_braidMove bm l = cs.apply_braidMove (cs.shift_braidMove bm) (a :: l) := by
  rcases bm with ⟨i, j, p⟩
  simp[shift_braidMove, apply_braidMove]

lemma braidMoveSequence_cons (bms : List (cs.BraidMove)) (l : List B) (a : B) :
    a :: cs.apply_braidMoveSequence bms l =
      cs.apply_braidMoveSequence (List.map cs.shift_braidMove bms) (a :: l) := by
  induction bms with
    | nil =>
       simp[apply_braidMoveSequence]
    | cons bm bms ih =>
      rw[apply_braidMoveSequence]
      rw[cs.braidMove_cons bm]
      rw[ih]
      simp[apply_braidMoveSequence_cons]

theorem isReduced_cons (a : B) (l : List B) : cs.IsReduced (a :: l) → cs.IsReduced l := by
  intro h
  have h' : l = (a::l).drop 1 := by simp
  rw[h']
  exact h.drop 1

lemma leftDescent_of_cons (i : B) (l : List B) (hr : cs.IsReduced (i :: l)) :
    cs.IsLeftDescent (π (i :: l)) i := by
  rw [IsLeftDescent, hr, wordProd_cons, simple_mul_simple_cancel_left, List.length_cons]
  exact Nat.lt_of_le_of_lt (cs.length_wordProd_le l) (Nat.lt_succ_self l.length)

lemma leftInversion_of_cons (i : B) (l : List B) (hr : cs.IsReduced (i :: l)) :
    cs.IsLeftInversion (π (i :: l)) (s i) :=
  (cs.isLeftInversion_simple_iff_isLeftDescent (π (i :: l)) i).mpr (cs.leftDescent_of_cons i l hr)

theorem alternatingWord_succ_ne_alternatingWord_eraseIdx [MatsumotoCondition cs]
 (i j : B) (p : ℕ) (hp : p < M i j) (hij : i ≠ j) :
    ∀ (k : ℕ) (_ : k < p),
      π (alternatingWord i j (p + 1)) ≠ π (alternatingWord i j p).eraseIdx k := by
  revert i j
  induction p with
  | zero =>
    intro i j
    simp[alternatingWord, cs.wordProd_cons]
  | succ p ih =>
    intro i j hp hij k hk
    have hp' : p < M i j := by linarith
    have hp'' : p < M j i := by
      rw [M.symmetric]
      exact hp'
    have zero_lt_p_succ : 0 < p + 1 := by linarith
    rw[alternatingWord_succ]
    nth_rewrite 2 [alternatingWord_succ]
    simp only [List.concat_eq_append, ne_eq]
    by_cases h_erase : k < (alternatingWord j i p).length
    · rw[List.eraseIdx_append_of_lt_length h_erase [j]]
      intro h_contra
      simp only [wordProd_append] at h_contra
      rw[mul_right_cancel_iff] at h_contra
      have hij' : j ≠ i := by
        intro h
        apply hij
        rw[h]
      have h_erase' : k < p := by
        simpa only [length_alternatingWord] using h_erase
      apply ih j i hp'' hij' k h_erase' h_contra
    · have h_erase' : (alternatingWord j i p).length ≤ k := by
        apply Nat.le_of_not_lt
        exact h_erase
      rw[List.eraseIdx_append_of_length_le h_erase' [j]]
      have h_erase_k : [j].eraseIdx (k - (alternatingWord j i p).length) = [] := by
        have h_index : k - (alternatingWord j i p).length = 0 := by
          have hk_le : k ≤ p := by omega
          simpa [length_alternatingWord] using Nat.sub_eq_zero_of_le hk_le
        rw [h_index]
        rfl
      rw[h_erase_k]
      simp only [List.append_nil, ne_eq]
      intro h_contra
      have :
          cs.wordProd (alternatingWord j i (p + 1) ++ [j]) =
            cs.wordProd (alternatingWord i j (p + 2)) := by
        simp[alternatingWord_succ]
      rw[this] at h_contra
      simp only [prod_alternatingWord_eq_mul_pow, Order.lt_two_iff, zero_le, Nat.add_div_right,
        ite_mul, one_mul] at h_contra
      by_cases p_even : Even p
      · have p_even' : Even (p + 2) := by
          exact Even.add p_even (by norm_num : Even 2)
        rw [if_pos p_even', if_pos p_even] at h_contra
        apply mul_inv_eq_one.mpr at h_contra
        rw[← inv_pow (s j * s i) (p/2)] at h_contra
        simp only [mul_inv_rev, inv_simple] at h_contra
        rw[← pow_add] at h_contra
        have : p / 2 + 1 + p / 2 = p + 1 := by
          have h_half : 2 * (p / 2) = p := Nat.two_mul_div_two_of_even p_even
          omega
        rw[this] at h_contra
        apply MatsumotoCondition.alternatingWords_ne_one i j hij (p + 1) zero_lt_p_succ _ h_contra
        linarith
      · have p_odd : ¬ Even (p + 2) := by
          intro h
          exact p_even ((Nat.even_add.mp h).mpr (by norm_num : Even 2))
        rw [if_neg p_odd, if_neg p_even] at h_contra
        apply (@mul_left_cancel_iff _ _ _ (s j) _ _).mpr at h_contra
        simp only [simple_mul_simple_cancel_left] at h_contra
        rw[← mul_assoc] at h_contra
        let p_succ := p / 2 + 1
        have p_succ_ne_zero : p_succ ≠ 0 := by
          apply Nat.succ_ne_zero
        have : (p / 2) = p_succ - 1 := by
          omega
        rw[this] at h_contra
        rw[mul_pow_sub_one p_succ_ne_zero (s j * s i)] at h_contra
        simp only [add_tsub_cancel_right, p_succ] at h_contra
        apply mul_inv_eq_one.mpr at h_contra
        rw[← inv_pow (s j * s i) (p/2 + 1)] at h_contra
        simp only [mul_inv_rev, inv_simple] at h_contra
        rw[← pow_add] at h_contra
        have : p / 2 + 1 + (p / 2 + 1) = p + 1 := by
          have p_odd_base : Odd p := Nat.not_even_iff_odd.mp p_even
          calc
            p / 2 + 1 + (p / 2 + 1) = 1 + p / 2 * 2 + 1 := by ring_nf
            _ = p + 1 := by rw [Nat.one_add_div_two_mul_two_of_odd p_odd_base]
        rw[this] at h_contra
        apply MatsumotoCondition.alternatingWords_ne_one i j hij (p + 1) zero_lt_p_succ _ h_contra
        linarith

lemma prefix_braidWord_aux [MatsumotoCondition cs] (w : W) (l l' : List B) (i j : B)
    (i_ne_j : i ≠ j) (hil : π(i :: l) = w) (hjl' : π(j :: l') = w)
    (hr : cs.IsReduced (i :: l)) (hr' : cs.IsReduced (j :: l')) :
    ∀ (p : ℕ) (_ : p ≤ M i j),
      ∃ t : List B, π (alternatingWord i j p ++ t) = w ∧
        cs.IsReduced (alternatingWord i j p ++ t) := by
  intro p
  induction p with
  | zero =>
    intro _
    use i :: l
    constructor
    · simpa only [alternatingWord, List.nil_append] using hil
    · simpa only [alternatingWord, List.nil_append] using hr
  | succ p ih =>
    intro hp
    have hp' : p ≤ M i j := by linarith
    have hp'' : p < M i j := by linarith
    rcases ih hp' with ⟨t, ht, htr⟩
    rw[← ht]
    rw[alternatingWord_succ']
    by_cases p_even : Even p
    · rw [if_pos p_even]
      change ∃ t_1 : List B,
        s j * π (alternatingWord i j p ++ t_1) = π (alternatingWord i j p ++ t) ∧
          cs.IsReduced (j :: alternatingWord i j p ++ t_1)
      suffices ∃ k : Fin t.length, s j * cs.wordProd (alternatingWord i j p ++ t) =
      cs.wordProd (alternatingWord i j p ++ (t.eraseIdx k)) from by
        rcases this with ⟨k, hk⟩
        use (t.eraseIdx k)
        have hw :
          cs.simple j * cs.wordProd (alternatingWord i j p ++ t.eraseIdx k) =
          cs.wordProd (alternatingWord i j p ++ t)
        := by
          rw[← hk]
          rw [simple_mul_simple_cancel_left]
        constructor
        · exact hw
        · rw [IsReduced]
          rw [IsReduced] at htr
          rw [List.cons_append]
          rw[cs.wordProd_cons]
          rw[hw]
          rw[htr]
          calc
            (alternatingWord i j p ++ t).length = p + t.length := by
              rw [List.length_append, length_alternatingWord]
            _ = (j :: (alternatingWord i j p ++ t.eraseIdx k)).length := by
              rw [List.length_cons, List.length_append, length_alternatingWord,
                List.length_eraseIdx_of_lt k.2]
              have h_t_pos : 0 < t.length :=
                Nat.lt_of_le_of_lt (Nat.zero_le k) k.2
              omega
      have h_left_inversion_j :
          cs.IsLeftInversion (cs.wordProd (alternatingWord i j p ++ t)) (s j) := by
        rw[ht, ← hjl']
        apply cs.leftInversion_of_cons j l' hr'
      rcases cs.strongExchangeProperty (alternatingWord i j p ++ t)
          ⟨s j, cs.isReflection_simple j⟩ h_left_inversion_j with ⟨k, hk⟩
      by_cases k_lt_len : k < p
      · exfalso
        have k_lt_len' : k < (alternatingWord i j p).length := by simp[k_lt_len]
        rw[List.eraseIdx_append_of_lt_length k_lt_len' t] at hk
        simp only [wordProd_append] at hk
        rw[← mul_assoc] at hk
        rw[mul_right_cancel_iff] at hk
        rw[← wordProd_cons] at hk
        have : j :: alternatingWord i j p = alternatingWord i j (p + 1) := by
          rw [alternatingWord_succ', if_pos p_even]
        rw[this] at hk
        exact cs.alternatingWord_succ_ne_alternatingWord_eraseIdx i j p hp'' i_ne_j k
          k_lt_len hk
      · rw [not_lt] at k_lt_len
        have k_ge_len : (alternatingWord i j p).length ≤ k := by
          simpa only [length_alternatingWord] using k_lt_len
        rw[List.eraseIdx_append_of_length_le k_ge_len t] at hk
        rw[hk]
        have : k - (alternatingWord i j p).length < t.length := by
          have kle := k.2
          simp only [List.length_append, length_alternatingWord] at kle
          simp only [length_alternatingWord]
          omega
        use ⟨k - (alternatingWord i j p).length, this⟩
    · rw [if_neg p_even]
      change ∃ t_1 : List B,
        s i * π (alternatingWord i j p ++ t_1) = π (alternatingWord i j p ++ t) ∧
          cs.IsReduced (i :: alternatingWord i j p ++ t_1)
      suffices ∃ k : Fin t.length, s i * cs.wordProd (alternatingWord i j p ++ t) =
      cs.wordProd (alternatingWord i j p ++ (t.eraseIdx k)) from by
        rcases this with ⟨k, hk⟩
        use (t.eraseIdx k)
        have hw :
            cs.simple i * cs.wordProd (alternatingWord i j p ++ t.eraseIdx k) =
              cs.wordProd (alternatingWord i j p ++ t) := by
          rw[← hk]
          rw [simple_mul_simple_cancel_left]
        constructor
        · exact hw
        · rw [IsReduced]
          rw [IsReduced] at htr
          rw [List.cons_append]
          rw[cs.wordProd_cons]
          rw[hw]
          rw[htr]
          calc
            (alternatingWord i j p ++ t).length = p + t.length := by
              rw [List.length_append, length_alternatingWord]
            _ = (i :: (alternatingWord i j p ++ t.eraseIdx k)).length := by
              rw [List.length_cons, List.length_append, length_alternatingWord,
                List.length_eraseIdx_of_lt k.2]
              have h_t_pos : 0 < t.length :=
                Nat.lt_of_le_of_lt (Nat.zero_le k) k.2
              omega
      have h_left_inversion_i :
          cs.IsLeftInversion (cs.wordProd (alternatingWord i j p ++ t)) (s i) := by
        rw[ht, ← hil]
        apply cs.leftInversion_of_cons i l hr
      rcases cs.strongExchangeProperty (alternatingWord i j p ++ t)
          ⟨s i, cs.isReflection_simple i⟩ h_left_inversion_i with ⟨k, hk⟩
      by_cases k_lt_len : k < p
      · exfalso
        have k_lt_len' : k < (alternatingWord i j p).length := by simp[k_lt_len]
        rw[List.eraseIdx_append_of_lt_length k_lt_len' t] at hk
        simp only [wordProd_append] at hk
        rw[← mul_assoc] at hk
        rw[mul_right_cancel_iff] at hk
        rw[← wordProd_cons] at hk
        have : i :: alternatingWord i j p = alternatingWord i j (p + 1) := by
          rw [alternatingWord_succ', if_neg p_even]
        rw[this] at hk
        exact cs.alternatingWord_succ_ne_alternatingWord_eraseIdx i j p hp'' i_ne_j k
          k_lt_len hk
      · rw [not_lt] at k_lt_len
        have k_ge_len : (alternatingWord i j p).length ≤ k := by
          simpa only [length_alternatingWord] using k_lt_len
        rw[List.eraseIdx_append_of_length_le k_ge_len t] at hk
        rw[hk]
        have : k - (alternatingWord i j p).length < t.length := by
          have kle := k.2
          simp only [List.length_append, length_alternatingWord] at kle
          simp only [length_alternatingWord]
          omega
        use ⟨k - (alternatingWord i j p).length, this⟩

lemma prefix_braidWord [MatsumotoCondition cs] (l l' : List B) (i j : B)
    (i_ne_j : i ≠ j) (pi_eq : π(i :: l) = π(j :: l'))
    (hr : cs.IsReduced (i :: l)) (hr' : cs.IsReduced (j :: l')) :
    ∃ t : List B, π (i :: l) = π (braidWord M i j ++ t) ∧
      cs.IsReduced (braidWord M i j ++ t) := by
  have h : M i j ≤ M i j := by linarith
  have h' : π (j :: l') = π (i :: l) := Eq.symm pi_eq
  rcases cs.prefix_braidWord_aux (π (i :: l)) l l' i j i_ne_j rfl h' hr hr'
      (M i j) h with ⟨t, ht, htr⟩
  use t
  rw[braidWord]
  constructor
  · simp[ht]
  · exact htr

theorem apply_braidMove_sequence_append (bms bms' : List (cs.BraidMove)) (l : List B) :
    cs.apply_braidMoveSequence (bms ++ bms') l =
      cs.apply_braidMoveSequence bms (cs.apply_braidMoveSequence bms' l) := by
  induction bms with
  | nil => rfl
  | cons bm bms ih =>
    rw [List.cons_append, apply_braidMoveSequence_cons, apply_braidMoveSequence_cons, ih]

theorem concatenate_braidMove_sequences (l l' l'' : List B)
    (h : ∃ bms : List (cs.BraidMove), cs.apply_braidMoveSequence bms l = l')
    (h' : ∃ bms' : List (cs.BraidMove), cs.apply_braidMoveSequence bms' l' = l'') :
    ∃ bms'' : List (cs.BraidMove), cs.apply_braidMoveSequence bms'' l = l'' := by
  rcases h with ⟨bms, hbms⟩
  rcases h' with ⟨bms', hbms'⟩
  use bms' ++ bms
  rw[apply_braidMove_sequence_append, hbms, hbms']

-- move to aux file
theorem isReduced_of_eq_length (l l' : List B) (h_len : l.length = l'.length) (h_eq : π l = π l')
   (hr : cs.IsReduced l) : cs.IsReduced l' := by
  rw[IsReduced]
  rw[IsReduced] at hr
  calc
    len π l' = len π l := by rw[h_eq]
    _ = l.length := by rw[hr]
    _ = l'.length := by rw[h_len]

theorem eq_length_of_isReduced (l l' : List B)
(h_eq : π l = π l') (hr : cs.IsReduced l) (hr' : cs.IsReduced l') :
    l.length = l'.length := by
  rw[IsReduced] at hr
  rw[IsReduced] at hr'
  calc l.length = len π l := by rw[hr]
    _ = len π l' := by rw[h_eq]
    _ = l'.length := by rw[hr']

lemma matsumoto_reduced_inductionStep_of_firstLetterEq (p : ℕ) (l_t l'_t : List B) (i : B)
    (len_l_t_eq_p : l_t.length = p) (len_l'_t_eq_p : l'_t.length = p)
    (h_eq : π(i :: l_t) = π(i :: l'_t))
    (l_reduced : cs.IsReduced (i :: l_t)) (l'_reduced : cs.IsReduced (i :: l'_t))
    (ih : ∀ (l l' : List B),
      l.length = p →
        l'.length = p →
          cs.IsReduced l →
            cs.IsReduced l' →
              cs.wordProd l = cs.wordProd l' →
                ∃ bms, cs.apply_braidMoveSequence bms l = l') :
    ∃ bms, cs.apply_braidMoveSequence bms (i :: l_t) = i :: l'_t := by
  have htr : cs.IsReduced l_t := cs.isReduced_cons i l_t l_reduced
  have htr' : cs.IsReduced l'_t := cs.isReduced_cons i l'_t l'_reduced
  have h_prod : π l_t = π l'_t := by
    apply @mul_left_cancel _ _ _ (cs.simple i) _ _
    rw[← cs.wordProd_cons i l_t, ← cs.wordProd_cons i l'_t, h_eq]
  have ⟨bms, ih'⟩ := ih l_t l'_t len_l_t_eq_p len_l'_t_eq_p htr htr' h_prod
  apply (List.cons_inj_right i).mpr at ih'
  rw[← ih']
  rw[braidMoveSequence_cons]
  use (List.map cs.shift_braidMove bms)

theorem matsumoto_reduced_aux [MatsumotoCondition cs] (p : ℕ) (l l' : List B)
(len_l_eq_p : l.length = p) (len_l'_eq_p : l'.length = p)
(l_reduced : cs.IsReduced l) (l'_reduced : cs.IsReduced l') (h_eq : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMoveSequence bms l = l' := by
  revert l l'
  induction p with
  | zero =>
    intro l l' hl hl' _ _ _
    use []
    change l = l'
    rw[List.length_eq_zero_iff] at hl
    rw[List.length_eq_zero_iff] at hl'
    rw[hl, hl']
  | succ p ih =>
    intro l l' len_l_eq_p len_l'_eq_p l_reduced l'_reduced h_eq
    rcases cons_of_length_succ l len_l_eq_p with ⟨i, l_t, rfl, len_l_t_eq_p⟩
    rcases cons_of_length_succ l' len_l'_eq_p with ⟨j, l'_t, rfl, len_l'_t_eq_p⟩
    by_cases first_letter_eq : i = j
    · rw[first_letter_eq]
      rw[first_letter_eq] at h_eq
      rw[first_letter_eq] at l_reduced
      apply cs.matsumoto_reduced_inductionStep_of_firstLetterEq p l_t l'_t j len_l_t_eq_p
        len_l'_t_eq_p h_eq l_reduced l'_reduced
      exact ih
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, M i j = m + 1 := by
        use M i j - 1
        simp[MatsumotoCondition.one_le_M cs i j]
      have hm' : M j i = m + 1 := by
        rw[M.symmetric]
        exact hm
      by_cases m_even : Even m
      · have j_ne_i : j ≠ i := by
          intro hji
          exact first_letter_eq hji.symm
        obtain ⟨b_tail, hb, b_reduced⟩ :=
          cs.prefix_braidWord l'_t l_t j i j_ne_i (Eq.symm h_eq) l'_reduced l_reduced
        have hb' : cs.wordProd (i :: l_t) = cs.wordProd (braidWord M j i ++ b_tail) := by
          rw[← hb]
          exact h_eq
        apply cs.concatenate_braidMove_sequences (i :: l_t) (braidWord M j i ++ b_tail) (j :: l'_t)
        · have b_word_cons :
              (braidWord M j i ++ b_tail) = i :: (alternatingWord j i m ++ b_tail) := by
            rw[braidWord, hm', alternatingWord_succ', if_pos m_even, List.cons_append]
          rw[b_word_cons]
          have b_len_p : (alternatingWord j i m ++ b_tail).length = p := by
            have h_length :
                (braidWord M j i ++ b_tail).length = p + 1 := by
              rw[← cs.eq_length_of_isReduced (i :: l_t) (braidWord M j i ++ b_tail)
                hb' l_reduced b_reduced]
              exact len_l_eq_p
            rw[b_word_cons] at h_length
            simp only [List.length_cons, List.length_append, length_alternatingWord] at h_length ⊢
            omega
          rw[b_word_cons] at hb'
          rw[b_word_cons] at b_reduced
          apply cs.matsumoto_reduced_inductionStep_of_firstLetterEq p l_t
            (alternatingWord j i m ++ b_tail) i len_l_t_eq_p b_len_p hb' l_reduced
            b_reduced ih
        · apply cs.concatenate_braidMove_sequences (braidWord M j i ++ b_tail)
            (braidWord M i j ++ b_tail) (j :: l'_t)
          · use [BraidMove.mk j i 0]
            rw[apply_braidMoveSequence_cons]
            change cs.apply_braidMove (BraidMove.mk j i 0) (braidWord M j i ++ b_tail) =
              braidWord M i j ++ b_tail
            rw[apply_braidMove]
            have htake :
                List.take (M j i) (braidWord M j i ++ b_tail) = braidWord M j i := by
              rw[← length_alternatingWord j i (M j i)]
              exact List.take_left
            have hdrop :
                List.drop (M j i) (braidWord M j i ++ b_tail) = b_tail := by
              rw[← length_alternatingWord j i (M j i)]
              exact List.drop_left
            rw[if_pos htake, hdrop]
          · have switch_braidWord :
                π (braidWord M j i ++ b_tail) = π (braidWord M i j ++ b_tail) := by
              rw[wordProd_append, wordProd_append, cs.wordProd_braidWord_eq j i]
            rw[switch_braidWord] at hb'
            have b_reduced' : cs.IsReduced (braidWord M i j ++ b_tail) := by
              apply cs.isReduced_of_eq_length (braidWord M j i ++ b_tail)
                (braidWord M i j ++ b_tail)
              · simp only [List.length_append, length_alternatingWord]
                rw[M.symmetric]
              · exact switch_braidWord
              · exact b_reduced
            have hb' : cs.wordProd (j :: l'_t) = cs.wordProd (braidWord M i j ++ b_tail) := by
              rw[← hb']
              exact Eq.symm h_eq
            have b_word_cons :
                (braidWord M i j ++ b_tail) = j :: (alternatingWord i j m ++ b_tail) := by
              rw[braidWord, hm, alternatingWord_succ', if_pos m_even, List.cons_append]
            have b_len_p : (alternatingWord i j m ++ b_tail).length = p := by
              have h_length :
                  (braidWord M i j ++ b_tail).length = p + 1 := by
                rw[← cs.eq_length_of_isReduced (j :: l'_t) (braidWord M i j ++ b_tail)
                  hb' l'_reduced b_reduced']
                exact len_l'_eq_p
              rw[b_word_cons] at h_length
              simp only [List.length_cons, List.length_append, length_alternatingWord] at h_length ⊢
              omega
            rw[b_word_cons] at hb'
            rw[b_word_cons] at b_reduced'
            rw[b_word_cons]
            apply cs.matsumoto_reduced_inductionStep_of_firstLetterEq p
              (alternatingWord i j m ++ b_tail) l'_t j b_len_p len_l'_t_eq_p
              (Eq.symm hb') b_reduced' l'_reduced ih
      · rcases cs.prefix_braidWord l_t l'_t i j first_letter_eq h_eq l_reduced l'_reduced
          with ⟨b_tail, hb, b_reduced⟩
        apply cs.concatenate_braidMove_sequences (i :: l_t) (braidWord M i j ++ b_tail) (j :: l'_t)
        · have b_word_cons :
              (braidWord M i j ++ b_tail) = i :: (alternatingWord i j m ++ b_tail) := by
            rw[braidWord, hm, alternatingWord_succ', if_neg m_even, List.cons_append]
          have b_len_p : (alternatingWord i j m ++ b_tail).length = p := by
            have h_length :
                (braidWord M i j ++ b_tail).length = p + 1 := by
              rw[← cs.eq_length_of_isReduced (i :: l_t) (braidWord M i j ++ b_tail)
                hb l_reduced b_reduced]
              exact len_l_eq_p
            rw[b_word_cons] at h_length
            simp only [List.length_cons, List.length_append, length_alternatingWord] at h_length ⊢
            omega
          have i_tail_reduced : cs.IsReduced l_t := by
            apply cs.isReduced_cons i l_t l_reduced
          have aword_is_reduced : cs.IsReduced (alternatingWord i j m ++ b_tail) := by
            apply cs.isReduced_cons i ((alternatingWord i j m) ++ b_tail)
            rw[← b_word_cons]
            exact b_reduced
          have i_tail_eq_aword : π l_t = π (alternatingWord i j m ++ b_tail) := by
            rw[b_word_cons] at hb
            rw[wordProd_cons, wordProd_cons] at hb
            rw[mul_left_cancel_iff] at hb
            exact hb
          rcases ih l_t (alternatingWord i j m ++ b_tail) len_l_t_eq_p b_len_p
            i_tail_reduced aword_is_reduced i_tail_eq_aword with ⟨bms, ih'⟩
          use (List.map cs.shift_braidMove bms)
          rw[← braidMoveSequence_cons]
          suffices cs.apply_braidMoveSequence bms l_t = (alternatingWord i j m ++ b_tail)
            from by
              rw[this]
              rw[← b_word_cons]
          exact ih'
        · apply cs.concatenate_braidMove_sequences (braidWord M i j ++ b_tail)
            (braidWord M j i ++ b_tail) (j :: l'_t)
          · use [BraidMove.mk i j 0]
            rw[apply_braidMoveSequence_cons]
            change cs.apply_braidMove (BraidMove.mk i j 0) (braidWord M i j ++ b_tail) =
              braidWord M j i ++ b_tail
            rw[apply_braidMove]
            have htake :
                List.take (M i j) (braidWord M i j ++ b_tail) = braidWord M i j := by
              rw[← length_alternatingWord i j (M i j)]
              exact List.take_left
            have hdrop :
                List.drop (M i j) (braidWord M i j ++ b_tail) = b_tail := by
              rw[← length_alternatingWord i j (M i j)]
              exact List.drop_left
            rw[if_pos htake, hdrop]
          · have b_word_cons :
                (braidWord M j i ++ b_tail) = j :: (alternatingWord j i m ++ b_tail) := by
              rw[braidWord, hm', alternatingWord_succ', if_neg m_even, List.cons_append]
            have switch_braidWord :
                π (braidWord M j i ++ b_tail) = π (braidWord M i j ++ b_tail) := by
              rw[wordProd_append, wordProd_append, cs.wordProd_braidWord_eq j i]
            have hb' : cs.wordProd (j :: l'_t) = cs.wordProd (braidWord M j i ++ b_tail) := by
              rw[switch_braidWord]
              rw[← hb]
              exact Eq.symm h_eq
            have b_reduced' : cs.IsReduced (braidWord M j i ++ b_tail) := by
              apply cs.isReduced_of_eq_length (braidWord M i j ++ b_tail)
                (braidWord M j i ++ b_tail)
              · simp only [List.length_append, length_alternatingWord]
                rw[M.symmetric]
              · exact Eq.symm switch_braidWord
              · exact b_reduced
            have b_len_p : (alternatingWord j i m ++ b_tail).length = p := by
              have h_length :
                  (braidWord M j i ++ b_tail).length = p + 1 := by
                rw[← cs.eq_length_of_isReduced (j :: l'_t) (braidWord M j i ++ b_tail)
                  hb' l'_reduced b_reduced']
                exact len_l'_eq_p
              rw[b_word_cons] at h_length
              simp only [List.length_cons, List.length_append, length_alternatingWord] at h_length ⊢
              omega
            have j_tail_reduced : cs.IsReduced l'_t := by
              apply cs.isReduced_cons j l'_t l'_reduced
            have aword_is_reduced : cs.IsReduced (alternatingWord j i m ++ b_tail) := by
              apply cs.isReduced_cons j ((alternatingWord j i m) ++ b_tail)
              rw[← b_word_cons]
              exact b_reduced'
            have j_tail_eq_aword : π (alternatingWord j i m ++ b_tail) = π l'_t := by
              rw[b_word_cons] at hb'
              rw[wordProd_cons, wordProd_cons] at hb'
              rw[mul_left_cancel_iff] at hb'
              exact Eq.symm hb'
            rcases ih (alternatingWord j i m ++ b_tail) l'_t b_len_p len_l'_t_eq_p
              aword_is_reduced j_tail_reduced j_tail_eq_aword with ⟨bms, ih'⟩
            use (List.map cs.shift_braidMove bms)
            rw[b_word_cons]
            rw[← braidMoveSequence_cons]
            suffices cs.apply_braidMoveSequence bms (alternatingWord j i m ++ b_tail) = l'_t
              from by
                rw[this]
            exact ih'

theorem matsumoto_reduced [MatsumotoCondition cs] (l l' : List B)
(hr : cs.IsReduced l) (hr' : cs.IsReduced l') (h : π l = π l') :
  ∃ bms : List (cs.BraidMove), cs.apply_braidMoveSequence bms l = l' := by
  apply cs.matsumoto_reduced_aux (l.length) l l' rfl _ hr hr' h
  calc
      l'.length = len (π l') := by
        rw[IsReduced] at hr'
        rw[← hr']
      _ = len (π l) := by rw[h]
      _ = l.length := by
        rw[IsReduced] at hr
        rw[← hr]

end

end CoxeterSystem
