/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Lifting
import LeanPool.Chomsky.Classes.Unrestricted.ClosureProperties.Concatenation

/-!
# Star

Closure of general-grammar languages under the Kleene star.
-/

open scoped Chomsky

namespace Chomsky


-- new nonterminal type
private abbrev nn (N : Type) : Type :=
  N ⊕ Fin 3

-- new symbol type
private abbrev ns (T N : Type) : Type :=
  Symbol T (nn N)

variable {T : Type}


section specific_symbols

private def Z {N : Type} : ns T N :=
  Symbol.nonterminal ▶0

private def H {N : Type} : ns T N :=
  Symbol.nonterminal ▶1

private def R {N : Type} : ns T N :=
  Symbol.nonterminal ▶2

private def S {g : Grammar T} : ns T g.nt :=
  Symbol.nonterminal ◄g.initial

private lemma Z_neq_H {N : Type} : Z ≠ @H T N :=
by
  intro ass
  have imposs := Sum.inr.inj (Symbol.nonterminal.inj ass)
  have zero_ne_one : (0 : Fin 3) ≠ (1 : Fin 3) := by
    decide
  exact zero_ne_one imposs

private lemma Z_neq_R {N : Type} : Z ≠ @R T N :=
by
  intro ass
  have imposs := Sum.inr.inj (Symbol.nonterminal.inj ass)
  have zero_ne_two : (0 : Fin 3) ≠ (2 : Fin 3) := by
    decide
  exact zero_ne_two imposs

private lemma H_neq_R {N : Type} : H ≠ @R T N :=
by
  intro ass
  have imposs := Sum.inr.inj (Symbol.nonterminal.inj ass)
  have one_ne_two : (1 : Fin 3) ≠ (2 : Fin 3) := by
    decide
  exact one_ne_two imposs

end specific_symbols


section construction

private def wrapSym {N : Type} : Symbol T N → ns T N :=
  liftSymbol Sum.inl

private def wrapGr {N : Type} : Grule T N → Grule T (nn N) :=
  liftRule Sum.inl

private def rulesThatScanTerminals (g : Grammar T) : List (Grule T (nn g.nt)) :=
  (allUsedTerminals g).map (fun t : T => Grule.mk [] ▶2 [Symbol.terminal t] [Symbol.terminal t, R])

-- grammar for iteration of `g.language`
@[reducible] private def Grammar.star (g : Grammar T) : Grammar T :=
  Grammar.mk (nn g.nt) ▶0 (
    Grule.mk [] ▶0 [] [Z, S, H] :: (
    Grule.mk [] ▶0 [] [R, H] :: (
    Grule.mk [] ▶2 [H] [R] :: (
    Grule.mk [] ▶2 [H] [] :: (
    g.rules.map wrapGr ++
    rulesThatScanTerminals g)))))

end construction


section easy_direction

private lemma short_induction {g : Grammar T} {w : List (List T)}
    (hwg : ∀ wᵢ ∈ w.reverse, wᵢ ∈ g.language) :
  g.star.Derives
    [Z]
    (Z :: ((w.reverse.map (List.map Symbol.terminal)).map (· ++ [H])).flatten) ∧
  ∀ p ∈ w, ∀ t ∈ p, Symbol.terminal t ∈ (g.rules.map Grule.output).flatten :=
by
  induction w with
  | nil =>
      constructor
      · apply gr_deri_self
      · intro p pin
        exfalso
        exact List.not_mem_nil pin
  | cons v x ih =>
      have vx_reverse : (v::x).reverse = x.reverse ++ [v] := by
        apply List.reverse_cons
      rw [vx_reverse] at hwg
      specialize ih (by
          intro wᵢ in_reversed
          apply hwg
          apply List.mem_append_left
          exact in_reversed)
      specialize hwg v (by
          apply List.mem_append_right
          apply List.mem_singleton_self)
      constructor
      · apply gr_deri_of_tran_deri
        · use g.star.rules.get ⟨0, Nat.zero_lt_succ _⟩
          constructor
          · apply List.get_mem
          use [], []
          constructor <;> rfl
        rw [List.nil_append, List.append_nil]
        change g.star.Derives [Z, S, H] _
        have ih_plus := gr_deri_append ([S, H] : List (Symbol T g.star.nt)) ih.left
        apply gr_deri_of_deri_deri ih_plus
        have hgSv : g.star.Derives [S] (v.map Symbol.terminal) := by
          clear * - hwg
          have wrap_eq_lift : @wrapSym T g.nt = liftSymbol Sum.inl := by
            ext x
            cases x <;> rfl
          let G : LiftedGrammar T :=
            LiftedGrammar.mk g g.star Sum.inl Sum.getLeft?
              (by
                intro x y hyp
                exact Sum.inl.inj hyp)
              (by
                intro x y hyp
                cases x
                · cases y
                  · simp only [Sum.getLeft?, Option.some.injEq] at hyp
                    left
                    exact congr_arg Sum.inl hyp
                  · simp [Sum.getLeft?] at hyp
                · cases y
                  · simp [Sum.getLeft?] at hyp
                  · right
                    rfl)
              (by
                intro x
                rfl)
              (by
                intro r rin
                apply List.mem_cons_of_mem
                apply List.mem_cons_of_mem
                apply List.mem_cons_of_mem
                apply List.mem_cons_of_mem
                apply List.mem_append_left
                rw [List.mem_map]
                use r, rin
                rfl)
              (by
                rintro r ⟨rin, n, nrn⟩
                cases rin with
                | head => simp at nrn
                | tail _ rin =>
                  cases rin with
                  | head => simp at nrn
                  | tail _ rin =>
                    cases rin with
                    | head => simp at nrn
                    | tail _ rin =>
                      cases rin with
                      | head => simp at nrn
                      | tail _ rin =>
                        change r ∈ g.rules.map wrapGr ++ rulesThatScanTerminals g at rin
                        rw [List.mem_append] at rin
                        cases rin with
                        | inl rin =>
                          rw [List.mem_map] at rin
                          convert rin
                        | inr rin =>
                          exfalso
                          unfold rulesThatScanTerminals at rin
                          rw [List.mem_map] at rin
                          rcases rin with ⟨t, tin, r_of_tg⟩
                          rw [←r_of_tg] at nrn
                          simp at nrn)
          convert_to G.g.Derives [Symbol.nonterminal ◄g.initial]
            (liftString G.liftNt (v.map Symbol.terminal))
          · symm
            apply List.map_map
          exact lift_deri G hwg
        have ass_postf := gr_deri_append [H] hgSv
        simp only [vx_reverse, ←List.cons_append,
          List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
            List.flatten_nil, List.append_nil]
        exact gr_append_deri _ ass_postf
      · intro p pin t tin
        cases pin with
        | head =>
          rcases grammar_generates_only_legit_terminals hwg (Symbol.terminal t)
              (show Symbol.terminal t ∈ v.map Symbol.terminal by rw [List.mem_map]; use t) with
            rule_exists | imposs
          · rcases rule_exists with ⟨r, rin, stirn⟩
            rw [List.mem_flatten]
            use r.output
            constructor
            · rw [List.mem_map]
              use r
            · exact stirn
          · exfalso
            simp at imposs
        | tail b pin => exact ih.right p pin t tin

private lemma terminal_scan_ind {g : Grammar T} {w : List (List T)} (n : ℕ)
    (n_lt_wl : n ≤ w.length)
    (terminals : ∀ v ∈ w, ∀ t ∈ v, Symbol.terminal t ∈ (g.rules.map Grule.output).flatten) :
  g.star.Derives
    (((w.take (w.length - n)).map (List.map Symbol.terminal)).flatten ++ [R] ++
     ((w.drop (w.length - n)).map ([H] ++ ·.map Symbol.terminal)).flatten ++ [H])
    (w.flatten.map Symbol.terminal ++ [R, H]) :=
by
  induction n with
  | zero =>
      rw [Nat.sub_zero, List.drop_length, List.map_nil, List.flatten, List.append_nil,
           List.take_length, List.map_flatten, List.append_assoc]
      apply gr_deri_self
  | succ k ih =>
      specialize ih (Nat.le_of_succ_le n_lt_wl)
      apply gr_deri_of_deri_deri _ ih
      clear ih
      have wlk_succ : w.length - k = (w.length - k.succ).succ := by
        omega
      have lt_wl : w.length - k.succ < w.length := by
        omega
      have split_ldw : w.drop (w.length - k.succ) = (w[w.length - k.succ]?).toList ++ w.drop
        (w.length - k) := by
        rw [wlk_succ]
        generalize substit : w.length - k.succ = q
        rw [substit] at lt_wl
        rw [←List.take_append_drop q w, List.getElem?_append_right (List.length_take_le ..)]
        have eq_q : (w.take q).length = q := by
          rw [List.length_take]
          exact min_eq_left_of_lt lt_wl
        rw [eq_q]
        rw [Nat.sub_self]
        have drop_q_succ : (w.take q ++ w.drop q).drop q.succ = (w.drop q).drop 1 := by
          rw [List.drop_drop, List.take_append_drop]
        rw [drop_q_succ, List.drop_left' eq_q, List.drop_drop]
        rw [←List.take_append_drop (1 + q) w]
        have q_lt : q < (w.take (1 + q)).length := by
          rw [List.length_take]
          exact lt_min (lt_one_add q) lt_wl
        rw [List.drop_append_of_le_length (le_of_lt q_lt)]
        apply congr_arg₂
        · rw [List.getElem?_append, List.getElem?_drop, add_zero, List.getElem?_take, add_comm,
               list_drop_take_succ lt_wl]
          simp [*]
        · rw [List.take_append_drop, add_comm]
      apply gr_deri_append
      rw [split_ldw, List.map_append, List.flatten_append, ←List.append_assoc]
      apply gr_deri_append
      rw [wlk_succ, List.take_add_one, List.map_append, List.flatten_append, List.append_assoc,
           List.append_assoc]
      apply gr_append_deri
      clear * - terminals lt_wl
      specialize terminals (w.get ⟨w.length - k.succ, lt_wl⟩) (w.get_mem ⟨w.length - k.succ, lt_wl⟩)
      simp only [List.cons_append, List.nil_append, Nat.succ_eq_add_one]
      have hw : 0 < w.length := by
        linarith
      simp only [tsub_lt_self_iff, hw, add_pos_iff, zero_lt_one, or_true, and_self, getElem?_pos,
        Option.toList_some, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      apply gr_deri_of_tran_deri
      · use g.star.rules[2]'(by simp [Grammar.star]), List.getElem_mem (by simp [Grammar.star]), [],
            (w[w.length - k.succ]'lt_wl).map Symbol.terminal, rfl
      rw [List.nil_append]
      have scan_segment :
        ∀ m : ℕ,
          m ≤ (w[w.length - k.succ]'lt_wl).length →
            g.star.Derives
              ([R] ++ (w[w.length - k.succ]'lt_wl).map Symbol.terminal)
              (((w[w.length - k.succ]'lt_wl).take m).map Symbol.terminal ++ ([R] ++
               ((w[w.length - k.succ]'lt_wl).drop m).map Symbol.terminal)) := by
        intro m small
        induction m with
        | zero => apply gr_deri_self
        | succ n ih =>
          apply gr_deri_of_deri_tran (ih (Nat.le_of_succ_le small))
          rw [Nat.succ_le_iff] at small
          use ⟨[], Sum.inr 2,
            [Symbol.terminal ((w[w.length - k.succ]'lt_wl)[n]'small)],
            [Symbol.terminal ((w[w.length - k.succ]'lt_wl)[n]'small), R]⟩
          constructor
          · apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            apply List.mem_append_right
            unfold rulesThatScanTerminals
            rw [List.mem_map]
            use (w[w.length - k.succ]'lt_wl)[n]'small
            constructor
            · unfold allUsedTerminals
              rw [List.mem_filterMap]
              use Symbol.terminal ((w[w.length - k.succ]'lt_wl)[n]'small)
              constructor
              · apply terminals
                exact List.getElem_mem small
              · rfl
            · rfl
          use ((w[w.length - k.succ]'lt_wl).take n).map Symbol.terminal
          use ((w[w.length - k.succ]'lt_wl).drop n.succ).map Symbol.terminal
          constructor
          · simp only [Nat.succ_eq_add_one, List.map_take, List.map_drop, List.cons_append,
                        List.nil_append, List.append_nil, Fin.isValue, List.append_assoc,
                        List.append_cancel_left_eq, List.cons.injEq]
            constructor
            · rfl
            · rw [←List.map_drop,
                   ←(((w[w.length - k.succ]'lt_wl).drop n).map Symbol.terminal).take_append_drop 1,
                   ←List.singleton_append]
              apply congr_arg₂
              · rewrite [←List.map_take, List.take_one_drop_eq_of_lt_length small]
                rfl
              · simp
          · rw [List.take_add_one, List.map_append]
            simp [*]
      convert scan_segment (w[w.length - k.succ]'lt_wl).length (by rfl) using 2
      · rw [List.take_length]
      · rewrite [List.drop_length, List.map_nil]
        rfl

private lemma terminal_scan_aux {g : Grammar T} {w : List (List T)}
    (terminals : ∀ v ∈ w, ∀ t ∈ v, Symbol.terminal t ∈ (g.rules.map Grule.output).flatten) :
  g.star.Derives
    ([R] ++ ((w.map (List.map Symbol.terminal)).map ([H] ++ ·)).flatten ++ [H])
    (w.flatten.map Symbol.terminal ++ [R, H]) :=
by
  rw [List.map_map]
  convert terminal_scan_ind w.length (by rfl) terminals using 1
  rewrite [Nat.sub_self, List.take_zero]
  rfl

end easy_direction


section hard_direction

lemma zero_of_not_ge_one {n : ℕ} (not_pos : ¬n ≥ 1) : n = 0 := by
  push Not at not_pos
  rwa [Nat.lt_one_iff] at not_pos

lemma length_ge_one_of_not_nil {α : Type _} {l : List α} (lnn : l ≠ []) : l.length ≥ 1 := by
  by_contra contra
  have llz := zero_of_not_ge_one contra
  rw [List.length_eq_zero_iff] at llz
  exact lnn llz

private lemma wrap_never_outputs_nt_inr {N : Type} {a : Symbol T N} (i : Fin 3) :
  wrapSym a ≠ Symbol.nonterminal ▶i :=
by
  cases a <;> unfold wrapSym
  · simp [liftSymbol]
  intro contr
  have inl_eq_inr := Symbol.nonterminal.inj contr
  simp at inl_eq_inr

private lemma wrap_never_outputs_Z {N : Type} {a : Symbol T N} : wrapSym a ≠ Z :=
  wrap_never_outputs_nt_inr 0

private lemma wrap_never_outputs_H {N : Type} {a : Symbol T N} : wrapSym a ≠ H :=
  wrap_never_outputs_nt_inr 1

private lemma wrap_never_outputs_R {N : Type} {a : Symbol T N} : wrapSym a ≠ R :=
  wrap_never_outputs_nt_inr 2

private lemma map_wrap_never_contains_nt_inr {N : Type} {l : List (Symbol T N)} (i : Fin 3) :
  Symbol.nonterminal ▶i ∉ l.map wrapSym :=
by
  intro contra
  rw [List.mem_map] at contra
  rcases contra with ⟨s, -, imposs⟩
  exact wrap_never_outputs_nt_inr i imposs

private lemma map_wrap_never_contains_Z {N : Type} {l : List (Symbol T N)} :
  Z ∉ l.map wrapSym :=
map_wrap_never_contains_nt_inr 0

private lemma map_wrap_never_contains_H {N : Type} {l : List (Symbol T N)} :
  H ∉ l.map wrapSym :=
map_wrap_never_contains_nt_inr 1

private lemma map_wrap_never_contains_R {N : Type} {l : List (Symbol T N)} :
  R ∉ l.map wrapSym :=
map_wrap_never_contains_nt_inr 2

private lemma wrapSym_inj {N : Type} {a b : Symbol T N} (wrap_eq : wrapSym a = wrapSym b) :
  a = b :=
by
  cases a
  · cases b
    · congr
      exact Symbol.terminal.inj wrap_eq
    · exfalso
      simp [wrapSym, liftSymbol] at wrap_eq
  · cases b
    · exfalso
      simp [wrapSym, liftSymbol] at wrap_eq
    · congr
      unfold wrapSym at wrap_eq
      exact Sum.inl.inj (Symbol.nonterminal.inj wrap_eq)

private lemma map_wrapSym_inj {N : Type} {x y : List (Symbol T N)}
    (wrap_eqs : x.map wrapSym = y.map wrapSym) :
  x = y :=
by
  ext1 n
  have eqnth := congr_arg (·[n]?) wrap_eqs
  rw [List.getElem?_map, List.getElem?_map] at eqnth
  rcases hxn : x[n]? with _ | xₙ
  · rcases hyn : y[n]? with _ | yₙ
    · rfl
    · exfalso
      simp_all
  · rcases hyn : y[n]? with _ | yₙ
    · exfalso
      simp_all
    · congr
      apply wrapSym_inj
      simp_all

private lemma H_not_in_rule_input {g : Grammar T} {r : Grule T g.nt} :
  H ∉ r.inputL.map wrapSym ++ [Symbol.nonterminal ◄r.inputN] ++ r.inputR.map wrapSym :=
by
  intro contra
  rw [List.mem_append] at contra
  cases contra with
  | inl hHrLN =>
    rw [List.mem_append] at hHrLN
    cases hHrLN with
    | inl hHrL => exact map_wrap_never_contains_H hHrL
    | inr hHrN =>
      rw [List.mem_singleton] at hHrN
      simp [H] at hHrN
  | inr hHrR => exact map_wrap_never_contains_H hHrR

private lemma snsri_not_in_join_mpHmmw {g : Grammar T} {x : List (List (Symbol T g.nt))} {i : Fin 3}
    (snsri_neq_H : Symbol.nonterminal ▶i ≠ @H T g.nt) :
  Symbol.nonterminal ▶i ∉ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten :=
by
  intro contra
  rw [List.mem_flatten, List.map_map] at contra
  rcases contra with ⟨l, l_in, in_l⟩
  rw [List.mem_map] at l_in
  rcases l_in with ⟨y, -, eq_l⟩
  rw [←eq_l] at in_l
  rw [Function.comp_apply, List.mem_append] at in_l
  cases in_l with
  | inl hiy => exact map_wrap_never_contains_nt_inr i hiy
  | inr hiH =>
    rw [List.mem_singleton] at hiH
    exact snsri_neq_H hiH

private lemma Z_not_in_join_mpHmmw {g : Grammar T} {x : List (List (Symbol T g.nt))} :
  Z ∉ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten :=
snsri_not_in_join_mpHmmw Z_neq_H

private lemma R_not_in_join_mpHmmw {g : Grammar T} {x : List (List (Symbol T g.nt))} :
  R ∉ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten :=
snsri_not_in_join_mpHmmw H_neq_R.symm

private lemma zero_Rs_in_the_long_part {g : Grammar T} {x : List (List (Symbol T g.nt))}
  [DecidableEq (ns T g.nt)] :
  ((x.map (List.map wrapSym)).map (· ++ [H])).flatten.countIn R = 0 :=
List.countIn_zero_of_notin R_not_in_join_mpHmmw

private lemma cases_1_and_2_and_3a_match_aux {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} (xnn : x ≠ [])
    (hyp :
      ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten
      :=
by
  have hypp : ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym) ++ v
        := by
    simpa [List.append_assoc] using hyp
  have mid_brack :
    ∀ u' v' : List (Symbol T g.nt),
      u' ++  r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR  ++ v' =
      u' ++ (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR) ++ v' := by
    intros
    simp only [List.append_assoc]
  simp_rw [mid_brack]
  clear hyp mid_brack
  classical
  have count_Hs := congr_arg (·.countIn H) hypp
  rw [List.countIn_append, List.countIn_append, List.countIn_zero_of_notin H_not_in_rule_input,
      add_zero, List.countIn_flatten, List.map_map, List.map_map] at count_Hs
  have lens := congr_arg List.length hypp
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
       List.length_singleton] at lens
  have ul_lt : u.length < ((x.map (List.map wrapSym)).map (· ++ [H])).flatten.length := by
    clear * - lens
    linarith
  rcases List.take_flatten_of_lt ul_lt with ⟨m, k, mlt, klt, init_ul⟩
  have vnn : v ≠ [] := by
    by_contra v_nil
    rw [v_nil, List.append_nil] at hypp
    clear * - hypp xnn
    have hlast := congr_arg (·.reverse[0]?) hypp
    rw [List.reverse_flatten, List.reverse_append, List.reverse_append_append,
         List.reverse_singleton] at hlast
    have hH : some H =
        ((r₀.inputR.map wrapSym).reverse ++ [Symbol.nonterminal ◄r₀.inputN]
          ++ (r₀.inputL.map wrapSym).reverse ++ u.reverse)[0]? := by
      convert hlast
      rw [List.map_map]
      change
        some H =
        ((x.map (List.map wrapSym)).map (· ++ [H] |>.reverse)).reverse.flatten[0]?
      simp_rw [List.reverse_append]
      rw [List.map_map]
      change
        some H =
        (x.map
          (fun l : List (Symbol T g.nt) => [H].reverse
          ++ (l.map wrapSym).reverse)).reverse.flatten[0]?
      rw [←List.map_reverse]
      have xrnn : x.reverse ≠ [] := by
        intro xr_nil
        rw [List.reverse_eq_iff] at xr_nil
        exact xnn xr_nil
      rcases hx : x.reverse with _ | ⟨d, l⟩
      · exfalso
        exact xrnn hx
      rw [List.map_cons, List.flatten]
      simp [H]
    rw [←List.map_reverse] at hH
    cases hr₀ : r₀.inputR.reverse
    · rw [hr₀] at hH
      simp [H] at hH
    · rw [hr₀] at hH
      simp at hH
      exact wrap_never_outputs_H hH.symm
  have urrrl_lt
    : (u
    ++ (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym)).length <
      ((x.map (List.map wrapSym)).map (· ++ [H])).flatten.length := by
    have vl_pos : v.length > 0 := List.length_pos_of_ne_nil vnn
    clear * - lens vl_pos
    rw [List.length_append, List.length_append, List.length_append, List.length_singleton]
    linarith
  rcases List.drop_flatten_of_lt urrrl_lt with ⟨m', k', mlt', klt', last_vl⟩
  have mxl : m < x.length := by
    rw [List.length_map] at mlt
    rw [List.length_map] at mlt
    exact mlt
  have mxl' : m' < x.length := by
    rw [List.length_map] at mlt'
    rw [List.length_map] at mlt'
    exact mlt'
  have mxlmm : m < (x.map (List.map wrapSym)).length := by
    rwa [List.length_map]
  have mxlmm' : m' < (x.map (List.map wrapSym)).length := by
    rwa [List.length_map]
  use m, (x.get ⟨m, mxl⟩).take k, (x.get ⟨m', mxl'⟩).drop k'
  have hyp_u := congr_arg (List.take u.length) hypp
  rw [List.append_assoc, List.take_left, init_ul] at hyp_u
  simp only [List.map_map, List.get_eq_getElem] at hyp_u
  rw [List.getElem_map] at hyp_u
  have hyp_v :=
    congr_arg
      (List.drop
        (u
          ++ (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map
          wrapSym)).length)
      hypp
  rw [List.drop_left, last_vl] at hyp_v
  rw [←hyp_u, ←hyp_v] at count_Hs
  have hmm : m = m' := by
    clear * - count_Hs mxl mxl' klt klt'
    simp only [Function.comp_apply, List.countIn_append, List.countIn_flatten, List.map_take,
                List.map_map, List.get_eq_getElem, List.getElem_map, Nat.succ_eq_add_one,
                List.map_drop] at count_Hs
    have inside_wrap : ∀ y : List (Symbol T g.nt), (y.map wrapSym).countIn H = 0 := by
      intro
      rw [List.countIn_zero_of_notin]
      apply map_wrap_never_contains_H
    have inside_one :
      ∀ z : List (Symbol T g.nt),
        (z.map wrapSym).countIn (@H T g.nt) + [@H T g.nt].countIn (@H T g.nt) = 1 := by
      intro
      rw [List.countIn_singleton_eq H, inside_wrap]
    have inside_take : (((x[m]'mxl).map wrapSym).take k).countIn H = 0 := by
      rw [←List.map_take, inside_wrap]
    have inside_drop : (((x[m']'mxl').map wrapSym).drop k').countIn H + [@H T g.nt].countIn H = 1
      := by
      rw [←List.map_drop, inside_wrap, List.countIn_singleton_eq (@H T g.nt)]
    have counted_Hs : x.length = (m + 0) + (1 + (x.length - m'.succ)) := by
      convert count_Hs using 3
      · change x.length = (x.map (·.map wrapSym ++ [H] |>.countIn H)).sum
        simp [List.countIn_append, inside_one]
      · change m = ((x.map (·.map wrapSym ++ [H] |>.countIn H)).take m).sum
        simp [List.countIn_append, inside_one, Nat.le_of_succ_le mxl]
      · rw [List.take_append_of_le_length, inside_take]
        apply Nat.le_of_lt_succ
        simpa using klt
      · rw [List.drop_append_of_le_length, List.countIn_append, inside_drop]
        apply Nat.le_of_lt_succ
        simpa using klt'
      · change x.length - m'.succ = ((x.map (·.map wrapSym ++ [H] |>.countIn H)).drop m'.succ).sum
        simp [List.countIn_append, inside_one]
    omega
  constructor
  · convert hyp_u.symm using 1
    simp_all only [ne_eq, List.map_map, List.append_assoc, List.cons_append, List.nil_append,
      List.length_append, List.length_map, List.length_cons, List.get_eq_getElem, List.getElem_map,
      Function.comp_apply, List.length_nil, zero_add, List.take_left', List.length_flatten,
      List.map_take, List.length_take, add_lt_add_iff_left, add_lt_add_iff_right,
      lt_add_iff_pos_right, Nat.succ_eq_add_one, List.append_cancel_left_eq, List.left_eq_take_iff,
      List.cons_ne_self, false_or]
    exact Nat.le_of_lt_succ klt
  constructor
  · have x_eq : x = x.take m ++ [x[m]'mxl] ++ x.drop m.succ := by
      simp
    have hxmxmxm :
      (((x.take m ++ [x[m]'mxl] ++ x.drop m.succ).map (List.map wrapSym)).map (· ++ [H])).flatten =
      (((x.map (List.map wrapSym)).map (· ++ [H])).take m).flatten ++
        ((x.map (List.map wrapSym))[m]'mxlmm).take k ++
        (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym) ++
        (((x.map (List.map wrapSym))[m]'mxlmm).drop k' ++ [H] ++
          (((x.map (List.map wrapSym)).map (· ++ [H])).drop m.succ).flatten) := by
      convert hypp
      · exact x_eq.symm
      · convert hyp_u using 1
        simp only [List.map_map, List.getElem_map, Function.comp_apply, List.append_cancel_left_eq,
                    List.left_eq_take_iff, List.cons_ne_self, List.length_map, false_or]
        apply Nat.le_of_lt_succ
        simpa using klt
      · convert hyp_v using 1
        simp only [List.getElem_map, Nat.succ_eq_add_one, List.map_map, List.append_assoc,
                    List.cons_append, List.nil_append, List.get_eq_getElem, Function.comp_apply]
        rw [←List.singleton_append, ←List.append_assoc, List.drop_append_of_le_length]
        · simp [hmm]
        · apply Nat.le_of_lt_succ
          simpa using klt'
    rw
      [List.map_append_append, List.map_append_append, List.flatten_append_append,
      List.append_assoc,
        List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
          List.append_assoc,
        List.map_take, List.map_take, List.append_right_inj, ←List.append_assoc, ←List.append_assoc,
        ←List.append_assoc, ←List.append_assoc, ←List.append_assoc, List.map_drop, List.map_drop,
        List.append_left_inj, List.map_singleton, List.map_singleton, List.flatten_singleton,
        List.append_left_inj] at hxmxmxm
    rw [List.getElem?_eq_some_iff]
    use mxl
    apply map_wrapSym_inj
    rw [hxmxmxm]
    simp [hmm]
    rfl
  · convert hyp_v.symm using 1
    simp only [List.get_eq_getElem, List.map_drop, Nat.succ_eq_add_one, List.map_map,
                List.append_assoc, List.cons_append, List.nil_append, List.getElem_map,
                Function.comp_apply]
    rw [←List.singleton_append, ←List.append_assoc, List.drop_append_of_le_length, hmm]
    simpa using Nat.le_of_lt_succ (by simpa using klt')

private lemma case_1_match_rule {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (hyp :
      (Z :: ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = (Z :: (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten) ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten
      :=
by
  by_cases is_x_nil : x = []
  · exfalso
    rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at hyp
    have hyp_len := congr_arg List.length hyp
    rw [List.length_singleton] at hyp_len
    repeat rw [List.length_append] at hyp_len
    rw [List.length_singleton] at hyp_len
    have left_nil : u ++ r₀.inputL.map wrapSym = [] := by
      rw [←List.length_eq_zero_iff, List.length_append]
      omega
    have right_nil : r₀.inputR.map wrapSym ++ v = [] := by
      rw [←List.length_eq_zero_iff, List.length_append]
      omega
    rw [left_nil, List.nil_append, List.append_assoc, right_nil, List.append_nil] at hyp
    have imposs := List.head_eq_of_cons_eq hyp
    unfold Z at imposs
    simp_all
  have unn : u ≠ [] := by
    by_contra u_nil
    rw [u_nil, List.nil_append] at hyp
    rcases hr₀ : r₀.inputL with _ | ⟨d, l⟩
    · rw [hr₀, List.map_nil, List.nil_append] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      have inr_eq_inl := Symbol.nonterminal.inj imposs
      simp at inr_eq_inl
    · rw [hr₀, List.map_cons] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      cases d
      · unfold wrapSym at imposs
        simp [liftSymbol, Z] at imposs
      · unfold wrapSym at imposs
        have inr_eq_inl := Symbol.nonterminal.inj imposs
        simp at inr_eq_inl
  have hypr := congr_arg List.tail hyp
  rw [List.tail] at hypr
  repeat rw [List.append_assoc] at hypr
  rw [List.tail_append_of_ne_nil unn] at hypr
  repeat rw [←List.append_assoc] at hypr
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hypr with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
  use m, u₁, v₁
  constructor
  · rcases u with _ | ⟨d, l⟩
    · exfalso
      exact unn rfl
    have headZ : d = Z := by
      repeat rw [List.cons_append] at hyp
      exact List.head_eq_of_cons_eq hyp.symm
    rw [headZ]
    rw [List.tail] at u_eq
    rw [u_eq]
    apply List.cons_append
  constructor
  · simp_all
  · exact v_eq

private lemma star_case_1 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp :
      ∃ x : List (List (Symbol T g.nt)),
        (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
          α = [Z] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = [Z] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
      α' = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :=
by
  rcases hyp with ⟨x, valid, cat⟩
  have no_R_in_alpha : R ∉ α := by
    intro contr
    rw [cat] at contr
    clear * - contr
    rw [List.mem_append] at contr
    cases contr with
    | inl hRZ => exact Z_neq_R.symm (List.mem_singleton.→ hRZ)
    | inr hRH => exact R_not_in_join_mpHmmw hRH
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  cases rin with
  | head =>
    dsimp only at *
    rw [List.append_nil, List.append_nil] at bef
    left
    use [Symbol.nonterminal g.initial] :: x
    constructor
    · intro xᵢ xin
      cases xin with
      | head => apply gr_deri_self
      | tail _ xin => exact valid xᵢ xin
    have u_nil : u = [] := by
      clear * - bef cat
      rw [←List.length_eq_zero_iff]
      by_contra
      have ul_pos : 0 < u.length := by
        rwa [pos_iff_ne_zero]
      have bef_tail := congr_arg List.tail bef
      rcases u with _ | ⟨d, l⟩
      · rw [List.length] at ul_pos
        exact Nat.lt_irrefl 0 ul_pos
      · have Z_in_tail : Z ∈ l ++ [Symbol.nonterminal ▶0] ++ v := by
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_singleton_self
        rw [cat, List.singleton_append, List.tail_cons, List.cons_append, List.cons_append,
             List.tail_cons] at bef_tail
        rw [←bef_tail] at Z_in_tail
        exact Z_not_in_join_mpHmmw Z_in_tail
    have v_rest : v = ((x.map (List.map wrapSym)).map (· ++ [H])).flatten := by
      rw [u_nil, cat] at bef
      convert congr_arg List.tail bef.symm
    rewrite [aft, u_nil, v_rest, List.nil_append, List.map_cons]
    rfl
  | tail _ rin =>
    cases rin with
    | head =>
      right
      dsimp only at *
      use x
      constructor
      · exact valid
      have u_nil : u = [] := by
        clear * - bef cat
        rw [←List.length_eq_zero_iff]
        by_contra
        have ul_pos : 0 < u.length := by
          rwa [pos_iff_ne_zero]
        have bef_tail := congr_arg List.tail bef
        rcases u with _ | ⟨d, l⟩
        · rw [List.length] at ul_pos
          exact Nat.lt_irrefl 0 ul_pos
        · have Z_in_tail : Z ∈ l ++ [Symbol.nonterminal ▶0] ++ v := by
            apply List.mem_append_left
            apply List.mem_append_right
            apply List.mem_singleton_self
          rw [cat, List.singleton_append, List.tail_cons,
            List.cons_append, List.cons_append, List.append_nil, List.append_nil, List.cons_append,
              List.tail_cons
          ] at bef_tail
          rw [←bef_tail] at Z_in_tail
          exact Z_not_in_join_mpHmmw Z_in_tail
      have v_rest : v = ((x.map (List.map wrapSym)).map (· ++ [H])).flatten := by
        rw [cat, u_nil] at bef
        convert congr_arg List.tail bef.symm
      rw [aft, u_nil, v_rest]
      rfl
    | tail _ rin =>
      cases rin with
      | head =>
        exfalso
        apply no_R_in_alpha
        rw [bef]
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        rw [List.mem_singleton]
        rfl
      | tail _ rin =>
        cases rin with
        | head =>
          exfalso
          apply no_R_in_alpha
          rw [bef]
          apply List.mem_append_left
          apply List.mem_append_left
          apply List.mem_append_right
          rw [List.mem_singleton]
          rfl
        | tail _ rin =>
          have rin' : r ∈ rulesThatScanTerminals g ∨ r ∈ g.rules.map wrapGr := by
            rwa [or_comm, ←List.mem_append]
          clear rin
          rcases rin' with rin' | rin'
          · exfalso
            apply no_R_in_alpha
            rw [bef]
            apply List.mem_append_left
            apply List.mem_append_left
            apply List.mem_append_right
            rw [List.mem_singleton]
            unfold rulesThatScanTerminals at rin'
            rw [List.mem_map] at rin'
            rcases rin' with ⟨t, -, form⟩
            rw [←form]
            rfl
          · left
            rw [List.mem_map] at rin'
            rcases rin' with ⟨r₀, orig_in, wrap_orig⟩
            rw [cat, ←wrap_orig] at bef
            obtain ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩ := case_1_match_rule bef
            clear bef
            rw [u_eq, v_eq] at aft
            use x.take m ++ [u₁ ++ r₀.output ++ v₁] ++ x.drop m.succ
            constructor
            · intro xᵢ xiin
              rw [List.mem_append_append] at xiin
              cases xiin with
              | inl xiin =>
                apply valid
                exact List.mem_of_mem_take xiin
              | inr xiin =>
                cases xiin with
                | inl xiin =>
                  rw [List.mem_singleton] at xiin
                  rw [xiin]
                  have last_step :
                    g.Transforms
                      (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                      (u₁ ++ r₀.output ++ v₁) := by
                    use r₀, orig_in, u₁, v₁
                  apply gr_deri_of_deri_tran _ last_step
                  apply valid (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                  exact List.mem_of_getElem? xm_eq
                | inr xiin =>
                  apply valid
                  exact List.mem_of_mem_drop xiin
            rw [List.singleton_append, aft]
            simp [←wrap_orig]
            rfl

private lemma uv_nil_of_RH_eq {g : Grammar T} {u v : List (ns T g.nt)}
    (ass : [R, H] = u ++ [] ++ [Symbol.nonterminal ▶2] ++ [H] ++ v) :
  u = [] ∧ v = [] :=
by
  rw [List.append_nil] at ass
  have lens := congr_arg List.length ass
  simp only [List.length_append, List.length, zero_add] at lens
  constructor <;>
    · rw [←List.length_eq_zero_iff]
      omega

private lemma u_nil_when_RH {g : Grammar T} {x : List (List (Symbol T g.nt))}
  {u v : List (ns T g.nt)}
    (ass :
      [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [] ++ [Symbol.nonterminal ▶2] ++ [H] ++ v) :
  u = [] :=
by
  rcases u with _ | ⟨d, l⟩
  · rfl
  rw [List.append_nil] at ass
  exfalso
  by_cases hdR : d = R
  · classical
    have imposs := congr_arg (·.countIn (@R T g.nt)) ass
    have long_zero :
        (((x.map (List.map wrapSym)).map (· ++ [H])).flatten).countIn (@R T g.nt) = 0 :=
      zero_Rs_in_the_long_part
    rw [hdR, List.countIn_append, long_zero] at imposs
    simp [List.countIn_append, List.countIn_cons, List.countIn_nil, R, H] at imposs
  · simp_all

private lemma case_2_match_rule {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (hyp :
      R :: H :: ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = (R :: H :: (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten) ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten
      :=
by
  by_cases is_x_nil : x = []
  · exfalso
    rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at hyp
    have imposs : (Symbol.nonterminal ◄r₀.inputN : ns T g.nt) = R ∨
        (Symbol.nonterminal ◄r₀.inputN : ns T g.nt) = H := by
      simpa using congr_arg ((Symbol.nonterminal ◄r₀.inputN : ns T g.nt) ∈ ·) hyp
    rcases imposs with imposs | imposs <;> simp [R, H] at imposs
  have unn : u ≠ [] := by
    by_contra u_nil
    rw [u_nil, List.nil_append] at hyp
    cases hrL : r₀.inputL with
    | nil =>
      rw [hrL] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      have inr_eq_inl := Symbol.nonterminal.inj imposs
      simp at inr_eq_inl
    | cons d l =>
      rw [hrL, List.map_cons] at hyp
      have imposs := List.head_eq_of_cons_eq hyp
      cases d
      · simp [wrapSym, liftSymbol, R] at imposs
      · have inr_eq_inl := Symbol.nonterminal.inj imposs
        simp at inr_eq_inl
  have hypt := congr_arg List.tail hyp
  rw [List.tail] at hypt
  repeat rw [List.append_assoc] at hypt
  rw [List.tail_append_of_ne_nil unn] at hypt
  have utnn : u.tail ≠ [] := by
    by_contra ut_nil
    rw [ut_nil, List.nil_append] at hypt
    cases hrL : r₀.inputL with
    | nil =>
      rw [hrL, List.map_nil, List.nil_append] at hypt
      have imposs := List.head_eq_of_cons_eq hypt
      have inr_eq_inl := Symbol.nonterminal.inj imposs
      simp at inr_eq_inl
    | cons d l =>
      rw [hrL, List.map_cons] at hypt
      have imposs := List.head_eq_of_cons_eq hypt
      cases d
      · unfold wrapSym at imposs
        simp [liftSymbol, H] at imposs
      · unfold wrapSym at imposs
        have inr_eq_inl := Symbol.nonterminal.inj imposs
        simp at inr_eq_inl
  have hyptt := congr_arg List.tail hypt
  rw [List.tail, List.tail_append_of_ne_nil utnn] at hyptt
  repeat rw [←List.append_assoc] at hyptt
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hyptt with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
  use m, u₁, v₁
  constructor
  · rcases u with _ | ⟨d, l⟩
    · exfalso
      exact unn rfl
    have headR : d = R := by
      repeat rw [List.cons_append] at hyp
      exact List.head_eq_of_cons_eq hyp.symm
    rw [List.tail] at u_eq hypt
    rcases l with _ | ⟨d', l'⟩
    · exfalso
      exact utnn rfl
    have tailHead : d' = H := by
      repeat rw [List.cons_append] at hypt
      exact List.head_eq_of_cons_eq hypt.symm
    rw [List.tail] at u_eq
    rw [headR, tailHead, u_eq, List.cons_append, List.cons_append]
  constructor
  · exact xm_eq
  · exact v_eq

private lemma star_case_2 {g : Grammar T} {α α' : List (Symbol T g.star.nt)}
    (hαα : g.star.Transforms α α')
    (hgg : ∃ x : List (List (Symbol T g.nt)),
        (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
        α = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H]
      ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α' = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rcases hgg with ⟨x, valid, cat⟩
  have no_Z_in_alpha : Z ∉ α := by
    intro contr
    rw [cat, List.mem_append] at contr
    refine contr.casesOn (fun ZRH => ?_) Z_not_in_join_mpHmmw
    rw [List.mem_pair] at ZRH
    exact ZRH.casesOn Z_neq_R Z_neq_H
  rcases hαα with ⟨r, rin, u, v, bef, aft⟩
  simp only [Grammar.star, List.mem_cons, List.mem_append, List.mem_map] at rin
  rcases rin with rinputZ | rinputZ | RH_R | RH_nil | original | Rt_tR
  iterate 2
    · exfalso
      apply no_Z_in_alpha
      rw [bef, rinputZ, List.mem_append_append, List.mem_append_append]
      left; right; right
      rewrite [List.mem_singleton]
      rfl
  · rcases x with _ | ⟨x₀, L⟩
    · right; right; right; left
      have empty_string : u = [] ∧ v = [] := by
        rw [RH_R, cat] at bef
        exact uv_nil_of_RH_eq bef
      rw [empty_string.left, List.nil_append, empty_string.right, List.append_nil] at aft
      use []
      rw [aft, List.map_nil, List.nil_append, RH_R]
    · right; left
      use [], [], x₀, L
      constructor
      · intro wᵢ wiin
        exfalso
        rw [List.mem_nil_iff] at wiin
        exact wiin
      constructor
      · rw [List.map_nil, List.nil_append]
        exact valid x₀ (List.mem_cons_self)
      constructor
      · intro xᵢ xiin
        exact valid xᵢ (List.mem_cons_of_mem x₀ xiin)
      rw [aft, List.map_nil, List.append_nil, List.flatten, List.map_nil, List.nil_append]
      rw [RH_R] at bef ⊢
      rw [cat] at bef
      have u_nil := u_nil_when_RH bef
      rw [u_nil, List.nil_append] at bef ⊢
      rw [←List.append_inj_right bef (by rfl), List.map_cons, List.map_cons, List.flatten]
      simp only [List.append_assoc, List.append_eq]
  · cases hx : x with
    | nil =>
      right; right; left
      rw [cat, hx, List.map_nil, List.map_nil, List.flatten, List.append_nil] at bef
      have empty_string : u = [] ∧ v = [] := by
        rw [RH_nil] at bef
        exact uv_nil_of_RH_eq bef
      rw [empty_string.left, List.nil_append, empty_string.right, List.append_nil] at aft
      use [], ⟨[], rfl, fun _ h => (List.not_mem_nil h).elim⟩
      rw [aft, List.map_nil, RH_nil]
    | cons x₀ L =>
      right; right; right; right
      rw [cat, RH_nil] at bef
      dsimp only at bef
      have u_nil := u_nil_when_RH bef
      rw [u_nil, List.nil_append] at bef
      have v_eq := (List.append_inj_right bef (by rfl)).symm
      rw [u_nil, List.nil_append, v_eq, RH_nil, List.nil_append, hx, List.map_cons, List.map_cons,
          List.flatten] at aft
      simp only [List.append_eq] at aft
      rw [List.append_assoc, List.append_flatten_map_append, ←List.append_assoc] at aft
      constructor
      · use x₀.map wrapSym ++ ((L.map (List.map wrapSym)).map ([H] ++ ·)).flatten
      rw [List.append_assoc, ←List.append_flatten_map_append] at aft
      rw [aft]
      constructor <;> intro contra <;> rw [List.mem_append] at contra
      · refine contra.casesOn map_wrap_never_contains_Z (fun contr => ?_)
        rw [List.mem_append] at contr
        refine contr.casesOn (fun hR => ?_) Z_not_in_join_mpHmmw
        simp_rw [List.mem_cons, List.not_mem_nil, or_false] at hR
        exact Z_neq_H hR
      · refine contra.casesOn map_wrap_never_contains_R (fun contr => ?_)
        rw [List.mem_append] at contr
        refine contr.casesOn (fun hR => ?_) R_not_in_join_mpHmmw
        simp_rw [List.mem_cons, List.not_mem_nil, or_false] at hR
        exact H_neq_R hR.symm
  · left
    rcases original with ⟨r₀, orig_in, wrap_orig⟩
    unfold wrapGr at wrap_orig
    rw [cat, ←wrap_orig] at bef
    rcases case_2_match_rule bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
    clear bef
    rw [u_eq, v_eq] at aft
    use x.take m ++ [u₁ ++ r₀.output ++ v₁] ++ List.drop m.succ x
    constructor
    · intro xᵢ xiin
      rw [List.mem_append_append] at xiin
      cases xiin with
      | inl xiin =>
        apply valid
        exact List.mem_of_mem_take xiin
      | inr xiin =>
        cases xiin with
        | inr xiin =>
          apply valid
          exact List.mem_of_mem_drop xiin
        | inl xiin =>
          rw [List.mem_singleton] at xiin
          rw [xiin]
          have last_step :
            g.Transforms
              (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
              (u₁ ++ r₀.output ++ v₁) := by
            use r₀, orig_in, u₁, v₁
          apply gr_deri_of_deri_tran _ last_step
          apply valid (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
          exact List.mem_of_getElem? xm_eq
    simp [aft, ←wrap_orig]
    rfl
  · exfalso
    unfold rulesThatScanTerminals at Rt_tR
    rw [List.mem_map] at Rt_tR
    rcases Rt_tR with ⟨t, -, form⟩
    rw [←form] at bef
    dsimp only at bef
    rw [List.append_nil] at bef
    have u_nil : u = [] := by
      rcases u with _ | ⟨d, l⟩
      · rfl
      exfalso
      rw [cat] at bef
      repeat rw [List.cons_append] at bef
      rw [List.nil_append] at bef
      have btail := List.tail_eq_of_cons_eq bef
      have imposs := congr_arg (R ∈ ·) btail
      apply false_of_true_eq_false
      convert imposs.symm
      · rw [true_iff]
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_singleton_self
      · rw [false_iff]
        intro hyp
        rw [List.mem_cons] at hyp
        cases hyp with
        | inl hRH => exact H_neq_R hRH.symm
        | inr Rin =>
          rw [List.mem_flatten] at Rin
          rcases Rin with ⟨p, pin, Rinp⟩
          rw [List.mem_map] at pin
          rcases pin with ⟨q, qin, eq_p⟩
          rw [←eq_p] at Rinp
          rw [List.mem_append] at Rinp
          cases Rinp with
          | inl hRq =>
            rw [List.mem_map] at qin
            rcases qin with ⟨p', -, eq_q⟩
            rw [←eq_q] at hRq
            exact map_wrap_never_contains_R hRq
          | inr hRH =>
            rw [List.mem_singleton] at hRH
            exact H_neq_R hRH.symm
    rw [u_nil, cat] at bef
    have second_symbol := (congr_arg (·[1]?) bef)
    simp [H] at second_symbol

private lemma case_3_ni_wb {g : Grammar T} {w : List (List T)} {β : List T} {i : Fin 3} :
  @Symbol.nonterminal T (nn g.nt) ▶i ∉
    w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map (@Symbol.terminal T (nn g.nt)) :=
by
  intro contra
  rw [List.mem_append] at contra
  rcases contra with contra | contra <;> rw [List.mem_map] at contra <;>
    rcases contra with ⟨t, -, imposs⟩ <;> simp at imposs

private lemma case_3_ni_u {g : Grammar T} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
      {s : ns T g.nt}
    (ass :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [R] ++ [s] ++ v) :
  R ∉ u :=
by
  intro R_in_u
  classical
  have count_R := congr_arg (·.countIn R) ass
  repeat rw [List.countIn_append] at count_R
  have R_ni_wb : @R T g.nt ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal := case_3_ni_wb
  rw [List.countIn_singleton_eq, List.countIn_singleton_neq H_neq_R, add_zero,
      ←List.countIn_append, List.countIn_zero_of_notin R_ni_wb, zero_add,
      List.countIn_zero_of_notin map_wrap_never_contains_R, add_zero,
      zero_Rs_in_the_long_part, add_zero
  ] at count_R
  have ucR_pos := List.countIn_pos_of_in R_in_u
  clear * - count_R ucR_pos
  linarith

private lemma case_3_u_eq_left_side {g : Grammar T} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
      {s : ns T g.nt}
    (ass :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [Symbol.nonterminal ▶2] ++ [s] ++ v) :
  u = w.flatten.map Symbol.terminal ++ β.map (@Symbol.terminal T (nn g.nt)) :=
by
  have R_ni_u : R ∉ u := case_3_ni_u ass
  have R_ni_wb : R ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++
      β.map (@Symbol.terminal T (nn g.nt)) := by
    apply @case_3_ni_wb T g
  repeat rw [List.append_assoc] at ass
  convert congr_arg (List.take u.length) ass.symm using 1
  · rw [List.take_left]
  rw [←List.append_assoc, List.take_left']
  classical
  have index_of_first_R := congr_arg (List.idxOf R) ass
  rwa
    [List.idxOf_append_of_notMem R_ni_u, @List.singleton_append _ _ ([s] ++ v), ←R,
    List.idxOf_cons_self, add_zero,
      ←List.append_assoc, List.idxOf_append_of_notMem R_ni_wb, List.singleton_append,
        List.idxOf_cons_self, add_zero
  ] at index_of_first_R

private lemma case_3_gamma_nil {g : Grammar T} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (ass :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ [Symbol.nonterminal ▶2] ++ [H] ++ v) :
  γ = [] :=
by
  have R_ni_wb : @R T g.nt ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal := case_3_ni_wb
  have H_ni_wb : @H T g.nt ∉ w.flatten.map Symbol.terminal ++ β.map Symbol.terminal := case_3_ni_wb
  have H_ni_wbrg : H ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal ++ [R]
    ++ γ.map wrapSym := by
    intro contra
    rw [List.mem_append] at contra
    refine contra.casesOn (fun hH => ?_) map_wrap_never_contains_H
    rw [List.mem_append] at hH
    refine hH.casesOn H_ni_wb (fun hHR => ?_)
    rw [List.mem_singleton] at hHR
    exact H_neq_R hHR
  have R_ni_u : @Symbol.nonterminal T (nn g.nt) ▶2 ∉ u := case_3_ni_u ass
  have H_ni_u : H ∉ u := case_3_u_eq_left_side ass ▸ H_ni_wb
  classical
  have first_R := congr_arg (List.idxOf R) ass
  have first_H := congr_arg (List.idxOf H) ass
  simp only [List.append_assoc (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal)] at first_R
  simp only
    [List.append_assoc
    (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym)] at first_H
  rw [List.idxOf_append_of_notMem R_ni_wb] at first_R
  rw [List.idxOf_append_of_notMem H_ni_wbrg] at first_H
  rw [List.cons_append, List.cons_append, List.cons_append, R, List.idxOf_cons_self,
       add_zero] at first_R
  rw [List.cons_append, List.idxOf_cons_self, add_zero] at first_H
  rw [List.append_assoc u, List.append_assoc u] at first_R first_H
  rw [List.idxOf_append_of_notMem R_ni_u] at first_R
  rw [List.idxOf_append_of_notMem H_ni_u] at first_H
  rw [List.append_assoc _ [H], List.singleton_append, List.idxOf_cons_self, add_zero] at first_R
  rw [List.append_assoc _ [H], List.singleton_append, ←R, List.idxOf_cons_ne _ H_neq_R.symm,
      List.singleton_append, H, List.idxOf_cons_self, ←first_R
  ] at first_H
  rw [List.length_append, List.length_append, List.length_append, List.length_singleton,
      ←add_zero ((w.flatten.map Symbol.terminal).length + (β.map Symbol.terminal).length + 1)
  ] at first_H
  simpa using first_H

private lemma case_3_v_nil {g : Grammar T} {w : List (List T)} {β : List T} {u v : List (ns T g.nt)}
    (ass : w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ [H] = u ++ [R] ++ [H]
      ++ v) :
  v = [] :=
by
  have rev := congr_arg List.reverse ass
  simp only [List.reverse_append, List.reverse_singleton] at rev
  rw [←List.reverse_nil]
  cases hv : v.reverse with
  | nil => exact List.reverse_eq_iff.→ hv
  | cons d l =>
    exfalso
    rw [hv, List.singleton_append] at rev
    have brt := List.tail_eq_of_cons_eq rev
    have brtt := congr_arg List.tail brt
    rw [List.singleton_append] at brtt
    rw [List.tail_cons] at brtt
    cases hl : l with
    | nil =>
      rw [hl] at brtt
      change (β.map Symbol.terminal).reverse ++ (w.flatten.map Symbol.terminal).reverse = [R]
        ++ u.reverse at brtt
      have imposs := congr_arg (R ∈ ·) brtt
      apply false_of_true_eq_false
      convert imposs.symm
      · rw [true_iff]
        apply List.mem_append_left
        apply List.mem_singleton_self
      · rw [false_iff, List.mem_append]
        push Not
        constructor <;> unfold H at * <;> aesop
    | cons e l' =>
      rw [hl] at brtt
      have imposs := congr_arg (H ∈ ·) brtt
      apply false_of_true_eq_false
      convert imposs.symm
      · rw [true_iff]
        apply List.mem_append_right
        apply List.mem_append_left
        apply List.mem_singleton_self
      · rw [false_iff]
        rw [List.mem_append]
        push Not
        constructor <;> unfold H at * <;> aesop

private lemma case_3_false_of_wbr_eq_urz {g : Grammar T} {r₀ : Grule T g.nt} {w : List (List T)}
    {β : List T} {u z : List (ns T g.nt)}
    (contradictory_equality :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ z) :
  False :=
by
  apply false_of_true_eq_false
  convert congr_arg ((Symbol.nonterminal ◄r₀.inputN ∈ ·)) contradictory_equality.symm
  · rw [true_iff]
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_singleton_self
  · rw [false_iff]
    intro hyp_N_in
    rw [List.mem_append] at hyp_N_in
    cases hyp_N_in with
    | inl hr₀ =>
      rw [List.mem_append] at hr₀
      cases hr₀ with
      | inl hw =>
        rw [List.mem_map] at hw
        rcases hw with ⟨t, -, impos⟩
        simp at impos
      | inr hβ =>
        rw [List.mem_map] at hβ
        rcases hβ with ⟨t, -, impos⟩
        simp at impos
    | inr hR =>
      rw [List.mem_singleton] at hR
      simp [R] at hR

private lemma case_3_le_u_len {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {v' : List (ns T g.nt)}
    (v'_from_left :
      (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ (γ.map wrapSym
        ++ [H])).drop u.length = v')
    (right_half :
      r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v =
        v' ++ ((x.map (List.map wrapSym)).map fun x ↦ x ++ [H]).flatten) :
  (w.flatten.map (@Symbol.terminal T (nn g.nt)) ++
      β.map (@Symbol.terminal T (nn g.nt)) ++ [@R T g.nt]).length ≤ u.length :=
by
  have very_middle : [@Symbol.nonterminal T _ ◄r₀.inputN] = List.map wrapSym
    [Symbol.nonterminal r₀.inputN] := by
    apply List.map_singleton
  by_contra! contr
  have contr' : u.length ≤ (w.flatten.map (@Symbol.terminal T (nn g.nt)) ++
      β.map (@Symbol.terminal T (nn g.nt))).length := by
    simp only [List.length_append] at contr ⊢
    rw [List.length_singleton] at contr
    exact Nat.le_of_lt_succ contr
  rw [List.append_assoc _ [R], List.drop_append_of_le_length contr'] at v'_from_left
  rw [←v'_from_left] at right_half
  have right_half' :
    r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v =
    ((w.flatten.map Symbol.terminal ++ β.map Symbol.terminal).drop u.length ++ [R])
      ++ ((γ.map wrapSym ++ [H]) ++
      ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) := by
    convert right_half using 1
    simp
  rw [List.append_eq_append_iff] at right_half'
  cases right_half' with
  | inl has =>
    have r₀Nin : Symbol.nonterminal ◄r₀.inputN ∈
      (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal).drop u.length ++ [R] := by
      obtain ⟨_, _, -⟩ := has
      aesop
    rw [List.mem_append] at r₀Nin
    cases r₀Nin with
    | inl among_terminals =>
      rw [←List.map_append, ←List.map_drop, List.mem_map] at among_terminals
      obtain ⟨t, -, ht⟩ := among_terminals
      simp at ht
    | inr hR =>
      rw [List.mem_singleton] at hR
      simp [R] at hR
  | inr hbs =>
    have Rin : R ∈ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map
      wrapSym := by
      obtain ⟨_, _, -⟩ := hbs
      simp_all
    rw [very_middle, ←List.map_append_append] at Rin
    exact map_wrap_never_contains_R Rin

private lemma case_3_lt_v'len {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} {w : List (List T)} {β : List T}
    {γ : List (Symbol T g.nt)} {v' : List (ns T g.nt)}
    (v'_empty : ¬v' = [])
    (left_half :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ (γ.map wrapSym ++ [H])
        = u ++ v')
    (right_half :
      r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v =
        v' ++ ((x.map (List.map wrapSym)).map fun x ↦ x ++ [H]).flatten) :
  (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym).length
    < v'.length :=
by
  have very_middle : [@Symbol.nonterminal T _ ◄r₀.inputN] = List.map wrapSym
    [Symbol.nonterminal r₀.inputN] := by
    apply List.map_singleton
  cases hv' : v'.reverse with
  | nil =>
    exfalso
    rw [List.reverse_eq_nil_iff] at hv'
    exact v'_empty hv'
  | cons vₗ vᵣ =>
    have hvₗ : vₗ = H := by
      have left_half_rev := congr_arg List.reverse left_half
      simp [hv'] at left_half_rev
      exact left_half_rev.left.symm
    rw [hvₗ] at hv'
    rw [very_middle, ←List.map_append_append] at right_half ⊢
    have right_middle := congr_arg
      (List.take
      ((r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).map wrapSym).length)
      right_half
    rw [List.take_left, List.take_append'] at right_middle
    by_contra! contr
    rw [List.take_of_length_le contr] at right_middle
    have Hin : H ∈ (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).map wrapSym
      := by
      rw [right_middle]
      apply List.mem_append_left
      rw [←List.mem_reverse, hv']
      apply List.mem_cons_self
    exact map_wrap_never_contains_H Hin

private lemma case_3_match_rule {g : Grammar T} {r₀ : Grule T g.nt}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)} {w : List (List T)} {β : List T}
      {γ : List (Symbol T g.nt)}
    (hyp :
      w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        ((x.map (List.map wrapSym)).map (· ++ [H])).flatten =
      u ++ r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym ++ v) :
  (∃ m : ℕ, ∃ u₁ v₁ : List (Symbol T g.nt),
    u = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
        (((x.map (List.map wrapSym)).take m).map (· ++ [H])).flatten ++ u₁.map wrapSym ∧
    x[m]? = some (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁) ∧
    v = v₁.map wrapSym ++ [H] ++ (((x.map (List.map wrapSym)).drop m.succ).map (· ++ [H])).flatten)
      ∨
  (∃ u₁ v₁ : List (Symbol T g.nt),
    u = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ u₁.map wrapSym ∧
    γ = u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁ ∧
    v = v₁.map wrapSym ++ [H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :=
by
  repeat rw [List.append_assoc u] at hyp
  rw [List.append_eq_append_iff] at hyp
  cases hyp with
  | inl hypl =>
    rcases hypl with ⟨u', u_eq, xj_eq⟩
    left
    repeat rw [←List.append_assoc] at xj_eq
    by_cases is_x_nil : x = []
    · exfalso
      rw [is_x_nil, List.map_nil, List.map_nil, List.flatten] at xj_eq
      have imposs := congr_arg List.length xj_eq
      rw [List.length, List.length_append, List.length_append, List.length_append,
           List.length_append, List.length_singleton] at imposs
      clear * - imposs
      linarith
    rcases cases_1_and_2_and_3a_match_aux is_x_nil xj_eq with ⟨m, u₁, v₁, u'_eq, xm_eq, v_eq⟩
    use m, u₁, v₁
    constructor
    · rw [u_eq, u'_eq, ←List.append_assoc]
    constructor
    · exact xm_eq
    · exact v_eq
  | inr hypr =>
    rcases hypr with ⟨v', left_half, right_half⟩
    have very_middle : [@Symbol.nonterminal T _ ◄r₀.inputN] = List.map wrapSym
      [Symbol.nonterminal r₀.inputN] := by
      apply List.map_singleton
    rw [List.append_assoc _ (γ.map wrapSym)] at left_half
    have v'_from_left := congr_arg (List.drop u.length) left_half
    simp only [List.drop_left'] at v'_from_left
    have le_u_len := case_3_le_u_len v'_from_left right_half
    have v'_is_suffix : v' = (γ.map wrapSym ++ [H]).drop
        (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)
          := by
      rw [←v'_from_left, List.drop_append']
      convert List.nil_append _
      exact List.drop_of_length_le le_u_len
    have same_r_input_lengths : (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length =
        (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map wrapSym).length
          := by
      simp
    if v'_empty : v' = [] then
      rw [v'_empty, List.nil_append] at right_half
      rw [v'_empty, List.append_nil] at left_half
      left
      cases x with
      | nil => simp_all
      | cons x₀ X =>
        use 0, [], x₀.drop (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length
        constructor
        · rw [List.map_nil, List.append_nil, List.take_zero, List.map_nil, List.flatten,
               List.append_nil, ←left_half, ←List.append_assoc]
        have len_r₀_le_len_x₀ : (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length ≤
          (x₀.map wrapSym).length := by
          classical
          have first_H := congr_arg (List.idxOf H) right_half
          rw [List.idxOf_append_of_notMem, List.map_cons, List.map_cons,
            List.flatten_cons] at first_H
          rotate_left
          · exact H_not_in_rule_input
          conv_rhs at first_H => rw [List.append_assoc]
          rw [List.idxOf_append_of_notMem] at first_H
          rotate_left
          · exact map_wrap_never_contains_H
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
            List.length_map, List.length_cons, List.map_map, List.idxOf_cons_self, add_zero,
            ge_iff_le] at first_H ⊢
          exact Nat.le.intro first_H
        constructor
        · simp only [List.getElem?_cons_zero, Option.some.injEq]
          convert_to x₀ =
              x₀.take (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length ++
              x₀.drop (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length
          · rw [List.nil_append]
            congr
            rw [List.map_cons, List.map_cons, List.flatten_cons, very_middle,
                 ←List.map_append_append, List.append_assoc _ [H]] at right_half
            have taken := congr_arg
              (List.take
              ((r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).map wrapSym).length)
              right_half
            rw [List.take_left,
                 List.take_append_of_le_length (by rw [List.length_map]; exact len_r₀_le_len_x₀)]
                   at taken
            apply map_wrapSym_inj
            rw [taken]
            simp
          symm
          apply List.take_append_drop
        · rw [List.map_cons, List.drop_one, List.tail_cons]
          have dropped := congr_arg
            (List.drop (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length) right_half
          conv_lhs at dropped => rw [same_r_input_lengths, List.drop_left]
          conv_rhs at dropped => rw [List.map_cons, List.map_cons, List.flatten_cons]
          rw [dropped, List.append_assoc _ [H], List.append_assoc _ [H],
               List.drop_append_of_le_length len_r₀_le_len_x₀, List.map_drop]
    else
      have lt_v'len := case_3_lt_v'len v'_empty left_half right_half
      have v'_nonempty : 0 < v'.length := List.length_pos_iff.← v'_empty
      have v'_eq : v' = (γ.map wrapSym).drop
        (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)
        ++ [H] := by
        rw [v'_is_suffix, List.drop_append_of_le_length]
        have left_lengths := congr_arg List.length left_half
        simp only [List.length_append, List.length_singleton] at left_lengths ⊢
        omega
      right
      use
        (γ.take
        (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length))
      use
        (γ.drop
        (u.length
        - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [@R T g.nt]).length)).drop
            (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map
              wrapSym).length
      constructor
      · have left_part := congr_arg (List.take u.length) left_half
        rw [List.take_left, List.take_append', List.take_of_length_le le_u_len] at left_part
        conv_lhs => rw [←left_part]
        rw [List.map_take, List.take_append_of_le_length]
        have left_part := congr_arg (List.length) left_half
        conv_lhs at left_part => rw [List.length_append]; congr; rfl; rw
          [List.length_append, List.length_singleton]
        conv_rhs at left_part => rw [List.length_append]
        omega
      constructor
      · convert_to γ =
          γ.take (u.length - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R]).length)
            ++
            (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR) ++
            (γ.drop
              (u.length
              - (w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R]).length)).drop
                  (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map
                    wrapSym).length
        · simp only [List.append_assoc]
          rfl
        have core :
          r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR =
          (γ.drop (u.length - (w.flatten.map (@Symbol.terminal T (nn g.nt)) ++
              β.map (@Symbol.terminal T (nn g.nt)) ++ [R]).length)).take
            (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length := by
          have right_middle := congr_arg
            (List.take (r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR).length) right_half
          rw [same_r_input_lengths,
              List.take_left,
              List.take_append_of_le_length lt_v'len.le,
              very_middle,
              ←List.map_append_append,
              v'_eq,
              List.take_append_of_le_length (by
                have v'_lengths := congr_arg List.length v'_eq
                simp at lt_v'len v'_lengths ⊢
                omega),
              ←List.map_drop,
              ←List.map_take,
          ] at right_middle
          simp_rw [List.length_map] at right_middle
          exact map_wrapSym_inj right_middle
        nth_rw 1 [core]
        rw [List.append_assoc, same_r_input_lengths, List.take_append_drop, List.take_append_drop]
      · rw [v'_is_suffix] at right_half
        have right_part := congr_arg
          (List.drop
          (r₀.inputL.map wrapSym ++ [Symbol.nonterminal ◄r₀.inputN] ++ r₀.inputR.map
          wrapSym).length) right_half
        rw [List.drop_left] at right_part
        rw [List.map_drop, List.map_drop]
        rwa [List.drop_append_of_le_length, List.drop_append_of_le_length,
              List.drop_append_of_le_length] at right_part
        · have v'_lengths := congr_arg List.length v'_eq
          simp at lt_v'len v'_lengths ⊢
          omega
        · have left_lengths := congr_arg List.length left_half
          simp only [List.length_append, List.length_singleton] at left_lengths ⊢
          omega
        · exact le_of_le_of_eq lt_v'len.le (congr_arg List.length v'_is_suffix)

private lemma case_3_no_Z {g : Grammar T} {α : List (ns T g.nt)}
    {w : List (List T)} {β : List T} {γ : List (Symbol T g.nt)}
    {x : List (List (Symbol T g.nt))}
    (cat : α = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H]
      ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  Z ∉ α :=
by
  intro contr
  rw [cat] at contr
  clear * - contr
  simp only [List.mem_append] at contr
  rcases contr with ((((hZw | hZβ) | hZR) | hZγ) | hZH) | hZx
  · rw [List.mem_map] at hZw
    obtain ⟨s, -, imposs⟩ := hZw
    simp [Z] at imposs
  · rw [List.mem_map] at hZβ
    obtain ⟨s, -, imposs⟩ := hZβ
    simp [Z] at imposs
  · rw [List.mem_singleton] at hZR
    exact Z_neq_R hZR
  · rw [List.mem_map] at hZγ
    obtain ⟨s, -, imposs⟩ := hZγ
    exact wrap_never_outputs_Z imposs
  · rw [List.mem_singleton] at hZH
    exact Z_neq_H hZH
  · exact Z_not_in_join_mpHmmw hZx

private lemma case_3_head_step {g : Grammar T} {α α' : List (ns T g.nt)}
    {w : List (List T)} {β : List T} {γ : List (Symbol T g.nt)}
    {x : List (List (Symbol T g.nt))} {u v : List (ns T g.nt)}
    (valid_w : ∀ wᵢ ∈ w, wᵢ ∈ g.language)
    (valid_middle : g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ))
    (cat : α = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H]
      ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten)
    (bef : α = u ++ [@R T g.nt] ++ [H] ++ v)
    (aft : α' = u ++ v) :
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
         ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α' = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rw [cat] at bef
  have gamma_nil_here := case_3_gamma_nil bef
  rw [←List.reverse_reverse x] at *
  rcases hx : x.reverse with _ | ⟨xₘ, L⟩
  · right; left
    rw [gamma_nil_here, List.map_nil, List.append_nil] at bef
    rw [hx, List.reverse_nil, List.map_nil, List.map_nil, List.flatten,
         List.append_nil] at bef
    have v_nil := case_3_v_nil bef
    rw [v_nil, List.append_nil] at bef aft
    use List.flatten w ++ β
    constructor
    · use w ++ [β]
      constructor
      · rw [List.flatten_append]
        rw [List.flatten_singleton]
      · intro y y_in
        rw [List.mem_append] at y_in
        aesop
    · rw [List.append_cancel_right_eq, R, List.append_cancel_right_eq] at bef
      rw [aft, ←bef, List.map_append]
  · right; right; right
    rw [hx, List.reverse_cons] at bef
    rw [aft]
    have Z_ni_wb : Z ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal
      := case_3_ni_wb
    have R_ni_wb : R ∉ w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal
      := case_3_ni_wb
    have u_eq : u = w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map Symbol.terminal :=
      case_3_u_eq_left_side bef
    have v_eq : v = (((L.reverse ++ [xₘ]).map (List.map wrapSym)).map (· ++ [H])).flatten
      := by
      rw [u_eq, gamma_nil_here, List.map_nil, List.append_nil] at bef
      exact List.append_cancel_left bef.symm
    rw [u_eq, v_eq]
    constructor
    · use w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++
            ((L.reverse.map (List.map wrapSym)).map (· ++ [H])).flatten ++
            xₘ.map wrapSym
      rw [List.map_append, List.map_append, List.flatten_append, List.map_singleton,
          List.map_singleton, List.flatten_singleton, ←List.append_assoc,
            ←List.append_assoc]
    constructor
    · rw [List.mem_append]
      exact (·.casesOn Z_ni_wb Z_not_in_join_mpHmmw)
    · rw [List.mem_append]
      exact (·.casesOn R_ni_wb R_not_in_join_mpHmmw)

private lemma star_case_3 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp :
      ∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List
        (List (Symbol T g.nt)),
        (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
        g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
        (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
        α = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
            ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) :
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α' = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H] ++
         ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α' = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rcases hyp with ⟨w, β, γ, x, valid_w, valid_middle, valid_x, cat⟩
  have no_Z_in_alpha : Z ∉ α := case_3_no_Z cat
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  cases rin with
  | head =>
    exfalso
    apply no_Z_in_alpha
    rw [bef]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    rewrite [List.mem_singleton]
    rfl
  | tail _ rin' =>
    cases rin' with
    | head =>
      exfalso
      apply no_Z_in_alpha
      rw [bef]
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      rewrite [List.mem_singleton]
      rfl
    | tail _ rin =>
      cases rin with
      | head =>
        dsimp only at bef aft
        rw [List.append_nil, cat] at bef
        have gamma_nil_here := case_3_gamma_nil bef
        cases x with
        | nil =>
          right; right; left
          rw [gamma_nil_here, List.map_nil, List.append_nil] at bef
          rw [List.map_nil, List.map_nil, List.flatten, List.append_nil] at bef
          have v_nil := case_3_v_nil bef
          rw [v_nil, List.append_nil] at bef aft
          use w.flatten.map Symbol.terminal ++ β.map Symbol.terminal
          rw [List.append_cancel_right_eq, R, List.append_cancel_right_eq] at bef
          rewrite [aft, ←bef, List.map_append, List.map_map, List.map_map]
          rfl
        | cons x₀ L =>
          left
          use w ++ [β], [], x₀, L
          constructor
          · intro wᵢ wiin
            rw [List.mem_append] at wiin
            exact wiin.casesOn (valid_w wᵢ) (by aesop)
          constructor
          · rw [gamma_nil_here] at valid_middle
            apply valid_x
            rw [List.map_nil, List.nil_append]
            exact List.mem_cons_self
          constructor
          · intro xᵢ xiin
            exact valid_x xᵢ (List.mem_cons_of_mem x₀ xiin)
          rw [aft]
          have u_eq : u = w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map
            (@Symbol.terminal T (nn g.nt)) := case_3_u_eq_left_side bef
          have v_eq : v = (((x₀::L).map (List.map wrapSym)).map (· ++ [H])).flatten := by
            rw [u_eq, gamma_nil_here, List.map_nil, List.append_nil] at bef
            exact List.append_cancel_left bef.symm
          rw [u_eq, v_eq]
          simp
      | tail _ rin' =>
        cases rin' with
        | head =>
          dsimp only at bef aft
          rw [List.append_nil] at bef aft
          exact case_3_head_step valid_w valid_middle cat bef aft
        | tail _ rin =>
          have rin' : r ∈ rulesThatScanTerminals g ∨ r ∈ g.rules.map wrapGr := by
            rwa [or_comm, ←List.mem_append]
          clear rin
          cases rin' with
          | inl hrg =>
            left
            unfold rulesThatScanTerminals at hrg
            rw [List.mem_map] at hrg
            rcases hrg with ⟨t, -, r_is⟩
            rw [←r_is] at bef aft
            dsimp only at bef aft
            rw [List.append_nil, cat] at bef
            have u_matches : u = w.flatten.map (@Symbol.terminal T (nn g.nt)) ++ β.map
              Symbol.terminal :=
              case_3_u_eq_left_side bef
            have tv_matches : [Symbol.terminal t] ++ v = γ.map wrapSym ++ [H]
              ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten := by
              rw [u_matches] at bef
              repeat rw [List.append_assoc] at bef
              rw [List.append_cancel_left_eq, List.append_cancel_left_eq, R,
                   List.append_cancel_left_eq, ←List.append_assoc] at bef
              exact bef.symm
            rcases γ with _ | ⟨a, δ⟩
            · exfalso
              rw [List.map_nil, List.nil_append, List.singleton_append,
                   List.singleton_append] at tv_matches
              have t_matches := List.head_eq_of_cons_eq tv_matches
              simp [H] at t_matches
            rw [List.singleton_append, List.map_cons, List.cons_append,
                 List.cons_append] at tv_matches
            use w, β ++ [t], δ, x, valid_w
            constructor
            · have t_matches' := List.head_eq_of_cons_eq tv_matches
              cases a <;> unfold wrapSym at t_matches'
              · have t_eq_a := Symbol.terminal.inj t_matches'
                rw [t_eq_a, List.map_append, List.map_singleton, List.append_assoc,
                     List.singleton_append]
                exact valid_middle
              · exfalso
                simp [liftSymbol] at t_matches'
            constructor
            · exact valid_x
            rw [aft, u_matches, List.map_append, List.map_singleton]
            have v_matches := List.tail_eq_of_cons_eq tv_matches
            simp [v_matches, List.append_assoc]
          | inr hrg =>
            left
            rw [List.mem_map] at hrg
            rcases hrg with ⟨r₀, orig_in, wrap_orig⟩
            unfold wrapGr at wrap_orig
            rw [cat, ←wrap_orig] at bef
            cases case_3_match_rule bef with
            | inl huv =>
              rcases huv with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩
              clear bef
              rw [u_eq, v_eq] at aft
              use w, β, γ, x.take m ++ [u₁ ++ r₀.output ++ v₁] ++ x.drop m.succ
              constructor
              · exact valid_w
              constructor
              · exact valid_middle
              constructor
              · intro xᵢ xiin
                rw [List.mem_append_append] at xiin
                cases xiin with
                | inl =>
                  apply valid_x
                  apply List.mem_of_mem_take
                  assumption
                | inr hxᵢ =>
                  cases hxᵢ with
                  | inl xiin =>
                    rw [List.mem_singleton] at xiin
                    rw [xiin]
                    have last_step :
                      g.Transforms
                        (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                        (u₁ ++ r₀.output ++ v₁) := by
                      use r₀, orig_in, u₁, v₁
                    apply gr_deri_of_deri_tran _ last_step
                    apply valid_x
                      (u₁ ++ r₀.inputL ++ [Symbol.nonterminal r₀.inputN] ++ r₀.inputR ++ v₁)
                    exact List.mem_of_getElem? xm_eq
                  | inr =>
                    apply valid_x
                    apply List.mem_of_mem_drop
                    assumption
              · rw [aft]
                simp [←wrap_orig]
                rfl
            | inr huv =>
              rcases huv with ⟨u₁, v₁, u_eq, γ_eq, v_eq⟩
              clear bef
              rw [u_eq, v_eq] at aft
              use w, β, u₁ ++ r₀.output ++ v₁, x, valid_w
              constructor
              · apply gr_deri_of_deri_tran valid_middle
                rw [γ_eq]
                use r₀, orig_in, β.map Symbol.terminal ++ u₁, v₁
                constructor
                repeat rw [←List.append_assoc]
              constructor
              · exact valid_x
              · rw [aft]
                simp [←wrap_orig]
                rfl

private lemma star_case_4 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp : ∃ u : List T, u ∈ KStar.kstar g.language ∧ α = u.map Symbol.terminal) :
  False :=
by
  rcases hyp with ⟨w, -, alpha_of_w⟩
  rw [alpha_of_w] at orig
  rcases orig with ⟨r, -, _, _, bef, -⟩
  simpa using congr_arg (Symbol.nonterminal r.inputN ∈ ·) bef

private lemma case_5_inl_hrg {g : Grammar T} {α' : List (ns T g.nt)}
    {w : List (Symbol T g.nt)} {r : Grule T g.star.nt} {u v : List (ns T g.nt)}
    {r₀ : Grule T g.nt}
    (bef : w.map wrapSym ++ [R] = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : α' = u ++ r.output ++ v)
    (r_of_r₀ : wrapGr r₀ = r) :
  ∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R] :=
by
  rw [List.append_eq_append_iff] at bef
  cases bef with
  | inl has =>
    rcases has with ⟨x, ur_eq, singleR⟩
    by_cases is_x_nil : x = []
    · have v_is_R : v = [R] := by
        rw [is_x_nil, List.nil_append] at singleR
        exact singleR.symm
      rw [v_is_R] at aft
      rw [is_x_nil, List.append_nil] at ur_eq
      have u_from_w : u = (w.map wrapSym).take u.length := by
        repeat rw [List.append_assoc] at ur_eq
        have tak := congr_arg (List.take u.length) ur_eq
        rw [List.take_left] at tak
        exact tak
      rw [←List.map_take] at u_from_w
      rw [u_from_w] at aft
      rw [←r_of_r₀] at aft
      dsimp only [wrapGr] at aft
      use w.take u.length ++ r₀.output
      rw [List.map_append]
      exact aft
    · exfalso
      have x_is_R : x = [R] := by
        by_cases is_v_nil : v = []
        · rw [is_v_nil, List.append_nil] at singleR
          exact singleR.symm
        · exfalso
          have imposs := congr_arg List.length singleR
          rw [List.length_singleton] at imposs
          rw [List.length_append] at imposs
          have xl_ge_one := length_ge_one_of_not_nil is_x_nil
          have vl_ge_one := length_ge_one_of_not_nil is_v_nil
          clear * - imposs xl_ge_one vl_ge_one
          linarith
      rw [x_is_R] at ur_eq
      have ru_eq := congr_arg List.reverse ur_eq
      repeat rw [List.reverse_append] at ru_eq
      repeat
        rw [List.reverse_singleton] at ru_eq
        rw [List.singleton_append] at ru_eq
      rw [←r_of_r₀] at ru_eq
      dsimp only [wrapGr, liftRule, liftString, R] at ru_eq
      rw [←List.map_reverse] at ru_eq
      cases hr₀ : r₀.inputR.reverse with
      | nil =>
        rw [hr₀, List.map_nil, List.nil_append] at ru_eq
        have imposs := List.head_eq_of_cons_eq ru_eq
        simp at imposs
      | cons d l =>
        rw [hr₀] at ru_eq
        have imposs := List.head_eq_of_cons_eq ru_eq
        cases d <;> simp [liftSymbol] at imposs
  | inr hbs =>
    rcases hbs with ⟨y, w_eq, v_eq⟩
    have u_from_w : u = (w.map wrapSym).take u.length := by
      repeat rw [List.append_assoc] at w_eq
      have tak := congr_arg (List.take u.length) w_eq
      rw [List.take_left] at tak
      exact tak.symm
    have y_from_w : y = (w.map wrapSym).drop
      (u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR).length := by
      have drp := congr_arg
        (List.drop (u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR).length)
        w_eq
      rw [List.drop_left] at drp
      exact drp.symm
    rw [u_from_w] at aft
    rw [y_from_w] at v_eq
    rw [v_eq] at aft
    use w.take u.length ++ r₀.output ++ w.drop
      (u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR).length
    rw [aft, ←r_of_r₀]
    simp [wrapGr]
    rfl

private lemma star_case_5 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp : ∃ σ : List (Symbol T g.nt), α = σ.map wrapSym ++ [R]) :
  ∃ σ : List (Symbol T g.nt), α' = σ.map wrapSym ++ [R] :=
by
  rcases hyp with ⟨w, ends_with_R⟩
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  rw [ends_with_R] at bef
  clear ends_with_R
  cases rin with
  | head =>
    exfalso
    simp only [List.append_nil] at bef
    have imposs := congr_arg (Z ∈ ·) bef
    simp only [List.mem_append] at imposs
    rw [List.mem_singleton] at imposs
    rw [List.mem_singleton] at imposs
    apply false_of_true_eq_false
    convert imposs.symm
    · simp [Z]
    · rw [false_iff]
      push Not
      constructor
      · apply map_wrap_never_contains_Z
      · exact Z_neq_R
  | tail _ rin' =>
    cases rin' with
    | head =>
      exfalso
      simp only [List.append_nil] at bef
      have imposs := congr_arg (Z ∈ ·) bef
      simp only [List.mem_append] at imposs
      rw [List.mem_singleton] at imposs
      rw [List.mem_singleton] at imposs
      apply false_of_true_eq_false
      convert imposs.symm
      · simp [Z]
      · rw [false_iff]
        push Not
        constructor
        · apply map_wrap_never_contains_Z
        · exact Z_neq_R
    | tail _ rin =>
      cases rin with
      | head =>
        exfalso
        dsimp only at bef
        rw [List.append_nil] at bef
        have rev := congr_arg List.reverse bef
        repeat rw [List.reverse_append] at rev
        repeat rw [List.reverse_singleton] at rev
        rw [List.singleton_append] at rev
        cases hv : v.reverse with
        | nil =>
          rw [hv, List.nil_append, List.singleton_append] at rev
          have tails := List.tail_eq_of_cons_eq rev
          rw [←List.map_reverse] at tails
          cases hw : w.reverse with
          | nil =>
            rw [hw, List.map_nil] at tails
            have imposs := congr_arg List.length tails
            rw [List.length, List.length_append, List.length_singleton] at imposs
            clear * - imposs
            linarith
          | cons d' l' =>
            rw [hw, List.map_cons, List.singleton_append] at tails
            have heads := List.head_eq_of_cons_eq tails
            exact wrap_never_outputs_R heads
        | cons d l =>
          rw [hv] at rev
          have tails := List.tail_eq_of_cons_eq rev
          have H_in_tails := congr_arg (H ∈ ·) tails
          rw [List.mem_reverse] at H_in_tails
          apply false_of_true_eq_false
          convert H_in_tails.symm
          · rw [true_iff]
            apply List.mem_append_right
            apply List.mem_append_left
            apply List.mem_singleton_self
          · rw [false_iff]
            intro hyp_H_in
            exact map_wrap_never_contains_H hyp_H_in
      | tail _ rin' =>
        cases rin' with
        | head =>
          exfalso
          dsimp only at bef
          rw [List.append_nil] at bef
          have rev := congr_arg List.reverse bef
          repeat rw [List.reverse_append] at rev
          repeat rw [List.reverse_singleton] at rev
          rw [List.singleton_append] at rev
          cases hv : v.reverse with
          | nil =>
            rw [hv, List.nil_append, List.singleton_append] at rev
            have tails := List.tail_eq_of_cons_eq rev
            rw [←List.map_reverse] at tails
            cases hw : w.reverse with
            | nil =>
              rw [hw, List.map_nil] at tails
              have imposs := congr_arg List.length tails
              rw [List.length, List.length_append, List.length_singleton] at imposs
              clear * - imposs
              linarith
            | cons d' l' =>
              rw [hw, List.map_cons, List.singleton_append] at tails
              have heads := List.head_eq_of_cons_eq tails
              exact wrap_never_outputs_R heads
          | cons d l =>
            rw [hv] at rev
            have tails := List.tail_eq_of_cons_eq rev
            have H_in_tails := congr_arg (H ∈ ·) tails
            rw [List.mem_reverse] at H_in_tails
            apply false_of_true_eq_false
            convert H_in_tails.symm
            · rw [true_iff]
              apply List.mem_append_right
              apply List.mem_append_left
              apply List.mem_singleton_self
            · rw [false_iff]
              intro hyp_H_in
              exact map_wrap_never_contains_H hyp_H_in
        | tail _ rin =>
          change r ∈ g.rules.map wrapGr ++ rulesThatScanTerminals g at rin
          rw [List.mem_append] at rin
          cases rin with
          | inl hrg =>
            rw [List.mem_map] at hrg
            rcases hrg with ⟨r₀, -, r_of_r₀⟩
            exact case_5_inl_hrg bef aft r_of_r₀
          | inr hrg =>
            exfalso
            unfold rulesThatScanTerminals at hrg
            rw [List.mem_map] at hrg
            rcases hrg with ⟨t, -, eq_r⟩
            rw [←eq_r] at bef
            clear eq_r
            dsimp only at bef
            rw [List.append_nil] at bef
            have rev := congr_arg List.reverse bef
            repeat rw [List.reverse_append] at rev
            repeat rw [List.reverse_singleton] at rev
            rw [List.singleton_append] at rev
            cases hv : v.reverse with
            | nil =>
              rw [hv, List.nil_append, List.singleton_append] at rev
              have tails := List.tail_eq_of_cons_eq rev
              rw [←List.map_reverse] at tails
              cases hw : w.reverse with
              | nil =>
                rw [hw, List.map_nil] at tails
                have imposs := congr_arg List.length tails
                rw [List.length, List.length_append, List.length_singleton] at imposs
                clear * - imposs
                linarith
              | cons d' l' =>
                rw [hw, List.map_cons, List.singleton_append] at tails
                have heads := List.head_eq_of_cons_eq tails
                exact wrap_never_outputs_R heads
            | cons d l =>
              rw [hv] at rev
              have tails := List.tail_eq_of_cons_eq rev
              have R_in_tails := congr_arg (R ∈ ·) tails
              rw [List.mem_reverse] at R_in_tails
              apply false_of_true_eq_false
              convert R_in_tails.symm
              · rw [true_iff]
                apply List.mem_append_right
                apply List.mem_append_right
                apply List.mem_append_left
                apply List.mem_singleton_self
              · rw [false_iff]
                intro hyp_R_in
                exact map_wrap_never_contains_R hyp_R_in

private lemma star_case_6 {g : Grammar T} {α α' : List (ns T g.nt)}
    (orig : g.star.Transforms α α')
    (hyp : (∃ ω : List (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α) :
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α' :=
by
  rcases hyp with ⟨⟨w, ends_with_H⟩, no_Z, no_R⟩
  rcases orig with ⟨r, rin, u, v, bef, aft⟩
  cases rin with
  | head =>
    exfalso
    simp only [List.append_nil] at bef
    rw [bef] at no_Z
    apply no_Z
    apply List.mem_append_left
    apply List.mem_append_right
    apply List.mem_singleton_self
  | tail _ rin' =>
    cases rin' with
    | head =>
      exfalso
      simp only [List.append_nil] at bef
      rw [bef] at no_Z
      apply no_Z
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_singleton_self
    | tail _ rin =>
      cases rin with
      | head =>
        exfalso
        dsimp only at bef
        rw [List.append_nil] at bef
        rw [bef] at no_R
        apply no_R
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_singleton_self
      | tail _ rin' =>
        cases rin' with
        | head =>
          exfalso
          dsimp only at bef
          rw [List.append_nil] at bef
          rw [bef] at no_R
          apply no_R
          apply List.mem_append_left
          apply List.mem_append_left
          apply List.mem_append_right
          apply List.mem_singleton_self
        | tail _ rin =>
          change r ∈ g.rules.map wrapGr ++ rulesThatScanTerminals g at rin
          rw [List.mem_append] at rin
          cases rin with
          | inl hrg =>
            rw [ends_with_H] at bef
            rw [List.mem_map] at hrg
            rcases hrg with ⟨r₀, -, r_of_r₀⟩
            constructor
            · use u ++ r.output ++ v.take (v.length - 1)
              rw [aft]
              have vlnn : v.length ≥ 1 := by
                by_contra contra
                have v_nil := zero_of_not_ge_one contra
                rw [List.length_eq_zero_iff] at v_nil
                rw [v_nil, ←r_of_r₀, List.append_nil] at bef
                unfold wrapGr liftRule liftString at bef
                have rev := congr_arg List.reverse bef
                clear * - rev
                repeat rw [List.reverse_append] at rev
                rw [←List.map_reverse, List.reverse_singleton] at rev
                cases hr₀ : r₀.inputR.reverse with
                | nil =>
                  have H_eq_N : (H : ns T g.nt) = Symbol.nonterminal ◄r₀.inputN := by
                    rw [hr₀] at rev
                    simp at rev
                    exact rev.left
                  unfold H at H_eq_N
                  have inr_eq_inl := Symbol.nonterminal.inj H_eq_N
                  simp at inr_eq_inl
                | cons d l =>
                  rw [hr₀, List.map_cons] at rev
                  have H_is : (H : ns T g.nt) = wrapSym d := by
                    simp at rev
                    exact rev.left
                  unfold H at H_is
                  cases d <;> unfold wrapSym at H_is
                  · simp [liftSymbol] at H_is
                  · simp [liftSymbol] at H_is
              have bef_rev := congr_arg List.reverse bef
              repeat rw [List.reverse_append] at bef_rev
              have bef_rev_tak := congr_arg (List.take 1) bef_rev
              rw [List.take_left' (by rfl)] at bef_rev_tak
              rw [List.take_append_of_le_length (by rwa [List.length_reverse])] at bef_rev_tak
              convert_to u ++ r.output ++ v = u ++ r.output ++ (v.take (v.length - 1) ++ [H])
              · simp
              conv_lhs => rw [←v.take_append_drop (v.length - 1)]
              congr
              have h1 : 1 = v.length - (v.length - 1) := by
                omega
              rw [h1, ←List.reverse_drop] at bef_rev_tak
              apply List.reverse_injective
              exact bef_rev_tak.symm
            · constructor
              · rw [aft]
                intro contra
                rw [List.mem_append, List.mem_append] at contra
                cases contra with
                | inl hZ =>
                  cases hZ with
                  | inl hZu =>
                    apply no_Z
                    rw [ends_with_H]
                    rw [bef]
                    repeat rw [List.append_assoc]
                    rw [List.mem_append]
                    left
                    exact hZu
                  | inr hZr =>
                    rw [←r_of_r₀] at hZr
                    unfold wrapGr liftRule liftString at hZr
                    rw [List.mem_map] at hZr
                    rcases hZr with ⟨s, -, imposs⟩
                    cases s
                    · simp [Z, liftSymbol] at imposs
                    · simp [liftSymbol, Z] at imposs
                | inr hZv =>
                  apply no_Z
                  rw [ends_with_H, bef, List.mem_append]
                  right
                  exact hZv
              · rw [aft]
                intro contra
                rw [List.mem_append] at contra
                rw [List.mem_append] at contra
                cases contra with
                | inl hR =>
                  cases hR with
                  | inl hRu =>
                    apply no_R
                    rw [ends_with_H]
                    rw [bef]
                    repeat rw [List.append_assoc]
                    rw [List.mem_append]
                    left
                    exact hRu
                  | inr hRr =>
                    rw [←r_of_r₀] at hRr
                    unfold wrapGr liftRule liftString at hRr
                    rw [List.mem_map] at hRr
                    rcases hRr with ⟨s, -, imposs⟩
                    cases s
                    · simp [R, liftSymbol] at imposs
                    · simp [liftSymbol, R] at imposs
                | inr hRv =>
                  apply no_R
                  rw [ends_with_H]
                  rw [bef]
                  rw [List.mem_append]
                  right
                  exact hRv
          | inr hrg =>
            exfalso
            unfold rulesThatScanTerminals at hrg
            rw [List.mem_map] at hrg
            rcases hrg with ⟨t, -, eq_r⟩
            rw [←eq_r] at bef
            dsimp only at bef
            rw [List.append_nil] at bef
            rw [bef] at no_R
            apply no_R
            apply List.mem_append_left
            apply List.mem_append_left
            apply List.mem_append_right
            apply List.mem_singleton_self

private lemma star_induction {g : Grammar T} {α : List (ns T g.nt)}
    (ass : g.star.Derives [Z] α) :
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧ α = [Z]
      ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ x : List (List (Symbol T g.nt)),
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α = [R, H] ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (Symbol T g.nt), ∃ x : List (List (Symbol T g.nt)),
    (∀ wᵢ ∈ w, wᵢ ∈ g.language) ∧
    g.Derives [Symbol.nonterminal g.initial] (β.map Symbol.terminal ++ γ) ∧
    (∀ xᵢ ∈ x, g.Derives [Symbol.nonterminal g.initial] xᵢ) ∧
    α = w.flatten.map Symbol.terminal ++ β.map Symbol.terminal ++ [R] ++ γ.map wrapSym ++ [H]
      ++ ((x.map (List.map wrapSym)).map (· ++ [H])).flatten) ∨
  (∃ u : List T, u ∈ KStar.kstar g.language ∧ α = u.map Symbol.terminal) ∨
  (∃ σ : List (Symbol T g.nt), α = σ.map wrapSym ++ [R]) ∨
  (∃ ω : List (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α :=
by
  induction ass with
  | refl =>
      left
      use []
      constructor
      · intro y imposs
        exfalso
        exact List.not_mem_nil imposs
      · rfl
  | tail _ orig ih =>
      rcases ih with ih | ih | ih | ih | ih | ih
      · rw [←or_assoc]
        left
        exact star_case_1 orig ih
      · right
        exact star_case_2 orig ih
      · right; right
        exact star_case_3 orig ih
      · exfalso
        exact star_case_4 orig ih
      · right; right; right; right; left
        exact star_case_5 orig ih
      · right; right; right; right; right
        exact star_case_6 orig ih

end hard_direction


/-- The class of grammar-generated languages is closed under the Kleene star. -/
theorem GG_of_star_GG (L : Language T) :
  Language.IsGG L → Language.IsGG (KStar.kstar L) :=
by
  rintro ⟨g, rfl⟩
  use g.star
  apply Set.eq_of_subset_of_subset
  · -- prove `L.star ⊇` here
    intro w hyp
    have result := star_induction hyp
    clear hyp
    rcases result with result | result | result | result | result | result
    · exfalso
      rcases result with ⟨x, -, contr⟩
      rcases w with _ | ⟨d, l⟩
      · tauto
      rw [List.map_cons] at contr
      have terminal_eq_Z : Symbol.terminal d = Z := List.head_eq_of_cons_eq contr
      simp [Z] at terminal_eq_Z
    · exfalso
      rcases result with ⟨x, -, contr⟩
      rcases w with _ | ⟨d, l⟩
      · tauto
      rw [List.map_cons] at contr
      have terminal_eq_R : Symbol.terminal d = R := List.head_eq_of_cons_eq contr
      simp [R] at terminal_eq_R
    · exfalso
      rcases result with ⟨α, β, γ, x, -, -, -, contr⟩
      have output_contains_R : R ∈ w.map (@Symbol.terminal T g.star.nt) := by
        rw [contr]
        simp only [List.mem_append, List.mem_cons]
        tauto
      rw [List.mem_map] at output_contains_R
      rcases output_contains_R with ⟨t, -, terminal_eq_R⟩
      simp [R] at terminal_eq_R
    · rcases result with ⟨u, win, map_eq_map⟩
      have w_eq_u : w = u := by
        have st_inj : Function.Injective (@Symbol.terminal T g.star.nt) := by
          apply Symbol.terminal.inj
        rw [←List.map_injective_iff] at st_inj
        exact st_inj map_eq_map
      rw [w_eq_u]
      exact win
    · exfalso
      obtain ⟨σ, contr⟩ := result
      have last_symbols := congr_arg (·[0]?) (congr_arg List.reverse contr)
      rw [←List.map_reverse, List.reverse_append, List.reverse_singleton,
           List.singleton_append] at last_symbols
      cases hw0 : w.reverse[0]?
      · simp_all
      · clear * - last_symbols
        unfold R at last_symbols
        cases hw : w.reverse <;> aesop
    · exfalso
      rcases result with ⟨⟨ω, contr⟩, -⟩
      have last_symbols := congr_arg (·[0]?) (congr_arg List.reverse contr)
      rw [←List.map_reverse, List.reverse_append, List.reverse_singleton,
           List.singleton_append] at last_symbols
      cases hw0 : w.reverse[0]?
      · simp_all
      · clear * - last_symbols
        unfold H at last_symbols
        cases hw : w.reverse <;> aesop
  · -- prove `L.star ⊆` here
    intro p ass
    rcases ass with ⟨w, w_join, parts_in_L⟩
    let v := w.reverse
    have v_reverse : v.reverse = w := by
      apply List.reverse_reverse
    rw [←v_reverse] at w_join parts_in_L
    rw [w_join]
    clear w_join p
    obtain ⟨derived, terminated⟩ := short_induction parts_in_L
    apply gr_deri_of_deri_deri derived
    apply gr_deri_of_tran_deri
    · use g.star.rules.get ⟨1, Nat.one_lt_succ_succ _⟩
      constructor
      · apply List.get_mem
      use [], ((v.reverse.map (List.map Symbol.terminal)).map (· ++ [H])).flatten
      constructor
      · rewrite [List.reverse_reverse]
        rfl
      · rfl
    rw [List.nil_append, v_reverse]
    have final_step :
      g.star.Transforms
        (w.flatten.map Symbol.terminal ++ [R, H])
        (w.flatten.map Symbol.terminal) := by
      use g.star.rules.get ⟨3, by simp [Grammar.star]⟩
      constructor
      · apply List.get_mem
      use w.flatten.map Symbol.terminal, []
      constructor
      · aesop
      · have out_nil : (g.star.rules.get ⟨3, by simp [Grammar.star]⟩).output = [] := by
          rfl
        rw [List.append_nil, out_nil, List.append_nil]
    apply gr_deri_of_deri_tran _ final_step
    convert_to
      g.star.Derives
        ([R] ++ ([H] ++ ((w.map (List.map Symbol.terminal)).map (· ++ [H])).flatten))
        (w.flatten.map Symbol.terminal ++ [R, H])
    have rebracket :
      [H] ++ ((w.map (List.map (@Symbol.terminal T (nn g.nt)))).map (· ++ [H])).flatten =
             ((w.map (List.map (@Symbol.terminal T (nn g.nt)))).map ([H] ++ ·)).flatten ++ [H] := by
      apply List.append_flatten_map_append
    rw [rebracket]
    apply terminal_scan_aux
    aesop

end Chomsky
