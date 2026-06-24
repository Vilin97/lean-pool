/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Toolbox
import LeanPool.Chomsky.Utilities.ListUtils
import Mathlib.Tactic.Linarith

/-!
# Concatenation

Closure of general-grammar languages under concatenation.
-/

open scoped Chomsky

namespace Chomsky


section list_technicalities

variable {α β : Type}

lemma list_drop_take_succ {l : List α} {i : ℕ} (hil : i < l.length) :
  (l.take (i + 1)).drop i = [l.get ⟨i, hil⟩] :=
by
  rw [List.drop_take, ←List.take_one_drop_eq_of_lt_length]
  congr
  omega

lemma list_forall₂_get {R : α → β → Prop} :
  ∀ x : List α, ∀ y : List β, List.Forall₂ R x y →
    ∀ i : ℕ, ∀ hix : i < x.length, ∀ hiy : i < y.length,
      R (x.get ⟨i, hix⟩) (y.get ⟨i, hiy⟩)
| [], [] => ↓(Nat.not_lt_zero · · |>.elim)
| [], _::_ => by simp
| _::_, [] => by simp
| _::_, _::_ => by
    intro hR i _ _
    rw [List.forall₂_cons] at hR
    cases i
    · exact hR.left
    unfold List.get
    apply list_forall₂_get
    exact hR.right

lemma list_filterMap_eq_of_map_eq_map_some {f : α → Option β} :
  ∀ x : List α, ∀ y : List β,
    x.map f = y.map Option.some → x.filterMap f = y
| [], [] => ↓rfl
| _::_, [] => by simp
| [], _::_ => by simp
| a::_, _::_ => by
    intro hf
    rw [List.map_cons, List.map_cons] at hf
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none =>
      rw [hfa] at hf
      simp at hf
    | some _ =>
      rw [hfa] at hf
      simp only [List.cons.injEq, Option.some.injEq] at hf ⊢
      exact ⟨hf.left, list_filterMap_eq_of_map_eq_map_some _ _ hf.right⟩

lemma list_length_append_singleton_append (a b d : List α) (c : α) :
    (a ++ b ++ [c] ++ d).length = a.length + b.length + 1 + d.length := by
  repeat rw [List.length_append]
  simp only [List.length_cons, List.length_nil]

end list_technicalities


-- new nonterminal type
/-- The nonterminal type of the concatenation grammar. -/
abbrev nnn (T N₁ N₂ : Type) : Type :=
  Option (N₁ ⊕ N₂) ⊕ (T ⊕ T)

-- new symbol type
/-- The symbol type of the concatenation grammar. -/
abbrev nst (T N₁ N₂ : Type) : Type :=
  Symbol T (nnn T N₁ N₂)

variable {T : Type}

section the_construction

/-- Embed a symbol of the first grammar into the concatenation grammar. -/
def wrapSymbol₁ {N₁ : Type} (N₂ : Type) : Symbol T N₁ → nst T N₁ N₂
  | Symbol.terminal t => Symbol.nonterminal ▶◄t
  | Symbol.nonterminal n => Symbol.nonterminal ◄(some ◄n)

/-- Embed a symbol of the second grammar into the concatenation grammar. -/
def wrapSymbol₂ {N₂ : Type} (N₁ : Type) : Symbol T N₂ → nst T N₁ N₂
  | Symbol.terminal t => Symbol.nonterminal ▶▶t
  | Symbol.nonterminal n => Symbol.nonterminal ◄(some ▶n)

/-- Embed a rule of the first grammar into the concatenation grammar. -/
def wrapGrule₁ {N₁ : Type} (N₂ : Type) (r : Grule T N₁) : Grule T (nnn T N₁ N₂) :=
  Grule.mk
    (r.inputL.map (wrapSymbol₁ N₂))
    ◄(some ◄r.inputN)
    (r.inputR.map (wrapSymbol₁ N₂))
    (r.output.map (wrapSymbol₁ N₂))

/-- Embed a rule of the second grammar into the concatenation grammar. -/
def wrapGrule₂ {N₂ : Type} (N₁ : Type) (r : Grule T N₂) : Grule T (nnn T N₁ N₂) :=
  Grule.mk
    (r.inputL.map (wrapSymbol₂ N₁))
    ◄(some ▶r.inputN)
    (r.inputR.map (wrapSymbol₂ N₁))
    (r.output.map (wrapSymbol₂ N₁))

/-- Terminal-scanning rules for the first grammar. -/
def rulesForTerminals₁ (N₂ : Type) (g : Grammar T) : List (Grule T (nnn T g.nt N₂)) :=
  (allUsedTerminals g).map (fun t : T => Grule.mk [] ▶◄t [] [Symbol.terminal t])

/-- Terminal-scanning rules for the second grammar. -/
def rulesForTerminals₂ (N₁ : Type) (g : Grammar T) : List (Grule T (nnn T N₁ g.nt)) :=
  (allUsedTerminals g).map (fun t : T => Grule.mk [] ▶▶t [] [Symbol.terminal t])


-- grammar for concatenation of `g₁.language` with `g₂.language`
/-- The grammar generating the concatenation of two languages. -/
@[reducible] def bigGrammar (g₁ g₂ : Grammar T) : Grammar T :=
  Grammar.mk (nnn T g₁.nt g₂.nt) ◄none (
    Grule.mk [] ◄none [] [
      Symbol.nonterminal ◄(some ◄g₁.initial),
      Symbol.nonterminal ◄(some ▶g₂.initial)
    ] :: ((
      g₁.rules.map (wrapGrule₁ g₂.nt) ++
      g₂.rules.map (wrapGrule₂ g₁.nt)
    ) ++ (
      rulesForTerminals₁ g₂.nt g₁ ++
      rulesForTerminals₂ g₁.nt g₂)))

@[simp]
lemma bigGrammar_nt {g₁ g₂ : Grammar T} : (bigGrammar g₁ g₂).nt = nnn T g₁.nt g₂.nt :=
  rfl

@[simp]
lemma bigGrammar_initial {g₁ g₂ : Grammar T} : (bigGrammar g₁ g₂).initial = ◄none :=
  rfl

@[simp]
lemma bigGrammar_rules {g₁ g₂ : Grammar T} :
    (bigGrammar g₁ g₂).rules =
      Grule.mk [] ◄none [] [
        Symbol.nonterminal ◄(some ◄g₁.initial),
        Symbol.nonterminal ◄(some ▶g₂.initial)] ::
        ((g₁.rules.map (wrapGrule₁ g₂.nt) ++ g₂.rules.map (wrapGrule₂ g₁.nt)) ++
          (rulesForTerminals₁ g₂.nt g₁ ++ rulesForTerminals₂ g₁.nt g₂)) :=
  rfl

/-- Membership in the rules of `bigGrammar` splits into the five rule families. -/
lemma mem_bigGrammar_rules_iff {g₁ g₂ : Grammar T} (r : Grule T (bigGrammar g₁ g₂).nt) :
    r ∈ (bigGrammar g₁ g₂).rules ↔
      r = Grule.mk [] ◄none [] [
          Symbol.nonterminal ◄(some ◄g₁.initial),
          Symbol.nonterminal ◄(some ▶g₂.initial)] ∨
        r ∈ g₁.rules.map (wrapGrule₁ g₂.nt) ∨
        r ∈ g₂.rules.map (wrapGrule₂ g₁.nt) ∨
        r ∈ rulesForTerminals₁ g₂.nt g₁ ∨
        r ∈ rulesForTerminals₂ g₁.nt g₂ := by
  simp only [List.mem_cons, List.mem_append, or_assoc]

end the_construction


section easy_direction

lemma grammar_generates_only_legit_terminals {g : Grammar T} {w : List (Symbol T g.nt)}
    (hgw : g.Derives [Symbol.nonterminal g.initial] w)
    (s : Symbol T g.nt) (hsw : s ∈ w) :
  (∃ r : Grule T g.nt, r ∈ g.rules ∧ s ∈ r.output) ∨ (s = Symbol.nonterminal g.initial) :=
by
  induction hgw with
  | refl =>
      rw [List.mem_singleton] at hsw
      right
      exact hsw
  | tail _ orig ih =>
      rcases orig with ⟨r, rin, u, v, bef, aft⟩
      rw [aft, List.mem_append, List.mem_append] at hsw
      rcases hsw with (s_in_u | s_in_out) | s_in_v
      · apply ih
        rw [bef]
        repeat
          rw [List.mem_append]
          left
        exact s_in_u
      · left
        use r
      · apply ih
        rw [bef, List.mem_append]
        right
        exact s_in_v

private lemma first_transformation {g₁ g₂ : Grammar T} :
  (bigGrammar g₁ g₂).Transforms
    [Symbol.nonterminal (bigGrammar g₁ g₂).initial]
    [Symbol.nonterminal ◄(some ◄g₁.initial),
     Symbol.nonterminal ◄(some ▶g₂.initial)] :=
by
  use (bigGrammar g₁ g₂).rules.get ⟨0, by simp [bigGrammar]⟩
  constructor
  · simp only [bigGrammar_rules, List.get_eq_getElem, List.getElem_cons_zero]
    exact List.mem_cons_self
  use [], []
  constructor <;> rfl

private lemma substitute_terminals {g₁ g₂ : Grammar T} {s : T → T ⊕ T} {w : List T}
  (rule_for_each_terminal : ∀ t ∈ w,
      Grule.mk [] ▶(s t) [] [Symbol.terminal t] ∈
        rulesForTerminals₁ g₂.nt g₁ ++ rulesForTerminals₂ g₁.nt g₂) :
  (bigGrammar g₁ g₂).Derives
    (w.map (Symbol.nonterminal ∘ Sum.inr ∘ s))
    (w.map Symbol.terminal) :=
by
  induction w with
  | nil =>
      apply gr_deri_self
  | cons d l ih =>
      rw [List.map_cons, List.map_cons, ←List.singleton_append, ←List.singleton_append]
      have step_head :
        (bigGrammar g₁ g₂).Transforms
          ([(Symbol.nonterminal ∘ Sum.inr ∘ s) d] ++ l.map (Symbol.nonterminal ∘ Sum.inr ∘ s))
          ([Symbol.terminal d] ++ l.map (Symbol.nonterminal ∘ Sum.inr ∘ s)) := by
        use Grule.mk [] ▶(s d) [] [Symbol.terminal d]
        constructor
        · change _ ∈ List.cons _ _
          apply List.mem_cons_of_mem
          apply List.mem_append_right
          apply rule_for_each_terminal
          apply List.mem_cons_self
        use [], l.map (Symbol.nonterminal ∘ Sum.inr ∘ s)
        constructor <;> rfl
      apply gr_deri_of_tran_deri step_head
      apply gr_append_deri
      apply ih
      · intro t tin
        apply rule_for_each_terminal t
        exact List.mem_cons_of_mem d tin

lemma in_big_of_in_concatenated {g₁ g₂ : Grammar T} {w : List T}
    (hwgg : w ∈ g₁.language * g₂.language) :
  w ∈ (bigGrammar g₁ g₂).language :=
by
  rw [Language.mem_mul] at hwgg
  rcases hwgg with ⟨u, hu, v, hv, hw⟩
  unfold Grammar.language at *
  change (bigGrammar g₁ g₂).Derives _ _
  apply gr_deri_of_tran_deri first_transformation
  rw [←hw, List.map_append]
  apply
    gr_deri_of_deri_deri
      (g := bigGrammar g₁ g₂)
      (v := u.map Symbol.terminal ++ [Symbol.nonterminal ◄(some ▶g₂.initial)])
  · clear * - hu
    rw [←List.singleton_append]
    apply gr_deri_append
    apply
      gr_deri_of_deri_deri
        (g := bigGrammar g₁ g₂)
        (v := u.map (@Symbol.nonterminal T (bigGrammar g₁ g₂).nt ∘ Sum.inr ∘ Sum.inl))
    · have upgrade_deri₁ :
        ∀ w : List (Symbol T g₁.nt),
          g₁.Derives [Symbol.nonterminal g₁.initial] w →
            (bigGrammar g₁ g₂).Derives
              [Symbol.nonterminal ◄(some ◄g₁.initial)]
              (w.map (wrapSymbol₁ g₂.nt)) := by
        clear * -
        intro w deri₁
        induction deri₁ with
        | refl =>
            apply gr_deri_self
        | tail _ orig ih =>
            apply gr_deri_of_deri_tran ih
            clear * - orig
            rcases orig with ⟨r, rin, u, v, bef, aft⟩
            use wrapGrule₁ g₂.nt r
            constructor
            · dsimp [bigGrammar]
              apply List.mem_cons_of_mem
              apply List.mem_append_left
              apply List.mem_append_left
              rw [List.mem_map]
              use r
            use u.map (wrapSymbol₁ g₂.nt)
            use v.map (wrapSymbol₁ g₂.nt)
            constructor
            · convert congr_arg (List.map (wrapSymbol₁ g₂.nt)) bef
              rewrite [List.map_append_append, List.map_append_append]
              rfl
            · convert congr_arg (List.map (wrapSymbol₁ g₂.nt)) aft
              rewrite [List.map_append_append]
              rfl
      have upgraded := upgrade_deri₁ _ hu
      rw [List.map_map] at upgraded
      exact upgraded
    · have legit_terminals₁ :
        ∀ t ∈ u, ∃ r : Grule T g₁.nt,
          r ∈ g₁.rules ∧ Symbol.terminal t ∈ r.output := by
        intro t tin
        have legit := grammar_generates_only_legit_terminals hu (Symbol.terminal t) (by
          rw [List.mem_map]
          use t)
        rcases legit with possibl | imposs
        · exact possibl
        · exact absurd imposs (by simp)
      apply substitute_terminals
      · intro t tin
        apply List.mem_append_left
        unfold rulesForTerminals₁
        refine List.mem_map.mpr ⟨t, ?_, rfl⟩
        unfold allUsedTerminals
        rw [List.mem_filterMap]
        use Symbol.terminal t
        constructor
        · rw [List.mem_flatten]
          obtain ⟨r, rin, sttin⟩ := legit_terminals₁ t tin
          use r.output
          constructor
          · apply List.mem_map_of_mem
            exact rin
          · exact sttin
        · rfl
  · clear * - hv
    apply gr_append_deri
    apply
      @gr_deri_of_deri_deri _ _ _
        (v.map (@Symbol.nonterminal T (bigGrammar g₁ g₂).nt ∘ Sum.inr ∘ Sum.inr)) _
    · have upgrade_deri₂ :
        ∀ w : List (Symbol T g₂.nt),
          g₂.Derives [Symbol.nonterminal g₂.initial] w →
            (bigGrammar g₁ g₂).Derives
              [Symbol.nonterminal ◄(some ▶g₂.initial)]
              (w.map (wrapSymbol₂ g₁.nt)) := by
        clear * -
        intro w deri₁
        induction deri₁ with
        | refl =>
            apply gr_deri_self
        | tail _ orig ih =>
            apply gr_deri_of_deri_tran ih
            clear * - orig
            rcases orig with ⟨r, rin, u, v, bef, aft⟩
            use wrapGrule₂ g₁.nt r
            constructor
            · change
                wrapGrule₂ g₁.nt r ∈
                  _ :: g₁.rules.map (wrapGrule₁ g₂.nt) ++ g₂.rules.map (wrapGrule₂ g₁.nt) ++ _
              apply List.mem_cons_of_mem
              apply List.mem_append_left
              apply List.mem_append_right
              rw [List.mem_map]
              use r
            use u.map (wrapSymbol₂ g₁.nt)
            use v.map (wrapSymbol₂ g₁.nt)
            constructor
            · convert congr_arg (List.map (wrapSymbol₂ g₁.nt)) bef
              rewrite [List.map_append_append, List.map_append_append]
              rfl
            · convert congr_arg (List.map (wrapSymbol₂ g₁.nt)) aft
              rewrite [List.map_append_append]
              rfl
      have upgraded := upgrade_deri₂ _ hv
      rw [List.map_map] at upgraded
      exact upgraded
    · have legit_terminals₂ :
        ∀ t ∈ v, ∃ r : Grule T g₂.nt,
          r ∈ g₂.rules ∧ Symbol.terminal t ∈ r.output := by
        intro t tin
        have legit := grammar_generates_only_legit_terminals hv (Symbol.terminal t) (by
          rw [List.mem_map]
          use t)
        rcases legit with possibl | imposs
        · exact possibl
        · exact absurd imposs (by simp)
      apply substitute_terminals
      · intro t tin
        apply List.mem_append_right
        unfold rulesForTerminals₂
        refine List.mem_map.mpr ⟨t, ?_, rfl⟩
        unfold allUsedTerminals
        rw [List.mem_filterMap]
        use Symbol.terminal t
        constructor
        · rw [List.mem_flatten]
          obtain ⟨r, rin, sttin⟩ := legit_terminals₂ t tin
          use r.output
          constructor
          · apply List.mem_map_of_mem
            exact rin
          · exact sttin
        · rfl

end easy_direction


section hard_direction

section correspondence_for_terminals

private def correspondingSymbols {N₁ N₂ : Type} : nst T N₁ N₂ → nst T N₁ N₂ → Prop
  | Symbol.terminal t, Symbol.terminal t' => t = t'
  | Symbol.nonterminal ▶◄a, Symbol.nonterminal ▶◄a' => a = a'
  | Symbol.nonterminal ▶▶a, Symbol.nonterminal ▶▶a' => a = a'
  | Symbol.nonterminal ▶◄a, Symbol.terminal t => t = a
  | Symbol.nonterminal ▶▶a, Symbol.terminal t => t = a
  | Symbol.nonterminal ◄(some ◄n), Symbol.nonterminal ◄(some ◄n') => n = n'
  | Symbol.nonterminal ◄(some ▶n), Symbol.nonterminal ◄(some ▶n') => n = n'
  | Symbol.nonterminal ◄none, Symbol.nonterminal ◄none => True
  | _, _ => False

private lemma correspondingSymbols_self {N₁ N₂ : Type} (s : nst T N₁ N₂) :
  correspondingSymbols s s :=
by
  rcases s with _ | ((_ | (_ | _)) | (_ | _)) <;> simp [correspondingSymbols]

private lemma correspondingSymbols_never₁ {N₁ N₂ : Type} {s₁ : Symbol T N₁} {s₂ : Symbol T N₂} :
  ¬ correspondingSymbols (wrapSymbol₁ N₂ s₁) (wrapSymbol₂ N₁ s₂) :=
by
  cases s₁ <;> cases s₂ <;> exact not_false

private lemma correspondingSymbols_never₂ {N₁ N₂ : Type} {s₁ : Symbol T N₁} {s₂ : Symbol T N₂} :
  ¬ correspondingSymbols (wrapSymbol₂ N₁ s₂) (wrapSymbol₁ N₂ s₁) :=
by
  cases s₁ <;> cases s₂ <;> exact not_false

private lemma correspondingSymbols_terminal_of_inl {N₁ N₂ : Type} {s : nst T N₁ N₂} {t : T}
    (hst : correspondingSymbols s (Symbol.nonterminal ▶◄t : nst T N₁ N₂)) :
  correspondingSymbols s (Symbol.terminal t) :=
by
  rcases s with _ | ((_ | (_ | _)) | (_ | _)) <;> simp_all [correspondingSymbols]

private lemma correspondingSymbols_terminal_of_inr {N₁ N₂ : Type} {s : nst T N₁ N₂} {t : T}
    (hst : correspondingSymbols s (Symbol.nonterminal ▶▶t : nst T N₁ N₂)) :
  correspondingSymbols s (Symbol.terminal t) :=
by
  rcases s with _ | ((_ | (_ | _)) | (_ | _)) <;> simp_all [correspondingSymbols]

private def correspondingStrings {N₁ N₂ : Type} : List (nst T N₁ N₂) → List (nst T N₁ N₂) → Prop :=
  List.Forall₂ correspondingSymbols

private lemma correspondingStrings_self {N₁ N₂ : Type} {x : List (nst T N₁ N₂)} :
  correspondingStrings x x :=
List.forall₂_same.← fun s _ => correspondingSymbols_self s

private lemma correspondingStrings_nil {N₁ N₂ : Type} :
  @correspondingStrings T N₁ N₂ [] [] :=
List.Forall₂.nil

private lemma correspondingStrings_cons {N₁ N₂ : Type} {d₁ d₂ : nst T N₁ N₂}
  {l₁ l₂ : List (nst T N₁ N₂)} :
  correspondingStrings (d₁::l₁) (d₂::l₂) ↔ correspondingSymbols d₁ d₂ ∧ correspondingStrings l₁ l₂
    :=
List.forall₂_cons

private lemma correspondingStrings_singleton {N₁ N₂ : Type} {s₁ s₂ : nst T N₁ N₂}
    (hss : correspondingSymbols s₁ s₂) :
  correspondingStrings [s₁] [s₂] :=
correspondingStrings_cons.← ⟨hss, correspondingStrings_nil⟩

private lemma correspondingStrings_append {N₁ N₂ : Type} {x₁ x₂ y₁ y₂ : List (nst T N₁ N₂)}
    (ass₁ : correspondingStrings x₁ y₁) (ass₂ : correspondingStrings x₂ y₂) :
  correspondingStrings (x₁ ++ x₂) (y₁ ++ y₂) :=
by
  unfold correspondingStrings at *
  exact List.rel_append ass₁ ass₂

private lemma correspondingStrings_length {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (hxy : correspondingStrings x y) :
  x.length = y.length :=
by
  unfold correspondingStrings at hxy
  exact List.Forall₂.length_eq hxy

private lemma correspondingStrings_getElem {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)} {i : ℕ}
    (i_lt_len_x : i < x.length) (i_lt_len_y : i < y.length)
    (hxy : correspondingStrings x y) :
  correspondingSymbols (x[i]'i_lt_len_x) (y[i]'i_lt_len_y) :=
by
  apply list_forall₂_get
  exact hxy

private lemma correspondingStrings_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (hxy : correspondingStrings x y) :
  correspondingStrings x.reverse y.reverse :=
by
  unfold correspondingStrings at *
  rwa [List.forall₂_reverse_iff]

private lemma correspondingStrings_of_reverse {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (hxy : correspondingStrings x.reverse y.reverse) :
  correspondingStrings x y :=
by
  unfold correspondingStrings at *
  rwa [List.forall₂_reverse_iff] at hxy

private lemma correspondingStrings_take {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (hxy : correspondingStrings x y) :
  correspondingStrings (x.take n) (y.take n) :=
by
  unfold correspondingStrings at *
  exact List.forall₂_take n hxy

private lemma correspondingStrings_drop {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (hxy : correspondingStrings x y) :
  correspondingStrings (x.drop n) (y.drop n) :=
by
  unfold correspondingStrings at *
  exact List.forall₂_drop n hxy

private lemma correspondingStrings_split {N₁ N₂ : Type} {x y : List (nst T N₁ N₂)}
    (n : ℕ) (hxy : correspondingStrings x y) :
  correspondingStrings (x.take n) (y.take n) ∧
  correspondingStrings (x.drop n) (y.drop n) :=
⟨correspondingStrings_take n hxy, correspondingStrings_drop n hxy⟩

end correspondence_for_terminals


section unwrapping_nst

private def unwrapSymbol₁ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (Symbol T N₁)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal ▶◄a => some (Symbol.terminal a)
  | Symbol.nonterminal ▶▶_ => none
  | Symbol.nonterminal ◄(some ◄n) => some (Symbol.nonterminal n)
  | Symbol.nonterminal ◄(some ▶_) => none
  | Symbol.nonterminal ◄none => none

private def unwrapSymbol₂ {N₁ N₂ : Type} : nst T N₁ N₂ → Option (Symbol T N₂)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal ▶◄_ => none
  | Symbol.nonterminal ▶▶a => some (Symbol.terminal a)
  | Symbol.nonterminal ◄(some ◄_) => none
  | Symbol.nonterminal ◄(some ▶n) => some (Symbol.nonterminal n)
  | Symbol.nonterminal ◄none => none

private lemma unwrap_wrap₁_symbol (N₁ N₂ : Type) :
  @unwrapSymbol₁ T N₁ N₂ ∘ wrapSymbol₁ N₂ = Option.some :=
by
  ext1 a
  cases a <;> rfl

private lemma unwrap_wrap₂_symbol (N₁ N₂ : Type) :
  @unwrapSymbol₂ T N₁ N₂ ∘ wrapSymbol₂ N₁ = Option.some :=
by
  ext1 a
  cases a <;> rfl

private lemma unwrap_wrap₁_string {N₁ : Type} (N₂ : Type) (w : List (Symbol T N₁)) :
  (w.map (wrapSymbol₁ N₂)).filterMap unwrapSymbol₁ = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₁_symbol]
  apply List.filterMap_some

private lemma unwrap_wrap₂_string {N₂ : Type} (N₁ : Type) (w : List (Symbol T N₂)) :
  (w.map (wrapSymbol₂ N₁)).filterMap unwrapSymbol₂ = w :=
by
  rw [List.filterMap_map]
  rw [unwrap_wrap₂_symbol]
  apply List.filterMap_some

private lemma unwrap_eq_some_of_correspondingSymbols₁ {N₁ N₂ : Type} {s₁ : Symbol T N₁}
  {s : nst T N₁ N₂}
    (hNss : correspondingSymbols (wrapSymbol₁ N₂ s₁) s) :
  unwrapSymbol₁ s = some s₁ :=
by
  rcases s₁ with t₁ | n₁
  · rcases s with t | n
    · rw [show t = t₁ from hNss]
      rfl
    · rcases n with o | t
      · rcases o with _ | n'
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
      · rcases t with t' | t''
        · rw [show t₁ = t' from hNss]
          rfl
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
  · rcases s with t | n
    · simp [wrapSymbol₁, correspondingSymbols] at hNss
    · rcases n with o | t
      · rcases o with _ | n'
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
        · rcases n' with n'₁ | n'₂
          · rw [show n₁ = n'₁ from hNss]
            rfl
          · simp [wrapSymbol₁, correspondingSymbols] at hNss
      · rcases t with t' | t''
        · simp [wrapSymbol₁, correspondingSymbols] at hNss
        · simp [wrapSymbol₁, correspondingSymbols] at hNss

private lemma unwrap_eq_some_of_correspondingSymbols₂ {N₁ N₂ : Type} {s₂ : Symbol T N₂}
  {s : nst T N₁ N₂}
    (hNss : correspondingSymbols (wrapSymbol₂ N₁ s₂) s) :
  unwrapSymbol₂ s = some s₂ :=
by
  rcases s₂ with t₂ | n₂
  · rcases s with t | n
    · rw [show t = t₂ from hNss]
      rfl
    · rcases n with o | t
      · rcases o with _ | n'
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
      · rcases t with t' | t''
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · rw [show t₂ = t'' from hNss]
          rfl
  · rcases s with t | n
    · simp [wrapSymbol₂, correspondingSymbols] at hNss
    · rcases n with o | t
      · rcases o with _ | n'
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · rcases n' with n'₁ | n'₂
          · simp [wrapSymbol₂, correspondingSymbols] at hNss
          · rw [show n₂ = n'₂ from hNss]
            rfl
      · rcases t with t' | t''
        · simp [wrapSymbol₂, correspondingSymbols] at hNss
        · simp [wrapSymbol₂, correspondingSymbols] at hNss

private lemma map_unwrap_eq_map_some_of_correspondingStrings₁ {N₁ N₂ : Type} :
  ∀ v : List (Symbol T N₁), ∀ w : List (nst T N₁ N₂),
    correspondingStrings (v.map (wrapSymbol₁ N₂)) w →
      w.map unwrapSymbol₁ = v.map Option.some
  | [], [] => by
      intro
      rw [List.map_nil, List.map_nil]
  | [], b::y => by
      simp [correspondingStrings]
  | a::x, [] => by
      simp [correspondingStrings]
  | a::x, b::y => by
      intro ass
      unfold correspondingStrings at ass
      rw [List.map_cons, List.forall₂_cons] at ass
      rw [List.map, List.map]
      apply congr_arg₂
      · exact unwrap_eq_some_of_correspondingSymbols₁ ass.left
      · apply map_unwrap_eq_map_some_of_correspondingStrings₁
        exact ass.right

private lemma map_unwrap_eq_map_some_of_correspondingStrings₂ {N₁ N₂ : Type} :
  ∀ v : List (Symbol T N₂), ∀ w : List (nst T N₁ N₂),
    correspondingStrings (v.map (wrapSymbol₂ N₁)) w →
      w.map unwrapSymbol₂ = v.map Option.some
  | [], [] => by
      intro
      rw [List.map_nil, List.map_nil]
  | [], b::y => by
      simp [correspondingStrings]
  | a::x, [] => by
      simp [correspondingStrings]
  | a::x, b::y => by
      intro ass
      unfold correspondingStrings at ass
      rw [List.map_cons, List.forall₂_cons] at ass
      rw [List.map, List.map]
      apply congr_arg₂
      · exact unwrap_eq_some_of_correspondingSymbols₂ ass.left
      · apply map_unwrap_eq_map_some_of_correspondingStrings₂
        exact ass.right

private lemma filterMap_unwrap_of_correspondingStrings₁ {N₁ N₂ : Type} {v : List (Symbol T N₁)}
  {w : List (nst T N₁ N₂)}
    (hNvw : correspondingStrings (v.map (wrapSymbol₁ N₂)) w) :
  w.filterMap unwrapSymbol₁ = v :=
by
  apply list_filterMap_eq_of_map_eq_map_some
  apply map_unwrap_eq_map_some_of_correspondingStrings₁
  exact hNvw

private lemma filterMap_unwrap_of_correspondingStrings₂ {N₁ N₂ : Type} {v : List (Symbol T N₂)}
  {w : List (nst T N₁ N₂)}
    (hNvw : correspondingStrings (v.map (wrapSymbol₂ N₁)) w) :
  w.filterMap unwrapSymbol₂ = v :=
by
  apply list_filterMap_eq_of_map_eq_map_some
  apply map_unwrap_eq_map_some_of_correspondingStrings₂
  exact hNvw

private lemma correspondingStrings_after_wrap_unwrap_self₁ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (hNw : ∃ z : List (Symbol T N₁), correspondingStrings (z.map (wrapSymbol₁ N₂)) w) :
  correspondingStrings ((w.filterMap unwrapSymbol₁).map (wrapSymbol₁ N₂)) w :=
by
  induction w with
  | nil =>
    exact correspondingStrings_nil
  | cons d l ih =>
    obtain ⟨z, hz⟩ := hNw
    specialize ih (by
        unfold correspondingStrings at *
        cases z <;> aesop)
    cases d with
    | terminal t =>
      exact List.Forall₂.cons rfl ih
    | nonterminal n =>
      rcases n with (_ | (_ | _)) | (_ | _) <;>
        · cases z with
          | nil => tauto
          | cons a => cases a <;> tauto

private lemma correspondingStrings_after_wrap_unwrap_self₂ {N₁ N₂ : Type} {w : List (nst T N₁ N₂)}
    (hNw : ∃ z : List (Symbol T N₂), correspondingStrings (z.map (wrapSymbol₂ N₁)) w) :
  correspondingStrings ((w.filterMap unwrapSymbol₂).map (wrapSymbol₂ N₁)) w :=
by
  induction w with
  | nil =>
    exact correspondingStrings_nil
  | cons d l ih =>
    obtain ⟨z, hz⟩ := hNw
    specialize ih (by
        unfold correspondingStrings at *
        cases z <;> aesop)
    cases d with
    | terminal t =>
      exact List.Forall₂.cons rfl ih
    | nonterminal n =>
      rcases n with (_ | (_ | _)) | (_ | _) <;>
        · cases z with
          | nil => tauto
          | cons a => cases a <;> tauto

end unwrapping_nst


section very_complicated

private lemma critical_bound {g₁ g₂ : Grammar T}
    {u v : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    {a : List (nst T g₁.nt g₂.nt)} {r₁ : Grule T g₁.nt}
    (bef : a = u ++ (r₁.inputL.map (wrapSymbol₁ g₂.nt)
      ++ ([Symbol.nonterminal ◄(some ◄r₁.inputN)]
      ++ (r₁.inputR.map (wrapSymbol₁ g₂.nt) ++ v))))
    (ih_concat :
      correspondingStrings (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)) a)
    (h_y_v_len : y ≠ [] → 0 < v.length) :
  (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
    + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length ≤ x.length - u.length :=
by
  have as_positive : u.length
    + ((r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
    + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length) ≤ x.length := by
    by_contra contra
    push Not at contra
    rw [bef] at ih_concat
    clear bef
    repeat rw [←List.append_assoc] at ih_concat
    have len_pos
      : (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]
      ++ r₁.inputR.map (wrapSymbol₁ g₂.nt)
        ).length > 0 := by
      apply List.length_pos_of_mem (a := Symbol.nonterminal ◄(some ◄r₁.inputN))
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_singleton_self _
    have equal_total_len := correspondingStrings_length ih_concat
    have inequality_m1 :
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
        r₁.inputR.map (wrapSymbol₁ g₂.nt)).length - 1 <
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
        r₁.inputR.map (wrapSymbol₁ g₂.nt)).length := by
      omega
    have inequality_cat :
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
        r₁.inputR.map (wrapSymbol₁ g₂.nt)).length - 1 <
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
        r₁.inputR.map (wrapSymbol₁ g₂.nt) ++ v).length := by
      rw [List.length_append (bs := v)]
      omega
    have len_lhs :
        (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
          r₁.inputR.map (wrapSymbol₁ g₂.nt)).length =
        u.length + r₁.inputL.length + 1 + r₁.inputR.length := by
      change (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++
          [(Symbol.nonterminal ◄(some ◄r₁.inputN) : nst T g₁.nt g₂.nt)] ++
          r₁.inputR.map (wrapSymbol₁ g₂.nt)).length = _
      simp only [List.append_assoc, List.length_append, List.length_map, List.length_cons,
        List.singleton_append]
      omega
    have equal_total_len' :
        (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length =
        u.length + r₁.inputL.length + 1 + r₁.inputR.length + v.length := by
      rw [equal_total_len]
      simp only [List.append_assoc, List.length_append, List.length_map, List.length_cons,
        List.singleton_append]
      omega
    have contra' : x.length < u.length + (r₁.inputL.length + 1 + r₁.inputR.length) := by
      simpa only [List.length_map] using contra
    have inequality_map :
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
        r₁.inputR.map (wrapSymbol₁ g₂.nt)).length - 1 <
      (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length := by
      rw [len_lhs, equal_total_len']
      omega
    have inequality_map_opp :
      (x.map (wrapSymbol₁ g₂.nt)).length ≤
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
        r₁.inputR.map (wrapSymbol₁ g₂.nt)).length - 1 := by
      rw [List.length_map, len_lhs]
      omega
    have clash := correspondingStrings_getElem inequality_map inequality_cat ih_concat
    simp_rw
      [List.append_assoc
      (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)])
      (r₁.inputR.map (wrapSymbol₁ g₂.nt)) v] at clash
    rw [List.getElem_append] at clash
    split at clash
    · rw [List.getElem_map] at clash
      have inequality_map := inequality_map
      rw [List.length_append (bs := y.map (wrapSymbol₂ g₁.nt))] at inequality_map
      rw [y.length_map] at inequality_map
      linarith
    · by_cases h1 : (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length ≥ 1
      · rw [List.getElem_append_right] at clash; swap
        · rw [List.length_append (bs := r₁.inputR.map (wrapSymbol₁ g₂.nt))]
          have trivi_ineq : ∀ m k : ℕ, k ≥ 1 → m ≤ m + k - 1 := by
            clear * -
            omega
          exact trivi_ineq (u ++ _ ++ [_]).length _ h1
        have h1' : (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length - 1 <
          (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length := by
          omega
        have index :
          (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]
            ++ r₁.inputR.map (wrapSymbol₁ g₂.nt)).length -
            1
              - (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
              ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length =
          (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length - 1 := by
          simp
          omega
        have y_len : 0 < y.length := by
          simp at equal_total_len contra
          omega
        have v_len : 0 < v.length := by
          apply h_y_v_len
          exact List.ne_nil_of_length_pos y_len
        have clash_copy :
          correspondingSymbols
            ((y.map (wrapSymbol₂ g₁.nt))[
                (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]
                  ++ r₁.inputR.map (wrapSymbol₁ g₂.nt)).length
                    - 1 - (x.map (wrapSymbol₁ g₂.nt)).length
                ]'(by
                  have hsum := equal_total_len'
                  rw [List.length_append, List.length_map, List.length_map] at hsum
                  have hopp := inequality_map_opp
                  rw [List.length_map, len_lhs] at hopp
                  rw [len_lhs, List.length_map, List.length_map]
                  omega))
            ((r₁.inputR.map (wrapSymbol₁ g₂.nt) ++
                v)[(u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
                  ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++ r₁.inputR.map
                  (wrapSymbol₁ g₂.nt)).length
                    - 1
                      - (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
                      ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length
                ]'(by simp; omega)) := by
          exact clash
        simp_rw [index] at clash_copy
        conv at clash_copy => congr; rfl; rw
          [List.getElem_append_left h1' (h' := by rw [List.length_append]; omega)]
        rw [List.getElem_map, List.getElem_map] at clash_copy
        exact correspondingSymbols_never₂ clash_copy
      · push Not at h1
        have ris_third_is_nil : r₁.inputR.map (wrapSymbol₁ g₂.nt) = [] := by
          rwa [←List.length_eq_zero_iff, ←Nat.lt_one_iff]
        have inequality_m0 :
          (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
            ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length - 1 <
          (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
            ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length := by
          rwa [ris_third_is_nil, List.append_nil] at inequality_m1
        simp_rw [ris_third_is_nil] at clash
        simp only [List.append_nil] at clash
        rw [List.getElem_append] at clash
        split at clash
        · have clash' :
            correspondingSymbols
              ((y.map (wrapSymbol₂ g₁.nt))[
                  (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
                    ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length
                     - 1 - (x.map (wrapSymbol₁ g₂.nt)).length
                  ]'(by
                    have hir : r₁.inputR.length = 0 := by
                      have := congr_arg List.length ris_third_is_nil
                      simpa using this
                    have hsum := equal_total_len'
                    rw [List.length_append, List.length_map, List.length_map] at hsum
                    have hopp := inequality_map_opp
                    rw [List.length_map, len_lhs] at hopp
                    have hsing : (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++
                        [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length =
                        u.length + r₁.inputL.length + 1 := by
                      change (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++
                          [(Symbol.nonterminal ◄(some ◄r₁.inputN) : nst T g₁.nt g₂.nt)]).length
                            = _
                      simp only [List.append_assoc, List.length_append, List.length_map,
                        List.length_cons, List.length_nil]
                      omega
                    rw [hsing, List.length_map, List.length_map]
                    omega))
              (Symbol.nonterminal ◄(some ◄r₁.inputN)) := by
            convert clash
            symm
            apply List.getElem_concat_length
            simp
          change correspondingSymbols _ (wrapSymbol₁ g₂.nt (Symbol.nonterminal r₁.inputN))
            at clash'
          rw [List.getElem_map] at clash'
          exact correspondingSymbols_never₂ clash'
        · omega
  omega

private lemma sum_of_min_lengths_eq {g₁ g₂ : Grammar T}
    {u : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {r₁ : Grule T g₁.nt}
    (critical : (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
      + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length ≤ x.length - u.length)
    (ul_le_xl : u.length ≤ x.length) :
  min u.length x.length +
      (min r₁.inputL.length (x.length - u.length) +
        (min 1 (x.length - (r₁.inputL.length + u.length)) +
          (min r₁.inputR.length (x.length - (1 + (r₁.inputL.length + u.length))) +
            (x.length - (r₁.inputR.length + (1 + (r₁.inputL.length + u.length))))))) =
      x.length :=
by
  simp only [List.length_map] at critical
  omega

private lemma segment_4_correspondingStrings {g₁ g₂ : Grammar T}
    {u : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {r₁ : Grule T g₁.nt}
    (equiv_sgmnt_4 :
      correspondingStrings
        (((x.map (wrapSymbol₁ g₂.nt)).take
          (u.length + (r₁.inputL.length + (r₁.inputR.length + 1)))).drop
          (u.length + (r₁.inputL.length + 1)))
        (r₁.inputR.map (wrapSymbol₁ g₂.nt))) :
  correspondingStrings
    (((x.drop (1 + (r₁.inputL.length + u.length))).take r₁.inputR.length).map
      (wrapSymbol₁ g₂.nt))
    (r₁.inputR.map (wrapSymbol₁ g₂.nt)) :=
by
  convert equiv_sgmnt_4
  rw [List.map_take]
  rw [List.map_drop]
  have sum_rearrange : u.length + (r₁.inputL.length + (r₁.inputR.length + 1)) =
      u.length + (r₁.inputL.length + 1) + r₁.inputR.length := by
    linarith
  rw [sum_rearrange, List.drop_take]
  have small_sum_rearr :  1 + (r₁.inputL.length + u.length) = u.length
    + (r₁.inputL.length + 1) := by
    linarith
  rw [small_sum_rearr]
  congr
  omega

private lemma first_conjunct_deriv {g₁ g₂ : Grammar T}
    {a u v : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    {r : Grule T (nnn T g₁.nt g₂.nt)} {r₁ : Grule T g₁.nt}
    (ih_x : g₁.Derives [Symbol.nonterminal g₁.initial] x) (rin₁ : r₁ ∈ g₁.rules)
    (wrap_r₁_eq_r : wrapGrule₁ g₂.nt r₁ = r)
    (ih_concat :
      correspondingStrings (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)) a)
    (bef : a = u ++ (r.inputL ++ ([Symbol.nonterminal r.inputN] ++ (r.inputR ++ v))))
    (critical : (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
      + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length ≤ x.length - u.length) :
  let m : ℕ := (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
    + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length
  let b' : List (nst T g₁.nt g₂.nt) := u ++ r₁.output.map (wrapSymbol₁ g₂.nt) ++ v.take
    (x.length - u.length - m)
  g₁.Derives [Symbol.nonterminal g₁.initial] (b'.filterMap unwrapSymbol₁) :=
by
  intro m b'
  apply gr_deri_of_deri_tran ih_x
  use r₁
  constructor
  · exact rin₁
  use u.filterMap unwrapSymbol₁, (v.take (x.length - u.length - m)).filterMap unwrapSymbol₁
  constructor
  · have x_equiv :
      correspondingStrings
        (x.map (wrapSymbol₁ g₂.nt))
        ((u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]
          ++ r₁.inputR.map (wrapSymbol₁ g₂.nt) ++
          v).take x.length) := by
      rw [bef] at ih_concat
      clear * - ih_concat wrap_r₁_eq_r
      rw [← wrap_r₁_eq_r] at ih_concat
      simp only [List.append_assoc] at ih_concat ⊢
      convert correspondingStrings_take x.length ih_concat using 2
      all_goals first
        | rfl
        | rw [← List.length_map (f := wrapSymbol₁ g₂.nt), List.take_left]
    clear * - x_equiv critical
    have ul_le_xl : u.length ≤ x.length := by
      clear * - critical
      have stupid_le : u.length + 1 ≤ x.length := by omega
      exact Nat.le_of_succ_le stupid_le
    repeat rw [List.take_append] at x_equiv
    rw [List.take_of_length_le ul_le_xl] at x_equiv
    repeat rw [List.append_assoc]
    have chunk2 : (r₁.inputL.map (wrapSymbol₁ g₂.nt)).take (x.length - u.length) = r₁.inputL.map
      (wrapSymbol₁ g₂.nt) := by
      apply List.take_of_length_le
      clear * - critical
      omega
    have chunk3 :
        [@Symbol.nonterminal T (nnn T g₁.nt g₂.nt) ◄(some ◄r₁.inputN)].take
          (x.length - (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)).length) =
        [Symbol.nonterminal ◄(some ◄r₁.inputN)] := by
      apply List.take_of_length_le
      clear * - critical
      change 1 ≤ x.length - (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)).length
      rw [List.length_append]
      have weakened : (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1 ≤ x.length - u.length := by
        omega
      have goal_as_le_sub_sub : 1 ≤ x.length - u.length
        - (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length := by omega
      rwa [tsub_add_eq_tsub_tsub]
    have chunk4 :
      (r₁.inputR.map (wrapSymbol₁ g₂.nt)).take
        (x.length
          - (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)
          ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length) =
      r₁.inputR.map (wrapSymbol₁ g₂.nt) := by
      apply List.take_of_length_le
      clear * - critical
      rw [List.length_append, List.length_append]
      change (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length ≤ x.length
        - (u.length + (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1)
      omega
    have chunk5 :
      v.take
        (x.length
          - (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
          r₁.inputR.map (wrapSymbol₁ g₂.nt)).length) =
        v.take (x.length - u.length - m) := by
      repeat rw [List.length_append]
      apply congr_arg₂; swap
      · rfl
      have rearrange_sum_of_four : ∀ a b c d : ℕ, a + b + c + d = a + (b + c + d) := by omega
      rw [rearrange_sum_of_four]
      change x.length - (u.length + m) = x.length - u.length - m
      clear * -
      omega
    rw [chunk2, chunk3, chunk4, chunk5] at x_equiv
    clear chunk2 chunk3 chunk4 chunk5
    obtain ⟨temp_5, equiv_segment_5⟩ :=
      correspondingStrings_split
        (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]
          ++ r₁.inputR.map (wrapSymbol₁ g₂.nt)).length
        x_equiv
    clear x_equiv
    rw [List.drop_left] at equiv_segment_5
    rw [List.take_left] at temp_5
    obtain ⟨temp_4, equiv_segment_4⟩ :=
      correspondingStrings_split
        (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt) ++ [Symbol.nonterminal ◄(some ◄r₁.inputN)]).length
        temp_5
    clear temp_5
    rw [List.drop_left] at equiv_segment_4
    rw [List.take_left] at temp_4
    rw [List.take_take] at temp_4
    obtain ⟨temp_3, equiv_segment_3⟩ :=
      correspondingStrings_split (u ++ r₁.inputL.map (wrapSymbol₁ g₂.nt)).length temp_4
    clear temp_4
    rw [List.drop_left] at equiv_segment_3
    rw [List.take_left] at temp_3
    rw [List.take_take] at temp_3
    obtain ⟨equiv_segment_1, equiv_segment_2⟩ := correspondingStrings_split u.length temp_3
    clear temp_3
    rw [List.drop_left] at equiv_segment_2
    rw [List.take_left] at equiv_segment_1
    rw [List.take_take] at equiv_segment_1
    have equiv_sgmnt_1 : correspondingStrings ((x.map (wrapSymbol₁ g₂.nt)).take u.length) u := by
      simpa using equiv_segment_1
    have equiv_sgmnt_2 :
      correspondingStrings
        ((((x.map (wrapSymbol₁ g₂.nt)).take (u.length + r₁.inputL.length))).drop u.length)
        (r₁.inputL.map (wrapSymbol₁ g₂.nt)) := by
      simpa using equiv_segment_2
    have equiv_sgmnt_3 :
      correspondingStrings
        (((x.map (wrapSymbol₁ g₂.nt)).take (u.length + (r₁.inputL.length + 1))).drop
          (u.length + r₁.inputL.length))
        [Symbol.nonterminal ◄(some ◄r₁.inputN)] := by
      simpa using equiv_segment_3
    have equiv_sgmnt_4 :
      correspondingStrings
        (((x.map (wrapSymbol₁ g₂.nt)).take
          (u.length + (r₁.inputL.length + (r₁.inputR.length + 1)))).drop
          (u.length + (r₁.inputL.length + 1)))
        (r₁.inputR.map (wrapSymbol₁ g₂.nt)) := by
      simpa using equiv_segment_4
    have equiv_sgmnt_5 :
      correspondingStrings
        ((x.map (wrapSymbol₁ g₂.nt)).drop
          (u.length + (r₁.inputL.length + (r₁.inputR.length + 1))))
        (v.take (x.length - u.length - m)) := by
      simpa using equiv_segment_5
    clear equiv_segment_1 equiv_segment_2 equiv_segment_3 equiv_segment_4 equiv_segment_5
    have segment_1_eqi : correspondingStrings ((x.take u.length).map (wrapSymbol₁ g₂.nt)) u := by
      convert equiv_sgmnt_1
      rw [List.map_take]
    have segment_1_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_1_eqi).symm
    rw [←List.take_append_drop u.length x]
    apply congr_arg₂
    · exact segment_1_equ
    clear segment_1_equ segment_1_eqi equiv_sgmnt_1
    have segment_2_eqi :
      correspondingStrings
        (((x.drop u.length).take r₁.inputL.length).map (wrapSymbol₁ g₂.nt))
        (r₁.inputL.map (wrapSymbol₁ g₂.nt)) := by
      convert equiv_sgmnt_2
      rw [List.map_take, List.map_drop, List.drop_take]
      simp
    have segment_2_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_2_eqi).symm
    rw [unwrap_wrap₁_string] at segment_2_equ
    rw [←List.take_append_drop r₁.inputL.length (x.drop u.length)]
    apply congr_arg₂
    · exact segment_2_equ
    clear segment_2_equ segment_2_eqi equiv_sgmnt_2
    rw [List.drop_drop]
    have segment_3_eqi :
      correspondingStrings
        (((x.drop (r₁.inputL.length + u.length)).take 1).map (wrapSymbol₁ g₂.nt))
        ([Symbol.nonterminal r₁.inputN].map (wrapSymbol₁ g₂.nt)) := by
      convert equiv_sgmnt_3
      all_goals first
        | rfl
        | (rw [List.map_take, List.map_drop, ←add_assoc, List.drop_take, add_comm]
           simp)
    have segment_3_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_3_eqi).symm
    rw [unwrap_wrap₁_string] at segment_3_equ
    rw [Nat.add_comm u.length r₁.inputL.length,
         ←List.take_append_drop 1 (x.drop (r₁.inputL.length + u.length))]
    apply congr_arg₂
    · exact segment_3_equ
    clear segment_3_equ segment_3_eqi equiv_sgmnt_3
    rw [List.drop_drop]
    have segment_4_eqi := segment_4_correspondingStrings equiv_sgmnt_4
    have segment_4_equ := (filterMap_unwrap_of_correspondingStrings₁ segment_4_eqi).symm
    rw [unwrap_wrap₁_string] at segment_4_equ
    rw [add_comm (r₁.inputL.length + u.length) 1,
         ←(x.drop (1 + (r₁.inputL.length + u.length))).take_append_drop r₁.inputR.length]
    apply congr_arg₂
    · exact segment_4_equ
    clear segment_4_equ segment_4_eqi equiv_sgmnt_4
    rw [List.drop_drop]
    repeat rw [List.length_append]
    repeat rw [List.length_take]
    repeat rw [List.length_drop]
    have sum_of_min_lengths := sum_of_min_lengths_eq critical ul_le_xl
    have porting_adjustment : 1 + (r₁.inputL.length + u.length) + r₁.inputR.length
      = r₁.inputR.length + (1 + (r₁.inputL.length + u.length)) := by omega
    rw [porting_adjustment, sum_of_min_lengths]
    clear * - equiv_sgmnt_5
    have another_rearranging : r₁.inputR.length + (1 + (r₁.inputL.length + u.length)) =
        u.length + (r₁.inputL.length + (r₁.inputR.length + 1)) := by omega
    rw [another_rearranging]
    rw [←List.map_drop] at equiv_sgmnt_5
    symm
    exact filterMap_unwrap_of_correspondingStrings₁ equiv_sgmnt_5
  · rw [←unwrap_wrap₁_string g₂.nt r₁.output]
    simp [b']

private lemma induction_step_for_lifted_rule_from_g₁ {g₁ g₂ : Grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    {r : Grule T (nnn T g₁.nt g₂.nt)} (rin : r ∈ g₁.rules.map (wrapGrule₁ g₂.nt))
    (bef : a = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : b = u ++ r.output ++ v)
    (ih_x : g₁.Derives [Symbol.nonterminal g₁.initial] x)
    (ih_y : g₂.Derives [Symbol.nonterminal g₂.initial] y)
    (ih_concat : correspondingStrings (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)) a) :
  ∃ x' : List (Symbol T g₁.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x'  ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y   ∧
    correspondingStrings (x'.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)) b :=
by
  rw [List.mem_map] at rin
  rcases rin with ⟨r₁, rin₁, wrap_r₁_eq_r⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append, wrapGrule₁] at *
  rw [←List.singleton_append] at bef
  have h_y_v_len : y ≠ [] → 0 < v.length := by
    intro ynn
    rw [List.length_pos_iff_ne_nil]
    intro v_nil
    rw [v_nil, List.append_nil] at bef aft
    rw [bef, ←wrap_r₁_eq_r] at ih_concat
    have y_nil : y = [] := by
      have ih_concat_rev := correspondingStrings_reverse ih_concat
      simp only [List.reverse_append, ← List.map_reverse, List.cons_append, List.nil_append,
                  List.reverse_cons, List.append_assoc] at ih_concat_rev
      cases hy : y.reverse with
      | nil =>
        rw [List.reverse_eq_nil_iff] at hy
        exact hy
      | cons d l =>
        exfalso
        rw [hy] at ih_concat_rev
        simp only [List.map_cons, List.cons_append] at ih_concat_rev
        cases hr₁ : r₁.inputR.reverse with
        | nil =>
          rw [hr₁, List.map_nil, List.nil_append] at ih_concat_rev
          rw [correspondingStrings_cons] at ih_concat_rev
          have imposs :  correspondingSymbols (wrapSymbol₂ g₁.nt d)
            (wrapSymbol₁ g₂.nt (Symbol.nonterminal r₁.inputN)) := by
            exact ih_concat_rev.left
          exact correspondingSymbols_never₂ imposs
        | cons d' l' =>
          rw [hr₁, List.map_cons, List.cons_append] at ih_concat_rev
          rw [correspondingStrings_cons] at ih_concat_rev
          exact correspondingSymbols_never₂ ih_concat_rev.left
    exact ynn y_nil
  let m : ℕ := (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
    + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length
  let b' : List (nst T g₁.nt g₂.nt) := u ++ r₁.output.map (wrapSymbol₁ g₂.nt) ++ v.take
    (x.length - u.length - m)
  use b'.filterMap unwrapSymbol₁
  have bef_wrapped : a = u ++ (r₁.inputL.map (wrapSymbol₁ g₂.nt)
      ++ ([Symbol.nonterminal ◄(some ◄r₁.inputN)]
      ++ (r₁.inputR.map (wrapSymbol₁ g₂.nt) ++ v))) := by
    rw [bef, ←wrap_r₁_eq_r]
  have critical := critical_bound bef_wrapped ih_concat h_y_v_len
  constructor
  · exact first_conjunct_deriv ih_x rin₁ wrap_r₁_eq_r ih_concat bef critical
  rw [aft]
  rw [bef] at ih_concat
  rw [List.filterMap_append_append, List.map_append_append, List.append_assoc, List.append_assoc]
  refine ⟨ih_y, ?_⟩
  apply correspondingStrings_append
  · have part_for_u := correspondingStrings_take u.length ih_concat
    rw [List.take_left] at part_for_u
    have trivi : u.length ≤ (x.map (wrapSymbol₁ g₂.nt)).length := by
      clear * - critical
      rw [List.length_map]
      omega
    rw [List.take_append_of_le_length trivi] at part_for_u
    clear * - part_for_u
    rw [←List.map_take] at part_for_u
    apply correspondingStrings_after_wrap_unwrap_self₁
    use x.take u.length
  apply correspondingStrings_append
  · rw [unwrap_wrap₁_string, ←wrap_r₁_eq_r]
    apply correspondingStrings_self
  convert_to
    correspondingStrings _
      (v.take (x.length - u.length - m) ++ v.drop (x.length - u.length - m))
  · rw [List.take_append_drop]
  apply correspondingStrings_append
  · have eqi := correspondingStrings_take (x.map (wrapSymbol₁ g₂.nt)).length ih_concat
    rw [List.take_left] at eqi
    have part_for_v_beginning := correspondingStrings_drop (u.length + m) eqi
    clear * - part_for_v_beginning critical wrap_r₁_eq_r
    rw [←List.map_drop] at part_for_v_beginning
    apply correspondingStrings_after_wrap_unwrap_self₁
    use x.drop (u.length + m)
    convert part_for_v_beginning using 1
    clear part_for_v_beginning
    rw [List.length_map]
    rw [List.take_append]
    rw [List.drop_append]
    have tul_lt : (u.take x.length).length ≤ u.length + m := by
      rw [List.length_take]
      calc
        min x.length u.length ≤ u.length := min_le_right _ _
        _ ≤ u.length + m := le_self_add
    rw [List.drop_eq_nil_of_le tul_lt]
    rw [List.nil_append]
    rw [←List.append_assoc _ _ v]
    rw [←List.append_assoc _ _ v]
    rw [←List.append_assoc]
    rw [List.take_append]
    rw [List.drop_append]
    have rul_inp_len :
      (r₁.inputL.map (wrapSymbol₁ g₂.nt) ++
              [Symbol.nonterminal ◄(some ◄r₁.inputN)] ++
            r₁.inputR.map (wrapSymbol₁ g₂.nt)).length =
        m := by
      rw [List.length_append, List.length_append, List.length_singleton]
    have u_is_shorter : min x.length u.length = u.length := by
      apply min_eq_right
      clear * - critical
      omega
    rw [List.drop_eq_nil_of_le]; swap
    · rw [List.length_take, ←wrap_r₁_eq_r, rul_inp_len, List.length_take, u_is_shorter]
      calc
        min (x.length - u.length) m ≤ m := min_le_right _ _
        _ ≤ u.length + m - u.length := le_add_tsub_swap
    rw [List.nil_append, List.length_take, List.length_take, ←wrap_r₁_eq_r, rul_inp_len]
    have zero_dropping : u.length + m - min x.length u.length - min (x.length - u.length) m = 0
      := by
      have middle_cannot_exceed : min (x.length - u.length) m = m := min_eq_right critical
      rw [u_is_shorter, middle_cannot_exceed]
      clear * -
      omega
    rewrite [zero_dropping]
    rfl
  -- now we have what `g₂` generated
  have reverse_concat := correspondingStrings_reverse ih_concat
  repeat rw [List.reverse_append] at reverse_concat
  have the_part := correspondingStrings_take y.length reverse_concat
  apply correspondingStrings_of_reverse
  have len_sum : y.length + (x.length - u.length - m) = v.length := by
    change
      y.length + (x.length - u.length - (
          (r₁.inputL.map (wrapSymbol₁ g₂.nt)).length + 1
            + (r₁.inputR.map (wrapSymbol₁ g₂.nt)).length)
        ) =
      v.length
    have len_concat := correspondingStrings_length ih_concat
    repeat rw [List.length_append] at len_concat
    rw [List.length_map, List.length_map, List.length_singleton, add_comm] at len_concat
    rw [←Nat.add_sub_assoc]; swap
    · exact critical
    rw [←Nat.add_sub_assoc]; swap
    · clear * - critical
      omega
    rw [len_concat, ←wrap_r₁_eq_r, add_tsub_cancel_left, ←Nat.add_assoc, ←Nat.add_assoc]
    apply Nat.add_sub_self_left
  have yl_lt_vl : y.length ≤ v.length := Nat.le.intro len_sum
  convert_to correspondingStrings _ (v.reverse.take y.length)
  · convert_to (v.drop (v.length - y.length)).reverse = v.reverse.take y.length
    · apply congr_arg
      apply congr_arg₂
      · clear * - len_sum
        omega
      · rfl
    exact List.take_reverse.symm
  clear * - the_part yl_lt_vl
  rw [List.take_append_of_le_length] at the_part; swap
  · rw [List.length_reverse]
    rw [List.length_map]
  repeat rw [List.append_assoc] at the_part
  rw [List.take_append_of_le_length] at the_part; swap
  · rw [List.length_reverse]
    exact yl_lt_vl
  rw [List.take_of_length_le] at the_part; swap
  · rw [List.length_reverse]
    rw [List.length_map]
  exact the_part

private lemma induction_step_for_lifted_rule_from_g₂ {g₁ g₂ : Grammar T}
    {a b u v : List (nst T g₁.nt g₂.nt)} {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    {r : Grule T (nnn T g₁.nt g₂.nt)} (rin : r ∈ g₂.rules.map (wrapGrule₂ g₁.nt))
    (bef : a = u ++ r.inputL ++ [Symbol.nonterminal r.inputN] ++ r.inputR ++ v)
    (aft : b = u ++ r.output ++ v)
    (ih_x : g₁.Derives [Symbol.nonterminal g₁.initial] x)
    (ih_y : g₂.Derives [Symbol.nonterminal g₂.initial] y)
    (ih_concat : correspondingStrings (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)) a) :
  ∃ y' : List (Symbol T g₂.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x   ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y'  ∧
    correspondingStrings (x.map (wrapSymbol₁ g₂.nt) ++ y'.map (wrapSymbol₂ g₁.nt)) b :=
by
  rw [List.mem_map] at rin
  rcases rin with ⟨r₂, rin₂, wrap_r₂_eq_r⟩
  rw [←wrap_r₂_eq_r] at bef aft
  clear wrap_r₂_eq_r r
  simp only [wrapGrule₂] at *
  simp only [List.append_assoc, List.cons_append, List.nil_append] at bef
  rw [←List.singleton_append] at bef
  rw [bef] at ih_concat
  let b' := u.drop x.length ++ r₂.output.map (wrapSymbol₂ g₁.nt) ++ v
  use b'.filterMap unwrapSymbol₂
  have total_len := correspondingStrings_length ih_concat
  repeat rw [List.length_append] at total_len
  repeat rw [List.length_map] at total_len
  have matched_right : u.length ≥ x.length := by
    by_contra! ul_lt_xl
    have ul_lt_ihls : u.length < (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length
      := by
      rw [List.length_append, List.length_map, List.length_map]
      exact Nat.lt_add_right _ ul_lt_xl
    have ulth := correspondingStrings_getElem ul_lt_ihls (by simp) ih_concat
    have ul_lt_xlm : u.length < (x.map (wrapSymbol₁ g₂.nt)).length := by
      rwa [List.length_map]
    simp_rw [List.getElem_append, ul_lt_xlm] at ulth
    simp only [↓reduceDIte, List.getElem_map, lt_self_iff_false, tsub_self, List.length_map,
                zero_tsub, List.length_cons, List.length_nil, zero_add, zero_lt_one,
                List.getElem_cons_zero] at ulth
    split at ulth
    · exact correspondingSymbols_never₁ ulth
    · change correspondingSymbols (wrapSymbol₁ g₂.nt x[u.length])
        (wrapSymbol₂ g₁.nt (Symbol.nonterminal r₂.inputN)) at ulth
      exact correspondingSymbols_never₁ ulth
  constructor
  · exact ih_x
  constructor
  · apply gr_deri_of_deri_tran ih_y
    use r₂, rin₂, (u.drop x.length).filterMap unwrapSymbol₂, v.filterMap unwrapSymbol₂
    constructor
    · have corres_y := correspondingStrings_drop (x.map (wrapSymbol₁ g₂.nt)).length ih_concat
      rw [List.drop_left] at corres_y
      rw [List.drop_append_of_le_length] at corres_y; swap
      · simp
        linarith
      clear * - corres_y total_len
      repeat rw [List.append_assoc]
      obtain ⟨seg1, rest1⟩ := correspondingStrings_split
        (u.drop (x.map (wrapSymbol₁ g₂.nt)).length).length corres_y
      clear corres_y
      rw [List.take_left] at seg1
      rw [List.drop_left] at rest1
      rw [←List.take_append_drop ((u.drop x.length).filterMap unwrapSymbol₂).length y]
      rw [←List.map_take] at seg1
      have min_uxy : min (u.length - x.length) y.length = u.length - x.length := by
        rw [min_eq_left]
        clear * - total_len
        omega
      have tuxy : y.take (y.take (u.length - x.length)).length = y.take (u.length - x.length) := by
        rw [List.length_take, min_uxy]
      have fmu1 := filterMap_unwrap_of_correspondingStrings₂ seg1
      rw [List.length_map] at fmu1
      have fml : ((u.drop x.length).filterMap unwrapSymbol₂).length = (u.drop x.length).length := by
        rw [List.length_take, min_uxy] at tuxy
        rw [congr_arg List.length fmu1, List.length_drop, congr_arg List.length tuxy,
             List.length_take]
        exact min_uxy
      apply congr_arg₂
      · rw [fmu1]
        rwa [List.length_drop]
      clear seg1 fmu1 tuxy min_uxy
      rw [List.length_map] at rest1
      obtain ⟨seg2, rest2⟩ := correspondingStrings_split (r₂.inputL.map (wrapSymbol₂ g₁.nt)).length
        rest1
      clear rest1
      rw [List.take_left] at seg2
      rw [List.drop_left] at rest2
      rw
        [←(y.drop ((u.drop x.length).filterMap unwrapSymbol₂).length).take_append_drop
        (r₂.inputL.map (wrapSymbol₂ g₁.nt)).length]
      apply congr_arg₂
      · clear * - seg2 fml
        rw [←List.map_drop] at seg2
        rw [←List.map_take] at seg2
        have fmu2 := filterMap_unwrap_of_correspondingStrings₂ seg2
        rw [List.length_map] at fmu2 ⊢
        rw [unwrap_wrap₂_string] at fmu2
        rw [fml]
        exact fmu2.symm
      clear seg2
      rw [List.length_map] at rest2
      rw [List.drop_drop] at rest2 ⊢
      obtain ⟨seg3, rest3⟩ := correspondingStrings_split 1 rest2
      clear rest2
      rw [List.take_left' List.length_singleton] at seg3
      rw [List.drop_left' List.length_singleton] at rest3
      rw [List.length_map, fml,
           ←(y.drop ((u.drop x.length).length + r₂.inputL.length)).take_append_drop 1]
      apply congr_arg₂
      · rw [←List.map_drop] at seg3
        rw [←List.map_take] at seg3
        have fmu3 := filterMap_unwrap_of_correspondingStrings₂ seg3
        exact fmu3.symm
      clear seg3
      rw [List.drop_drop] at rest3 ⊢
      rw [←List.map_drop] at rest3
      rw [←filterMap_unwrap_of_correspondingStrings₂ rest3, List.filterMap_append,
           unwrap_wrap₂_string]
    · rw [List.filterMap_append_append]
      congr
      apply unwrap_wrap₂_string
  · rw [aft, List.filterMap_append_append, List.map_append_append, List.append_assoc,
        ←List.append_assoc (x.map (wrapSymbol₁ g₂.nt)), List.append_assoc u]
    clear b'
    apply correspondingStrings_append; swap
    · rw [unwrap_wrap₂_string]
      apply correspondingStrings_append
      · apply correspondingStrings_self
      apply correspondingStrings_after_wrap_unwrap_self₂
      repeat rw [←List.append_assoc] at ih_concat
      have rev := correspondingStrings_reverse ih_concat
      rw [List.reverse_append (bs := v)] at rev
      have tak := correspondingStrings_take v.reverse.length rev
      rw [List.take_left] at tak
      have rtr := correspondingStrings_reverse tak
      have nec : v.reverse.length ≤ (y.map (wrapSymbol₂ g₁.nt)).reverse.length := by
        clear * - matched_right total_len
        rw [List.length_reverse, List.length_reverse, List.length_map]
        linarith
      rw [List.reverse_reverse, List.reverse_append, List.take_append_of_le_length nec,
           List.reverse_take, List.reverse_reverse, ←List.map_drop] at rtr
      exact ⟨_, rtr⟩
    · rw [←List.take_append_drop x.length u]
      apply correspondingStrings_append
      · have almost := correspondingStrings_take x.length ih_concat
        rw [List.take_append_of_le_length matched_right] at almost
        convert almost
        have xl_eq : x.length = (x.map (wrapSymbol₁ g₂.nt)).length := by
          rw [List.length_map]
        rw [xl_eq, List.take_left]
      · rw [List.take_append_drop]
        apply correspondingStrings_after_wrap_unwrap_self₂
        have tdc := correspondingStrings_drop x.length
          (correspondingStrings_take u.length ih_concat)
        have ul_eq : u.length = x.length + (u.length - x.length) := by
          rw [←Nat.add_sub_assoc matched_right, add_comm, Nat.add_sub_assoc (by rfl), Nat.sub_self,
               add_zero]
        rw [List.take_left, ul_eq, List.drop_take, List.drop_left' (List.length_map ..),
             ←List.map_take] at tdc
        exact ⟨_, tdc⟩

private lemma bigGrammar_init_absurd {g₁ g₂ : Grammar T}
    {α : List (nst T g₁.nt g₂.nt)} {u v : List (nst T g₁.nt g₂.nt)}
    {x : List (Symbol T g₁.nt)} {y : List (Symbol T g₂.nt)}
    (bef : α = u ++ [Symbol.nonterminal ◄none] ++ v)
    (ih_concat :
      correspondingStrings (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)) α) :
  False :=
by
  rw [bef] at ih_concat
  have same_lengths := correspondingStrings_length ih_concat
  clear bef
  have ulen₁ : u.length < (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length
    := by
    rw [List.length_append (bs := v), List.length_append (as := u),
      List.length_singleton] at same_lengths
    clear * - same_lengths
    linarith
  rw [List.append_assoc] at ih_concat
  have eqi_symb := correspondingStrings_getElem ulen₁ ?_ ih_concat; swap
  · rw [List.length_append, List.length_append, List.length_singleton]
    clear * -
    linarith
  have eq_none : (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[u.length]'ulen₁
    = Symbol.nonterminal ◄none := by
    simp at eqi_symb
    cases hxyu : (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[u.length] with
    | terminal t =>
      exfalso
      simp_all [correspondingSymbols]
    | nonterminal s =>
      cases s with
      | inl sₒ =>
        cases sₒ with
        | none => rfl
        | some => simp_all [correspondingSymbols]
      | inr sₜ => simp_all [correspondingSymbols]
  have impossible_in : Symbol.nonterminal ◄none ∈ x.map (wrapSymbol₁ g₂.nt) ++ y.map
    (wrapSymbol₂ g₁.nt) := by
    rw [List.mem_iff_getElem]
    exact ⟨u.length, ulen₁, eq_none⟩
  rw [List.mem_append] at impossible_in
  cases impossible_in with
  | inl hinx =>
    rw [List.mem_map] at hinx
    rcases hinx with ⟨s, -, contradic⟩
    clear * - contradic
    cases s <;> simp [wrapSymbol₁] at contradic
  | inr hiny =>
    rw [List.mem_map] at hiny
    rcases hiny with ⟨s, -, contradic⟩
    clear * - contradic
    cases s <;> simp [wrapSymbol₂] at contradic

private lemma big_induction {g₁ g₂ : Grammar T} {w : List (nst T g₁.nt g₂.nt)}
    (hggw : (bigGrammar g₁ g₂).Derives
        [Symbol.nonterminal ◄(some ◄g₁.initial),
         Symbol.nonterminal ◄(some ▶g₂.initial)]
        w) :
  ∃ x : List (Symbol T g₁.nt), ∃ y : List (Symbol T g₂.nt),
    g₁.Derives [Symbol.nonterminal g₁.initial] x  ∧
    g₂.Derives [Symbol.nonterminal g₂.initial] y  ∧
    correspondingStrings
      (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))
      w  :=
by
  induction hggw with
  | refl =>
      use [Symbol.nonterminal g₁.initial], [Symbol.nonterminal g₂.initial]
      constructor
      · apply gr_deri_self
      constructor
      · apply gr_deri_self
      simp only [wrapSymbol₁, wrapSymbol₂, List.map_singleton, List.singleton_append]
      exact correspondingStrings_self
  | tail _ orig ih =>
      rcases ih with ⟨x, y, ih_x, ih_y, ih_concat⟩
      rcases orig with ⟨r, rin, u, v, bef, aft⟩
      rw [mem_bigGrammar_rules_iff] at rin
      rcases rin with rinit | rin₁ | rin₂ | rte₁ | rte₂
      · exfalso
        rw [rinit] at bef
        simp only [List.append_nil] at bef
        exact bigGrammar_init_absurd bef ih_concat
      · obtain ⟨x', pros⟩ :=
          induction_step_for_lifted_rule_from_g₁ rin₁ bef aft ih_x ih_y ih_concat
        exact ⟨x', y, pros⟩
      · use x
        exact induction_step_for_lifted_rule_from_g₂ rin₂ bef aft ih_x ih_y ih_concat
      · use x, y, ih_x, ih_y
        unfold rulesForTerminals₁ at rte₁
        rw [List.mem_map] at rte₁
        rcases rte₁ with ⟨t, -, eq_r⟩
        rw [←eq_r] at bef aft
        clear eq_r r
        dsimp only at bef aft
        have xy_split_u : x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt) =
            (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).take u.length ++
            (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).drop u.length :=
          (List.take_append_drop _ _).symm
        rw [xy_split_u, aft]
        have part_for_u := correspondingStrings_take u.length ih_concat
        rw [List.append_assoc]
        apply correspondingStrings_append
        · convert part_for_u
          convert (congr_arg (List.take u.length) bef).symm
          simp
        · rw [bef, List.append_nil, List.append_nil] at ih_concat
          have ul_lt_len_um : u.length < (u ++ [Symbol.nonterminal ▶◄t]).length := by simp
          have ul_lt_len_umv : u.length < (u ++ [Symbol.nonterminal ▶◄t] ++ v).length := by
            rw [List.length_append]
            exact lt_of_lt_of_le ul_lt_len_um le_self_add
          have ul_lt_len_xy : u.length <
            (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length := by
            rw [correspondingStrings_length ih_concat]
            simp
          have middle_nt := correspondingStrings_getElem ul_lt_len_xy ul_lt_len_umv ih_concat
          have middle_nt_elem :
            correspondingSymbols
              ((x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[u.length]'ul_lt_len_xy)
              (Symbol.nonterminal ▶◄t) := by
            convert middle_nt
            simp
          have xy_split_nt : (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).drop u.length
            =
              ((x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).drop u.length).take 1 ++
              ((x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).drop u.length).drop 1 :=
            (List.take_append_drop _ _).symm
          rw [xy_split_nt]
          apply correspondingStrings_append; swap
          · rw [List.drop_drop]
            have part_for_v := correspondingStrings_drop u.length.succ ih_concat
            convert part_for_v
            have correct_len : 1 + u.length = (u ++ [Symbol.nonterminal ▶◄t]).length := by
              rw [add_comm, List.length_append, List.length_singleton]
            simp
          · convert_to
              correspondingStrings
                [(x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[u.length]'ul_lt_len_xy]
                [Symbol.terminal t]
            · apply List.take_one_drop_eq_of_lt_length
            clear * - middle_nt_elem
            apply correspondingStrings_singleton
            exact correspondingSymbols_terminal_of_inl middle_nt_elem
      · use x, y, ih_x, ih_y
        unfold rulesForTerminals₂ at rte₂
        rw [List.mem_map] at rte₂
        rcases rte₂ with ⟨t, -, eq_r⟩
        rw [←eq_r] at bef aft
        clear eq_r r
        dsimp only at bef aft
        have xy_split_u : x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt) =
            (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).take u.length.succ ++
            (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).drop u.length.succ :=
          (List.take_append_drop _ _).symm
        rw [xy_split_u, aft]
        have part_for_v := correspondingStrings_drop u.length.succ ih_concat
        apply correspondingStrings_append
        · rw [bef, List.append_nil, List.append_nil] at ih_concat
          have ul_lt_len_um : u.length < (u ++ [Symbol.nonterminal ▶▶t]).length := by
            rw [List.length_append]
            rw [List.length_singleton]
            apply lt_add_one
          have ul_lt_len_umv : u.length < (u ++ [Symbol.nonterminal ▶▶t] ++ v).length := by
            rw [List.length_append]
            exact lt_of_lt_of_le ul_lt_len_um le_self_add
          have ul_lt_len_xy : u.length <
            (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length := by
            have same_len := correspondingStrings_length ih_concat
            rwa [same_len]
          have middle_nt := correspondingStrings_getElem ul_lt_len_xy ul_lt_len_umv ih_concat
          have middle_nt_elem :
            correspondingSymbols
              ((x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[u.length]'ul_lt_len_xy)
              (Symbol.nonterminal ▶▶t) := by
            convert middle_nt
            simp
          have xy_split_nt : (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).take
            u.length.succ =
              ((x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).take u.length.succ).take
                u.length ++
              ((x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).take u.length.succ).drop
                u.length :=
            (List.take_append_drop _ _).symm
          rw [xy_split_nt]
          apply correspondingStrings_append
          · rw [List.take_take]
            have part_for_u := correspondingStrings_take u.length ih_concat
            convert part_for_u
            · apply min_eq_left
              apply Nat.le_succ
            rw [List.append_assoc, List.take_left]
          · convert_to
              correspondingStrings
                [(x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[u.length]'ul_lt_len_xy]
                [Symbol.terminal t]
            · apply list_drop_take_succ
            clear * - middle_nt_elem
            apply correspondingStrings_singleton
            exact correspondingSymbols_terminal_of_inr middle_nt_elem
        · convert part_for_v using 1
          convert (congr_arg (List.drop u.length.succ) bef).symm
          simp

lemma in_concatenated_of_in_big {g₁ g₂ : Grammar T} {w : List T}
    (hwgg : w ∈ (bigGrammar g₁ g₂).language) :
  w ∈ g₁.language * g₂.language :=
by
  rw [Language.mem_mul]
  rcases gr_eq_or_tran_deri_of_deri hwgg with case_id | case_step
  · exfalso
    have nonmatch := congr_arg (·[0]?) case_id
    clear * - nonmatch
    cases w
    · rw [List.map_nil] at nonmatch
      simp at nonmatch
    · unfold List.map at nonmatch
      have imposs := Option.some.inj nonmatch
      simp at imposs
  clear hwgg
  rcases case_step with ⟨w₁, hyp_tran, hyp_deri⟩
  have w₁eq : w₁ =
      [Symbol.nonterminal ◄(some ◄g₁.initial),
       Symbol.nonterminal ◄(some ▶g₂.initial)] := by
    clear * - hyp_tran
    -- only the first rule is applicable
    rcases hyp_tran with ⟨r, rin, u, v, bef, aft⟩
    have bef_len := congr_arg List.length bef
    rw [List.length_append, List.length_append, List.length_append, List.length_append,
        List.length_singleton, List.length_singleton] at bef_len
    have u_nil : u = [] := by
      clear * - bef_len
      rw [←List.length_eq_zero_iff]
      linarith
    have v_nil : v = [] := by
      clear * - bef_len
      rw [←List.length_eq_zero_iff]
      linarith
    have rif_nil : r.inputL = [] := by
      clear * - bef_len
      rw [←List.length_eq_zero_iff]
      linarith
    have nt_match : (Symbol.nonterminal (bigGrammar g₁ g₂).initial : Symbol T (bigGrammar g₁ g₂).nt)
      =
        Symbol.nonterminal r.inputN := by
      have bef_fst := congr_arg (·[0]?) bef
      rw [u_nil, rif_nil] at bef_fst
      rwa [←Option.some_inj]
    simp only [bigGrammar, List.mem_cons, List.mem_append, or_assoc, List.mem_map] at rin
    rcases rin with rinit | rin₁ | rin₂ | rte₁ | rte₂
    · rw [rinit] at bef aft
      dsimp only at bef aft
      rw [u_nil, v_nil] at aft
      rw [List.nil_append, List.append_nil] at aft
      exact aft
    · exfalso
      rcases rin₁ with ⟨r₀, hr₀g₁, wrap_eq_r⟩
      rw [←wrap_eq_r] at nt_match
      unfold wrapGrule₁ at nt_match
      have inl_match := Symbol.nonterminal.inj nt_match
      change Sum.inl none = Sum.inl (some ◄r₀.inputN) at inl_match
      have none_eq_some := Sum.inl.inj inl_match
      simp at none_eq_some
    · exfalso
      rcases rin₂ with ⟨r₀, hr₀g₂, wrap_eq_r⟩
      rw [←wrap_eq_r] at nt_match
      unfold wrapGrule₂ at nt_match
      have inl_match := Symbol.nonterminal.inj nt_match
      change Sum.inl none = Sum.inl (some ▶r₀.inputN) at inl_match
      have none_eq_some := Sum.inl.inj inl_match
      simp at none_eq_some
    · unfold rulesForTerminals₁ at rte₁
      rw [List.mem_map] at rte₁
      rcases rte₁ with ⟨t, htg₁, tt_eq_r⟩
      rw [←tt_eq_r] at nt_match
      have inl_eq_inr := Symbol.nonterminal.inj nt_match
      simp at inl_eq_inr
    · unfold rulesForTerminals₂ at rte₂
      rw [List.mem_map] at rte₂
      rcases rte₂ with ⟨t, htg₂, tt_eq_r⟩
      rw [←tt_eq_r] at nt_match
      have inl_eq_inr := Symbol.nonterminal.inj nt_match
      simp at inl_eq_inr
  clear hyp_tran
  rw [w₁eq] at hyp_deri
  have hope_result := big_induction hyp_deri
  clear * - hope_result
  rcases hope_result with ⟨x, y, deri_x, deri_y, concat_xy⟩
  use w.take x.length
  constructor
  · clear deri_y
    change g₁.Derives [Symbol.nonterminal g₁.initial] ((w.take x.length).map Symbol.terminal)
    convert deri_x
    clear deri_x
    have xylen := correspondingStrings_length concat_xy
    rw [List.length_append] at xylen
    repeat rw [List.length_map] at xylen
    apply List.ext_getElem
    · simpa using Nat.le.intro xylen
    intros i iltwl iltxl
    have i_lt_lenl : i < (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt)).length := by
      rw [List.length_append, List.length_map]
      exact Nat.lt_add_right (y.map (wrapSymbol₂ g₁.nt)).length iltxl
    have i_lt_lenr : i < (w.map (Symbol.terminal (N := nnn T g₁.nt g₂.nt))).length := by
      simp_all
    have equivalent_ith := correspondingStrings_getElem i_lt_lenl i_lt_lenr concat_xy
    have hxyg₂ : (x.map (wrapSymbol₁ g₂.nt) ++ y.map (wrapSymbol₂ g₁.nt))[i]'i_lt_lenl = wrapSymbol₁
      g₂.nt (x[i]'iltxl) := by
      simp_all
    rw [hxyg₂, List.getElem_map] at equivalent_ith
    aesop (add simp nnn) (add simp wrapSymbol₁) (add simp correspondingSymbols)
  use w.drop x.length
  constructor
  · clear deri_x
    change g₂.Derives [Symbol.nonterminal g₂.initial] ((w.drop x.length).map Symbol.terminal)
    convert deri_y
    clear deri_y
    have xylen := correspondingStrings_length concat_xy
    rw [List.length_append] at xylen
    have remaining : (w.drop x.length).map Symbol.terminal = y := by
      ext1 i
      by_cases hiy : i ≥ y.length
      · convert_to none = none
        · have ylen : y.length = ((w.drop x.length).map (@Symbol.terminal T g₂.nt)).length := by
            clear * - xylen
            rw [List.length_map, List.length_drop]
            simp only [List.length_map, bigGrammar_nt] at xylen
            exact Nat.eq_sub_of_add_eq' xylen
          rw [ylen] at hiy
          exact List.getElem?_eq_none_iff.← hiy
        · exact List.getElem?_eq_none_iff.← hiy
        rfl
      push Not at hiy
      rw [←List.take_append_drop (x.map (wrapSymbol₁ g₂.nt)).length (w.map Symbol.terminal)]
        at concat_xy
      have equivalent_second_parts :
        correspondingStrings
          (y.map (wrapSymbol₂ g₁.nt))
          ((w.map Symbol.terminal).drop (x.map (wrapSymbol₁ g₂.nt)).length) := by
        convert correspondingStrings_drop (x.map (wrapSymbol₁ g₂.nt)).length concat_xy
        · rw [List.drop_left]
        · rw [List.take_append_drop]
      have i_lt_len_lwy : i < (y.map (wrapSymbol₂ g₁.nt)).length := by
        rwa [List.length_map]
      have i_lt_len_dxw :
          i < ((w.map (Symbol.terminal (N := g₂.nt))).drop x.length).length := by
        simp only [List.length_map, bigGrammar_nt] at xylen
        rw [List.length_drop, List.length_map, ←xylen]
        convert i_lt_len_lwy
        rw [List.length_map, add_comm, Nat.add_sub_assoc (by rfl), Nat.sub_self, Nat.add_zero]
      have i_lt_len_mtw :
          i < ((w.drop x.length).map (Symbol.terminal (N := g₂.nt))).length := by
        rwa [List.map_drop]
      have goal_as_ith_drop : y[i]'hiy
        = (List.drop x.length (w.map Symbol.terminal))[i]'i_lt_len_dxw := by
        have xli_lt_len_w : x.length + i < w.length := by
          apply Nat.add_lt_of_lt_sub'
          simpa using i_lt_len_dxw
        have eqiv_symb := correspondingStrings_getElem i_lt_len_lwy (by simpa using i_lt_len_dxw)
          equivalent_second_parts
        simp only [correspondingSymbols] at eqiv_symb
        split at eqiv_symb <;> aesop (add simp nnn) (add simp wrapSymbol₂)
      have goal_as_some_ith : some (y[i]'hiy) = some
        (((w.drop x.length).map Symbol.terminal)[i]'i_lt_len_mtw) := by
        rw [goal_as_ith_drop]
        congr
        symm
        apply List.map_drop
      simp_all
    repeat rw [List.length_map] at xylen
    exact remaining
  apply List.take_append_drop

end very_complicated

end hard_direction


/-- The class of grammar-generated languages is closed under concatenation. -/
theorem GG_of_GG_c_GG (L₁ : Language T) (L₂ : Language T) :
  Language.IsGG L₁ ∧ Language.IsGG L₂ → Language.IsGG (L₁ * L₂) :=
by
  rintro ⟨⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩
  use bigGrammar g₁ g₂
  exact Set.eq_of_subset_of_subset ↓in_concatenated_of_in_big ↓in_big_of_in_concatenated

end Chomsky
