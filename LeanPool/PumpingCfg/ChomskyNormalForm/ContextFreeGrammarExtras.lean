/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
import Mathlib.Computability.ContextFreeGrammar

/-!
# Extra lemmas about context-free grammars

Additions to `Mathlib.Computability.ContextFreeGrammar` from the authors'
in-review Mathlib branch (`alex-loitzl-cnf`) that are not yet available in the
Mathlib release pinned here: the step-counting derivation relation
`ContextFreeGrammar.DerivesIn` with its induction principles and splitting
lemmas, plus a few facts about `ContextFreeGrammar.Produces`.
-/

universe uT

variable {T : Type uT}

namespace ContextFreeGrammar

variable {g : ContextFreeGrammar T}

lemma Produces.input_output {r : ContextFreeRule T g.NT} (hrg : r ∈ g.rules) :
    g.Produces [.nonterminal r.input] r.output := ⟨r, hrg, ContextFreeRule.Rewrites.input_output⟩

lemma Produces.rule {n : g.NT} {u : List (Symbol T g.NT)}
    (hnu : g.Produces [Symbol.nonterminal n] u) :
    ⟨n, u⟩ ∈ g.rules := by
  obtain ⟨_, _, hr⟩ := hnu
  cases hr
  · rwa [List.append_nil]
  · contradiction

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
    {u : List (Symbol T g.NT)} (huv : g.Derives u v)
    (refl : P v (Derives.refl v))
    (head : ∀ {u w} (huw : g.Produces u w) (hwv : g.Derives w v),
      P w hwv → P u (hwv.head huw)) :
    P u huv := Relation.ReflTransGen.head_induction_on huv refl head

end ContextFreeGrammar

/-! Alternative definition of `ContextFreeGrammar.Derives` which allows to use well-founded
induction on derivations, by explicitely counting the number of steps of the transformation -/
section derivesIn

namespace ContextFreeGrammar

/-- Given a context-free grammar `g`, strings `u` and `v`, and number `n`
`g.DerivesIn u v n` means that `g` can transform `u` to `v` in `n` rewriting steps. -/
inductive DerivesIn (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop
  /-- 0 steps entail no transformation -/
  | refl (w : List (Symbol T g.NT)) : g.DerivesIn w w 0
  /-- n + 1 steps, if transforms `u` to `v` in n steps, and `v` to `w` in 1 step  -/
  | tail (u v w : List (Symbol T g.NT)) (n : ℕ) :
    g.DerivesIn u v n → g.Produces v w → g.DerivesIn u w n.succ

lemma derives_iff_derivesIn (g : ContextFreeGrammar T) (v w : List (Symbol T g.NT)) :
    g.Derives v w ↔ ∃ n : ℕ, g.DerivesIn v w n := by
  constructor
  · intro hgvw
    induction hgvw with
    | refl =>
      use 0
      left
    | tail _ last ih =>
      obtain ⟨n, ihn⟩ := ih
      exact ⟨n.succ, .tail _ _ _ _ ihn last⟩
  · intro ⟨n, hgvwn⟩
    induction hgvwn with
    | refl => rfl
    | tail _ _ _ _ last ih => exact ih.trans_produces last

lemma mem_language_iff_derivesIn (g : ContextFreeGrammar T) (w : List T) :
    w ∈ g.language ↔
      ∃ n, g.DerivesIn [Symbol.nonterminal g.initial] (w.map Symbol.terminal) n := by
  rw [mem_language_iff, derives_iff_derivesIn]

variable {g : ContextFreeGrammar T}

lemma DerivesIn.zero_steps (w : List (Symbol T g.NT)) : g.DerivesIn w w 0 := by left

lemma Produces.single_step {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) :
    g.DerivesIn v w 1 := .tail _ _ _ _ (.refl v) hvw

variable {n : ℕ}

lemma DerivesIn.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.DerivesIn u v n) (hvw : g.Produces v w) :
    g.DerivesIn u w n.succ := DerivesIn.tail u v w n huv hvw

@[trans]
lemma DerivesIn.trans {u v w : List (Symbol T g.NT)} {m : ℕ}
    (huv : g.DerivesIn u v n) (hvw : g.DerivesIn v w m) :
    g.DerivesIn u w (n + m) := by
  induction hvw with
  | refl => exact huv
  | tail _ _ _ _ last ih => exact trans_produces ih last

lemma Produces.trans_derivesIn {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.DerivesIn v w n) :
    g.DerivesIn u w n.succ := n.succ_eq_one_add ▸ huv.single_step.trans hvw

lemma DerivesIn.tail_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.DerivesIn u v n ∧ g.Produces v w := by
  cases huw with
  | tail v w n huv hvw =>
    use v

lemma DerivesIn.head_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.DerivesIn v w n := by
  induction n generalizing w with
  | zero =>
    cases huw with
    | tail v w n huv hvw =>
      cases huv with
      | refl => exact ⟨w, hvw, zero_steps w⟩
  | succ m ih =>
    cases huw with
    | tail v w n huv hvw =>
      obtain ⟨x, hux, hxv⟩ := ih huv
      exact ⟨x, hux, hxv.trans_produces hvw⟩

/-- Add extra prefix to context-free deriving (number of steps unchanged). -/
lemma DerivesIn.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (p ++ v) (p ++ w) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving (number of steps unchanged). -/
lemma DerivesIn.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (v ++ p) (w ++ p) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_right p

lemma DerivesIn.append_split {p q w : List (Symbol T g.NT)} {n : ℕ}
    (hpqw : g.DerivesIn (p ++ q) w n) :
    ∃ x y m₁ m₂,
      w = x ++ y ∧ g.DerivesIn p x m₁ ∧ g.DerivesIn q y m₂ ∧ n = m₁ + m₂ := by
  cases n with
  | zero =>
    cases hpqw
    exact ⟨p, q, 0, 0, rfl, DerivesIn.refl p, DerivesIn.refl q, rfl⟩
  | succ n =>
    obtain ⟨v, hp, hd⟩ := hpqw.head_of_succ
    obtain ⟨r, hrg, hr⟩ := hp
    obtain ⟨p', q', heq, hv⟩ := hr.exists_parts
    rw [List.append_assoc, List.singleton_append] at heq
    have append_eq_append_cons {p q x y : List (Symbol T g.NT)} {v : Symbol T g.NT}
        (hpqxvy : p ++ q = x ++ v :: y) :
        (∃ w, y = w ++ q ∧ p = x ++ v :: w) ∨ (∃ w, x = p ++ w ∧ q = w ++ v :: y) := by
      rw [List.append_eq_append_iff] at hpqxvy
      cases hpqxvy with
      | inl hxq =>
        obtain ⟨a, _, hq⟩ := hxq
        right
        use a
      | inr hpy =>
        obtain ⟨a, rfl, hq⟩ := hpy
        cases a with
        | nil =>
          right
          use []
          rw [hq, List.append_nil, List.append_nil]
          exact ⟨rfl, rfl⟩
        | cons d l =>
          left
          use l
          rw [List.cons_append, List.cons.injEq] at hq
          rw [hq.1]
          exact ⟨hq.2, rfl⟩
    rcases append_eq_append_cons heq with ⟨a, hq', hp⟩ | ⟨a, hp', hq⟩
    · rw [hv, hq', ← List.append_assoc] at hd
      obtain ⟨x, y, m₁, m₂, hw, hd₁, hd₂, hn⟩ := hd.append_split
      refine ⟨x, y, m₁ + 1, m₂, hw, ?_, hd₂, by omega⟩
      refine Produces.trans_derivesIn ⟨r, hrg, ?_⟩ hd₁
      rw [hp, ← List.singleton_append, ← List.append_assoc]
      apply r.rewrites_of_exists_parts
    · rw [hv, hp', List.append_assoc, List.append_assoc] at hd
      obtain ⟨x, y, m₁, m₂, hw, hd₁, hd₂, hn⟩ := hd.append_split
      refine ⟨x, y, m₁, m₂ + 1, hw, hd₁, ?_, by omega⟩
      apply Produces.trans_derivesIn
      · refine ⟨r, hrg, ?_⟩
        rw [hq, ← List.singleton_append, ← List.append_assoc]
        apply r.rewrites_of_exists_parts
      · rwa [List.append_assoc]

lemma DerivesIn.three_split {p q r w : List (Symbol T g.NT)} {n : ℕ}
    (hg : g.DerivesIn (p ++ q ++ r) w n) :
  ∃ x y z m₁ m₂ m₃, w = x ++ y ++ z ∧ g.DerivesIn p x m₁ ∧ g.DerivesIn q y m₂
    ∧ g.DerivesIn r z m₃ ∧ n = m₁ + m₂ + m₃ := by
  obtain ⟨x', z, m₁', m₃, hw₂, hd₁', hd₃, hn₂⟩ := hg.append_split
  obtain ⟨x, y, m₁, m₂, hw₁, hd₁, hd₂, hn₁⟩ := hd₁'.append_split
  exact ⟨x, y, z, m₁, m₂, m₃, hw₁ ▸ hw₂, hd₁, hd₂, hd₃, hn₁ ▸ hn₂⟩

@[elab_as_elim]
lemma DerivesIn.head_induction_on {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesIn a b n → Prop}
    (refl : P 0 b (DerivesIn.zero_steps b))
    (head : ∀ {n a c} (hac : g.Produces a c) (hcb : g.DerivesIn c b n),
      P n c hcb → P n.succ a (hac.trans_derivesIn hcb))
    {a : List (Symbol T g.NT)} (hab : g.DerivesIn a b n) :
    P n a hab := by
  induction hab with
  | refl => exact refl
  | tail _ _ _ _ last ih =>
    apply ih
    · exact head last _ refl
    · intro _ _ _ produc deriv
      exact head produc (deriv.tail _ _ _ _ last)

end ContextFreeGrammar

end derivesIn
