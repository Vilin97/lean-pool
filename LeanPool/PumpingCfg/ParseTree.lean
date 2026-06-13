/-
Copyright (c) 2026 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import LeanPool.PumpingCfg.ChomskyNormalForm.Basic
import LeanPool.PumpingCfg.ToMathlib

/-!
# Parse trees for Chomsky normal form grammars

Defines `ChomskyNormalFormGrammar.parseTree`, binary parse trees for grammars in Chomsky
normal form, together with their yield and the subtree relation used by the pumping argument.
-/

universe uN uT

variable {T : Type uT}

namespace ChomskyNormalFormGrammar

variable {g : ChomskyNormalFormGrammar T}

-- TODO to be included in file: ChomskyNormalformgrammar

section parseTree

/-- A `parseTree n` encodes a `ChomskyNormalFormGrammar` derivation of a word from a nonterminal
`n` -/
inductive parseTree : g.NT → Type _ where
  /-- Single rule application transforming a nonterminal into a terminal. -/
  | leaf {n : g.NT} (t : T)
      (hnt : (ChomskyNormalFormRule.leaf n t) ∈ g.rules) : parseTree n
  /-- Application of rule of the second kind. -/
  | node {n c₁ c₂ : g.NT} (t₁ : parseTree c₁) (t₂ : parseTree c₂)
      (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) : parseTree n

namespace parseTree

/-- The `yield` of a tree is the word the tree derives -/
def yield {n : g.NT} (p : parseTree n) : List T :=
  match p with
  | leaf t _ => [t]
  | node t₁ t₂ _ => yield t₁ ++ yield t₂

/-- The `height` of a tree -/
def height {n : g.NT} (p : parseTree n) : ℕ :=
  match p with
  | leaf _ _ => 1
  | node t₁ t₂ _ => max (height t₁) (height t₂) + 1

/-- `IsSubTreeOf p₁ p₂` encodes that `p₁` is a subtree of `p₂` -/
inductive IsSubtreeOf : {n₁ : g.NT} → {n₂ : g.NT} → parseTree n₁ → parseTree n₂ → Prop where
  /-- A parse tree is a subtree of itself -/
  | eq {n : g.NT} (p : parseTree n) : IsSubtreeOf p p
  /-- If `p₁` is a subtree of `p₂`, it is also a subtree of `node p₂ p₃` -/
  | left_sub {l r n₁ n₂ : g.NT} (p₁ : parseTree l) (p₂ : parseTree r) (p : parseTree n₂)
      (hrn₁ : (ChomskyNormalFormRule.node n₁ l r) ∈ g.rules) (hpp₁ : IsSubtreeOf p p₁) :
      IsSubtreeOf p (node p₁ p₂ hrn₁)
  /-- If `p₁` is a subtree of `p₃`, it is also a subtree of `node p₂ p₃` -/
  | right_sub {l r n₁ n₂ : g.NT} (p₁ : parseTree l) (p₂ : parseTree r) (p : parseTree n₂)
      (hrn₁ : (ChomskyNormalFormRule.node n₁ l r) ∈ g.rules) (hpp₂ : IsSubtreeOf p p₂) :
      IsSubtreeOf p (node p₁ p₂ hrn₁)

variable {n : g.NT} {p : parseTree n}

lemma yield_derives : g.Derives [Symbol.nonterminal n] (p.yield.map Symbol.terminal) := by
  induction p with
  | leaf t hg =>
    exact Produces.single ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
  | node l r hg ihl ihr =>
    simp only [yield]
    apply Produces.trans_derives ⟨_, hg, ChomskyNormalFormRule.Rewrites.input_output⟩
    rw [ChomskyNormalFormRule.output, List.map_append, ← List.singleton_append]
    exact (ihr.append_left _).trans (ihl.append_right _)

lemma height_pos : p.height > 0 := by cases p <;> simp [height]

lemma yield_length_le_two_pow_height : p.yield.length ≤ 2 ^ (p.height - 1) := by
  induction p with
  | leaf => simp [yield, height]
  | node t₁ t₂ hpg ih₁ ih₂=>
    simp only [yield, height, List.length_append, Nat.add_one_sub_one]
    have ht : t₁.yield.length + t₂.yield.length ≤ 2 ^ (t₁.height - 1) + 2 ^ (t₂.height - 1) := by
      omega
    have ht' : 2 ^ (t₁.height - 1) + 2 ^ (t₂.height - 1)
        ≤ 2 ^ (max t₁.height t₂.height - 1) + 2 ^ (max t₁.height t₂.height - 1) := by
      apply Nat.add_le_add <;> apply Nat.pow_le_pow_right <;> omega
    apply le_trans ht
    apply le_trans ht'
    have ht'' : max t₁.height t₂.height = max t₁.height t₂.height - 1 + 1 := by
      rw [Nat.sub_one_add_one]
      have : 0 < max t₁.height t₂.height := lt_sup_of_lt_left t₁.height_pos
      omega
    nth_rewrite 3 [ht'']
    rw [Nat.two_pow_succ]

lemma yield_length_pos : p.yield.length > 0 := by
  induction p with
  | leaf => simp [yield]
  | node =>
    simp only [yield, List.length_append]
    omega


lemma subtree_decomposition {n₁ n₂ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂}
    (hpp : IsSubtreeOf p₂ p₁) :
    ∃ u v, p₁.yield = u ++ p₂.yield ++ v ∧
      g.Derives [Symbol.nonterminal n₁]
        (u.map Symbol.terminal ++ [Symbol.nonterminal n₂] ++ v.map Symbol.terminal) := by
  induction hpp with
  | eq =>
    use [], []
    simpa using Derives.refl [Symbol.nonterminal _]
  | left_sub q₁ q₂ p₂ hrn hpq₁ ih =>
    simp only [yield, List.append_assoc]
    obtain ⟨u, v, huv, hguv⟩ := ih
    refine ⟨u, v ++ q₂.yield, by simp [huv], ?_⟩
    apply (Produces.input_output hrn).trans_derives
    simp only [ChomskyNormalFormRule.output]
    nth_rewrite 3 [← List.singleton_append]
    rw [← List.singleton_append, List.map_append, ← List.append_assoc, ← List.append_assoc]
    exact (Derives.append_left q₂.yield_derives _).trans (hguv.append_right _)
  | right_sub q₁ q₂ p₂ hrn hpq₁ ih =>
    simp only [yield, List.append_assoc]
    obtain ⟨u, v, huv, hguv⟩ := ih
    refine ⟨q₁.yield ++ u, v, by simp [huv], ?_⟩
    apply (Produces.input_output hrn).trans_derives
    simp only [ChomskyNormalFormRule.output]
    nth_rewrite 3 [← List.singleton_append]
    rw [← List.singleton_append, List.map_append, List.append_assoc]
    nth_rewrite 2 [← List.append_assoc]
    exact (hguv.append_left _).trans (Derives.append_right q₁.yield_derives _)

lemma strict_subtree_decomposition {n : g.NT} {p₁ : parseTree n} {p₂ : parseTree n}
    (hpp : IsSubtreeOf p₂ p₁) (hne : p₁ ≠ p₂) :
    ∃ u v, p₁.yield = u ++ p₂.yield ++ v ∧ (u ++ v).length > 0
      ∧ g.Derives [Symbol.nonterminal n]
        (u.map Symbol.terminal ++ [Symbol.nonterminal n] ++ v.map Symbol.terminal) := by
  cases hpp with
  | eq => contradiction
  | left_sub q₁ q₂ p₂ hrn hp₂ =>
    obtain ⟨u, v, huv, hguv⟩ := subtree_decomposition hp₂
    simp_rw [yield, huv]
    refine ⟨u, v ++ q₂.yield, by simp, ?_, ?_⟩
    · have h := q₂.yield_length_pos
      repeat rw [List.length_append]
      omega
    · apply (Produces.input_output hrn).trans_derives
      simp only [ChomskyNormalFormRule.output]
      rw [← List.singleton_append, List.map_append, ← List.append_assoc]
      exact Derives.trans (Derives.append_left q₂.yield_derives _) (Derives.append_right hguv _)
  | right_sub q₁ q₂ p₂ hrn hp₂ =>
    obtain ⟨u, v, huv, hguv⟩ := subtree_decomposition hp₂
    simp_rw [yield, huv]
    refine ⟨q₁.yield ++ u, v, by simp, ?_, ?_⟩
    · have := q₁.yield_length_pos
      repeat rw [List.length_append]
      omega
    · apply (Produces.input_output hrn).trans_derives
      simp only [ChomskyNormalFormRule.output]
      rw [← List.singleton_append, List.map_append, List.append_assoc, List.append_assoc]
      nth_rewrite 2 [← List.append_assoc]
      exact (hguv.append_left _).trans (Derives.append_right q₁.yield_derives _)

@[refl]
lemma IsSubtreeOf.refl {n : g.NT} {p : parseTree n} : p.IsSubtreeOf p := IsSubtreeOf.eq p

lemma IsSubtreeOf.trans {n₁ n₂ n₃ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂}
    {p₃ : parseTree n₃} (hp₁ : p₁.IsSubtreeOf p₂) (hp₂ : p₂.IsSubtreeOf p₃) :
    p₁.IsSubtreeOf p₃ := by
  induction hp₂ with
  | eq => exact hp₁
  | left_sub _ _ _ _ _ ih => exact left_sub _ _ _ _ (ih hp₁)
  | right_sub _ _ _ _ _ ih => exact right_sub _ _ _ _ (ih hp₁)

lemma subtree_height {n₁ n₂ : g.NT} {p₁ : parseTree n₁} {p₂ : parseTree n₂}
    (hpp : p₁.IsSubtreeOf p₂) :
    p₁.height ≤ p₂.height := by
    induction hpp with
    | eq => simp
    | left_sub _ _ _ _ _ ht | right_sub _ _ _ _ _ ht =>
      apply ht.trans
      simp only [height]
      omega

end parseTree

lemma Produces.rule {n : g.NT} {u : List (Symbol T g.NT)}
    (hnu : g.Produces [Symbol.nonterminal n] u) :
    ∃ r ∈ g.rules, r.input = n ∧ r.output = u := by
  obtain ⟨r, hrg, hnu⟩ := hnu
  cases hnu
  · exact ⟨_, hrg, rfl, rfl⟩
  · exact ⟨_, hrg, rfl, rfl⟩
  · contradiction

lemma DerivesIn.terminal_refl {u v : List T} {m : ℕ}
    (huv : g.DerivesIn (u.map Symbol.terminal) (v.map Symbol.terminal) m) :
    u = v := by
  cases m with
  | zero =>
    apply Function.Injective.list_map _ huv.zero_steps_eq
    apply Symbol.terminal.inj
  | succ m =>
    obtain ⟨w, huw, hwv⟩ := huv.head_of_succ
    obtain ⟨r, hrg, huw⟩ := huw
    exfalso
    exact huw.word

private lemma DerivesIn.yield_rec {n : g.NT} {u : List T} {m : ℕ}
    (hvu : g.DerivesIn [Symbol.nonterminal n] (u.map Symbol.terminal) m) :
    ∃ p : parseTree n, p.yield = u := by
  cases m with
  | zero =>
    apply DerivesIn.zero_steps_eq at hvu
    cases u <;> simp at hvu
  | succ m =>
    obtain ⟨w, hvw, hwu⟩ := hvu.head_of_succ
    obtain ⟨r, hrg, hr₁, hr₂⟩ := hvw.rule
    cases r with
    | leaf n t =>
      rw [ChomskyNormalFormRule.input] at hr₁
      rw [ChomskyNormalFormRule.output] at hr₂
      rw [hr₁] at hrg
      rw [← hr₂] at hwu
      exact ⟨parseTree.leaf t hrg, hwu.terminal_refl⟩
    | node nᵢ n₁ n₂ =>
      rw [ChomskyNormalFormRule.input] at hr₁
      rw [ChomskyNormalFormRule.output] at hr₂
      rw [hr₁] at hrg
      rw [← hr₂, ← List.singleton_append] at hwu
      obtain ⟨u₁, u₂, k₁, k₂, hu, hnu₁, hnu₂, hm⟩ := hwu.append_split
      rw [List.map_eq_append_iff] at hu
      obtain ⟨u₁', u₂', hu, hu₁, hu₂⟩ := hu
      rw [← hu₁] at hnu₁
      rw [← hu₂] at hnu₂
      obtain ⟨p₁, hp₁⟩ := hnu₁.yield_rec
      obtain ⟨p₂, hp₂⟩ := hnu₂.yield_rec
      use parseTree.node p₁ p₂ hrg
      unfold parseTree.yield
      rw [hp₁, hp₂, hu]

lemma Derives.yield {n : g.NT} {u : List T}
    (hnu : g.Derives [Symbol.nonterminal n] (u.map Symbol.terminal)) :
    ∃ p : parseTree n, p.yield = u := by
  rw [derives_iff_derivesIn] at hnu
  exact hnu.choose_spec.yield_rec

end parseTree

end ChomskyNormalFormGrammar
