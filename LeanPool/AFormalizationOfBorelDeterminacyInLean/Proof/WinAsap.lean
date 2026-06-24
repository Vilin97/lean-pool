/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.GaleStewart

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.WinAsap

Auxiliary declarations for the Borel determinacy formalization.
-/


lemma choose_eq {α : Type*} {p q : α → Prop} (hpq : ∀ a, p a ↔ q a) (h : ∃ a, p a) :
  h.choose = (by simpa [hpq] using h : ∃ a, q a).choose := by
  have : p = q := funext fun x ↦ propext (hpq x)
  subst this; rfl
universe u in
lemma choose_eq' {α β : Type u} {p : α → Prop} {q : β → Prop} (hab : α = β)
  (hpq : ∀ a, p a ↔ q (cast hab a)) (h : ∃ a, p a) :
  HEq h.choose (by subst hab; simpa [hpq] using h : ∃ b, q b).choose := by
  subst hab; apply heq_of_eq; apply choose_eq hpq

namespace GaleStewartGame.PreStrategy
open Descriptive
open Stream'.Discrete Tree Game

noncomputable section «Section1»
variable {A : Type*} (G : Game A) (p : Player)
/-- whether there exists a prefix of `x` that is a winning position for `p` -/
def WinningPrefix (x : List A) := ∃ (n : ℕ),
  (G.residual (x.take n)).ExistsWinning (p.residual (x.take n))
lemma winningPrefix_of_notMem {x} (h : x ∉ G.tree) : WinningPrefix G p x := by
  use x.length; simpa [residual_notMem G x h] using existsWinning_empty
variable {G p}
lemma _root_.GaleStewartGame.Game.WinningPosition.winningPrefix {x} (h : WinningPosition G x p) :
  WinningPrefix G (p.residual x) x := ⟨x.length, by simpa⟩
namespace WinningPrefix
lemma mem_defensiveQuasi (x : G.tree) (h : ¬ WinningPrefix G p.swap x.val) hpr :
  x.val ∈ (defensiveQuasi G p hpr).1.subtree := by
  apply subtree_induction (S := ⊤) (by simp)
  intro n hn hx hp _
  conv => simp [defensiveQuasi, tryAndElse, defensivePre, preserveProp, ExtensionsAt.val']
  intro _ hW; apply h; use n + 1
  rwa [show Player.residual (List.take (n + 1) x.val) p.swap = Player.zero by synthIsPosition]
lemma winningPrefix_of_residual {x y : List A}
  (hW : WinningPrefix (G.residual x) p y) :
  WinningPrefix G (p.residual x) (x ++ y) := by
  obtain ⟨n, hW⟩ := hW; use x.length + n
  convert hW using 1
  · simp_rw [List.take_length_add_append, residual_append]
  · synthIsPosition
section «Section2»
variable {x : List A} (h : WinningPrefix G p x)

/-- the length of the shortest prefix of `x` that is winning for `p` -/
noncomputable def num := by
  classical
  exact Nat.find h
lemma num_spec : (G.residual (x.take h.num)).ExistsWinning (p.residual (x.take h.num)) := by
  classical
  exact Nat.find_spec h
@[simp] lemma num_le_length : h.num ≤ x.length := by
  classical
  rw [← _root_.not_imp_self (a := _ ≤ _)] --change after update
  intro hn; apply Nat.find_le
  have h' := h.num_spec
  rwa [List.take_of_length_le] at * <;> omega
--the choices of Exists.choose here just depend on x|n, not x
lemma take_num {y} : (x ++ y).take h.num = x.take h.num := by simp
lemma extend (y : List A) (h : WinningPrefix G p x) : WinningPrefix G p (x ++ y) :=
  ⟨h.num, by simpa [take_num] using h.num_spec⟩
lemma of_take {n} (h : WinningPrefix G p (x.take n)) : WinningPrefix G p x := by
  simpa using h.extend (x.drop n)
lemma of_prefix {y} (xy : x <+: y) (h : WinningPrefix G p x) : WinningPrefix G p y := by
  obtain ⟨z, rfl⟩ := xy; exact h.extend z
lemma of_prefix' {G' p' y} (xy : x <+: y) (hG : G = G') (hp : p = p')
  (h : WinningPrefix G p x) : WinningPrefix G' p' y := by
  subst hG hp; exact h.of_prefix xy

lemma extend_num y : (h.extend y).num = h.num := by
  classical
  apply le_antisymm <| Nat.find_le <| by simpa [take_num] using h.num_spec
  by_contra h'; rw [Nat.le_find_iff] at h'; push Not at h'; obtain ⟨m, hmn, hm⟩ := h'
  rw [List.take_append_of_le_length (hmn.le.trans h.num_le_length)] at hm
  rw [num, Nat.lt_find_iff] at hmn; exact hmn m le_rfl hm
lemma prefix_num {G' p' y} (xy : x <+: y) (hG : G = G') (hp : p = p') :
  (h.of_prefix' xy hG hp).num = h.num := by
  subst hG hp; obtain ⟨z, rfl⟩ := xy; exact h.extend_num z
end «Section2»

variable {x : List A} (h : WinningPrefix G p x)
/-- the winning strategy chosen for the shortest winning prefix of `x` -/
def strat := h.num_spec.choose
lemma strat_winning : h.strat.pre.IsWinning := h.num_spec.choose_spec

lemma extracted_1 {G : Game A} {p : Player} {x : List A} (h : WinningPrefix G p x) {y : List A} :
  Strategy (G.residual ((x ++ y).take (h.extend y).num)).tree
    (p.residual ((x ++ y).take (h.extend y).num)) =
  Strategy (G.residual (x.take h.num)).tree
    (p.residual (x.take h.num)) := by
  rw [h.extend_num, h.take_num]
lemma extracted_2 {G : Game A} {p : Player} {x : List A} (h : WinningPrefix G p x) {y : List A}
  (a : Strategy (G.residual ((x ++ y).take (h.extend y).num)).tree
    (p.residual ((x ++ y).take (h.extend y).num))) :
  a.pre.IsWinning ↔ (cast h.extracted_1 a).pre.IsWinning := by
  congr! 1
  · rw [h.extend_num, h.take_num]
  · rw [h.extend_num, h.take_num]
  · congr!
    exact (cast_heq _ _).symm
lemma extend_strat y : HEq (h.extend y).strat h.strat :=
  choose_eq' --even explicit arguments do not help with performance
    (α := Strategy (G.residual ((x ++ y).take (h.extend y).num)).tree
      (p.residual ((x ++ y).take (h.extend y).num)))
    (β := Strategy (G.residual (x.take h.num)).tree (p.residual (x.take h.num)))
    (@extracted_1 A G p x h y) (@extracted_2 A G p x h y)
    (@Nat.find_spec (fun n ↦ ExistsWinning (G.residual ((x ++ y).take n))
    (p.residual ((x ++ y).take n))) (fun _ ↦ Classical.propDecidable _) (extend y h))

lemma extend_strat_subtree y : (h.extend y).strat.pre.subtree = h.strat.pre.subtree := by
  congr! 2 <;> try rw [h.extend_num, h.take_num]
  apply extend_strat
lemma prefix_strat_subtree {G' p' y} (xy : x <+: y) (hG : G = G') (hp : p = p') :
  (h.of_prefix' xy hG hp).strat.pre.subtree = h.strat.pre.subtree := by
  subst hG hp; obtain ⟨z, rfl⟩ := xy; exact h.extend_strat_subtree z
lemma strat_eval_val_congr {p p'} (U U' : tree A) (hU : U = U') (hep : p = p')
  (S : Strategy U p) (S' : Strategy U' p')
  (h : HEq S S') (x : U) hp :
  (S x hp).val = (S' ⟨x.val, by subst hU; exact x.prop⟩ (by subst hU hep h; exact hp)).val := by
  subst hU hep h; rfl
--this lemma is new and could simplify things below
lemma prefix_strat_apply {G' p' y} (xy : x <+: y) (hG : G = G') (hp : p = p') {a}
  (hpa) :
  have xy' : y.take (h.of_prefix' xy hG hp).num = x.take h.num := by
    rw [h.prefix_num xy hG hp]
    obtain ⟨z, rfl⟩ := xy
    rw [List.take_append_of_le_length (by simp)]
  ((h.of_prefix' xy hG hp).strat a hpa).val =
    (h.strat
      ⟨a.val, by as_aux_lemma =>
        subst hG
        simpa [xy'] using a.prop⟩
      (by as_aux_lemma =>
        subst hG hp
        simpa [xy'] using hpa)).val := by
  have xy' : y.take (h.of_prefix' xy hG hp).num = x.take h.num := by
    rw [h.prefix_num xy hG hp]
    obtain ⟨z, rfl⟩ := xy
    rw [List.take_append_of_le_length (by simp)]
  subst hG hp; dsimp
  apply strat_eval_val_congr _ (G.residual (x.take h.num)).tree (by rw [xy']) (by rw [xy'])
  obtain ⟨z, rfl⟩ := xy; apply extend_strat
lemma prefix_strat_apply' {G' p' y} (xy : x <+: y) (hG : G = G') (hp : p = p') {a a'}
  (ha : a.val = a'.val) (hpa) :
  have xy' : y.take (h.of_prefix' xy hG hp).num = x.take h.num := by
    rw [h.prefix_num xy hG hp]; obtain ⟨z, rfl⟩ := xy; rw [List.take_append_of_le_length (by simp)]
  ((h.of_prefix' xy hG hp).strat a hpa).val = (h.strat a' (by
    as_aux_lemma => subst hG hp; simpa [xy', ha] using hpa)).val := by
  rw [h.prefix_strat_apply xy hG hp]; congr!

/-- Auxiliary declaration for the Borel determinacy formalization. -/
lemma shrink : WinningPrefix G p (x.take h.num) :=
  ⟨h.num, by simpa [List.take_take] using h.num_spec⟩
lemma shrink_num : h.shrink.num = h.num := by
  symm; simpa using h.shrink.extend_num (x.drop h.num)
lemma shrink_strat : HEq h.shrink.strat h.strat := by
  symm; apply HEq.trans _ <| h.shrink.extend_strat (x.drop h.num)
  congr!; simp

--TODO nicer than HEq?
lemma lem1 {y} : (x.take h.num ++ y).take (h.shrink.extend y).num = x.take h.num := by
  rw [List.take_append_of_le_length, h.shrink.extend_num, h.shrink_num, List.take_take, min_self]
  simp [h.shrink.extend_num, h.shrink_num, h.num_le_length]
lemma lem2 {y} : (x.take h.num ++ y).drop (h.shrink.extend y).num = y := by
  rw [List.drop_append_of_le_length, h.shrink.extend_num, h.shrink_num]
    <;> simp [h.shrink.extend_num, h.shrink_num, h.num_le_length]
lemma val_cast {T y} (h : x = y) (a : subAt T x) (b : subAt T y) :
  cast (by rw [h]) a = b ↔ a.val = b.val := by subst h; simp
lemma val_cast' {T T' : tree A} {b : T} {b' : T'} (hT : T = T')
  (h : b = cast (by rw [hT]) b') (x : ExtensionsAt b) (y : ExtensionsAt b') :
  cast (by subst hT h; rfl) x = y ↔ x.val = y.val := by
    subst h hT; symm; apply Subtype.val_inj
lemma cast_val {T y} (h : x = y) (a : subAt T x) :
  Subtype.val (cast (by rw [h]) a) = a.val := by
  symm; apply (val_cast h a (cast (by rw [h]) a)).mp; rfl
lemma hEq_drop_take {y} (hy : y ∈ subAt G.tree (x.take h.num)) (hxy) :
  HEq (Tree.drop _ (h.shrink.extend y).num
  (⟨List.take h.num x ++ y, hxy⟩ : G.tree)) (⟨y, hy⟩ : subAt _ _) := by
  rw [← cast_eq_iff_heq (e := by simp [lem1])]
  apply Subtype.ext
  conv => simp [Tree.drop, lem2, lem1]
  exact cast_val (h := by simp [lem1]) _
universe u in
lemma congr_2_heq {α α'} {β : α → Prop} {γ : α → Type u} {β' : α → Prop} {γ' : α → Type u}
  {a : α} {a' : α'} (ha : HEq a a') (f : ∀ a : α, β a → γ a)
  (f' : ∀ a'' : α', β' (cast (by cases ha; rfl) a'') → γ' (cast (by cases ha; rfl) a''))
  (b : β a) (b' : β' (cast (by cases ha; rfl) a'))
  (hb : β = β') (hct : γ = γ') (hf : HEq f f') : HEq (f a b) (f' a' b') := by
  cases ha; subst hct hb; cases hf; rfl
universe u in
lemma congr_2_heq' {α α'} {β : α → Prop} {γ : α → Type u} {β' : α' → Prop} {γ' : α' → Type u}
  {a : α} {a' : α'} (ha : HEq a a') (f : ∀ a : α, β a → γ a)
  (f' : ∀ a' : α', β' a' → γ' a')
  (b : β a) (b' : β' (cast (by cases ha; rfl) a'))
  (hB : HEq β β') (hC : HEq γ γ') (hf : HEq f f') : HEq (f a b) (f' a' b') := by
  cases ha
  apply congr_2_heq (hf := hf) (ha := by rfl)
  · simpa using hB
  · simpa using hC
lemma extend_strat_apply {y} {a : (G.residual _).tree} {a' : (G.residual (x.take h.num)).tree}
  (ha : HEq a a') {hpa} {hpa'} :
  ((h.shrink.extend y).strat a hpa).val = (h.strat a' hpa').val := by
  have h' := val_cast' (by rw [lem1]) (by symm; rw [cast_eq_iff_heq]; exact ha.symm)
    ((h.shrink.extend y).strat a hpa) (h.strat a' hpa')
  apply h'.mp; apply cast_eq_iff_heq.mpr
  apply congr_2_heq' ha (h.shrink.extend y).strat h.strat
  · rw [lem1]
  · rw [lem1]
  · apply HEq.trans
    · apply h.shrink.extend_strat
    · apply h.shrink_strat
end WinningPrefix

variable (G p)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def winAsap : PreStrategy G.tree p := by
  classical
  exact fun x hp ↦
    if h : WinningPrefix G p x.val then
      {ExtensionsAt.drop.symm <| h.strat (Tree.drop _ h.num x) (by synthIsPosition)}
    else Set.univ
lemma mem_winAsap_subtree_of_no_prefix
  {x} {a} (h : ¬ WinningPrefix G p x) (ha : x ++ [a] ∈ G.tree) :
  x ++ [a] ∈ (winAsap G p).subtree := by
  apply subtree_induction (S := ⊤) (by simpa); intro n hn _ hp
  conv => simp [winAsap]
  split_ifs with hW
  · cases h (by
      simp at hn
      simpa [List.take_append_of_le_length, hn] using hW.extend (x.drop n))
  · trivial
lemma winAsap_subtree {x} (h : WinningPrefix G p x) :
  Tree.subAt (winAsap G p).subtree (x.take h.num) = h.strat.pre.subtree := by --TODO nice proof
  ext y
  induction y using List.reverseRecOn with
  | nil =>
    simp only [mem_subAt, List.append_nil, residual_tree, subtree_ne]
    use ((winAsap G p).subtree_sub ·)
    intro h'; rcases h.num.eq_zero_or_eq_succ_pred with h'' | h''
    · simpa [h''] using h'
    · dsimp at h''
      have hlen : h.num - 1 < x.length := by have := h.num_le_length; omega
      rw [h'', ← List.take_concat_get' _ _ hlen]
      apply mem_winAsap_subtree_of_no_prefix
      · intro h'; have hl := h'.num_le_length
        simp [← h'.extend_num (y := x.drop (h.num - 1))] at hl
        omega
      · rwa [List.take_concat_get' _ _ hlen, ← h'']
  | append_singleton y a ih =>
    by_cases hp : IsPosition y (p.residual (x.take h.num)) <;>
      (constructor <;> (intro h'; conv at ih => simp [mem_of_append h', - residual_tree]))
    · rw [subtree_compatible_iff _ ⟨y, ih⟩ (by as_aux_lemma => synthIsPosition)]
      use (winAsap G p).subtree_sub h'
      conv at h' => simp [← List.append_assoc]
      rw [subtree_compatible_iff _ ⟨_, mem_of_append h'⟩
        (by as_aux_lemma => synthIsPosition)] at h'
      conv at h' => simp [winAsap, h.shrink.extend y]
      conv => simp [winAsap, h.shrink.extend y]
      obtain ⟨_, h'⟩ := h'; apply_fun Subtype.val at h'
      apply ExtensionsAt.ext (x := (PreStrategy.subtreeIncl _ ⟨_, _⟩)) --why necessary?
      rw [h']
      conv => simp
      apply h.extend_strat_apply; apply h.hEq_drop_take
    · conv => simp [← List.append_assoc]
      rw [subtree_compatible_iff _ ⟨_, ih⟩ (by as_aux_lemma => synthIsPosition)]
      simp_rw [List.append_assoc]
      use h.strat.pre.subtree_sub h'
      rw [subtree_compatible_iff _ ⟨_, mem_of_append h'⟩
        (by as_aux_lemma => synthIsPosition)] at h'
      obtain ⟨_, h'⟩ := h'
      have hval := congrArg Subtype.val h'
      conv => simp [winAsap, h.shrink.extend y]
      apply ExtensionsAt.ext (x := (PreStrategy.subtreeIncl _ ⟨_, _⟩)) --why necessary?
      rw [hval]
      dsimp only [PreStrategy.subtreeIncl]
      symm
      apply h.extend_strat_apply
      apply h.hEq_drop_take
    · rw [subtree_fair _ ⟨y, ih⟩ (by as_aux_lemma => synthIsPosition)]
      exact (winAsap G p).subtree_sub h'
    · conv => simp [← List.append_assoc]
      rw [subtree_fair _ ⟨_, ih⟩ (by as_aux_lemma => synthIsPosition)]
      simpa [subAt, List.append_assoc] using h.strat.pre.subtree_sub h'
lemma winAsap_body (x : body (winAsap G p).subtree)
  (h : ∃ n, WinningPrefix G p (x.val.take n)) :
  ⟨x.val, body_mono (subtree_sub _) x.prop⟩ ∈ p.payoff G := by
  obtain ⟨N, h⟩ := h; have hN : h.num ≤ N := by simpa using h.num_le_length
  suffices x.val.drop h.num ∈ body h.strat.pre.subtree by
    have hW := h.strat_winning this
    conv at hW => simp [hN]
    obtain ⟨_, hpay⟩ := hW
    change (body.append (Stream'.take h.num x.val) ⟨Stream'.drop h.num x.val, _⟩ : body G.tree) ∈
      p.payoff G at hpay
    simpa [body.append, Stream'.append_take_drop] using hpay
  apply mem_body_of_take 0; intro n _
  rw [← winAsap_subtree]; simp [hN]
lemma winAsap_body' (x : body (winAsap G p).followUntilWon.subtree)
  (h : ∃ n, WinningPrefix G p (x.val.take n)) :
  ⟨x.val, body_mono (subtree_sub _) x.prop⟩ ∈ p.payoff G := by
  rcases followUntilWon_body _ x.prop with h' | h'
  · exact winAsap_body _ _ ⟨x.val, h'⟩ h
  · simpa [body_mono (subtree_sub _) x.prop] using h'
end «Section1»

end GaleStewartGame.PreStrategy
