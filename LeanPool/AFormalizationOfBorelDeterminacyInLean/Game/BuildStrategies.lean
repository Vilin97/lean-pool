/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Games

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.BuildStrategies

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame
open Stream'.Discrete Descriptive Tree Game PreStrategy

variable {A : Type*} {T : tree A}
namespace PreStrategy

section «tryAndElse»
variable {p : Player}
/-- try following PreStrategy `planA` if possible, else follow `planB` -/
noncomputable def tryAndElse (planA planB : PreStrategy T p) :
  PreStrategy T p := by
  classical
  exact fun x hp ↦
    if (planA x hp).Nonempty then planA x hp else planB x hp
variable {planA planB planB' : PreStrategy T p}
@[gcongr] lemma tryAndElse_mono (hB : planB ≤ planB') :
  tryAndElse planA planB ≤ tryAndElse planA planB' := by
  intro _ _; unfold tryAndElse; split_ifs <;> [rfl; apply hB]
lemma quasi_of_planB (h : planB.IsQuasi) :
  (planA.tryAndElse planB).IsQuasi := by
  dsimp [IsQuasi, tryAndElse]; intros; split_ifs <;> [assumption; apply h]
lemma planA_sub : planA ≤ planA.tryAndElse planB := by
  intro _ _ _ h'; dsimp [tryAndElse]; split_ifs with h
  · exact h'
  · cases h ⟨_, h'⟩
lemma eq_planA (hQ : ∀ (x : planA.subtree) (hp : IsPosition x.val p),
  ∃ a, a ∈ planA ⟨x.val, x.prop.1⟩ hp) :
  (planA.tryAndElse planB).subtree = planA.subtree := by
  apply le_antisymm _ (subtree_mono planA_sub)
  intro x hx; apply subtree_induction hx
  intro _ _ hx _; unfold tryAndElse; split_ifs with h
  · exact id
  · cases h (hQ ⟨_, hx⟩ (by synthIsPosition))
@[simp] lemma tryAndElse_residual (x : List A) :
  (tryAndElse planA planB).residual x = tryAndElse (planA.residual x) (planB.residual x) := by
  ext1 y hp; dsimp [tryAndElse, PreStrategy.residual]
  split_ifs with h h' h' <;> try rfl
  · obtain ⟨a, h⟩ := h; cases h' ⟨⟨a.1, by simpa using a.2⟩, h⟩
  · obtain ⟨a, h'⟩ := h'; cases h ⟨⟨a.1, by simpa using a.2⟩, h'⟩
end «tryAndElse»

section «void»
variable {p : Player}
instance (T : tree A) (p : Player) : OrderBot (PreStrategy T p) where
  bot _ _ := ∅
  bot_le S _ := by simp
@[simp] lemma eval_bot x hp : (⊥ : PreStrategy T p) x hp = ∅ := rfl
instance (T : tree A) (p : Player) : OrderTop (PreStrategy T p) where
  top _ _ := Set.univ
  le_top S _ := by simp
@[simp] lemma eval_top x hp : (⊤ : PreStrategy T p) x hp = Set.univ := rfl
lemma top_isQuasi (h : IsPruned T) : (⊤ : PreStrategy T p).IsQuasi := by
  intro x _; obtain ⟨xa⟩ := h x
  rw [eval_top, ← Set.nonempty_iff_univ_nonempty]; exact ⟨xa⟩
@[simp] lemma top_subtree : (⊤ : PreStrategy T p).subtree = T :=
  CompleteSublattice.ext fun x ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, by simp⟩⟩
@[simp] lemma top_residual (x : List A) : (⊤ : PreStrategy T p).residual x = ⊤ := rfl

variable (A p) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def emptyStrategy : Strategy (A := A) ⊥ p := fun x _ ↦ x.prop.elim
@[simp] lemma emptyStrategy_subtree : (emptyStrategy A p).pre.subtree = ⊥ := by
  ext x
  simp [emptyStrategy, PreStrategy.subtree]
lemma existsWinning_empty : ExistsWinning (A := A) ⟨⊥, ∅⟩ p :=
  ⟨emptyStrategy A p, by simp [PreStrategy.IsWinning]⟩

lemma _root_.GaleStewartGame.Game.AllWinning.existsWinning
  {G : Game A} (h : G.AllWinning p) (hP : IsPruned G.tree) :
  G.ExistsWinning p := existsWinning_iff_quasi.mpr ⟨⟨⊤, top_isQuasi hP⟩,
  subset_trans (by simp) (Set.image_mono h.superset)⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev extQuasi (S : PreStrategy T p) (h : IsPruned T) : QuasiStrategy T p :=
  ⟨tryAndElse S ⊤, quasi_of_planB <| top_isQuasi h⟩
lemma eq_extQuasi (S : PreStrategy T p) (hT : IsPruned T)
  (h : ∀ (x : S.subtree) (hp : IsPosition x.val p), ∃ a, a ∈ S (S.subtreeIncl x) hp) :
  (S.extQuasi hT).1.subtree = S.subtree := eq_planA h
@[simp] lemma extQuasi_residual (S : PreStrategy T p) (h : IsPruned T) (x : List A) :
  (S.extQuasi h).residual x = (S.residual x).extQuasi (h.sub x) := by ext1; simp
end «void»

section «sew»
variable (f : ∀ a, [a] ∈ T → PreStrategy (subAt T [a]) Player.zero)
/-- sew a map from possible opponent moves to strategies in the resulting residual games to a
  strategy in the original game -/
def sew : PreStrategy T Player.one
  | ⟨[], _⟩, hp => by synthIsPosition
  | ⟨a :: x, hx⟩, hp => f a (singleton_mem T hx) ⟨x, hx⟩ (by synthIsPosition)
lemma sew_isQuasi (hf : ∀ a ha, (f a ha).IsQuasi) : (sew f).IsQuasi := by
  intro ⟨x, hx⟩ hp; rcases x
  · synthIsPosition
  · apply hf
lemma sew_subtree a x :
  a :: x ∈ (sew f).subtree ↔ ∃ h, x ∈ (f a h).subtree := ⟨
    fun ⟨ht, hs⟩ ↦ ⟨(singleton_mem T ht), ⟨ht, fun hpr hpo ↦
    hs (y := a :: _) (List.cons_prefix_cons.mpr ⟨rfl, hpr⟩) (by synthIsPosition)⟩⟩,
    fun ⟨_, ht, hs⟩ ↦ ⟨ht, by
      intro y b hpr hpo
      rcases y with (_ | ⟨a', y⟩) <;> [synthIsPosition; skip]
      obtain ⟨rfl, hpr'⟩ := List.cons_prefix_cons.mp hpr
      exact hs hpr' (by synthIsPosition)⟩⟩
lemma sew_body (x : Stream' A) a :
  x.cons a ∈ body (PreStrategy.sew f).subtree ↔ ∃ h, x ∈ body (f a h).subtree := by
  constructor <;> intro h
  · use (h _ (by simp)).1; intro y hy
    specialize h ([a] ++ y) ((principalOpen_append _ _ _).mpr hy)
    rw [List.singleton_append, sew_subtree] at h; exact h.2
  · intro y hy; rcases y with (_ | ⟨a', y⟩)
    · conv => simp
      apply mem_of_append; exact (h.2 [] (by simp)).1
    · simp_rw [principalOpen_cons] at hy; obtain ⟨rfl, hy⟩ := hy
      rw [sew_subtree]; use h.1; exact h.2 _ hy
variable {G : Game A} (f : ∀ a, [a] ∈ G.tree → PreStrategy (G.residual [a]).tree Player.zero)
lemma sew_isWinning (h : ∀ a h, (f a h).IsWinning) :
  (PreStrategy.sew f).IsWinning := by
  intro a h'; rw [← Stream'.cons_head_tail a, sew_body] at h'
  obtain ⟨ha, htail⟩ := h'
  have hwin := h (a.get 0) ha htail
  simpa [Player.payoff, Game.residual, body.append, Stream'.cons_head_tail, subAt_body] using hwin
lemma sew_residual (S : PreStrategy T Player.one) : sew (fun a _ ↦ S.residual [a]) = S := by
  ext x hp; rcases x with (_ | ⟨x, a⟩)
  · synthIsPosition
  · rfl
end «sew»

section «firstMove»
variable (a : A) (h : [a] ∈ T) (s : PreStrategy (subAt T [a]) Player.one)
/-- in the first move, play `a`, then follow `s` -/
noncomputable def firstMove : PreStrategy T Player.zero := by
  classical
  exact fun
    | ⟨[], _⟩, _ => {⟨a, h⟩}
    | ⟨b :: x, hx⟩, hp =>
      if heq : a = b then by
        subst heq
        exact s ⟨x, hx⟩ (by synthIsPosition)
      else ∅
@[simp] lemma firstMove_subtree a' x :
  a' :: x ∈ (s.firstMove a h).subtree ↔ a = a' ∧ x ∈ s.subtree := by
  constructor
  · intro ⟨hf, hs⟩; have heq : a = a' := by
      specialize hs (y := []) (List.prefix_iff_eq_take.mpr rfl) (by synthIsPosition)
      simp_rw [PreStrategy.firstMove] at hs
      exact congrArg Subtype.val hs |>.symm
    subst heq; use rfl, hf; intro y b hpr hpo
    convert hs (y := a :: y) (by simpa) (by synthIsPosition) using 1
    · rfl
    · rfl
    · rfl
    · simp only [PreStrategy.firstMove, dif_pos]; rfl
    · rfl
  · rintro ⟨rfl, hf, hs⟩; use hf; intro y b hpr hpo
    rcases y with (_ | ⟨a', y⟩)
    · simp [List.cons_prefix_cons] at hpr; simp [hpr, PreStrategy.firstMove]
    · obtain ⟨rfl, hpr2⟩ := List.cons_prefix_cons.mp hpr
      convert hs hpr2 (by synthIsPosition) using 1
      · rfl
      · rfl
      · rfl
      · simp only [PreStrategy.firstMove, dif_pos]; rfl
      · rfl
@[simp] lemma firstMove_body a' (x : Stream' A) :
  x.cons a' ∈ body (s.firstMove a h).subtree ↔ a = a' ∧ x ∈ body s.subtree := by
  constructor
  · intro h; have heq : a = a' := by
      specialize h [a'] (by simp); rw [firstMove_subtree] at h; exact h.1
    subst heq; use rfl
    intro y hy; specialize h ([a] ++ y) ((principalOpen_append _ _ _).mpr hy)
    rw [List.singleton_append, firstMove_subtree] at h; exact h.2
  · rintro ⟨rfl, h⟩ y hy; rcases y with (_ | ⟨a', y⟩)
    · conv => simp
      exact mem_of_append (h [] (by simp)).1
    · simp_rw [principalOpen_cons] at hy; obtain ⟨rfl, hy⟩ := hy
      rw [firstMove_subtree]; exact ⟨rfl, h _ hy⟩
variable {G : Game A} (h : [a] ∈ G.tree) (s : PreStrategy (G.residual [a]).tree Player.one)
@[simp] lemma firstMove_isWinning :
  (s.firstMove a h).IsWinning ↔ s.IsWinning := by
  constructor
  · intro hw b hb
    have hb' : Stream'.cons a b ∈ body (s.firstMove a h).subtree :=
      (firstMove_body a h s a b).mpr ⟨rfl, hb⟩
    have hw' := hw hb'
    simpa [Player.payoff, Game.residual, body.append] using hw'
  · intro hw b hb
    rw [← Stream'.cons_head_tail b, firstMove_body] at hb
    obtain ⟨rfl, hb⟩ := hb
    have hw' := hw hb
    simpa [Player.payoff, Game.residual, body.append] using hw'
lemma firstMove_extQuasi_tree (hs : s.IsQuasi) (hT : IsPruned G.tree) :
  ((s.firstMove a h).extQuasi hT).1.subtree = (s.firstMove a h).subtree := by
  apply eq_extQuasi; intro ⟨x, hx⟩ hp
  rcases x with (_ | ⟨b, x⟩)
  · use ⟨a, h⟩
    rfl
  · conv at hx => simp
    obtain ⟨rfl, hx'⟩ := hx
    obtain ⟨b, hbs⟩ := hs ⟨_, hx'.1⟩ (by synthIsPosition)
    exact ⟨b, by
      convert hbs using 1 <;>
        first
          | rfl
          | (simp only [firstMove, subtreeIncl, dif_pos]; rfl)⟩
@[simp] lemma firstMove_extQuasi_isWinning (hT : IsPruned G.tree) (hs : s.IsQuasi) :
  ((s.firstMove a h).extQuasi hT).1.IsWinning ↔ s.IsWinning := by
  unfold IsWinning; rw [firstMove_extQuasi_tree a h s hs]; apply firstMove_isWinning a h s
end «firstMove»

section «PreserveProp»
variable {p : Player}
variable (P : ∀ x : T, IsPosition x.val p.swap → Prop)
/-- play such that the proposition `P x` holds in every position `x` resulting from your move -/
def preserveProp : PreStrategy T p := fun x hp ↦ {a | P a.valT' (by synthIsPosition)}
lemma preserveProp_eq_extQuasi (h : ∀ x hp, P x hp → ∀ a : ExtensionsAt x,
  (preserveProp P a.valT' (by as_aux_lemma => synthIsPosition)).Nonempty) (hT : IsPruned T)
  (hst0 : (hp : p = Player.zero) → ∃ a ha, P ⟨[a], ha⟩ (by as_aux_lemma => synthIsPosition))
  (hst1 : (hp : p = Player.one) → (hn : [] ∈ T) →
    P ⟨[], hn⟩ (by as_aux_lemma => synthIsPosition)) :
  ((preserveProp P).extQuasi hT).1.subtree = (preserveProp P).subtree := by
  apply PreStrategy.eq_extQuasi; intro ⟨x, hx⟩ hp
  rcases x.eq_nil_or_concat' with rfl | ⟨x, a, rfl⟩
  · obtain ⟨a, aT, ha⟩ := hst0 (by synthIsPosition); exact ⟨⟨a, aT⟩, ha⟩
  · rcases x.eq_nil_or_concat' with rfl | ⟨x, b, rfl⟩
    · exact h _ _ (hst1 (by synthIsPosition) (mem_of_append hx).1) ⟨_, hx.1⟩
    · exact h ⟨x ++ [b], mem_of_append hx.1⟩ (by synthIsPosition)
        (((preserveProp P).subtree_compatible_iff ⟨x, mem_of_append (mem_of_append hx)⟩
        (by synthIsPosition)).mp (mem_of_append hx)).2 ⟨a, hx.1⟩
end «PreserveProp»
end PreStrategy

variable {G G' : Game A} {p p' : Player}
namespace Game
/-- a position is winning if there is a winning strategy in the residual game -/
def WinningPosition (G : Game A) (x : List A) (p : Player := Player.zero) :=
  (G.residual x).ExistsWinning p
@[simp] lemma winningPosition_residual x y :
  (G.residual x).WinningPosition y p ↔ G.WinningPosition (x ++ y) p := by
  simp [WinningPosition]
/-- a position is won if it cannot be lost by playing however -/
def WonPosition (G : Game A) (x : List A) (p : Player := Player.zero) :=
  (G.residual x).AllWinning p
@[simp] lemma wonPosition_residual x y :
 (G.residual x).WonPosition y p ↔ G.WonPosition (x ++ y) p := by
  simp [WonPosition]
lemma WonPosition.extend {x} y (hW : WonPosition G x p) :
  WonPosition G (x ++ y) (p.residual y) := by
  rw [WonPosition, ← Game.residual_append]
  exact Game.AllWinning.residual hW y
lemma wonPosition_iff_disjoint' {x} :
  G.WonPosition x p ↔ Set.range (body.append x) ∩ (p.swap.residual x).payoff G = ∅ := by
  rw [WonPosition, AllWinning]
  simp only [Set.eq_univ_iff_forall, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff,
    Set.mem_range]
  constructor
  · rintro h z ⟨⟨a, rfl⟩, hpay⟩
    rw [Player.payoff_swap_residual] at hpay
    have hpre := h a
    rw [Player.payoff_residual] at hpre
    exact hpay hpre
  · intro h a
    by_contra hpay
    have hpay' : body.append x a ∉ (Player.residual x p).payoff G := by
      intro hp
      apply hpay
      rwa [Player.payoff_residual]
    exact h (body.append x a) ⟨⟨a, rfl⟩, by
      rw [Player.payoff_swap_residual]
      exact hpay'⟩
lemma wonPosition_iff_disjoint {x} :
  G.WonPosition x p ↔ principalOpen x ∩ (p.swap.residual x).payoff G = ∅ := by
  simpa [← Set.image_val_inj, Set.inter_assoc, ← Set.inter_sdiff_assoc] using
    wonPosition_iff_disjoint'

/-- the defensive PreStrategy never moves into a winning position of the opponent -/
def defensivePre (G : Game A) (p : Player) : PreStrategy G.tree p :=
  preserveProp (fun x _ ↦ ¬ WinningPosition G x.val)
@[simp] lemma defensivePre_residual {x} :
  (defensivePre G p).residual x = defensivePre (G.residual x) (p.residual x) := by
  ext y hp a
  simp [PreStrategy.residual, defensivePre, preserveProp, ExtensionsAt.valT'_coe,
    ExtensionsAt.val', List.append_assoc, Set.mem_setOf_eq, winningPosition_residual]
  rfl
@[congr] lemma defensivePre_subtree {hG : G = G'} {hp : p = p'} :
  (defensivePre G p).subtree = (defensivePre G' p').subtree := by congr!
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def defensiveQuasi (G : Game A) (p : Player) := (defensivePre G p).extQuasi
@[congr] lemma defensiveQuasi_subtree {hG : G = G'} {hp : p = p'} h :
  (defensiveQuasi G p h).1.subtree = (defensiveQuasi G' p' (hG ▸ h)).1.subtree := by
  subst hG hp; rfl
end Game
namespace PreStrategy

lemma subtree_induction_body {f g : PreStrategy T p} {x} (h : x ∈ body f.subtree)
  (h' : ∀ n, x.take n ∈ g.subtree → ∀ hp,
    ⟨x.get n, by apply subtree_sub; apply h; simp⟩ ∈
      f (f.subtreeIncl (body.take n ⟨x, h⟩)) hp →
    ⟨x.get n, by apply subtree_sub; apply h; simp⟩ ∈
      g (f.subtreeIncl (body.take n ⟨x, h⟩)) hp) : x ∈ body g.subtree := by
  apply mem_body_of_take 0; intro n _; apply f.subtree_induction (by apply h; simp)
  intro m hm hx hp; simp at hm
  have hnode : take m (f.subtreeIncl ⟨Stream'.take n x, by apply h; simp⟩) =
      f.subtreeIncl (body.take m ⟨x, h⟩) := by ext; simp [hm.le]
  intro ha
  let hp' : IsPosition (f.subtreeIncl (body.take m ⟨x, h⟩)).val p := by
    simpa [← hnode] using hp
  have ha' : ⟨x.get m, by apply subtree_sub; apply h; simp⟩ ∈
      f (f.subtreeIncl (body.take m ⟨x, h⟩)) hp' :=
    (PreStrategy.eval_mem_congr f hnode hp hp' (by simp)).mp ha
  have hb' := h' m (by simpa [hm.le] using hx) hp' ha'
  exact (PreStrategy.eval_mem_congr g hnode hp hp' (by simp)).mpr hb'

section «followUntilWon»
variable (S : PreStrategy G.tree p)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def followUntilWon : PreStrategy G.tree p := by
  classical
  exact fun x hp ↦
    if G.WonPosition x.val (p.residual x.val) then Set.univ else S x hp
lemma le_followUntilWon : S ≤ S.followUntilWon := by
  intro; unfold followUntilWon; split_ifs <;> simp
lemma followUntilWon_body : body S.followUntilWon.subtree ≤ body S.subtree ∪ p.payoff G := by
  intro x hx; by_cases h' : ∃ n, G.WonPosition (x.take n) (p.residual (x.take n))
  · right; have hx' := body_mono S.followUntilWon.subtree_sub hx; conv => simp [hx']
    let ⟨n, h'⟩ := h'
    conv at h' => simp [WonPosition, AllWinning]
    have hmem := Set.eq_univ_iff_forall.mp h' (body.drop n ⟨x, hx'⟩)
    simpa [body.append] using hmem
  · left; apply subtree_induction_body hx
    intros _ _ _; unfold followUntilWon; split_ifs
    · tauto
    · exact id
@[simp] lemma followUntilWon_isWinning : S.followUntilWon.IsWinning ↔ S.IsWinning :=
  ⟨sub_winning S.le_followUntilWon, fun h ↦ subset_trans S.followUntilWon_body (by simpa)⟩
end «followUntilWon»

end GaleStewartGame.PreStrategy
