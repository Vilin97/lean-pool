/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.Trees
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Player

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Strategies

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace GaleStewartGame
open Descriptive Tree
variable {A : Type*} (T : tree A) (p : Player)
/-- a `PreStrategy` is a weak form of a strategy given by specifying not a single move,
  but a possibly empty set of valid moves in all positions. This can be defined for
  arbitrary trees and not just games as the payoff set is irrelevant -/
def PreStrategy := ∀ x : T, IsPosition x.val p → Set (ExtensionsAt x) --TODO synth arg?
variable {T p}
namespace PreStrategy
@[ext] lemma ext {f g : PreStrategy T p} (h : ∀ x hp, f x hp = g x hp) : f = g :=
  funext fun x ↦ funext (h x)
instance : PartialOrder (PreStrategy T p) where
  le f g := ∀ x hx, f x hx ⊆ g x hx
  le_refl _ _ _ := subset_rfl
  le_trans _ _ _ ab bc _ _ := subset_trans (ab _ _) (bc _ _)
  le_antisymm _ _ ab ba := PreStrategy.ext fun x hp ↦ subset_antisymm (ab x hp) (ba x hp)
variable (S : PreStrategy T p)

/-- the tree of plays valid with a `PreStrategy` -/
def subtree : tree A where
  val := { x | ∃ (hx : x ∈ T), ∀ {y} {a}, (hpr : y ++ [a] <+: x) → (hpo : IsPosition y p)
    → ⟨a, mem_of_prefix hpr hx⟩ ∈ S ⟨y, mem_of_append (mem_of_prefix hpr hx)⟩ hpo }
  property := fun _ _ ⟨hx, h⟩ ↦
    ⟨mem_of_append hx, fun hpr _ ↦ h (hpr.trans (List.prefix_append _ _)) _⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp] lemma subtree_ne : [] ∈ S.subtree ↔ [] ∈ T := by simp [subtree]
@[simp] lemma subtree_sub : S.subtree ≤ T := fun _ ⟨h, _⟩ ↦ h
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def subtreeIncl (x : S.subtree) : T := ⟨x.val, S.subtree_sub x.prop⟩
attribute [simp_lengths] subtreeIncl_coe

@[gcongr] lemma subtree_mono {f g : PreStrategy T p} (h : f ≤ g) : f.subtree ≤ g.subtree :=
  fun _ ⟨hx, h'⟩ ↦ ⟨hx, fun {y} {_} hpr hpo ↦ h ⟨y, _⟩ hpo (h' hpr hpo)⟩
lemma subtree_fair (x : S.subtree) {a : A} (hp : IsPosition x.val p.swap) :
  x ++ [a] ∈ S.subtree ↔ x ++ [a] ∈ T := by
  refine ⟨fun h ↦ S.subtree_sub h, fun ha ↦ ⟨ha, fun {y b} hpr hpo ↦ ?_⟩⟩
  obtain ⟨hx, h'⟩ := x.prop; rcases List.prefix_concat_iff.mp hpr with heq | hpr
  · synthIsPosition
  · exact h' hpr hpo
lemma subtree_compatible (x : S.subtree) (hp : IsPosition x.val p) {a}
  (hx : x.val ++ [a] ∈ S.subtree) : ⟨a, hx.1⟩ ∈ S (S.subtreeIncl x) hp :=
  hx.2 List.prefix_rfl _
lemma subtree_compatible_iff (x : S.subtree) (hp : IsPosition x.val p) {a} :
  x.val ++ [a] ∈ S.subtree ↔ ∃ hx : x.val ++ [a] ∈ T, ⟨a, hx⟩ ∈ S (S.subtreeIncl x) hp := by
  refine ⟨fun h ↦ ⟨h.1, (subtree_compatible S x hp h)⟩, fun h ↦ ⟨h.1, fun {y b} hpr hpo ↦ ?_⟩⟩
  rcases List.prefix_concat_iff.mp hpr with heq | hpr
  · obtain ⟨rfl, heq⟩ := List.append_inj' heq rfl; obtain rfl := by simpa using heq
    exact h.2
  · apply x.prop.2 hpr
lemma subtree_induction {S S' : PreStrategy T p} {x} (h : x ∈ S.subtree)
  (h' : ∀ n (hn : n < x.length), x.take n ∈ S'.subtree → ∀ hp,
    ⟨x[n], by simpa using take_mem ⟨x, subtree_sub _ h⟩⟩ ∈
      S (Tree.take n (S.subtreeIncl ⟨x, h⟩)) hp →
    ⟨x[n], by simpa using take_mem ⟨x, subtree_sub _ h⟩⟩ ∈
      S' (Tree.take n (S.subtreeIncl ⟨x, h⟩)) hp) : x ∈ S'.subtree := by
  suffices ∀ n ≤ x.length, x.take n ∈ S'.subtree by simpa using this x.length le_rfl
  intro n hn
  induction n with
  | zero =>
    simpa using mem_of_prefix x.nil_prefix h
  | succ n ih =>
    rw [← List.take_concat_get' _ _ hn]; specialize ih (by omega)
    by_cases hp : IsPosition (x.take n) p
    · rw [S'.subtree_compatible_iff ⟨_, ih⟩ hp]
      use by simpa using S.subtree_sub (take_mem ⟨x, h⟩)
      apply h' n hn ih
      apply S.subtree_compatible (Tree.take _ ⟨x, h⟩); simpa using take_mem ⟨x, h⟩
    · rw [S'.subtree_fair ⟨_, ih⟩ (by synthIsPosition)]
      simpa using S.subtree_sub (take_mem ⟨x, h⟩)

/-- restrict a `PreStrategy` to a subtree of the game tree -/
def restrictTree (rto : tree A) (hr : rto ≤ T) :
  PreStrategy rto p := fun x hx a ↦ S ⟨x.val, hr x.prop⟩ hx ⟨a.val, hr a.prop⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev restrict (rto : PreStrategy T p.swap) :
  PreStrategy rto.subtree p := S.restrictTree rto.subtree rto.subtree_sub
lemma restrict_sub (rto : tree A) (hr : rto ≤ T) :
  (S.restrictTree rto hr).subtree ≤ S.subtree := fun _ ⟨hx, h⟩ ↦ ⟨hr hx, h⟩
lemma restrict_valid (rto : tree A) (hr : rto ≤ T) :
  (S.restrictTree rto hr).subtree ≤ rto := by simp
@[simp] lemma restrict_subtree (rto : tree A) (hr : rto ≤ T) :
  (S.restrictTree rto hr).subtree = S.subtree ⊓ rto :=
  le_antisymm
    (le_inf (restrict_sub S rto hr) (restrict_valid S rto hr))
    (fun _ h ↦ ⟨h.2, h.1.2⟩)

/-- the residual strategy for the game starting in position x -/
def residual (x : List A) : PreStrategy (subAt T x) (p.residual x) :=
  fun y hy ↦ {a | ⟨a.val, by simpa [List.append_assoc] using a.prop⟩ ∈
      S ⟨x ++ y.val, y.prop⟩ (by synthIsPosition)}
lemma sub_residual_subtree (x : List A) :
  subAt S.subtree x ≤ (S.residual x).subtree := by
  intro y ⟨hT, h⟩; use hT; intro _ _ hpr _
  replace hpr := (List.prefix_append_right_inj x).mpr hpr; rw [← List.append_assoc] at hpr
  exact h hpr (by synthIsPosition)
@[simp] lemma residual_subtree (x : S.subtree) :
  (S.residual x).subtree = subAt S.subtree x := by
  ext y; constructor
  · intro ⟨h, h'⟩; use h; intro z a hpr hpo; have ⟨_, hx⟩ := x.prop
    rcases List.prefix_or_prefix_of_prefix hpr (List.prefix_append _ _) with h | ⟨y', h⟩
    · exact hx h hpo
    · induction y' using List.reverseRecOn with
      | nil => simp [hx, ← h]
      | append_singleton y' b ih =>
        rw [← List.append_assoc] at h; obtain ⟨rfl, rfl⟩ : x ++ y'= z ∧ b = a := by
          have ⟨hz, ha'⟩ := List.append_inj' h rfl; exact ⟨hz, by injection ha'⟩
        apply h'
        · apply (List.prefix_append_right_inj x).mp; rwa [← List.append_assoc]
        · synthIsPosition
  · apply sub_residual_subtree

/-- A quasistrategy is a `PreStrategy` that allows at least one move in every position -/
def IsQuasi (S : PreStrategy T p) := ∀ x hx, (S x hx).Nonempty
end PreStrategy
variable (T p) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def QuasiStrategy := PSigma (@PreStrategy.IsQuasi A T p)
@[ext] lemma QuasiStrategy.ext {f g : QuasiStrategy T p} (h : f.1 = g.1) : f = g := by
  obtain ⟨f, hf⟩ := f; obtain ⟨g, hg⟩ := g
  conv at h => simp
  simp_rw [h] --make general lemma?
variable (T p) in
/-- A quasistrategy is a `PreStrategy` that allows exactly one move in every position -/
def Strategy := ∀ x : T, IsPosition x.val p → ExtensionsAt x
@[ext] lemma Strategy.ext {f g : Strategy T p} (h : ∀ x hp, f x hp = g x hp) : f = g :=
  funext fun x ↦ funext (h x)

@[congr] lemma PreStrategy.eval_val_congr {U : tree A}
  (S S' : PreStrategy U p) (h : S = S') (x x' : U) (h' : x = x') hp :
  Subtype.val '' (S x hp) = Subtype.val '' (S' x' (by subst h'; exact hp)) := by
  subst h
  subst h'
  rfl
lemma PreStrategy.eval_mem_congr {U : tree A} (S : PreStrategy U p) {x x' : U}
    (hx : x = x') (hp : IsPosition x.val p) (hp' : IsPosition x'.val p)
    {a : ExtensionsAt x} {a' : ExtensionsAt x'} (ha : a.val = a'.val) :
    a ∈ S x hp ↔ a' ∈ S x' hp' := by
  subst hx
  have haa : a = a' := ExtensionsAt.ext ha
  subst haa
  have hhp : hp = hp' := Subsingleton.elim hp hp'
  subst hhp
  rfl
@[congr] lemma Strategy.eval_val_congr {U : tree A} (S S' : Strategy U p) (h : S = S') (x x' : U)
  (h' : x = x') hp : (S x hp).val = (S' x' (by subst h'; exact hp)).val := by
  subst h
  subst h'
  rfl

/-- regard a Strategy as PreStrategy -/
abbrev Strategy.pre (S : Strategy T p) : PreStrategy T p := fun x hx ↦ {S x hx}
@[simp] lemma Strategy.isQuasi (S : Strategy T p) : S.pre.IsQuasi := by
  simp [PreStrategy.IsQuasi]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev Strategy.quasi (S : Strategy T p) : QuasiStrategy T p := ⟨S.pre, S.isQuasi⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
noncomputable def PreStrategy.IsQuasi.choose {S : PreStrategy T p} (h : S.IsQuasi) :
  Strategy T p := fun x hp ↦ (h x hp).some
lemma PreStrategy.choose_sub {S : PreStrategy T p} (h : S.IsQuasi) :
  h.choose.pre ≤ S := by
  intro x hp
  simpa [GaleStewartGame.PreStrategy.IsQuasi.choose] using (h x hp).some_mem

lemma QuasiStrategy.subtree_isPruned (S : QuasiStrategy T p) (hT : IsPruned T) :
  IsPruned S.1.subtree := by
  intro ⟨x, ⟨hx, h⟩⟩; by_cases hp : IsPosition x p
  · use (S.2 ⟨x, hx⟩ hp).some.val; rw [S.1.subtree_compatible_iff _ hp]
    exact ⟨_, (S.2 ⟨x, hx⟩ hp).some_mem⟩
  · obtain ⟨a, ha⟩ := hT ⟨_, hx⟩
    exact ⟨a, (S.1.subtree_fair ⟨x, ⟨hx, h⟩⟩ (by synthIsPosition)).mpr ha⟩
lemma PreStrategy.IsQuasi.restrictTree_isQuasi {S : PreStrategy T p} (rto : tree A)
  (h : S.IsQuasi) (hfair : ∀ (x : rto) (a : A), IsPosition x.val p →
  x ++ [a] ∈ T → x ++ [a] ∈ rto) (hr : rto ≤ T) : (S.restrictTree rto hr).IsQuasi := by
  intro x hp; let ⟨nev, nep⟩ := h ⟨x.val, hr x.prop⟩ hp
  use ⟨nev.val, hfair _ _ (by synthIsPosition) nev.prop⟩, nep
lemma PreStrategy.IsQuasi.restrict_isQuasi {S : PreStrategy T p} (rto : PreStrategy T p.swap)
  (h : S.IsQuasi) : (S.restrict rto).IsQuasi :=
  GaleStewartGame.PreStrategy.IsQuasi.restrictTree_isQuasi rto.subtree h (by
    intro x a hp hx; rwa [rto.subtree_fair x (by synthIsPosition)])
    rto.subtree_sub
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev QuasiStrategy.restrict (S : QuasiStrategy T p) (rto : PreStrategy T p.swap) :
  QuasiStrategy rto.subtree p := ⟨_, S.2.restrict_isQuasi rto⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def QuasiStrategy.residual (S : QuasiStrategy T p) (x : List A) :
  QuasiStrategy (subAt T x) (p.residual x) := ⟨S.1.residual x, by
  intro y hy; have ne := S.2 ⟨x ++ y.val, y.prop⟩ (by synthIsPosition)
  use ⟨ne.choose.val, by simpa using ne.choose.prop⟩, ne.choose_spec⟩

end GaleStewartGame
