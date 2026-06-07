/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren

namespace LeanSubst
  universe u
  variable {S T : Type}

  inductive Subst.Action (T : Type) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T
  deriving Repr

  export Subst.Action (re su)

  structure Subst (T : Type) where
    act : Nat -> Subst.Action T

  @[coe]
  def Ren.to : Ren -> Subst T
  | r  => .mk λ n => re (r.act n)

  instance : Coe Ren (Subst T) where
    coe := Ren.to

  class SubstMap (S T : Type) where
    smap : Subst T -> S -> S

  export SubstMap (smap)

  def Subst.lift [RenMap T] (σ : Subst T) (k : Nat := 1) : Subst T := .mk λ n =>
    if n < k then re n else
      match σ.act (n - k) with
      | su t => su (rmap (Ren.add k) t)
      | re i => re (i + k)

  def Subst.cons (a : Subst.Action T) (σ : Subst T) : Subst T := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => σ.act n

  def Subst.append : List (Subst.Action T) -> Subst T -> Subst T
  | .nil, σ => σ
  | .cons hd tl, σ => append tl (σ.cons hd)

  instance : HAppend (List $ Subst.Action T) (Subst T) (Subst T) where
    hAppend := Subst.append

  @[simp]
  abbrev smap1 [SubstMap S S] := smap (S := S) (T := S)

  def Subst.compose [RenMap T] [SubstMap T T] : Subst T -> Subst T -> Subst T
  | σ, τ => .mk λ n =>
    match σ.act n with
    | su t => su (smap τ t)
    | re k => τ.act k

  def Subst.hcompose [RenMap T] [SubstMap S T] : Subst S -> Subst T -> Subst S
  | σ, τ => .mk λ n =>
    match σ.act n with
    | su t => su (smap τ t)
    | re k => re k

  def Subst.id : Subst T := ⟨λ n => re n⟩
  def Subst.succ : Subst T := ⟨λ n => re (n + 1)⟩
  def Subst.pred : Subst T := ⟨λ n => re (n - 1)⟩

  notation "+0" => Subst.id
  macro "+0@" noWs T:term : term =>`(@Subst.id $T)
  notation "+1" => Subst.succ
  macro "+1@" noWs T:term : term =>`(@Subst.succ $T)
  notation "-1" => Subst.pred
  macro "-1@" noWs T:term : term =>`(@Subst.pred $T)

  @[simp, grind =]
  theorem Subst.id_action {n} : (+0@T).act n = re n := by simp [Subst.id]

  @[simp, grind =]
  theorem Subst.succ_action {n} : (+1@T).act n = re (n + 1) := by simp [Subst.succ]

  @[simp, grind =]
  theorem Subst.pred_action {n} : (-1@T).act n = re (n - 1) := by simp [Subst.pred]

  @[simp, grind =]
  theorem Ren.to_id : Ren.to (T := T) id = +0 := by
    unfold Ren.to; unfold Subst.id; simp [id]

  @[simp, grind =]
  theorem Ren.to_succ : Ren.to (T := T) (Ren.add 1) = +1 := by
    unfold Ren.to; simp; unfold Subst.succ; simp [Ren.add]

  @[simp, grind =]
  theorem Ren.to_pred : Ren.to (T := T) (Ren.sub 1) = -1 := by
    unfold Ren.to; simp; unfold Subst.pred; simp [Ren.sub]

  @[simp, grind =]
  theorem Ren.pred_succ [RenMap T] [SubstMap T T] : Subst.compose (T := T) +1 -1 = +0 := by
    unfold Subst.compose; simp
    unfold Subst.id; rfl

  @[grind =]
  theorem Ren.to_lift [RenMap T] {r : Ren} {k} : (r.lift k).to = (@Ren.to T r).lift k := by
    cases r; simp [Ren.lift, Ren.to, Subst.lift]; case _ act =>
    funext; case _ x =>
    cases x
    case zero => grind
    case _ n => cases Nat.decLt (n + 1) k <;> simp [ite]

  macro:max t:term noWs "[" σ:term "]" : term => `(smap1 $σ $t)
  macro:max t:term noWs "[" σ:term ":" T:term "]" : term => `(smap (T := $T) $σ $t)
  infixr:67 (name := Subst.cons_notation) " :: " => Subst.cons
  infixr:85 (name := Subst.compose_notation) " ∘ " => Subst.compose
  infixr:85 " ◾ " => Subst.hcompose

  @[app_unexpander smap1]
  def unexpandSubstApply1 : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ])
  | _ => throw ()

  @[app_unexpander smap]
  def unexpandSubstApply : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ : _])
  | `($_ (T := $T) $σ $t) => `($t[$σ : $T])
  | _ => throw ()

  @[simp, grind =]
  theorem Ren.to_compose {r1 r2 : Ren} [RenMap T] [SubstMap T T]
    : Ren.to (T := T) (r1 ∘ r2) = Subst.compose r1 r2
  := by
    funext; case _ x =>
    cases x <;> simp [Ren.to, Subst.compose, Ren.compose]

  @[simp]
  theorem Subst.cons_head_action {t} {σ : Subst T} : (t::σ).act 0 = t := by simp [Subst.cons]

  @[simp]
  theorem Subst.cons_tail_action {t i} {σ : Subst T} : (t::σ).act (i + 1) = σ.act i := by simp [Subst.cons]

end LeanSubst
