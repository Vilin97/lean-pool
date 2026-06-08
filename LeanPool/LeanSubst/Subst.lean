/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren

namespace LeanSubst
  universe u
  variable {S T : Type}

  /-- A single substitution action: either a renamed variable (`re`) or a term (`su`). -/
  inductive Subst.Action (T : Type) where
  | re : Nat -> Subst.Action T
  | su : T -> Subst.Action T
  deriving Repr

  export Subst.Action (re su)

  /-- A substitution, represented as its action on each De Bruijn index. -/
  structure Subst (T : Type) where
    /-- The substitution action assigned to each De Bruijn index. -/
    act : Nat -> Subst.Action T

  /-- Embed a renaming into a substitution. -/
  @[coe]
  def Ren.to : Ren -> Subst T
  | r  => .mk λ n => re (r.act n)

  instance : Coe Ren (Subst T) where
    coe := Ren.to

  /-- A type `S` whose values support being acted on by a substitution over `T`. -/
  class SubstMap (S T : Type) where
    /-- Apply a substitution to a value. -/
    smap : Subst T -> S -> S

  export SubstMap (smap)

  /-- Lift a substitution under `k` binders, leaving the first `k` indices fixed. -/
  def Subst.lift [RenMap T] (σ : Subst T) (k : Nat := 1) : Subst T := .mk λ n =>
    if n < k then re n else
      match σ.act (n - k) with
      | su t => su (rmap (Ren.add k) t)
      | re i => re (i + k)

  /-- Extend a substitution by assigning action `a` to index `0` and shifting the rest. -/
  def Subst.cons (a : Subst.Action T) (σ : Subst T) : Subst T := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => σ.act n

  /-- Prepend a list of actions to a substitution via repeated `Subst.cons`. -/
  def Subst.append : List (Subst.Action T) -> Subst T -> Subst T
  | .nil, σ => σ
  | .cons hd tl, σ => append tl (σ.cons hd)

  instance : HAppend (List $ Subst.Action T) (Subst T) (Subst T) where
    hAppend := Subst.append

  /-- Apply a homogeneous substitution (the `S = T` case of `smap`). -/
  @[simp]
  abbrev smap1 [SubstMap S S] := smap (S := S) (T := S)

  /-- Homogeneous composition of substitutions: apply `σ` then `τ`. -/
  def Subst.compose [SubstMap T T] : Subst T -> Subst T -> Subst T
  | σ, τ => .mk λ n =>
    match σ.act n with
    | su t => su (smap τ t)
    | re k => τ.act k

  /-- Heterogeneous composition: substitute over `S` then over `T`. -/
  def Subst.hcompose [SubstMap S T] : Subst S -> Subst T -> Subst S
  | σ, τ => .mk λ n =>
    match σ.act n with
    | su t => su (smap τ t)
    | re k => re k

  /-- The identity substitution, mapping each index to itself. -/
  def Subst.id : Subst T := ⟨λ n => re n⟩
  /-- The shift-up substitution, mapping each index `n` to `n + 1`. -/
  def Subst.succ : Subst T := ⟨λ n => re (n + 1)⟩
  /-- The shift-down substitution, mapping each index `n` to `n - 1`. -/
  def Subst.pred : Subst T := ⟨λ n => re (n - 1)⟩

  /-- Notation `+0` for the identity substitution. -/
  notation "+0" => Subst.id
  /-- Notation `+0@T` for the identity substitution at type `T`. -/
  macro "+0@" noWs T:term : term =>`(@Subst.id $T)
  /-- Notation `+1` for the shift-up substitution. -/
  notation "+1" => Subst.succ
  /-- Notation `+1@T` for the shift-up substitution at type `T`. -/
  macro "+1@" noWs T:term : term =>`(@Subst.succ $T)
  /-- Notation `-1` for the shift-down substitution. -/
  notation "-1" => Subst.pred
  /-- Notation `-1@T` for the shift-down substitution at type `T`. -/
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

  /-- Notation `t[σ]` for applying a homogeneous substitution `σ` to `t`. -/
  macro:max t:term noWs "[" σ:term "]" : term => `(smap1 $σ $t)
  /-- Notation `t[σ : T]` for applying a substitution `σ` over `T` to `t`. -/
  macro:max t:term noWs "[" σ:term ":" T:term "]" : term => `(smap (T := $T) $σ $t)
  /-- Notation `a :: σ` for `Subst.cons`. -/
  infixr:67 (name := Subst.consNotation) " :: " => Subst.cons
  /-- Notation `σ ∘ τ` for `Subst.compose`. -/
  infixr:85 (name := Subst.composeNotation) " ∘ " => Subst.compose
  /-- Notation `σ ◾ τ` for `Subst.hcompose`. -/
  infixr:85 " ◾ " => Subst.hcompose

  /-- Pretty-printer that displays `smap1 σ t` as `t[σ]`. -/
  @[app_unexpander smap1]
  def unexpandSubstApply1 : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t[$σ])
  | _ => throw ()

  /-- Pretty-printer that displays `smap σ t` as `t[σ : _]`. -/
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
