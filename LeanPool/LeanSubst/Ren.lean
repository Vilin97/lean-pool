/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
namespace LeanSubst
  universe u
  variable {S T : Type}

  /-- A renaming, represented as its action on De Bruijn indices. -/
  structure Ren where
    /-- The underlying function on De Bruijn indices. -/
    act : Nat -> Nat

  /-- The identity renaming. -/
  def Ren.id : Ren := ⟨λ x => x⟩

  /-- The renaming that shifts every index up by `k`. -/
  def Ren.add (k : Nat) : Ren := ⟨(· + k)⟩

  /-- The renaming that shifts every index down by `k` (truncating at zero). -/
  def Ren.sub (k : Nat) : Ren := ⟨(· - k)⟩

  /-- Lift a renaming under `k` binders, leaving the first `k` indices fixed. -/
  def Ren.lift (r : Ren) (k : Nat := 1) : Ren := .mk λ n =>
    if n < k then n else r.act (n - k) + k

  /-- Extend a renaming by mapping the zeroth index to `a` and shifting the rest. -/
  def Ren.cons (a : Nat) (r : Ren) : Ren := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => r.act n

  /-- Prepend a list of indices to a renaming via repeated `Ren.cons`. -/
  def Ren.append : List Nat -> Ren -> Ren
  | .nil, r => r
  | .cons hd tl, r => append tl (r.cons hd)

  instance : HAppend (List Nat) Ren Ren where
    hAppend := Ren.append

  /-- Sequential composition of renamings: apply `r1` then `r2`. -/
  def Ren.compose : Ren -> Ren -> Ren
  | r1, r2 => .mk λ n => r2.act (r1.act n)

  /-- A type whose values support being acted on by a renaming. -/
  class RenMap (T : Type) where
    /-- Apply a renaming to a value. -/
    rmap : Ren -> T -> T

  export RenMap (rmap)

  /-- Notation `t⟨r⟩` for applying renaming `r` to value `t`. -/
  macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)
  /-- Notation `a :: r` for `Ren.cons`. -/
  infixr:67 (name := Ren.consNotation) " :: " => Ren.cons
  /-- Notation `r1 ∘ r2` for `Ren.compose`. -/
  infixr:85 (name := Ren.composeNotation) " ∘ " => Ren.compose

  /-- Pretty-printer that displays `rmap r t` as `t⟨r⟩`. -/
  @[app_unexpander rmap]
  def unexpandRenApply : Lean.PrettyPrinter.Unexpander
  | `($_ $r $t) => `($t⟨$r⟩)
  | _ => throw ()

  @[simp, grind =]
  theorem Ren.lift_zero {r : Ren} : r.lift 0 = r := by
    unfold Ren.lift; congr

  @[grind =]
  theorem Ren.lift_succ {r : Ren} {k} : r.lift (k + 1) = (r.lift k).lift := by
    induction k; simp
    case _ n ih =>
      unfold Ren.lift; congr; funext; case _ i =>
      simp; unfold Ren.lift at ih; simp at ih
      grind

  @[simp]
  theorem Ren.id_action {x} : Ren.id.act x = x := by simp [Ren.id]

  @[simp]
  theorem Ren.lift_id {k} : Ren.lift Ren.id k = Ren.id := by
    simp [Ren.id, Ren.lift]; congr; funext; case _ x =>
    cases x <;> simp; omega

  @[simp]
  theorem Ren.cons_head_action {n} {r : Ren} : (n::r).act 0 = n := by simp [Ren.cons]

  @[simp]
  theorem Ren.cons_tail_action {n i} {r : Ren} : (n::r).act (i + 1) = r.act i := by simp [Ren.cons]

  @[simp]
  theorem Ren.compose_id_left {r : Ren} : id ∘ r = r := by
    simp [Ren.compose, Ren.id]

  @[simp]
  theorem Ren.compose_id_right {r : Ren} : r ∘ id = r := by
    simp [Ren.compose, Ren.id]

  @[simp]
  theorem Ren.compose_assoc {r1 r2 r3 : Ren} : (r1 ∘ r2) ∘ r3 = r1 ∘ r2 ∘ r3 := by
    simp [Ren.compose]

  @[simp]
  theorem Ren.compose_action {r1 r2 : Ren} {x} : (r1 ∘ r2).act x = r2.act (r1.act x) := by
    simp [Ren.compose]

  theorem Ren.compose_lift_k1 {r1 r2 : Ren} : (r1 ∘ r2).lift = r1.lift ∘ r2.lift := by
    simp [Ren.compose, Ren.lift]
    funext; case _ x =>
    cases x <;> simp

  @[simp]
  theorem Ren.compose_lift {k} {r1 r2 : Ren} : (r1 ∘ r2).lift k = r1.lift k ∘ r2.lift k := by
    induction k generalizing r1 r2; simp
    case _ k ih =>
      rw [lift_succ, ih]
      rw [lift_succ (r := r1)]
      rw [lift_succ (r := r2)]
      rw [compose_lift_k1]

  /-- A `RenMap` for which applying the identity renaming is the identity. -/
  class RenMapId (S : Type) [RenMap S] where
    /-- Applying the identity renaming leaves a value unchanged. -/
    apply_id {t : S} : t⟨Ren.id⟩ = t

  /-- A `RenMap` for which renaming is functorial in composition. -/
  class RenMapCompose (S : Type) [RenMap S] where
    /-- Applying two renamings in sequence equals applying their composition. -/
    apply_compose {s : S} {r1 r2 : Ren} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

  @[simp, grind =]
  theorem Ren.apply_id [RenMap T] [RenMapId T] {t : T} : t⟨id⟩ = t := RenMapId.apply_id

  @[simp, grind =]
  theorem Ren.apply_compose [RenMap T] [RenMapCompose T] {t : T} {r1 r2 : Ren}
    : t⟨r1⟩⟨r2⟩ = t⟨r1 ∘ r2⟩
  := RenMapCompose.apply_compose

end LeanSubst
