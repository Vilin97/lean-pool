/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
namespace LeanSubst
  universe u
  variable {S T : Type}

  structure Ren where
    act : Nat -> Nat

  def Ren.id : Ren := ⟨λ x => x⟩

  def Ren.add (k : Nat) : Ren := ⟨(· + k)⟩

  def Ren.sub (k : Nat) : Ren := ⟨(· - k)⟩

  def Ren.lift (r : Ren) (k : Nat := 1) : Ren := .mk λ n =>
    if n < k then n else r.act (n - k) + k

  def Ren.cons (a : Nat) (r : Ren) : Ren := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => r.act n

  def Ren.append : List Nat -> Ren -> Ren
  | .nil, r => r
  | .cons hd tl, r => append tl (r.cons hd)

  instance : HAppend (List Nat) Ren Ren where
    hAppend := Ren.append

  def Ren.compose : Ren -> Ren -> Ren
  | r1, r2 => .mk λ n => r2.act (r1.act n)

  class RenMap (T : Type) where
    rmap : Ren -> T -> T

  export RenMap (rmap)

  macro:max t:term noWs "⟨" r:term "⟩" : term => `(rmap $r $t)
  infixr:67 (name := Ren.cons_notation) " :: " => Ren.cons
  infixr:85 (name := Ren.compose_notation) " ∘ " => Ren.compose

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

  class RenMapId (S : Type) [RenMap S] where
    apply_id {t : S} : t⟨Ren.id⟩ = t

  class RenMapCompose (S : Type) [RenMap S] where
    apply_compose {s : S} {r1 r2 : Ren} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

  @[simp, grind =]
  theorem Ren.apply_id [RenMap T] [RenMapId T] {t : T} : t⟨id⟩ = t := RenMapId.apply_id

  @[simp, grind =]
  theorem Ren.apply_compose [RenMap T] [RenMapCompose T] {t : T} {r1 r2 : Ren}
    : t⟨r1⟩⟨r2⟩ = t⟨r1 ∘ r2⟩
  := RenMapCompose.apply_compose

end LeanSubst
