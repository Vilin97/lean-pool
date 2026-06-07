/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren

namespace LeanSubst
  universe u
  variable {S T : Type}

  structure HetRen (T : Type) where
    act : Nat -> Nat

  def HetRen.id T : HetRen T := ⟨λ x => x⟩

  def HetRen.add T (k : Nat) : HetRen T := ⟨(· + k)⟩

  def HetRen.sub T (k : Nat) : HetRen T := ⟨(· - k)⟩

  def HetRen.lift (r : HetRen T) (k : Nat := 1) : HetRen T := .mk λ n =>
    if n < k then n else r.act (n - k) + k

  def HetRen.cons (a : Nat) (r : HetRen T) : HetRen T := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => r.act n

  def HetRen.append : List Nat -> HetRen T -> HetRen T
  | .nil, r => r
  | .cons hd tl, r => append tl (r.cons hd)

  instance : HAppend (List Nat) (HetRen T) (HetRen T) where
    hAppend := HetRen.append

  def HetRen.compose : HetRen T -> HetRen T -> HetRen T
  | r1, r2 => .mk λ n => r2.act (r1.act n)

  def Ren.het T (r : Ren) : HetRen T := ⟨r.act⟩

  @[simp]
  theorem Ren.het_action {T i} {r : Ren} : (r.het T).act i = r.act i := by simp [Ren.het]

  class HetRenMap (S T : Type) where
    hrmap : HetRen T -> S -> S

  export HetRenMap (hrmap)

  macro:max t:term noWs "⟨" r:term "⟩" : term => `(hrmap $r $t)
  infixr:67 (name := HetRen.cons_notation) " :: " => HetRen.cons
  infixr:85 (name := HetRen.compose_notation) " ∘ " => HetRen.compose

  @[app_unexpander hrmap]
  def unexpandHetRenApply : Lean.PrettyPrinter.Unexpander
  | `($_ $r $t) => `($t⟨$r⟩)
  | _ => throw ()

  @[simp, grind =]
  theorem HetRen.lift_zero {r : HetRen T} : r.lift 0 = r := by
    unfold HetRen.lift; congr

  @[grind =]
  theorem HetRen.lift_succ {r : HetRen T} {k} : r.lift (k + 1) = (r.lift k).lift := by
    induction k; simp
    case _ n ih =>
      unfold HetRen.lift; congr; funext; case _ i =>
      simp; unfold HetRen.lift at ih; simp at ih
      grind

  @[simp]
  theorem HetRen.id_action {x} : (HetRen.id T).act x = x := by simp [HetRen.id]

  @[simp]
  theorem HetRen.lift_id {k} : HetRen.lift (HetRen.id T) k = HetRen.id T := by
    simp [HetRen.id, HetRen.lift]; congr; funext; case _ x =>
    cases x <;> simp; omega

  @[simp]
  theorem HetRen.cons_head_action {n} {r : HetRen T} : (n::r).act 0 = n := by simp [HetRen.cons]

  @[simp]
  theorem HetRen.cons_tail_action {n i} {r : HetRen T} : (n::r).act (i + 1) = r.act i := by simp [HetRen.cons]

  @[simp]
  theorem HetRen.compose_id_left {r : HetRen T} : (id T) ∘ r = r := by
    simp [HetRen.compose, HetRen.id]

  @[simp]
  theorem HetRen.compose_id_right {r : HetRen T} : r ∘ (id T) = r := by
    simp [HetRen.compose, HetRen.id]

  @[simp]
  theorem HetRen.compose_assoc {r1 r2 r3 : HetRen T} : (r1 ∘ r2) ∘ r3 = r1 ∘ r2 ∘ r3 := by
    simp [HetRen.compose]

  @[simp]
  theorem HetRen.compose_action {r1 r2 : HetRen T} {x} : (r1 ∘ r2).act x = r2.act (r1.act x) := by
    simp [HetRen.compose]

  theorem HetRen.compose_lift_k1 {r1 r2 : HetRen T} : (r1 ∘ r2).lift = r1.lift ∘ r2.lift := by
    simp [HetRen.compose, HetRen.lift]
    funext; case _ x =>
    cases x <;> simp

  @[simp]
  theorem HetRen.compose_lift {k} {r1 r2 : HetRen T} : (r1 ∘ r2).lift k = r1.lift k ∘ r2.lift k := by
    induction k generalizing r1 r2; simp
    case _ k ih =>
      rw [lift_succ, ih]
      rw [lift_succ (r := r1)]
      rw [lift_succ (r := r2)]
      rw [compose_lift_k1]

  class HetRenMapId (S T : Type) [HetRenMap S T] where
    apply_id {t : S} : t⟨HetRen.id T⟩ = t

  class HetRenMapCompose (S T : Type) [HetRenMap S T] where
    apply_compose {s : S} {r1 r2 : HetRen T} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

  @[simp, grind =]
  theorem HetRen.apply_id [HetRenMap S T] [HetRenMapId S T] {t : S} : t⟨id T⟩ = t := HetRenMapId.apply_id

  @[simp, grind =]
  theorem HetRen.apply_compose [HetRenMap S T] [HetRenMapCompose S T] {t : S} {r1 r2 : HetRen T}
    : t⟨r1⟩⟨r2⟩ = t⟨r1 ∘ r2⟩
  := HetRenMapCompose.apply_compose

end LeanSubst
