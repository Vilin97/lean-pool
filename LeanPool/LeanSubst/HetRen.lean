/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren

namespace LeanSubst
  universe u
  variable {S T : Type}

  /-- A renaming tagged by a target type `T`, represented by its action on indices. -/
  structure HetRen (T : Type) where
    /-- The underlying function on De Bruijn indices. -/
    act : Nat -> Nat

  /-- The identity heterogeneous renaming at type `T`. -/
  def HetRen.id T : HetRen T := ⟨λ x => x⟩

  /-- The heterogeneous renaming that shifts every index up by `k`. -/
  def HetRen.add T (k : Nat) : HetRen T := ⟨(· + k)⟩

  /-- The heterogeneous renaming that shifts every index down by `k`. -/
  def HetRen.sub T (k : Nat) : HetRen T := ⟨(· - k)⟩

  /-- Lift a heterogeneous renaming under `k` binders, fixing the first `k` indices. -/
  def HetRen.lift (r : HetRen T) (k : Nat := 1) : HetRen T := .mk λ n =>
    if n < k then n else r.act (n - k) + k

  /-- Extend a heterogeneous renaming by mapping index `0` to `a` and shifting the rest. -/
  def HetRen.cons (a : Nat) (r : HetRen T) : HetRen T := .mk λ n =>
    match n with
    | 0 => a
    | n + 1 => r.act n

  /-- Prepend a list of indices to a heterogeneous renaming via repeated `HetRen.cons`. -/
  def HetRen.append : List Nat -> HetRen T -> HetRen T
  | .nil, r => r
  | .cons hd tl, r => append tl (r.cons hd)

  instance : HAppend (List Nat) (HetRen T) (HetRen T) where
    hAppend := HetRen.append

  /-- Sequential composition of heterogeneous renamings: apply `r1` then `r2`. -/
  def HetRen.compose : HetRen T -> HetRen T -> HetRen T
  | r1, r2 => .mk λ n => r2.act (r1.act n)

  /-- View a plain renaming as a heterogeneous renaming at type `T`. -/
  def Ren.het T (r : Ren) : HetRen T := ⟨r.act⟩

  @[simp]
  theorem Ren.het_action {T i} {r : Ren} : (r.het T).act i = r.act i := by simp [Ren.het]

  /-- A type `S` whose values support being acted on by a heterogeneous renaming over `T`. -/
  class HetRenMap (S T : Type) where
    /-- Apply a heterogeneous renaming to a value. -/
    hrmap : HetRen T -> S -> S

  export HetRenMap (hrmap)

  /-- Notation `t⟨r⟩` for applying heterogeneous renaming `r` to `t`. -/
  macro:max t:term noWs "⟨" r:term "⟩" : term => `(hrmap $r $t)
  /-- Notation `a :: r` for `HetRen.cons`. -/
  infixr:67 (name := HetRen.consNotation) " :: " => HetRen.cons
  /-- Notation `r1 ∘ r2` for `HetRen.compose`. -/
  infixr:85 (name := HetRen.composeNotation) " ∘ " => HetRen.compose

  /-- Pretty-printer that displays `hrmap r t` as `t⟨r⟩`. -/
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

  /-- A `HetRenMap` for which applying the identity renaming is the identity. -/
  class HetRenMapId (S T : Type) [HetRenMap S T] where
    /-- Applying the identity heterogeneous renaming leaves a value unchanged. -/
    apply_id {t : S} : t⟨HetRen.id T⟩ = t

  /-- A `HetRenMap` for which heterogeneous renaming is functorial in composition. -/
  class HetRenMapCompose (S T : Type) [HetRenMap S T] where
    /-- Applying two renamings in sequence equals applying their composition. -/
    apply_compose {s : S} {r1 r2 : HetRen T} : s⟨r1⟩⟨r2⟩ = s⟨r1 ∘ r2⟩

  @[simp, grind =]
  theorem HetRen.apply_id [HetRenMap S T] [HetRenMapId S T] {t : S} : t⟨id T⟩ = t := HetRenMapId.apply_id

  @[simp, grind =]
  theorem HetRen.apply_compose [HetRenMap S T] [HetRenMapCompose S T] {t : S} {r1 r2 : HetRen T}
    : t⟨r1⟩⟨r2⟩ = t⟨r1 ∘ r2⟩
  := HetRenMapCompose.apply_compose

end LeanSubst
