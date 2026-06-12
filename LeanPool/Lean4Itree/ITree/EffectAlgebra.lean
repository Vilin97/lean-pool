/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.ITree.Monad

/-!
# Effect algebra for interaction trees

This module provides the algebra of effects used to combine and interpret
interaction trees: natural transformations between effect families, the empty
and sum effects (`VoidE`, `SumE`), the `MonadIter` class of iterable monads, the
`iter` iteration combinator, and the `interp` interpretation of an `ITree`
against an effect handler into an arbitrary iterable monad.
-/

namespace Lean4Itree

/-- A natural transformation between effect families: a uniform map `ε1 α → ε2 α`. -/
abbrev naturalTransformation (ε1 : Type u → Type v1) (ε2 : Type u → Type v2) :=
  ∀ {α : Type u}, ε1 α → ε2 α
/-- Notation `ε1 ⟶ ε2` for a natural transformation between effect families. -/
scoped infixr:50 " ⟶ " => naturalTransformation

/-- The empty effect family, with no operations. -/
inductive VoidE : Type u → Type v

/-- The sum of two effect families: an effect is either from `ε1` or from `ε2`. -/
inductive SumE (ε1 ε2 : Type u → Type v) : Type u → Type v
  | inl {α : Type u} (e1 : ε1 α) : SumE ε1 ε2 α
  | inr {α : Type u} (e2 : ε2 α) : SumE ε1 ε2 α

/-- Addition of effect families is their sum `SumE`. -/
instance instAddEffect : Add (Type u → Type v) where
  add := SumE

/-- Coerce a left effect into the sum `SumE ε1 ε2`. -/
instance instCoeSumEInl {ε1 ε2 : Type u → Type v} : Coe (ε1 α) (SumE ε1 ε2 α) where
  coe e := .inl e

/-- Coerce a right effect into the sum `SumE ε1 ε2`. -/
instance instCoeSumEInr {ε1 ε2 : Type u → Type v} : Coe (ε2 α) (SumE ε1 ε2 α) where
  coe e := .inr e

/-- Coerce a left effect into the sum `(ε1 + ε2)`. -/
instance instCoeAddInl {ε1 ε2 : Type u → Type v} : Coe (ε1 α) ((ε1 + ε2) α) where
  coe e := .inl e

/-- Coerce a right effect into the sum `(ε1 + ε2)`. -/
instance instCoeAddInr {ε1 ε2 : Type u → Type v} : Coe (ε2 α) ((ε1 + ε2) α) where
  coe e := .inr e

/-- The result of one iteration step: either `done` with a result or `recur`
with the next accumulator. -/
inductive IterState (ι : Type u) (ρ : Type v)
  | done  (r : ρ)
  | recur (i : ι)

/-- The class of monads supporting tail-recursive iteration via `iter`. -/
class MonadIter (m : Type u → Type v) where
  /-- Iterate a step function until it returns `done`. -/
  iter : {ρ ι : Type u} → (ι → m (IterState ι ρ)) → ι → m ρ

/-- `StateT` lifts `MonadIter` by threading the state through each iteration step. -/
instance instMonadIterStateT {σ : Type u} {m : Type u → Type u} [Monad m] [MI : MonadIter m] :
    MonadIter (StateT σ m) where
  iter step i s :=
    MonadIter.iter (fun (i, s) =>
      step i s >>= fun (i, s) =>
      match i with
      | .done r  => pure <| .done  (r, s)
      | .recur i => pure <| .recur (i, s)
    ) (i, s)

namespace ITree

/-- The traversal mode used by `iter`: either start a new iteration (`iterS`) or
continue binding the tree produced by a step (`bindS`). -/
inductive IterMode {ε ρ ι}
  | iterS (i : ι)
  | bindS (t : ITree ε (IterState ι ρ))

/-- Iterate `step` from the seed `i`, producing the interaction tree that loops
until a step returns `done`. -/
def iter {ε ρ ι} (step : ι → ITree ε (IterState ι ρ)) (i : ι) : ITree ε ρ :=
  .corec' (fun rec (s : IterMode) =>
    match s with
    | .bindS t =>
      match t.dest with
      | ⟨.ret v, _⟩ =>
        match v with
        | .done r => .inl <| ret r
        | .recur l => .inr <| tau' <| rec <| .bindS (step l)
      | ⟨.tau, c⟩ => .inr <| tau' <| rec <| .bindS <| c 0
      | ⟨.vis _ e, k⟩ => .inr <| vis' e <| fun a => rec <| .bindS <| k a
    | .iterS i => .inr <| tau' <| rec <| .bindS (step i)
  ) (.iterS i)

/-- Interaction trees iterate via the `ITree.iter` combinator. -/
instance instMonadIterITree {ε : Type u → Type v} : MonadIter (ITree ε) where
  iter := ITree.iter

/-- Interpret an interaction tree by handling each effect with `handler` and
running the resulting computation in an iterable monad `m`. -/
def interp {ε : Type → Type} {m : Type 1 → Type 1} {ρ : Type} [Monad m] [MI : MonadIter m]
  (handler : {α : Type} → ε α → m (ULift α)) (t : ITree ε ρ) : m (ULift ρ) :=
  MonadIter.iter (fun t =>
    match t.dest with
    | ⟨.ret v, _⟩ => return .done <| .up v
    | ⟨.tau, c⟩   => return .recur (c 0)
    | ⟨.vis _ e, k⟩ => do
      let a ← handler e
      let i := k (ULift.down a)
      return .recur i
  ) t

end ITree

end Lean4Itree
