/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.ITree.Monad

abbrev naturalTransformation (ε1 : Type u → Type v1) (ε2 : Type u → Type v2) :=
  ∀ {α : Type u}, ε1 α → ε2 α
infixr:50 " ⟶ "=> naturalTransformation

inductive VoidE : Type u → Type v

inductive SumE (ε1 ε2 : Type u → Type v) : Type u → Type v
  | inl {α : Type u} (e1 : ε1 α) : SumE ε1 ε2 α
  | inr {α : Type u} (e2 : ε2 α) : SumE ε1 ε2 α

instance : Add (Type u → Type v) where
  add := SumE

instance {ε1 ε2 : Type u → Type v} : Coe (ε1 α) (SumE ε1 ε2 α) where
  coe e := .inl e

instance {ε1 ε2 : Type u → Type v} : Coe (ε2 α) (SumE ε1 ε2 α) where
  coe e := .inr e

instance {ε1 ε2 : Type u → Type v} : Coe (ε1 α) ((ε1 + ε2) α) where
  coe e := .inl e

instance {ε1 ε2 : Type u → Type v} : Coe (ε2 α) ((ε1 + ε2) α) where
  coe e := .inr e

inductive IterState (ι : Type u) (ρ : Type v)
  | done  (r : ρ)
  | recur (i : ι)

class MonadIter (m : Type u -> Type v) where
  iter : {ρ ι : Type u} → (ι -> m (IterState ι ρ)) -> ι -> m ρ

instance instMonadIterStateT {σ m} [Monad m] [MI : MonadIter m] : MonadIter (StateT σ m) where
  iter step i s :=
    MonadIter.iter (fun (i, s) =>
      step i s >>= fun (i, s) =>
      match i with
      | .done r  => pure <| .done  (r, s)
      | .recur i => pure <| .recur (i, s)
    ) (i, s)

namespace ITree

inductive IterMode {ε ρ ι}
  | iterS (i : ι)
  | bindS (t : ITree ε (IterState ι ρ))

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

instance {ε : Type u → Type v} : MonadIter (ITree ε) where
  iter := ITree.iter

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
