/-
Copyright (c) 2026 Mary Jane. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mary Jane
-/

-- Source: the example from https://lean-lang.org/doc/reference/latest/Type-Classes/Deriving-Instances/
-- extended with case for empty type
import Lean
import Mathlib.Logic.IsEmpty
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

open Lean Elab Parser Term Command

universe u

class IsEnum (α : Type u) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x

def deriveIsEnum (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size = 1 then
    let env ← getEnv
    if let some (.inductInfo ind) := env.find? declNames[0] then
      if ind.ctors.isEmpty then
        let cmd ← `(
          instance : IsEnum $(mkIdent declNames[0]) where
            size      := 0
            toIdx     := Empty.elim
            fromIdx   := Fin.elim0
            to_from_id := by simp only [IsEmpty.forall_iff]
            from_to_id := by simp only [IsEmpty.forall_iff]
        )
        elabCommand cmd
        return true
      else
      let mut tos : Array (TSyntax ``matchAlt) := #[]
      let mut froms := #[]
      let mut to_froms := #[]
      let mut from_tos := #[]
      let mut i := 0

      for ctorName in ind.ctors do
        let c := mkIdent ctorName
        let n := Syntax.mkNumLit (toString i)

        tos      := tos.push      (← `(matchAltExpr| | $c => $n))
        from_tos := from_tos.push (← `(matchAltExpr| | $c => rfl))
        froms    := froms.push    (← `(matchAltExpr| | $n => $c))
        to_froms := to_froms.push (← `(matchAltExpr| | $n => rfl))

        i := i + 1

      let cmd ← `(instance : IsEnum $(mkIdent declNames[0]) where
                    size := $(quote ind.ctors.length)
                    toIdx $tos:matchAlt*
                    fromIdx $froms:matchAlt*
                    to_from_id $to_froms:matchAlt*
                    from_to_id $from_tos:matchAlt*)
      elabCommand cmd

      return true
  return false

initialize
  registerDerivingHandler ``IsEnum deriveIsEnum


namespace IsEnum
variable {α} {enum : IsEnum α}


def left_inv : Function.LeftInverse enum.fromIdx enum.toIdx :=
  enum.from_to_id

def right_inv : Function.RightInverse enum.fromIdx enum.toIdx :=
  enum.to_from_id

def equiv : α ≃ Fin (enum.size) where
  toFun := enum.toIdx
  invFun := enum.fromIdx
  left_inv := left_inv
  right_inv := right_inv

instance : Finite α := @Finite.intro _ (enum.size) equiv

def fromIdx_injective : Function.Injective enum.fromIdx := Function.LeftInverse.injective right_inv
def toIdx_injective : Function.Injective enum.toIdx := Function.LeftInverse.injective left_inv

-- Inspired by Mathlib.Data.Finset.Dedup.lean; toList, nodup_toList...
-- https://github.com/leanprover-community/mathlib4/blob/f4506f7151c9057fd9f8714b2a1f13a647fe2352/Mathlib/Data/Finset/Dedup.lean#L162-L164
section ToList
def toList : List α := List.ofFn enum.fromIdx

theorem nodup_toList : enum.toList.Nodup := by
  unfold List.Nodup
  unfold toList
  rw [List.pairwise_ofFn]
  intro i j hij
  apply Function.Injective.ne fromIdx_injective
  exact Fin.ne_of_lt hij

end ToList

end IsEnum
