/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Tactic
namespace LeanLJ

class HasSqrt (α : Type) where
  sqrt : α → α

instance : HasSqrt Float where
  sqrt := Float.sqrt

instance : HasSqrt ℕ where
  sqrt := Nat.sqrt

instance : HasSqrt ℤ where
  sqrt := Int.sqrt

instance : HasSqrt ℚ where
  sqrt := Rat.sqrt

noncomputable instance : HasSqrt ℝ where
  sqrt := Real.sqrt


class HasRound (α : Type) where
  pround : α → α

instance : HasRound Float where
  pround := Float.round

class RealLike (α : Type) extends HasRound α, HasSqrt α where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  pow : α → Nat → α
  le : α → α → Bool
  lt : α → α → Bool
  zero : α
  one : α
  ofNat : Nat → α
  ofInt : Int → α

instance {α : Type} [RealLike α] : Add α where
  add := RealLike.add

instance {α : Type} [RealLike α] : Sub α where
  sub := RealLike.sub

instance {α : Type} [RealLike α] : Mul α where
  mul := RealLike.mul

instance {α : Type} [RealLike α] : Div α where
  div := RealLike.div

instance {α : Type} [RealLike α] : Neg α where
  neg := RealLike.neg

instance {α : Type} [RealLike α] : Pow α Nat where
  pow := RealLike.pow

-- Helper functions for comparison that return Bool
def compLe {α : Type} [RealLike α] (a b : α) : Bool :=
  RealLike.le a b

def compLt {α : Type} [RealLike α] (a b : α) : Bool :=
  RealLike.lt a b

instance {α : Type} [RealLike α] {n : Nat} : OfNat α n where
  ofNat := RealLike.ofNat n

-- Provide a Coe instance for literals
instance {α : Type} [RealLike α] : Coe Nat α where
  coe := RealLike.ofNat

-- Float instance
instance : RealLike Float where
  pround := Float.round
  sqrt := Float.sqrt
  add := Float.add
  sub := Float.sub
  mul := Float.mul
  div := Float.div
  neg := Float.neg
  pow := fun x n =>
    let rec go (x : Float) (n : Nat) : Float :=
      match n with
      | 0 => 1.0
      | k + 1 => x * go x k
    go x n
  le a b := a ≤  b
  lt a b := a < b
  zero := 0.0
  one := 1.0
  ofNat n := Float.ofNat n
  ofInt n := Float.ofInt n

-- Int instance (for completeness)
instance : RealLike Int where
  pround := fun x => x
  sqrt := fun x => x
  add := Int.add
  sub := Int.sub
  mul := Int.mul
  div a b := if b == 0 then 0 else a / b  -- Simple integer division
  neg := Int.neg
  pow a n :=
    let rec go (a : Int) (n : Nat) : Int :=
      match n with
      | 0 => 1
      | k + 1 => a * go a k
    go a n
  le a b := a ≤  b
  lt a b := a < b
  zero := 0
  one := 1
  ofNat := Int.ofNat
  ofInt n := n
/-
instance {α : Type} [ComputableReal α] : LE α where
  le a b := ComputableReal.le a b -/

instance {α : Type} [RealLike α] : LT α where
  lt a b := RealLike.lt a b = true


-- Define LT instance for ComputableReal
instance {α : Type} [RealLike α] : DecidableRel (@LT.lt α _) :=
  fun a b =>
    if h : RealLike.lt a b = true then
      isTrue h
    else
      isFalse (by intro h'; contradiction)


-- Define LE instance for ComputableReal
instance {α : Type} [RealLike α] : LE α where
  le a b := RealLike.le a b = true

-- Define DecidableRel instance for LE.le
instance {α : Type} [RealLike α] : DecidableRel (@LE.le α _) :=
  fun a b =>
    if h : RealLike.le a b = true then
      isTrue h
    else
      isFalse (by intro h'; contradiction)


end LeanLJ
