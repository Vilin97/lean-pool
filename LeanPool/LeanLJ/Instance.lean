/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import Mathlib.Data.Rat.Sqrt
import Mathlib.Analysis.Real.Sqrt

/-!
# A `RealLike` typeclass for generic numeric backends

This file introduces the `HasSqrt`, `HasRound` and `RealLike` typeclasses together with
instances for `Float`, `Int` and the standard ordered fields, so that the Lennard-Jones
functions can be stated uniformly over any numeric type that supports the needed operations.
-/

namespace LeanLJ

/-- Numeric types equipped with a square-root operation. -/
class HasSqrt (α : Type) where
  /-- The square root of an element. -/
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


/-- Numeric types equipped with a rounding operation (round to nearest). -/
class HasRound (α : Type) where
  /-- Round an element to the nearest integral value of the same type. -/
  pround : α → α

instance : HasRound Float where
  pround := Float.round

/-- A lightweight interface bundling the field-like operations used by the Lennard-Jones
functions, so they can be evaluated over `Float`, `Int`, `ℝ`, etc. -/
class RealLike (α : Type) extends HasRound α, HasSqrt α where
  /-- Addition. -/
  add : α → α → α
  /-- Subtraction. -/
  sub : α → α → α
  /-- Multiplication. -/
  mul : α → α → α
  /-- Division. -/
  div : α → α → α
  /-- Negation. -/
  neg : α → α
  /-- Natural-number power. -/
  pow : α → Nat → α
  /-- Less-than-or-equal comparison as a `Bool`. -/
  le : α → α → Bool
  /-- Strict-less-than comparison as a `Bool`. -/
  lt : α → α → Bool
  /-- The additive identity. -/
  zero : α
  /-- The multiplicative identity. -/
  one : α
  /-- Coercion from a natural number. -/
  ofNat : Nat → α
  /-- Coercion from an integer. -/
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

/-- Helper that compares two `RealLike` elements with `≤`, returning a `Bool`. -/
def compLe {α : Type} [RealLike α] (a b : α) : Bool :=
  RealLike.le a b

/-- Helper that compares two `RealLike` elements with `<`, returning a `Bool`. -/
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


/-- Decidability of `<` on a `RealLike` type, via its `Bool`-valued comparison. -/
instance instDecidableRelLt {α : Type} [RealLike α] : DecidableRel (@LT.lt α _) :=
  fun a b =>
    if h : RealLike.lt a b = true then
      isTrue h
    else
      isFalse (by intro h'; contradiction)


-- Define LE instance for ComputableReal
instance {α : Type} [RealLike α] : LE α where
  le a b := RealLike.le a b = true

/-- Decidability of `≤` on a `RealLike` type, via its `Bool`-valued comparison. -/
instance instDecidableRelLe {α : Type} [RealLike α] : DecidableRel (@LE.le α _) :=
  fun a b =>
    if h : RealLike.le a b = true then
      isTrue h
    else
      isFalse (by intro h'; contradiction)


end LeanLJ
