/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Tactic.Basic

/-!
# LeanPool.EcTateLean.Algebra.EllipticCurve.KodairaTypes

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.EllipticCurve.KodairaTypes`.
-/

-- For imperfect residue fields of characteristic 2 or 3 there are new types:
-- Z1, Z2, X1, X2, Y1, Y2, Y3, K n (n ≥ 2), K' n (even n ≥ 2), T n (n ≥ 1)

/-- The Kodaira symbol classifying the reduction type of an elliptic curve at a
place, including the extra symbols that arise over imperfect residue fields of
characteristic 2 or 3. -/
inductive Kodaira where
  | I     : Nat → Kodaira --for both I0 and In with n > 0
  | II    : Kodaira
  | III   : Kodaira
  | IV    : Kodaira
  | Is    : Nat → Kodaira
  | IIs   : Kodaira
  | IIIs  : Kodaira
  | IVs   : Kodaira
  | Z1    : Kodaira
  | Z2    : Kodaira
  | X1    : Kodaira
  | X2    : Kodaira
  | Y1    : Kodaira
  | Y2    : Kodaira
  | Y3    : Kodaira
  | K     : Nat → Kodaira -- only occurs for n ≥ 2
  | K'    : Nat → Kodaira -- only occurs for even n ≥ 2
  | T     : Nat → Kodaira -- only occurs for n ≥ 1
deriving DecidableEq, Inhabited

open Kodaira

instance : Repr Kodaira where
  reprPrec
    | I m, _   => "I" ++ repr m
    | II, _    => "II"
    | III, _   => "III"
    | IV, _    => "IV"
    | Is m, _  => "I*" ++ repr m
    | IIs, _   => "II*"
    | IIIs, _  => "III*"
    | IVs, _   => "IV*"
    | Z1, _    => "Z1"
    | Z2, _    => "Z2"
    | X1, _    => "X1"
    | X2, _    => "X2"
    | Y1, _    => "Y1"
    | Y2, _    => "Y2"
    | Y3, _    => "Y3"
    | K m, _   => "K" ++ repr m
    | K' m, _   => "K'" ++ repr m
    | T m, _   => "T" ++ repr m

lemma eq_I_Nat (m n : Nat) : m = n ↔ I m = I n := by
  apply Iff.intro
  · intro h
    exact congrArg I h
  · intro h
    cases h
    rfl

lemma eq_Is_Nat (m n : Nat) : m = n ↔ Is m = Is n := by
  apply Iff.intro
  · intro h
    exact congrArg Is h
  · intro h
    cases h
    rfl

/-- The coarse reduction type of an elliptic curve at a place: good, split or
non-split multiplicative, or additive. -/
inductive ReductionType
  | Good
  | SplitMultiplicative
  | NonSplitMultiplicative
  | Additive
deriving DecidableEq, Repr, Inhabited

/-- The integer code that the LMFDB uses for a reduction type. -/
def ReductionType.toLmfdb : ReductionType → Int
  | Good                   => unreachable! -- LMFDB has no code for good reduction
  | SplitMultiplicative    => 1
  | NonSplitMultiplicative => -1
  | Additive               => 0
