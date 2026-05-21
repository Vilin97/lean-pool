/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log

/-!
# SLang

This file describes the SLang language.

## Implementation notes

Each ``SLang`` value is a distribution over a type (normalization of these distributions
is proven separately). There are no restrictions on the type; the underlying probability
space should be interpreted as discrete.
-/

open Classical Nat ENNReal PMF

/--
The monad of ``SLang`` values
-/
abbrev SLang.{u} (α : Type u) : Type u := α → ℝ≥0∞

namespace PMF

/--
``SLang`` value from ``PMF``
-/
def toSLang (p : PMF α) : SLang α := p.1

@[simp]
theorem toSLang_apply (p : PMF α) (x : α) : (toSLang p x) = p x := by
  unfold toSLang
  unfold DFunLike.coe
  unfold instFunLike
  simp

instance : Coe (PMF α) (SLang α) where
  coe a := toSLang a

end PMF

namespace SLang

/-!
### Program terms of ``SLang``
-/

variable {T U : Type}

/--
The zero distribution as a ``SLang``.
-/
def probZero : SLang T := λ _ : T => 0

/--
The Dirac distribution as a ``SLang``.
-/
@[extern "prob_Pure"]
def probPure (a : T) : SLang T := fun a' => if a' = a then 1 else 0

/--
Monadic bind for ``SLang`` values.
-/
@[extern "prob_Bind"]
def probBind (p : SLang T) (f : T → SLang U) : SLang U :=
  fun b => ∑' a, p a * f a b

instance : Monad SLang where
  pure a := probPure a
  bind pa pb := pa.probBind pb


/--
Uniform distribution on a byte
-/
@[extern "prob_UniformByte"]
def probUniformByte : SLang UInt8 := (fun _ => 1 / UInt8.size)

/--
Upper i bits from a unifomly sampled byte
-/
def probUniformByteUpperBits (i : ℕ) : SLang ℕ := do
  let w <- probUniformByte
  return w.toNat.shiftRight (8 - i)

/--
Uniform distribution on the set [0, 2^i) ⊆ ℕ
-/
def probUniformP2 (i : ℕ) : SLang ℕ :=
  if (i < 8)
  then probUniformByteUpperBits i
  else do
    let v <- probUniformByte
    let w <- probUniformP2 (i - 8)
    return UInt8.size * w + v.toNat

/--
``SLang`` value for the uniform distribution over ``m`` elements, where
the number``m`` is the largest power of two that is at most ``n``.
-/
def UniformPowerOfTwoSample (n : ℕ+) : SLang ℕ :=
  probUniformP2 (log 2 n)


/--
``SLang`` functional which executes ``body`` only when ``cond`` is ``false``.
-/
def probWhileFunctional (cond : T → Bool) (body : T → SLang T) (wh : T → SLang T) : T → SLang T :=
  λ a : T =>
  if cond a
    then do
      let v ← body a
      wh v
    else return a

/--
``SLang`` value obtained by unrolling a loop body exactly ``n`` times.
-/
def probWhileCut (cond : T → Bool) (body : T → SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => probZero
  | succ n => probWhileFunctional cond body (probWhileCut cond body n) a


/--
``SLang`` value for an unbounded iteration of a loop.
-/
@[extern "prob_While"]
def probWhile (cond : T → Bool) (body : T → SLang T) (init : T) : SLang T :=
  fun x => ⨆ (i : ℕ), (probWhileCut cond body i init x)

/--
``SLang`` value which rejects samples from ``body`` until they satisfy ``cond``.
-/
--@[extern "prob_Until"]
def probUntil (body : SLang T) (cond : T → Bool) : SLang T := do
  let v ← body
  probWhile (λ v : T => ¬ cond v) (λ _ : T => body) v

end SLang

namespace PMF

@[extern "my_run"]
opaque run (c : PMF T) : IO T

end PMF
