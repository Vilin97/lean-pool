/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.Samplers.Bernoulli.Code

/-!
# Implementation of the Bernoulli Negative Exponential distribution

This file implements the Bernoulli Negative Exponential (BNE) distribution: the distribution
on ``Bool`` which samples ``true`` with probability ``exp (-num / den)``.

## Implementation Notes

This implementation uses an method for sampling from the BNE widely known as ``Von Neumann's algorithm``.

The following identifiers violate our naming scheme, but are currently necessary for extraction:
  - ``BernoulliExpNegSampleUnitLoop``
  - ``BernoulliExpNegSampleUnitAux``
  - ``BernoulliExpNegSampleUnit``
  - ``BernoulliExpNegSampleGenLoop``
  - ``BernoulliExpNegSample``
-/

namespace SLang

lemma halve_wf (num : Nat) (den st : PNat) (wf : num ≤ den) :
  num ≤ ↑(st * den) := by
  simp
  cases st
  rename_i v p
  simp
  exact le_mul_of_one_le_of_le p wf

/--
``SLang`` term which changes the state, according to the discrete Von Neumann's algorithm.

In particular, it updates the state ``(_, n)`` to
  - ``(true, n+1)`` with probability ``(num/den) / n``
  - ``(false, n+1)`` with probability ``1 - (num/den) / n``
-/
def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den) (state : (Bool × PNat)) : SLang (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
  return (A, state.2 + 1)

/--
``SLang`` term for the distribution over ``ℕ`` obtained by performing discrete Von Neumann
updates until the state becomes ``false``, and returning one more than the total number
of updates.

In particular, at ``n ≥ 2`` this distribution evaluates to
```
  (num/den)/1 ⬝ (num/den)/2 ⬝ ⋯ ⬝ (num/den)/(n-2) ⬝ (1 - (num/den)(n-1))
= (num/den)^(n-2) / (n-2)! - (num/den)^(n-1) / (n-1)!
```
and evaluates to ``0`` at ``0``.
-/
def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Nat := do
  let r ← probWhile (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
  return r.2

/--
``SLang`` term which samples ``true`` with probability ``exp (-num/den)``.


This program implments this distrubution by returning ``true`` when
``BernoulliExpNegSampleUnitAux`` is even, namely with probability
```
  0 + (num/den)^0 / 0! - (num/den)^1 / 1! + (num/den)^2 / 2! - (num/den)^3 / 3! + ...
= ∑ (n : ℕ) (-num/den)^i / i!
= exp (-num/den)
```
-/
def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Bool := do
  let K ← BernoulliExpNegSampleUnitAux num den wf
  if K % 2 = 0 then return true else return false

/--
``SLang`` term which samples ``true`` with probability ``exp (- iter)``.

In particular this program returns true upon the success of ``iter`` trials of
``BernoulliExpNegSampleUnit 1 1``, which occurs with probability
  ```
    exp (-1/1) ⬝ ... ⬝ exp (-1/1) = exp (- iter)
  ```
-/
def BernoulliExpNegSampleGenLoop (iter : Nat) : SLang Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
    if ¬ B then return B else
      let R ← BernoulliExpNegSampleGenLoop (iter - 1)
      return R

/--
Proof term to apply a a call to ``BernoulliExpNegSampleUnit``.
-/
lemma rat_less_floor_le1 (num : Nat) (den : PNat) :
  (num % den) ≤ den := by
  have A := Nat.mod_lt num (PNat.pos den)
  exact Nat.lt_succ.mp (Nat.le.step A)

/--
``SLang`` term which samples ``true`` with probability ``exp (- num / den)``.

The algorithm returns ``true`` when a trial for both the integral and fractional
parts of ``num/den``, since
```
exp (-num/den) = exp((-num/den : ℕ_{≤0}) + (num % den)) = exp (-num/den : ℕ_{≤0}) ⬝exp (num % den)
```
-/
-- Can I combine the cases here? Can't tell which way would be less annoying down the road.
def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := do
  if h : num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den h
       return X
  else
    let gamf := num / den
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
      let X ← BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)
      return X
    else return false

end SLang
