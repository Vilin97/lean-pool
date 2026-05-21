/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.SLang
import LeanPool.HopfieldNet.SampCert.Samplers.Uniform.Code
import LeanPool.HopfieldNet.SampCert.Samplers.BernoulliNegativeExponential.Code

/-!
# ``DiscreteLaplaceSample`` Implementation

This file implements a sampler for the discrete laplace distribution.

## Implementation notes

The following identifiers violate our naming scheme, but are currently necessary for extraction:
  - ``DiscreteLaplaceSampleLoopIn1Aux``
  - ``DiscreteLaplaceSampleLoopIn1``
  - ``DiscreteLaplaceSampleLoopIn2Aux``
  - ``DiscreteLaplaceSampleLoopIn2``
  - ``DiscreteLaplaceSampleLoop``
  - ``DiscreteLaplaceSample``
-/

namespace SLang

def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : SLang (Nat × Bool) := do
  let U ← UniformSample t
  let D ← BernoulliExpNegSample U t
  return (U,D)

def DiscreteLaplaceSampleLoopIn1 (t : PNat) : SLang Nat := do
  let r1 ← probUntil (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
  return r1.1

-- Note that for the arxiv algorithm, we can call Unit directly
def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat)  (K : Bool × Nat) : SLang (Bool × Nat) := do
  let A ← BernoulliExpNegSample num den
  return (A, K.2 + 1)

def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : SLang Nat := do
  let r2 ← probWhile (λ K : Bool × Nat => K.1) (DiscreteLaplaceSampleLoopIn2Aux num den) (true,0)
  return r2.2

-- We need to generate and test both implementations
def DiscreteLaplaceSampleLoop' (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
  let U ← DiscreteLaplaceSampleLoopIn1 num
  let v ← DiscreteLaplaceSampleLoopIn2 1 1
  let V := v - 1
  let X := U + num * V
  let Y := X / den
  let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
  return (B,Y)

def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
  let v ← DiscreteLaplaceSampleLoopIn2 den num
  let V := v - 1
  let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
  return (B,V)

/--
``SLang`` term to obtain a sample from the discrete Laplace distribution, optimized for
`num/den` (≤ or ≥) `DiscreteLaplaceSampleOptThresh`
-/
def DiscreteLaplaceSample (num den : PNat) : SLang ℤ := do
  let r ← probUntil (DiscreteLaplaceSampleLoop num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

/--
``SLang`` term to obtain a sample from the discrete Laplace distribution, optimized for
`num/den` (≤ or ≥) `DiscreteLaplaceSampleOptThresh`.
-/
def DiscreteLaplaceSampleOptimized (num den : PNat) : SLang ℤ := do
  let r ← probUntil (DiscreteLaplaceSampleLoop' num den) (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
  let Z : Int := if r.1 then - r.2 else r.2
  return Z

/--
``SLang`` term to obtain a sample from the discrete Laplace distribution, optimized
based on (num/den).

FIXME: Extractor breaks when we move 50 to an external constant, even when we specify @[always_inline]
-/
def DiscreteLaplaceSampleMixed (num den : PNat) (mix: ℕ) : SLang ℤ := do
  if num ≤ den * mix
    then let v <- DiscreteLaplaceSample num den; return v
    else let v <- DiscreteLaplaceSampleOptimized num den; return v

end SLang
