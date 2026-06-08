/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic

/-!
# Group closure of spin point group generators

This module computes the multiplicative closure of a finite list of
`SPGElement` generators by fixed-point iteration: it repeatedly adds all
pairwise products until the deduplicated list stops growing.

The closure operator `closureStep` is monotone in the sense that the result
always contains its input, so the length is nondecreasing.  The driver
`closureFuel` performs the iteration with an explicit fuel counter, giving a
structurally terminating recursion: as long as the list keeps growing the
length strictly increases, so the fixed point is reached within
`fuel` steps for any fuel that bounds the size of the closure.  The public
`generateGroup` supplies a fuel that is more than sufficient for the finite
point groups studied here, while still returning as soon as the closure is
stable.
-/

namespace SPG.Algebra

/-- One step of the closure: add all pairwise products of the current list and
deduplicate. -/
def closureStep (current : List SPGElement) : List SPGElement :=
  let newElements :=
    (current.flatMap fun g1 => current.flatMap fun g2 => [g1 * g2]).eraseDups
  (current ++ newElements).eraseDups

/-- Iterate `closureStep` until the deduplicated list stops growing or the
fuel runs out.  The recursion is structural in the fuel counter. -/
def closureFuel : Nat → List SPGElement → List SPGElement
  | 0, current => current
  | fuel + 1, current =>
    let combined := closureStep current
    if combined.length == current.length then current
    else closureFuel fuel combined

/--
Generate the group closure from a list of generators.
This uses a fixed-point iteration: repeatedly adding all pairwise products
until the set size stabilizes.

The fuel `2 ^ (gens.length + 8)` is a safe over-approximation of the number of
iterations: each iteration that recurses adds at least one new element, and the
closures of the finite point groups considered here are far smaller than this
bound, so the iteration always reaches the genuine fixed point.
-/
def generateGroup (gens : List SPGElement) : List SPGElement :=
  closureFuel (2 ^ (gens.length + 8)) gens

/-- Combine Generators. -/
def combineGenerators (gens₁ gens₂ : List SPGElement) : List SPGElement :=
  generateGroup (gens₁ ++ gens₂)

end SPG.Algebra
