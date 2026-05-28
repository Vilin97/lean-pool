/-
Copyright (c) 2026 Luka Opravš. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luka Opravš
-/

import LeanPool.PolyaEnumerationTheorem.Basic
import LeanPool.PolyaEnumerationTheorem.PermutationAuxiliary
import LeanPool.PolyaEnumerationTheorem.ReductionToFin
import LeanPool.PolyaEnumerationTheorem.Concrete
import LeanPool.PolyaEnumerationTheorem.StirlingFirstKindSum

/-!
# Pólya's enumeration theorem

Source: url:https://github.com/Luka-O/polya-enumeration-theorem
Authors: Luka Opravš
Status: verified
Main declarations: `LeanPool.PolyaEnumerationTheorem.polya_theorem`
Tags: combinatorics, group-theory, enumeration
MSC: 05A15, 20B30
-/

/-!
## Mathematical overview

Pólya's enumeration theorem (also known as the Redfield–Pólya theorem) counts
the number of distinct colorings of a set `X` with colors in `Y`, under a group
action `G ↷ X`, by averaging powers of `|Y|` over the cycle structure of each
group element acting on `X`. The formal statement proved here is

  `|X → Y / ∼| = (∑ g : G, |Y| ^ (number of cycles of g acting on X)) / |G|`,

where two colorings `f₁, f₂ : X → Y` are equivalent when there exists `g : G`
with `f₁ = g • f₂`.

The development also includes:

- a reduction lemma allowing any finitely enumerable `X` to be replaced by
  `Fin n` for explicit computations;
- definitions of distinct colorings for several concrete groups: the trivial
  group, the cyclic-rotation group on necklaces, the dihedral group on
  bracelets, the rotational symmetry group of the cube, and the symmetric
  group acting on a finite set.

Imported from <https://github.com/Luka-O/polya-enumeration-theorem> (originally
Lean v4.14.0-rc2) and ported to Lean Pool's v4.30.0-rc2 / Mathlib v4.30.0-rc2.
The upstream development additionally provides a fast `Array`-based computation
function and its correctness proof, plus the closed-form count of weak
compositions via the permutation group and an identity for unsigned Stirling
numbers of the first kind. These are omitted here, since their proofs rely
heavily on the pre-`setIfInBounds` `Array` API and on cycle-decomposition
tactics that do not transfer cleanly to the current Mathlib.
-/
