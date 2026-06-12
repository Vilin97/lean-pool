/-
Copyright (c) 2026 Antoine de Saint Germain, Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint Germain, Ambrose Tang
-/

import LeanPool.RootSystem.An
import LeanPool.RootSystem.BCn

/-!
# Explicit type Aₙ and BCₙ root pairings

Source: doi:10.1007/978-1-4612-6398-2, url:https://antoine-dsg.github.io/root_system/
Authors: Antoine de Saint Germain, Ambrose Tang
Status: verified
Main declarations: `An.rootPairing`, `BCn.rootPairing`, `BCn.isReflective_iff_isClassicalRoot`
Tags: representation-theory, root-systems, lie-theory, combinatorics
MSC: 17B22, 20F55
-/

/-!
## Mathematical overview

This project gives explicit, computation-friendly constructions of the type `Aₙ`
and `BCₙ` root pairings over `ℤ`, exhibited as Mathlib `RootPairing`s.

- `An.rootPairing`: the type `Aₙ` root pairing, built combinatorially from *signed
  intervals* on `Fin n`, with the root/coroot pairing and reflection identities
  verified and the pairing shown to be finite, reduced, and crystallographic.
- `BCn.rootPairing`: the type `BCₙ` root pairing, built from the reflective vectors
  of the standard dot product on `ℤⁿ`; `BCn.isReflective_iff_isClassicalRoot` and
  `BCn.range_rootPairing_root` identify its roots with the classical type-`BCₙ`
  root set `{±eᵢ, ±2eᵢ, ±eᵢ ± eⱼ (i ≠ j)}`.

## References

For the classification and explicit data of the classical root systems see
N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Springer, 2002
(Plates I-IV), and J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Graduate Texts in Mathematics 9, Springer, 1972,
Chapter III (DOI 10.1007/978-1-4612-6398-2).
-/
