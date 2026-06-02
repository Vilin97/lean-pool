/-
Copyright (c) 2026 Antoine de Saint Germain, Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint Germain, Ambrose Tang
-/

import LeanPool.RootSystem.An
import LeanPool.RootSystem.BCn

/-!
# Explicit construction of classical root systems

Source: url:https://antoine-dsg.github.io/root_system/
Authors: Antoine de Saint Germain, Ambrose Tang
Status: verified
Main declarations: `An.rootPairing`, `BCn.rootPairing`
Tags: representation-theory, root-systems, lie-theory, combinatorics
MSC: 17B22, 20F55
-/

/-!
## Mathematical overview

This project gives explicit, computation-friendly constructions of the classical
root systems and exhibits them as Mathlib `RootPairing`s.

- `An`: the type `Aₙ` root pairing, built combinatorially from *signed intervals*
  on `Fin n`, with the root/coroot pairing and reflection identities verified.
- `BCn.rootPairing`: the type `BCₙ` root pairing, built from the standard
  dot-product space, using a symmetric nondegenerate bilinear form.

## References

For the classification and explicit data of the classical root systems see
N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Springer, 2002
(Plates I-IV), and J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, Graduate Texts in Mathematics 9, Springer, 1972,
Chapter III.
-/
