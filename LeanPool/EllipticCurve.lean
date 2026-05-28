/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import LeanPool.EllipticCurve.CategoryTheory
import LeanPool.EllipticCurve.Lemmas
import LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricMap
import LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.BaseChange
import LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricPower

/-!
# EllipticCurve

Source: url:https://github.com/kckennylau/EllipticCurve
Authors: Kenny Lau
Status: verified
Main declarations: `SymmetricPower.lift`, `MultilinearMap.hom_ext`
Tags: algebraic-geometry, elliptic-curves, multilinear-maps, symmetric-powers
MSC: 14H52, 15A69, 18A40
-/

/-!
## Mathematical overview

Imports the elliptic-curve scaffolding from
<https://github.com/kckennylau/EllipticCurve>. The upstream project aims at a
general definition of elliptic curves over schemes, building up symmetric
powers, Grassmannians, the Proj of a graded algebra, and the big Zariski site on
the opposite category of commutative rings.

Much of that infrastructure has since been upstreamed to Mathlib in a
*generalized* form (`SymmetricPower` over an arbitrary index type, the graded
homomorphism hierarchy `GradedFunLike`/`GradedRingHom`/`GradedAlgHom`,
`HomogeneousIdeal.irrelevant_*`, `Submodule.toBaseChange`,
`TensorProduct.directSumLeft`/`directSumRight`, `Module.Grassmannian`, etc.).

What this Lean Pool import preserves is the upstream-only content that is **not**
yet in Mathlib and does not depend on internals that were refactored
incompatibly between Lean v4.25 and Lean v4.30:

- `LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricMap` — symmetric
  multilinear maps `M [Σ^ι]→ₗ[R] N` as a module, with composition, base point
  reindexing, and the empty/subsingleton special cases. Mathlib has no
  `SymmetricMap`.
- `LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.BaseChange` — base change
  of (symmetric) multilinear maps along an algebra for a finite index type.
- `LeanPool.EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricPower` — the
  `Fin n`-indexed symmetric tensor power as a graded commutative algebra: the
  universal property `lift`, functoriality `map`, the graded multiplication
  `mul`, evaluation, base change, and the `GradedMonoid.GCommMonoid` structure.
  Mathlib's `SymmetricPower` only fixes the underlying module and notation; all
  of the algebra here is upstream-only (it is the contents of Mathlib's TODO
  list for that file).
- `LeanPool.EllipticCurve.Lemmas` — the upstream `Lemmas.lean` collection of
  small lemmas, lightly adapted to Lean v4.30/Mathlib v4.30-rc2.
- `LeanPool.EllipticCurve.CategoryTheory.EqualizerCorepresentable` —
  `CorepresentableBy.homOfNatTrans` and its compatibility lemma.

The remaining upstream files — the graded homomorphism `Equiv`/`Admissible`
layers, the Proj/scheme constructions, the Grassmannian charts, and the big
Zariski site — were written against the bundled `GradedFunLike` design and the
pre-refactor `TypeCat`/`ConcreteCategory` limit and sites APIs, and reproducing
them against the new APIs is out of scope for this import.

## Provenance

Imported from <https://github.com/kckennylau/EllipticCurve> (originally on
Lean v4.25.0-rc2) and ported to Lean Pool's v4.30.0-rc2 / Mathlib v4.30.0-rc2.
-/
