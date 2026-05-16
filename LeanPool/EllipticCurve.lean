/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import LeanPool.EllipticCurve.CategoryTheory
import LeanPool.EllipticCurve.Lemmas

/-!
# EllipticCurve

Source: url:https://github.com/kckennylau/EllipticCurve
Authors: Kenny Lau
Status: verified
Main declarations: `MultilinearMap.hom_ext`
Tags: algebraic-geometry, elliptic-curves, multilinear-maps
MSC: 14H52, 15A69, 18A40
-/

/-!
## Mathematical overview

Imports the elliptic-curve scaffolding from
<https://github.com/kckennylau/EllipticCurve>. The upstream project aims at a
general definition of elliptic curves over schemes, building up Grassmannians,
symmetric powers, the Proj of a graded algebra, and the big Zariski site on the
opposite category of commutative rings.

Most of that infrastructure has since been upstreamed to Mathlib
(`SymmetricPower`, `GradedFunLike`, `GradedRingHom`/`GradedAlgHom`,
`HomogeneousIdeal.irrelevant_*`, `Submodule.toBaseChange`, etc.), and the parts
that remain upstream-only depended on internals that were heavily refactored in
the move from Lean v4.25 to Lean v4.30 (the `PreZeroHypercover` rework of the
covering API, the `TypeCat`/`ConcreteCategory` rework of limits in `Type`, the
`@[simps]`/`cat_disch` defaults, and others). Reproducing those proofs against
the new APIs is out of scope for this import.

What this Lean Pool import preserves is:

- `LeanPool.EllipticCurve.Lemmas` — the upstream `Lemmas.lean` collection of
  small lemmas, lightly adapted to Lean v4.30/Mathlib v4.30-rc2. This is the
  "PR'able to Mathlib" scratchpad the upstream author maintains alongside the
  rest of the project (see the file's own docstring).
- `LeanPool.EllipticCurve.CategoryTheory.EqualizerCorepresentable` —
  `CorepresentableBy.homOfNatTrans` and its compatibility lemma, the only
  declarations from this file that are referenced downstream in the upstream
  project.

## Provenance

Imported from <https://github.com/kckennylau/EllipticCurve> (originally on
Lean v4.25.0-rc2) and ported to Lean Pool's v4.30.0-rc2 / Mathlib v4.30.0-rc2.
-/
