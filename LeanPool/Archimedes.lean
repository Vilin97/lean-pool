/-
Copyright (c) 2026 misaka10987. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: misaka10987
-/

import LeanPool.Archimedes.Basic

/-!
# Archimedes: 3D Euclidean Geometry

Source: url:https://github.com/misaka10987/archimedes
Authors: misaka10987
Status: verified
Main declarations: `A.Point.inner_product`, `A.Point.vector_product`, `A.Point.parallel_eq`
Tags: geometry, linear-algebra
-/

/-!
## Mathematical overview

*Archimedes* is a small mathematics library for Euclidean geometry in
3-dimensional Euclidean space, built on top of Mathlib's
`EuclideanSpace ℝ (Fin 3)`. It exposes intuitive, non-abstract
definitions for the common geometric primitives:

* `A.Point` — a point/vector in `ℝ³` with `x`, `y`, `z` accessors and a
  `NonZero` subtype.
* Dot and cross products (`∘`, `⨯`) with the explicit component formulas
  (`inner_product`, `vector_product`).
* The norm and unit-vector operations (`len`, `unit`, `unit_norm_one`,
  `len_dot_unit`, `sq_norm_eq_dot_self`).
* Distance between points (`dist`, `metric`).
* Parallel (`∥`), non-parallel (`∦`), perpendicular (`⟂`), and linear
  (in)dependence relations on `Point`, with reflexivity, symmetry,
  transitivity, and commutativity lemmas, plus an `Equivalence`
  instance `parallel_eq`.
* An asymmetric choice between a non-zero vector and its opposite
  (`asymm_chosen`, `NonZero.asymm_choose`) used to canonicalise lines
  spanned by a single direction.

## Provenance

Imported from <https://github.com/misaka10987/archimedes>; upstream
contains no `sorry`s. Ported from Lean v4.25.0-rc2 to Lean Pool's
v4.30.0-rc2. Local dotted-name proof identifiers (e.g. `parallel.refl`)
were renamed to snake_case (`parallel_refl`) to comply with Lean Pool's
naming conventions.
-/
