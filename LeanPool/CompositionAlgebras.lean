/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/

import LeanPool.CompositionAlgebras.Octonions
import LeanPool.CompositionAlgebras.OctonionTrace
import LeanPool.CompositionAlgebras.OctonionNucleus
import LeanPool.CompositionAlgebras.OctonionModule
import LeanPool.CompositionAlgebras.Composition.Defs
import LeanPool.CompositionAlgebras.Composition.Instances
import LeanPool.CompositionAlgebras.Composition.Doubling
import LeanPool.CompositionAlgebras.Composition.CayleyDickson
import LeanPool.CompositionAlgebras.Composition.Hurwitz
import LeanPool.CompositionAlgebras.Composition.Isomorphisms
import LeanPool.CompositionAlgebras.Composition.Classification

/-!
# Hurwitz's Classification of Euclidean Composition Algebras

Source: url:https://eudml.org/doc/58420
Authors: Bryan Ehrlich
Status: verified
Main declarations: `CompositionAlgebra.hurwitz_classification`
Tags: nonassociative-algebra, composition-algebras, octonions, hurwitz-theorem, cayley-dickson
MSC: 17A75, 17A35, 11E88
-/

/-!
# Euclidean composition algebras over `ℝ`

The root module: importing this pulls in the whole development.

## Layout

* `Octonions.lean` -- the octonions as a concrete 8-tuple of reals, with the
  Cayley-Dickson multiplication table written out, conjugation, and the real part
* `OctonionTrace.lean` -- the trace form `re (x y)` and its symmetry and cyclicity
* `OctonionNucleus.lean` -- the substantive inclusion from the octonion nucleus into `ℝ`
* `OctonionModule.lean` -- `AddCommGroup`, `Module ℝ`, `FiniteDimensional ℝ` on `𝕆`,
  the Euclidean form `octIp`, and `finrank ℝ 𝕆 = 8`
* `Composition/Defs.lean` -- the `CompositionAlgebra` class and its identity toolkit
* `Composition/Instances.lean` -- `ℝ`, `ℂ`, `ℍ`, `𝕆` as composition algebras
* `Composition/Doubling.lean` -- composition subalgebras and the doubling step
* `Composition/CayleyDickson.lean` -- the `CD` type former and its instance
* `Composition/Hurwitz.lean` -- the dimension theorem
* `Composition/Isomorphisms.lean` -- the iterated doubles are `ℝ`, `ℂ`, `ℍ`, `𝕆`
* `Composition/Classification.lean` -- Hurwitz's classification theorem

## Lean Pool port

This copy is modified from upstream commit `e37e22b0571a170ba18a0d8db29fe2a857906b92`
for Lean Pool's Lean/Mathlib toolchain and repository rules. It keeps the complete Hurwitz
dimension and classification chain, its Cayley--Dickson infrastructure, and the concrete
octonion results used by the registered claims. The port omits the independent Palomar
challenge/solution packets and audit harness, the unfinished Hermitian-matrix carrier and
its unused complex-subspace support tail, and three unused coordinate-expanded Moufang
lemmas. Generic alternativity remains available through the octonion `CompositionAlgebra`
instance. The octonion-nucleus proof was also
refactored to use seven sufficient coordinate equations instead of generating all 56.
-/
