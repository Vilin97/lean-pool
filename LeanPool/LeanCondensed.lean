/-
Copyright (c) 2026 Dagur Asgeirsson, Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/

import LeanPool.LeanCondensed.Mathlib
import LeanPool.LeanCondensed.Projects

/-!
# LeanCondensed: split short exact sequence and infrastructure for light condensed modules

Source: url:https://github.com/dagurtomas/LeanCondensed
Authors: Dagur Asgeirsson, Jonas van der Schaaf
Status: verified
Main declarations: `LightCondensed.PSequence_exact`
Tags: condensed-mathematics, category-theory, monoidal-categories
MSC: 18N99, 18F20
-/

/-!
## Mathematical overview

`LeanCondensed` collects formalised condensed-mathematics results due to
Dustin Clausen and Peter Scholze, following Scholze's *Lectures on
Condensed Mathematics* (Bonn, 2019) and the theory of *light condensed
sets* introduced by Clausen and Scholze. The vendored subset consists of
the sorry-free, port-stable fragment of the upstream development.

The headline result, `LightCondensed.PSequence_exact`, exhibits the short
complex

`(free R) PUnit ⟶ (free R) (ℕ∪{∞}) ⟶ P R`

as a (split) short exact sequence in `LightCondMod R`, where `P R` is the
cokernel of the inclusion induced by the unique map `PUnit ⟶ ℕ∪{∞}` and
`free R` is the left adjoint to the forgetful functor on light condensed
modules.

The supporting infrastructure includes:

- An explicit colimit cone witnessing that an effective epimorphism in
  `LightProfinite` is an effective epimorphism after applying
  `lightProfiniteToLightCondSet`.
- Preservation of finite coproducts by the topology-level Yoneda
  embedding for a subcanonical topology under which every sheaf
  preserves finite products.
- A monoidal equivalence between a category `D` and its localized
  monoidal counterpart `LocalizedMonoidal L W ε`.
- Monoidal preadditive and monoidal linear structures transported from a
  monoidal localization to its `LocalizedMonoidal` and to a category of
  sheaves, specialized to light condensed modules.
- Auxiliary lemmas on countable thin categories and on preservation of
  epimorphisms under retracts of natural transformations.

## Provenance

Imported from <https://github.com/dagurtomas/LeanCondensed> (originally
Lean v4.28.0-rc1) and ported to Lean Pool's v4.30.0-rc2 / Mathlib
v4.30.0-rc2. Upstream files that still depend on `sorry` placeholders
(`AdjointFunctorTheorem`, `FreeCondensed`, `LightSolid`, `SheafMonoidal`,
and the `Mathlib/CategoryTheory/Sites/DirectImage.lean` supplement) are
not part of this import. The upstream proof of
`LightCondensed.internallyProjective_free_natUnionInfty` is sorry-free
but relies on a long, rewrite-driven proof in `Projects/Proj.lean` that
the Lean v4.28 → v4.30 toolchain bump broke at multiple sites; it is
omitted from this import.
-/
