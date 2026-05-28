/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/

import LeanPool.ArtinWedderburn.IdealProd
import LeanPool.ArtinWedderburn.SetProd
import LeanPool.ArtinWedderburn.Auxiliary
import LeanPool.ArtinWedderburn.NonUnitalToUnital
import LeanPool.ArtinWedderburn.PrimeRing
import LeanPool.ArtinWedderburn.CornerRing
import LeanPool.ArtinWedderburn.MinIdeals
import LeanPool.ArtinWedderburn.Idempotents
import LeanPool.ArtinWedderburn.CornerCornerLemma
import LeanPool.ArtinWedderburn.MatrixUnits
import LeanPool.ArtinWedderburn.NiceIdeals
import LeanPool.ArtinWedderburn.ArtinWedderburnTheorem

/-!
# Artin-Wedderburn Theorem

Source: url:https://doi.org/10.1007/978-1-4419-8616-0
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
Status: verified
Main declarations: `LeanPool.ArtinWedderburn.ArtinWedderburnForPrime`
Tags: ring-theory, noncommutative-algebra, artinian-rings
MSC: 16K20, 16P20
-/

/-!
## Mathematical overview

The classical Artin–Wedderburn theorem describes the structure of semisimple
Artinian rings. This development formalises two flavours of the theorem in
Lean 4. For a nontrivial prime Artinian ring `R`, there exist a natural number
`n`, a division ring `D`, and a ring isomorphism
`R ≃+* Matrix (Fin n) (Fin n) D`
(`LeanPool.ArtinWedderburn.ArtinWedderburnForPrime`). The same conclusion holds
for any nontrivial Artinian simple ring
(`LeanPool.ArtinWedderburn.ArtinWedderburnForSimple`), since simple rings are
prime.

The proof factors `R` through a system of pairwise orthogonal idempotents whose
corner subrings are division rings (`OrtIdemDiv`), upgrades these idempotents to
matrix units, and concludes that `R` is isomorphic to a matrix ring over the
corner subring of the first matrix unit. The argument follows the standard
matrix-unit proof of the Artin-Wedderburn theorem for Artinian prime and simple
rings.

The exported modules mirror the proof structure: products of ideals
(`LeanPool.ArtinWedderburn.IdealProd`, `LeanPool.ArtinWedderburn.SetProd`),
elementary lemmas on division (sub)rings
(`LeanPool.ArtinWedderburn.Auxiliary`,
`LeanPool.ArtinWedderburn.NonUnitalToUnital`), the prime-ring characterisation
(`LeanPool.ArtinWedderburn.PrimeRing`), corner subrings and their basic theory
(`LeanPool.ArtinWedderburn.CornerRing`,
`LeanPool.ArtinWedderburn.CornerCornerLemma`), minimal-ideal idempotent
extraction (`LeanPool.ArtinWedderburn.MinIdeals`), the orthogonal-idempotent
machinery (`LeanPool.ArtinWedderburn.Idempotents`), matrix-unit data
(`LeanPool.ArtinWedderburn.MatrixUnits`), the nice-ideal induction
(`LeanPool.ArtinWedderburn.NiceIdeals`), and the main theorems
(`LeanPool.ArtinWedderburn.ArtinWedderburnTheorem`).

## Provenance

Imported from <https://github.com/JobPetrovcic/ArtinWedderburn>. The upstream
project is sorry-free at import time. Ported from Lean `v4.14.0-rc2` (the
upstream toolchain) to Lean Pool's `v4.30.0-rc2`. All declarations have been
wrapped in the `LeanPool.ArtinWedderburn` namespace to avoid collisions with
Mathlib symbols.
-/
