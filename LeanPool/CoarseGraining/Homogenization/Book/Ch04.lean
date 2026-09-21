/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.MuLocalityGate
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Observable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionLaw
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionObservable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Source
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems

/-!
# Chapter 4

Chapter 4 exposes source-facing laws, local observables, annealed objects, and
theorem APIs used by later chapters. Its unprefixed law, locality, and
observable facade names have the exact coarse-source, integral-local semantics.
The pointwise-restriction/sup-metric engineering lane is explicit throughout:
its semantic API names begin with `Restriction`, including
`RestrictionCoeffLaw`, `RestrictionLawCarrier`, and `RestrictionObservable`.

Route-specific witnesses and proof packages live under `Internal` namespaces or
inside private declarations. The `Source` umbrella faithfully imports the
current Chapter 4 source modules, while the restriction lane remains available
through its explicit modules and endpoints.
-/
