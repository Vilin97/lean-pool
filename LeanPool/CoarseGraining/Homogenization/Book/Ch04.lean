/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Law
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.MuLocalityGate
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Observable
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionLaw
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.RestrictionObservable
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Source
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems

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

@[expose] public section
