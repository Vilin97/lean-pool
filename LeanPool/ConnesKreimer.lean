/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/

import LeanPool.ConnesKreimer.Coassoc
import LeanPool.ConnesKreimer.Core
import LeanPool.ConnesKreimer.PowerSeriesLogMul

/-!
# Connes-Kreimer Hopf algebra of rooted trees

Source: doi:10.5281/zenodo.20762280
Authors: Carles Marín
Status: verified
Main declarations: `CK.instCKHopf`, `CK.instHabHopf`, `CK.eulerian1_idem_ab`
Tags: hopf-algebras, rooted-trees, renormalization, combinatorics
MSC: 16T05, 05C05, 81T15
-/

/-!
Top-level import for the Connes-Kreimer / Foissy Hopf algebra development.

The main module `LeanPool.ConnesKreimer.Core` constructs the planar rooted-tree
Hopf algebra, its commutative quotient, Adams operators, and the Eulerian
idempotent on the quotient.  The auxiliary modules keep the standalone
power-series logarithm lemmas and the core list-level coassociativity proof
available as separate imports.
-/
