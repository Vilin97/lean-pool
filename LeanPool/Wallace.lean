/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.GeneralMain
import LeanPool.Wallace.RealMain
import LeanPool.Wallace.TychonoffWallace

/-!
# Countably compact groups and the Wallace counterexample

This library proves the paper's main theorem for every torsion-free Abelian group of cardinality
continuum.  It also exposes the free, rational, real, and Baer--Specker specializations.  The
nonnegative cone in the free Abelian group gives a commutative Tychonoff countably compact
cancellative topological additive monoid which is not a group.  The internal Section 10
propositions on large closures and suitable sets are included as well.

The public entry point exposes the three principal statements from the paper.
-/
