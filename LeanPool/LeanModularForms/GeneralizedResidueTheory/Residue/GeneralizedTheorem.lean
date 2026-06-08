/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.GeneralizedResidueTheorem

/-!
# Residue/GeneralizedTheorem (legacy stub)

The original file under `Residue/GeneralizedTheorem.lean` re-declared
`generalizedResidueTheorem` at root namespace, clashing with the canonical
`GeneralizedResidueTheory.GeneralizedResidueTheorem` (which is the version that other
parts of the project — `Cycle.lean`, `ViazovskaMagicFunction.lean` — actually import).
We retire this duplicate as a re-export.
-/
