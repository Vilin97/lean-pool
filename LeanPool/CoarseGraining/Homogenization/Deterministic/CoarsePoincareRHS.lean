/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Correctors

/-!
# Coarse Poincare with right-hand side

Foundational wrapper for the local zero-trace RHS corrector package.
The recurrence and note-facing theorem files live under
`Homogenization/Deterministic/CoarsePoincareRHS/` and are re-exported by
`CoarsePoincareRHSLocalRecurrence.lean` until the Caccioppoli bridge import can be
retargeted without creating an import cycle.
-/
