/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.ConvexBody
import LeanPool.NandakumarRamanaRao.NRR.SupportFunction
import LeanPool.NandakumarRamanaRao.NRR.HalfSpace

/-!
# `NRR.PowerDiagram.Defs` — core definitions

Base definitions for the power-diagram API: the power (Laguerre) distance `powerDist` and the
power cell `cell` of a site.

These definitions are isolated so that the implementation modules under `NRR/PowerDiagram/` can depend on the
core definitions, while the top-level `NRR.PowerDiagram` re-exports the full, proved API
(see `NRR/PowerDiagram.lean`). This breaks what would otherwise be an import cycle.

Given `n` sites `s : Fin n → E2` and weights `w : Fin n → ℝ`, the power cell of site `i` is
`{x : ∀ j, ‖x - sᵢ‖² - wᵢ ≤ ‖x - sⱼ‖² - wⱼ}`.
-/

open NRR MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Power (Laguerre) distance** of `x` to site `i` with weight `w i`. -/
noncomputable def powerDist (s : Fin n → E2) (w : Fin n → ℝ) (i : Fin n) (x : E2) : ℝ :=
  ‖x - s i‖ ^ 2 - w i

/-- **Power cell** of site `i`: the points closer (in power distance) to `i` than to any `j`. -/
noncomputable def cell (s : Fin n → E2) (w : Fin n → ℝ) (i : Fin n) : Set E2 :=
  {x | ∀ j, powerDist s w i x ≤ powerDist s w j x}

end NRR.PowerDiagram
