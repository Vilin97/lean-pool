/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/

import LeanPool.SingularModuli.QuadraticOrder.Basic

/-!
# Quadratic-order verification checks

This file records a small sanity check for the defining minimal polynomial of
`tau`.
-/

/-- Sanity check: `τ` satisfies its minimal polynomial `X² - dX + (d²-d)/4 = 0`. -/
example (d : ℤ) : (QuadraticOrder.tau (d := d)) ^ 2 - d • QuadraticOrder.tau +
    ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 :=
  QuadraticOrder.tau_minimal_poly
