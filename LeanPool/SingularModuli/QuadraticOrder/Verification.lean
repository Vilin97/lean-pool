/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Caleb L. Geiger
-/
module

public import LeanPool.SingularModuli.QuadraticOrder.Basic

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Quadratic-order verification checks

This file records a small sanity check for the defining minimal polynomial of
`tau`.
-/

@[expose] public section

/-- Sanity check: `τ` satisfies its minimal polynomial `X² - dX + (d²-d)/4 = 0`. -/
example (d : ℤ) : (QuadraticOrder.tau (d := d)) ^ 2 - d • QuadraticOrder.tau +
    ((d ^ 2 - d) / 4 : ℤ) • (1 : QuadraticOrder d) = 0 :=
  QuadraticOrder.tau_minimal_poly
