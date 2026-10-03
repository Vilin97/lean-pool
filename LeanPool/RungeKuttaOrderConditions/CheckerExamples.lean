/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

import LeanPool.RungeKuttaOrderConditions.ButcherOrder

/-!
# Imported Runge-Kutta checker examples

These examples exercise the public computational definitions and tactic implementations
from a separate module, where only the exported interface is available.
-/

open RungeKuttaOrderConditions.Butcher

example : orderCond eulerA eulerB t1 := by butcherCheck
example : orderCond heunA heunB t2 := by butcherCheck
example : orderCond rk4A rk4B t44 := by butcherCheck
example : orderCond dpA dpB t5bushy := by butcherCheck
example : orderCond gaussA gaussB t1 := by gaussCheck
example : orderCond gaussA gaussB t2 := by gaussCheck
example : order leaf = 1 := by decide +kernel
