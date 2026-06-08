/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import LeanPool.SPG.Geometry.SpinOps

/-!
# Notation for spin point group elements

This module introduces the `^1` / `^-1` spin notation and the `Op[·, ·]`
constructor syntax for building `SPGElement`s concisely.
-/

namespace SPG.Interface

open SPG.Geometry.SpinOps

-- Notation for spin operations
-- ^1 for spin identity (spinI)
-- ^-1 for spin reversal (spinNegI)

/-- Notation `^1` for the spin identity operation. -/
syntax "^1" : term
/-- Notation `^-1` for the spin reversal (time-reversal) operation. -/
syntax "^-1" : term

macro_rules
  | `(^1) => `(spinI)
  | `(^-1) => `(spinNegI)

-- Notation for creating SPGElement
-- Op[spatial, spin]

/-- Notation `Op[spatial, spin]` for building an `SPGElement`. -/
syntax "Op[" term "," term "]" : term

macro_rules
  | `(Op[ $spatial, $spin ]) => `({ spatial := $spatial, spin := $spin : SPGElement })

end SPG.Interface
