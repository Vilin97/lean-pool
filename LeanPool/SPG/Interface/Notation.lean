/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import LeanPool.SPG.Geometry.SpinOps

namespace SPG.Interface

open SPG.Geometry.SpinOps

-- Notation for spin operations
-- ^1 for spin identity (spin_I)
-- ^-1 for spin reversal (spin_neg_I)

syntax "^1" : term
syntax "^-1" : term

macro_rules
  | `(^1) => `(spin_I)
  | `(^-1) => `(spin_neg_I)

-- Notation for creating SPGElement
-- Op[spatial, spin]

syntax "Op[" term "," term "]" : term

macro_rules
  | `(Op[ $spatial, $spin ]) => `({ spatial := $spatial, spin := $spin : SPGElement })

end SPG.Interface
