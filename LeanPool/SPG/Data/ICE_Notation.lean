/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import LeanPool.SPG.Geometry.SpinOps

namespace SPG.Data

open SPG.Geometry.SpinOps

def mk_ice_element (spatial : Matrix (Fin 3) (Fin 3) ℚ) (time_reversal : Bool) : SPGElement :=
  { spatial := spatial,
    spin := if time_reversal then spin_neg_I else spin_I }

end SPG.Data
