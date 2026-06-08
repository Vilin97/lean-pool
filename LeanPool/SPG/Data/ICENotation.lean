/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import LeanPool.SPG.Geometry.SpinOps

/-!
# ICE notation for spin point group elements

This module provides a constructor turning a spatial matrix and a
time-reversal flag into an `SPGElement`, encoding the ICE convention for spin
point group operations.
-/

namespace SPG.Data

open SPG.Geometry.SpinOps

/-- Mk Ice Element. -/
def mkIceElement (spatial : Matrix (Fin 3) (Fin 3) ℚ) (time_reversal : Bool) : SPGElement :=
  { spatial := spatial,
    spin := if time_reversal then spinNegI else spinI }

end SPG.Data
