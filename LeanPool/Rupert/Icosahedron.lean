/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.NumberTheory.Real.GoldenRatio
import LeanPool.Rupert.Basic
import LeanPool.Rupert.Convex
import LeanPool.Rupert.MatrixSimps
import LeanPool.Rupert.Quaternion
import LeanPool.Rupert.Equivalences.RupertEquivRupertPrime

/-!
# LeanPool.Rupert.Icosahedron

Imported Lean Pool material for `LeanPool.Rupert.Icosahedron`.
-/

namespace Icosahedron

open scoped Matrix goldenRatio

/-- The twelve vertices of a regular icosahedron in `ℝ³`. -/
noncomputable def icosahedron : Fin 12 → ℝ³ := ![
  !₂[ 1,  φ,  0],
  !₂[ 1, -φ,  0],
  !₂[-1,  φ,  0],
  !₂[-1, -φ,  0],
  !₂[ φ,  0,  1],
  !₂[ φ,  0, -1],
  !₂[-φ,  0,  1],
  !₂[-φ,  0, -1],
  !₂[ 0,  1,  φ],
  !₂[ 0,  1, -φ],
  !₂[ 0, -1,  φ],
  !₂[ 0, -1, -φ]]

proof_wanted rupert : IsRupert icosahedron

end Icosahedron
