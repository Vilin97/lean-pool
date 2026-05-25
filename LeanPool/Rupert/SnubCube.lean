/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Basic

namespace SnubCube

/-- Real cube root, written using real powers. -/
noncomputable abbrev cbrt (x : ℝ) : ℝ := x ^ (1/3 : ℝ)

/-- tribonacci constant -/
noncomputable def trib : ℝ :=
  (1 + cbrt (19 + 3 * √33) + cbrt (19 - 3 * √33) ) / 3

/-- Coordinates for a snub cube. -/
noncomputable def snub_cube : Fin 24 → ℝ³ :=
 ![ !₂[      -1,  1/trib,    trib],
    !₂[       1, -1/trib,    trib],
    !₂[       1,  1/trib,   -trib],
    !₂[      -1, -1/trib,   -trib],
    !₂[ -1/trib,    trib,       1],
    !₂[  1/trib,   -trib,       1],
    !₂[  1/trib,    trib,      -1],
    !₂[ -1/trib,   -trib,      -1],
    !₂[   -trib,       1,  1/trib],
    !₂[    trib,      -1,  1/trib],
    !₂[    trib,       1, -1/trib],
    !₂[   -trib,      -1, -1/trib],
    !₂[       1,   -trib, -1/trib],
    !₂[      -1,    trib, -1/trib],
    !₂[      -1,   -trib,  1/trib],
    !₂[      -1,    trib,  1/trib],
    !₂[  1/trib,      -1,   -trib],
    !₂[ -1/trib,       1,   -trib],
    !₂[ -1/trib,      -1,    trib],
    !₂[  1/trib,       1,    trib],
    !₂[     trib, -1/trib,     -1],
    !₂[    -trib,  1/trib,     -1],
    !₂[    -trib, -1/trib,      1],
    !₂[     trib,  1/trib,      1]
  ]

proof_wanted rupert : ¬ IsRupert snub_cube

end SnubCube
