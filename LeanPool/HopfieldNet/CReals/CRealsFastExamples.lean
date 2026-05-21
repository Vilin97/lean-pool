/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealsFast

open Computable.Fast

namespace Computable.Fast.Examples
set_option autoImplicit false
/-!
This file is intentionally “executable-first”: it exists to demonstrate that the
`Computable.Fast` API works with `#eval` and `decide`.
-/

def dyadicHalf : Dyadic := ⟨1, -1⟩
def dyadicTwo  : Dyadic := ⟨1, 1⟩

-- Sanity: 1/2 at exponent 0 (integers)
-- floor(0.5) = 0, ceil(0.5) = 1, round-to-nearest-ties-to-even(0.5) = 0
#eval Dyadic.divDown 1 dyadicTwo 0
#eval Dyadic.divUp   1 dyadicTwo 0
#eval Dyadic.div     1 dyadicTwo 0

-- FastReal basic arithmetic and transcendental demo
#eval (2 : FastReal) + (dyadicHalf : Dyadic)  -- ~ 2.5
#eval FastReal.sqrt (4 : FastReal)            -- ~ 2
#eval FastReal.exp  (1 : FastReal)            -- ~ e
#eval FastReal.toDecimal (FastReal.exp 1) 12  -- exact decimal rendering (slow, but precise)
#eval FastReal.pi                         -- ~ π
#eval FastReal.toDecimal FastReal.pi 12

-- Partial ops: evaluated at a requested precision `n`
#eval (FastReal.inv? (2 : FastReal) 20)         -- some ~ 0.5
#eval (FastReal.log? (FastReal.exp 1) 20)       -- some ~ 1

def quarter : FastReal := (⟨1, -2⟩ : Dyadic)
def piOver4 : FastReal := FastReal.mul FastReal.pi quarter
#eval (FastReal.tan? piOver4 18)                -- some ~ 1 (may be `none` if cos can't be certified away from 0)

-- `decide` demo (semi-decision via fuel + `Option`)
#eval decide (FastReal.compare (2 : FastReal) (3 : FastReal) 40 == some Ordering.lt)

end Computable.Fast.Examples
