/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.SLang

/-!
# ``probGeometric`` Implementation
-/

namespace SLang

section Geometric

variable (trial : SLang Bool)

/--
Termination condition: Check to see if has sampled ``true``.
-/
def geoLoopCond (st : Bool × ℕ) : Bool := st.1

/--
Sampling program: sample from ``trial`` and increment the number of attempts.
-/
def geoLoopBody (st : Bool × ℕ) : SLang (Bool × ℕ):= do
  let x ← trial
  return (x,st.2 + 1)

/-- ``SLang`` term for a geometric distrubution on ``Nat``.

Iteratively samples from ``trial``, returning the number of attempts before a ``true`` sample.
-/
def probGeometric : SLang ℕ := do
  let st ← probWhile geoLoopCond (geoLoopBody trial) (true,0)
  return st.2

end Geometric

end SLang
