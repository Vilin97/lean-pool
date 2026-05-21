/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert
import LeanPool.HopfieldNet.SampCert.SLang

-- Entry point to check properties of the FFI

def main : IO Unit := do
  -- Check if FFI is working
  IO.print "Sampling bytes: "
  for _ in [:10000] do
    let x <- PMF.run <| SLang.probUniformByte_PMF
    IO.println x
