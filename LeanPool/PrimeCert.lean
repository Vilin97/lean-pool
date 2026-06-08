/-
Copyright (c) 2026 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import LeanPool.PrimeCert.Interval
import LeanPool.PrimeCert.Meta.PrimeCert
import LeanPool.PrimeCert.Meta.SmallPrime
import LeanPool.PrimeCert.Pocklington
import LeanPool.PrimeCert.Pocklington3
import LeanPool.PrimeCert.PowMod
import LeanPool.PrimeCert.PredMod
import LeanPool.PrimeCert.SmallPrimes
import LeanPool.PrimeCert.Wieferich

/-!
# Formally verified primality certificates

Source: doi:10.1090/S0025-5718-1975-0384673-1, url:https://github.com/b-mehta/PrimeCert
Authors: Kenny Lau, Bhavik Mehta
Status: verified
Main declarations: `pocklington_test`, `PrimeCert.pocklington3_test`, `wieferich_mirimanoff`
Tags: number-theory, primality-testing, pocklington, primality-certificate, metaprogramming
MSC: 11A41, 11Y11
-/
