/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.KummerValuation
import LeanPool.Egrs75.CentralBinomialDigits
import LeanPool.Egrs75.Defs
import LeanPool.Egrs75.RoundUp
import LeanPool.Egrs75.LeafInduction
import LeanPool.Egrs75.DigitVector
import LeanPool.Egrs75.DigitAtToolkit
import LeanPool.Egrs75.AddBranch
import LeanPool.Egrs75.SubtractBranch
import LeanPool.Egrs75.ConditionThreeWindow
import LeanPool.Egrs75.LogIrrationality
import LeanPool.Egrs75.ClearingHigh
import LeanPool.Egrs75.Reduction
import LeanPool.Egrs75.BadPrefixRoute
import LeanPool.Egrs75.SeedWindow
import LeanPool.Egrs75.MoveDigits
import LeanPool.Egrs75.MuFinish
import LeanPool.Egrs75.Instances

/-!
# The Erdős–Graham–Ruzsa–Straus two-prime theorem

Source: doi:10.1090/S0025-5718-1975-0369288-3
Authors: Egor Lyfar
Status: verified
Main declarations: `Egrs75.MuFinish.egrs_two_prime_mu`, `Egrs75.Finish.egrs_two_prime_finish`
Tags: number-theory, central-binomial-coefficients, digit-representations, erdos-problems
MSC: 11A63, 11B65
-/
