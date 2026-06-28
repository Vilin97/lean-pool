/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import LeanPool.Redhill.BB94
import LeanPool.Redhill.Common.Conjectures
import LeanPool.Redhill.Common.MaxAbs
import LeanPool.Redhill.Common.PairwiseCoprime
import LeanPool.Redhill.Common.PrimeChain
import LeanPool.Redhill.Common.Quality
import LeanPool.Redhill.Common.SubsumCondition
import LeanPool.Redhill.Common.VWPair
import LeanPool.Redhill.General.Coprime
import LeanPool.Redhill.General.Defs
import LeanPool.Redhill.General.Main
import LeanPool.Redhill.General.Subsum
import LeanPool.Redhill.KonyaginPrelude
import LeanPool.Redhill.Odd.Defs
import LeanPool.Redhill.Odd.Main
import LeanPool.Redhill.Odd.Pell
import LeanPool.Redhill.Odd.Subsum
import LeanPool.Redhill.ToMathlib.NatAbs
import LeanPool.Redhill.ToMathlib.NatSumProd

/-!
# Improved Lower Bounds for Strong n-Conjectures

Source: doi:10.1017/S1446788725000084
Authors: Jeremy Tan
Status: verified
Main declarations: `not_ramaekersConjecture_ge_six`, `le_quality_nConjectureTuples`
Tags: number-theory, abc-conjecture, n-conjecture, ramaekers-conjecture
MSC: 11A41, 11D75
-/
