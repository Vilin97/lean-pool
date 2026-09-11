/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import LeanPool.Redhill.BB94
public import LeanPool.Redhill.Common.Conjectures
public import LeanPool.Redhill.Common.MaxAbs
public import LeanPool.Redhill.Common.PairwiseCoprime
public import LeanPool.Redhill.Common.PrimeChain
public import LeanPool.Redhill.Common.Quality
public import LeanPool.Redhill.Common.SubsumCondition
public import LeanPool.Redhill.Common.VWPair
public import LeanPool.Redhill.General.Coprime
public import LeanPool.Redhill.General.Defs
public import LeanPool.Redhill.General.Main
public import LeanPool.Redhill.General.Subsum
public import LeanPool.Redhill.KonyaginPrelude
public import LeanPool.Redhill.Odd.Defs
public import LeanPool.Redhill.Odd.Main
public import LeanPool.Redhill.Odd.Pell
public import LeanPool.Redhill.Odd.Subsum
public import LeanPool.Redhill.ToMathlib.NatAbs
public import LeanPool.Redhill.ToMathlib.NatSumProd

/-!
# Improved Lower Bounds for Strong n-Conjectures

Source: doi:10.1017/S1446788725000084
Authors: Jeremy Tan
Status: verified
Main declarations: `not_ramaekersConjecture_ge_six`, `le_quality_nConjectureTuples`
Tags: number-theory, abc-conjecture, n-conjecture, ramaekers-conjecture
MSC: 11A41, 11D75
-/

@[expose] public section
