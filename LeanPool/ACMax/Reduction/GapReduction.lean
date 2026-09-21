/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.NormNum
import LeanPool.ACMax.Counting.LargeN
import LeanPool.ACMax.Spectral.AlgConnK2

/-!
# Numerical specialization of the linear large-order bound

`boundLin_sharp2_value` evaluates the bound from
`Counting.LargeN.acmax_conjecture_large_n_sharp2` to `17692`.
The complete all-order theorem is assembled separately in `Band.Final`.
-/

namespace ACMax

open Classical in
/-- The **doubly-sharpened** large-`n` threshold (`acmax_conjecture_large_n_sharp2`,
`Counting.WallSharp`, mid-leaf bound `108` ⟹ usable cap `C_m ≤ 306`) evaluates to
`17 692` — the current finite frontier. -/
theorem boundLin_sharp2_value : boundLin ((128 * 306 + 34508) / 23) = 17692 := boundLin_sharp2_eq

end ACMax
