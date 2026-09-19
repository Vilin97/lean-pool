/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import LeanPool.PentagonalNumberTheorem.Complex
public import LeanPool.PentagonalNumberTheorem.Generic
public import LeanPool.PentagonalNumberTheorem.Old
public import LeanPool.PentagonalNumberTheorem.Partition
public import LeanPool.PentagonalNumberTheorem.PowerSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Euler's pentagonal number theorem

Source: url:https://en.wikipedia.org/wiki/Pentagonal_number_theorem
Authors: Weiyi Wang
Status: verified
Main declarations: `pentagonalNumberTheorem_powerSeries`, `Nat.Partition.sum_partition`
Tags: number-theory, combinatorics, partitions, power-series, pentagonal-number-theorem
MSC: 11P81, 05A17
-/

@[expose] public section
