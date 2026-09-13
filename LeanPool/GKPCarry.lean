/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.GKPCarry.DensityOne
public import LeanPool.GKPCarry.FiniteRangeCorollary
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Density-One GKP Divisibility and Its Carry-Language Characterization

Source: url:https://cs.stanford.edu/~knuth/gkp.html
Authors: Egor Lyfar
Status: verified
Main declarations: `GKPCarry.tendsto_gkpSuccessProportion_one`
Tags: number-theory, finite-automata, asymptotic-density
MSC: 11A63, 11B65, 68Q45
-/

@[expose] public section
