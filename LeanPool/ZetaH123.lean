/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
module

public import LeanPool.ZetaH123.H1
public import LeanPool.ZetaH123.H2
public import LeanPool.ZetaH123.H3
public import LeanPool.ZetaH123.Lem41
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Thakur's hypotheses on power sums of F_q[t]

Source: arxiv:2606.16239
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
Status: verified
Main declarations: `ZetaH123.H1.main_theorem`, `ZetaH123.Lem41.main`
Tags: number-theory, function-fields, zeta-functions
MSC: 11M38, 11T55, 11G09
-/

@[expose] public section
