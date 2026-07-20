/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import LeanPool.Erdos137.Finiteness
import LeanPool.Erdos137.Base
import LeanPool.Erdos137.BlockFramework
import LeanPool.Erdos137.RefinedOverlap
import LeanPool.Erdos137.JointFiniteness
import LeanPool.Erdos137.SmoothRefinement
import LeanPool.Erdos137.TaoPoint
import LeanPool.Erdos137.RoughPartStructure
import LeanPool.Erdos137.SpliceFiniteness
import LeanPool.Erdos137.QuarticCrude
import LeanPool.Erdos137.SexticCrude
import LeanPool.Erdos137.SquarefreeCapacity
import LeanPool.Erdos137.CombinedSplice
import LeanPool.Erdos137.AxiomAudit

/-!
# Erdős Problem #137: powerful products of consecutive integers

Source: url:https://www.erdosproblems.com/137
Authors: Scott D. Hughes
Status: verified
Main declarations: `Erdos137.erdos137_finite`, `Erdos137.erdos137_eventually_not_powerful`
Tags: number-theory, powerful-numbers, erdos-problems
MSC: 11A51, 11N25
-/
