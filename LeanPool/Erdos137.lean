/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import LeanPool.Erdos137.Finiteness
public import LeanPool.Erdos137.Base
public import LeanPool.Erdos137.BlockFramework
public import LeanPool.Erdos137.RefinedOverlap
public import LeanPool.Erdos137.JointFiniteness
public import LeanPool.Erdos137.SmoothRefinement
public import LeanPool.Erdos137.TaoPoint
public import LeanPool.Erdos137.RoughPartStructure
public import LeanPool.Erdos137.SpliceFiniteness
public import LeanPool.Erdos137.QuarticCrude
public import LeanPool.Erdos137.SexticCrude
public import LeanPool.Erdos137.SquarefreeCapacity
public import LeanPool.Erdos137.CombinedSplice
public import LeanPool.Erdos137.AxiomAudit

/-!
# Erdős Problem #137: powerful products of consecutive integers

Source: url:https://www.erdosproblems.com/137
Authors: Scott D. Hughes
Status: verified
Main declarations: `Erdos137.erdos137_finite`, `Erdos137.erdos137_eventually_not_powerful`
Tags: number-theory, powerful-numbers, erdos-problems
MSC: 11A51, 11N25
-/

@[expose] public section
