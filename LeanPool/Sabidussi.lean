/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
module

public import LeanPool.Sabidussi.Color
public import LeanPool.Sabidussi.CyclicWord
public import LeanPool.Sabidussi.LocalPattern
public import LeanPool.Sabidussi.LoopGraphBridge
public import LeanPool.Sabidussi.LoopMultigraph
public import LeanPool.Sabidussi.OddBalance
public import LeanPool.Sabidussi.OrdinaryCircuit
public import LeanPool.Sabidussi.Parity
public import LeanPool.Sabidussi.Statement
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Sabidussi's compatibility conjecture for Eulerian multigraphs

Source: url:https://github.com/gexahedron/sabidussi-lean/blob/032e640df0cc41d4d3d217f7c68628ab19cb3767/sabidussi_proof.pdf
Authors: Nikolay Ulyanov
Status: verified
Main declarations: `Sabidussi.LoopMultigraph.loop_sabidussi_compatibility_ordinary`
Tags: graph-theory, eulerian-graphs, circuit-decomposition, sabidussi
MSC: 05C45
-/

@[expose] public section
