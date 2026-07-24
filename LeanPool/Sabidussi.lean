/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/

import LeanPool.Sabidussi.Color
import LeanPool.Sabidussi.CyclicWord
import LeanPool.Sabidussi.LocalPattern
import LeanPool.Sabidussi.LoopGraphBridge
import LeanPool.Sabidussi.LoopMultigraph
import LeanPool.Sabidussi.OddBalance
import LeanPool.Sabidussi.OrdinaryCircuit
import LeanPool.Sabidussi.Parity
import LeanPool.Sabidussi.Statement

/-!
# Sabidussi's compatibility conjecture for Eulerian multigraphs

Source: url:https://github.com/gexahedron/sabidussi-lean/blob/032e640df0cc41d4d3d217f7c68628ab19cb3767/sabidussi_proof.pdf
Authors: Nikolay Ulyanov
Status: verified
Main declarations: `Sabidussi.LoopMultigraph.loop_sabidussi_compatibility_ordinary`
Tags: graph-theory, eulerian-graphs, circuit-decomposition, sabidussi
MSC: 05C45
-/
