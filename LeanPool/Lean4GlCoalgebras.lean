/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.General.Completeness
import LeanPool.Lean4GlCoalgebras.General.Game
import LeanPool.Lean4GlCoalgebras.General.Proof
import LeanPool.Lean4GlCoalgebras.General.Soundness
import LeanPool.Lean4GlCoalgebras.Interpolation.Interpolants
import LeanPool.Lean4GlCoalgebras.Interpolation.Interpolation
import LeanPool.Lean4GlCoalgebras.Split.ProofTransformations
import LeanPool.Lean4GlCoalgebras.Logic.FixedPointTheorem
import LeanPool.Lean4GlCoalgebras.Logic.Semantics
import LeanPool.Lean4GlCoalgebras.Logic.Syntax
import LeanPool.Lean4GlCoalgebras.Pdl.Game
import LeanPool.Lean4GlCoalgebras.Split.Completeness
import LeanPool.Lean4GlCoalgebras.Split.CutProof
import LeanPool.Lean4GlCoalgebras.Split.Game
import LeanPool.Lean4GlCoalgebras.Split.Proof

/-!
# Craig Interpolation for Gödel-Löb logic via coalgebraic proofs

Source: doi:10.1134/S0081543811060198
Authors: Madeleine Gignoux
Status: verified
Main declarations: `Lean4GlCoalgebras.interpolation`
Tags: modal-logic, provability-logic, craig-interpolation, proof-theory
MSC: 03B45, 03F45
-/
