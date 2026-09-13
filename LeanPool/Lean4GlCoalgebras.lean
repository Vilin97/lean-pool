/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/
module

public import LeanPool.Lean4GlCoalgebras.General.Completeness
public import LeanPool.Lean4GlCoalgebras.General.Game
public import LeanPool.Lean4GlCoalgebras.General.Proof
public import LeanPool.Lean4GlCoalgebras.General.Soundness
public import LeanPool.Lean4GlCoalgebras.Interpolation.Interpolants
public import LeanPool.Lean4GlCoalgebras.Interpolation.Interpolation
public import LeanPool.Lean4GlCoalgebras.Split.ProofTransformations
public import LeanPool.Lean4GlCoalgebras.Logic.FixedPointTheorem
public import LeanPool.Lean4GlCoalgebras.Logic.Semantics
public import LeanPool.Lean4GlCoalgebras.Logic.Syntax
public import LeanPool.Lean4GlCoalgebras.Pdl.Game
public import LeanPool.Lean4GlCoalgebras.Split.Completeness
public import LeanPool.Lean4GlCoalgebras.Split.CutProof
public import LeanPool.Lean4GlCoalgebras.Split.Game
public import LeanPool.Lean4GlCoalgebras.Split.Proof
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Craig Interpolation for Gödel-Löb logic via coalgebraic proofs

Source: doi:10.1134/S0081543811060198
Authors: Madeleine Gignoux
Status: verified
Main declarations: `Lean4GlCoalgebras.interpolation`
Tags: modal-logic, provability-logic, craig-interpolation, proof-theory
MSC: 03B45, 03F45
-/

@[expose] public section
