/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import LeanPool.ZFLean.Basic
public import LeanPool.ZFLean.Booleans
public import LeanPool.ZFLean.Naturals
public import LeanPool.ZFLean.Integers
public import LeanPool.ZFLean.Rationals
public import LeanPool.ZFLean.Tactics
public import LeanPool.ZFLean.Functions
public import LeanPool.ZFLean.Embeddings
public import LeanPool.ZFLean.Isomorphisms
public import LeanPool.ZFLean.IsomorphismsFunsToPowRel
public import LeanPool.ZFLean.IsomorphismsZFNatIso
public import LeanPool.ZFLean.Sum
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# ZFLean

Source: url:https://doi.org/10.1007/3-540-44761-X
Authors: Vincent Trélat
Status: verified
Main declarations: `ZFSet.isIso_of_biembedding`, `ZFSet.ZFNat.induction`, `ZFSet.ZFInt.induction`
Tags: set-theory, zfc, foundations
MSC: 03E30, 03B35
-/

@[expose] public section

/-!
# ZFLean

A practical framework for set-theoretical development in Lean.
-/
