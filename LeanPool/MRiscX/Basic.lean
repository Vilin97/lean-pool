/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import LeanPool.MRiscX.Elab.CodeElaborator
public import LeanPool.MRiscX.Semantics.Specification
public import LeanPool.MRiscX.Delab.DelabCode
public import LeanPool.MRiscX.Elab.HoareElaborator
public import LeanPool.MRiscX.Hoare.HoareRules
public import LeanPool.MRiscX.Util.BasicTheorems
public import LeanPool.MRiscX.Tactics.CodeProofTactics

/-!
# Basic

This module provides the top-level entry point gathering the MRiscX modules.
-/

@[expose] public section
