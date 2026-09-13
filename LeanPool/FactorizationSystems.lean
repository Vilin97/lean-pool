/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/
module

public import LeanPool.FactorizationSystems.Basic
public import LeanPool.FactorizationSystems.Examples
public import LeanPool.FactorizationSystems.Orthogonality
public import LeanPool.FactorizationSystems.OrthogonalComplements
public import LeanPool.FactorizationSystems.Characterization
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike

/-!
# Factorization Systems

Source: url:https://emilyriehl.github.io/files/context.pdf
Authors: Ivan Kobe
Status: verified
Main declarations: `CategoryTheory.FactorizationSystemCharacterization`
Tags: category-theory, factorization-systems, orthogonality
MSC: 18A32, 18A40
-/

@[expose] public section
