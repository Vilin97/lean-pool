/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.ITree.Basic
import LeanPool.Lean4Itree.ITree.EffectAlgebra
import LeanPool.Lean4Itree.ITree.Monad
import LeanPool.Lean4Itree.ITree.Utils

/-!
# Interaction trees

Aggregator module re-exporting the interaction-tree development: the core
coinductive definition and bisimulation (`Basic`), supporting utilities
(`Utils`), the monad structure (`Monad`), and the effect algebra and
interpretation combinators (`EffectAlgebra`).
-/
