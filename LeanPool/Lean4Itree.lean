/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/
import LeanPool.Lean4Itree.ITree
import LeanPool.Lean4Itree.Paco

/-!
# Coinductive Interaction Trees using QPFs

Source: url:https://github.com/mit-plv/lean4-itree
Authors: Paul Mure, Joonhyup Lee
Status: verified
Main declarations: `ITree`, `ITree.IEq`, `ITree.ieq_iff_eq`, `ITree.bind_assoc`, `ITree.iter`, `ITree.interp`, `plfp_acc`
Tags: coinduction, interaction-trees, monads, qpf, semantics
-/
