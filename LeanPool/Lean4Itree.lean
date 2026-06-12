/-
Copyright (c) 2026 Paul Mure, Joonhyup Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Mure, Joonhyup Lee
-/

import LeanPool.Lean4Itree.ITree
import LeanPool.Lean4Itree.Paco

/-!
# Coinductive Interaction Trees using QPFs

Source: arxiv:1906.00046, doi:10.1145/3371119
Authors: Paul Mure, Joonhyup Lee
Status: verified
Main declarations: `Lean4Itree.ITree`, `Lean4Itree.ITree.ieq_iff_eq`, `Lean4Itree.plfp_acc`
Tags: coinduction, interaction-trees, monads, qpf, semantics
MSC: 68Q55, 18C50, 68N18
-/
