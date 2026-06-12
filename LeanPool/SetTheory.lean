/-
Copyright (c) 2026 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/

import LeanPool.SetTheory.KunenInconsistency

/-!
# The Kunen inconsistency theorem

Source: doi:10.2307/2269948, url:https://github.com/znssong/SetTheory
Authors: Shuhao Song
Status: verified
Main declarations: `SetTheory.kunen_inconsistency_V`, `NontrivialElementaryEmbedding`
Tags: set-theory, large-cardinals, elementary-embedding, kunen-inconsistency, model-theory
MSC: 03E55, 03C90
-/

/-!
## Overview

A Lean 4 formalization of elementary embeddings of models of ZF set theory,
culminating in the Kunen inconsistency theorem: there is no nontrivial elementary
embedding from the universe of sets into itself.
-/
