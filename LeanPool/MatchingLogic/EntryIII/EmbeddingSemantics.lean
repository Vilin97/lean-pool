/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/- Semantic invariance under injective variable embeddings is implemented by
the shared renaming stack.  This module remains as its source-compatible import. -/
module

public import LeanPool.MatchingLogic.EntryIII.Injection

import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# MatchingLogic.EntryIII.EmbeddingSemantics
-/

@[expose] public section
