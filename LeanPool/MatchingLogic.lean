/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

import LeanPool.MatchingLogic.Applicative
import LeanPool.MatchingLogic.BoxesControl
import LeanPool.MatchingLogic.Definedness
import LeanPool.MatchingLogic.EntryIII.All
import LeanPool.MatchingLogic.EntryIII.AlphaFreshWitnessed
import LeanPool.MatchingLogic.EntryIII.EmbeddingSemantics
import LeanPool.MatchingLogic.EntryIII.Injection
import LeanPool.MatchingLogic.EntryIII.WitnessSupply
import LeanPool.MatchingLogic.Independence
import LeanPool.MatchingLogic.Necessity
import LeanPool.MatchingLogic.Sanity
import LeanPool.MatchingLogic.SetVariables
import LeanPool.MatchingLogic.SortedProof

/-!
# Global completeness of definedness-free matching logic

Source: arxiv:2608.13306, url:https://hdl.handle.net/2142/102281
Authors: Aurélien Eveil, Anthropic, OpenAI
Status: verified
Main declarations: `MatchingLogic.global_completeness_entryIII`
Tags: matching-logic, mathematical-logic, modal-logic, completeness, formal-methods
MSC: 03B45, 03B70
-/
