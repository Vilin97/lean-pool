/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/
module

public import LeanPool.MatchingLogic.Applicative
public import LeanPool.MatchingLogic.BoxesControl
public import LeanPool.MatchingLogic.Definedness
public import LeanPool.MatchingLogic.EntryIII.All
public import LeanPool.MatchingLogic.EntryIII.AlphaFreshWitnessed
public import LeanPool.MatchingLogic.EntryIII.EmbeddingSemantics
public import LeanPool.MatchingLogic.EntryIII.Injection
public import LeanPool.MatchingLogic.EntryIII.WitnessSupply
public import LeanPool.MatchingLogic.Independence
public import LeanPool.MatchingLogic.Necessity
public import LeanPool.MatchingLogic.Sanity
public import LeanPool.MatchingLogic.SetVariables
public import LeanPool.MatchingLogic.SortedProof
import Mathlib.Tactic.Bound.Init

/-!
# Global completeness of one-sorted definedness-free matching logic

Source: arxiv:2608.13306, url:https://hdl.handle.net/2142/102281
Authors: Aurélien Eveil, Anthropic, OpenAI
Status: verified
Main declarations: `MatchingLogic.global_completeness_entryIII`
Tags: matching-logic, mathematical-logic, modal-logic, completeness, formal-methods
MSC: 03B45, 03B70
-/

@[expose] public section
