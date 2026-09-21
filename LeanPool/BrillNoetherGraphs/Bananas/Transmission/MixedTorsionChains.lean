/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Wedge.KGeneralWedgeGenerality
import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeSubmodularity
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.ChainGluing

/-!
# Chains with mixed torsion orders

This file formalizes the first half of Corollary 6.16 (`thm:bngChain`).  The
factors are bundled with their individual periods and `k`-general transmission
hypotheses.  `ChainPrefixBudget g L` is the recursive form of the paper's
condition

`k_i > g₁ + ... + gᵢ`.

Starting from an accumulated graph of genus `g`, its first conjunct says that
the next period is larger than `g` plus the genus of the next factor; its tail
then uses that enlarged genus.  This presentation follows the left-associated
recursion in `MarkedGraph.chain` and avoids any indexing conventions.
-/

namespace Bananas

open Utilities

/-- One factor of a mixed-torsion chain, including precisely the hypotheses
used by Corollary 6.16. -/
structure KGeneralChainFactor where
  marked : MarkedGraph
  period : ℕ
  connected : _root_.graph_connected marked.graph
  kGeneral : KGeneralTransmission
    (mark marked.graph marked.left marked.right) period

/-- The prefix-genus period inequalities for the factors still to be attached
to a chain whose accumulated genus is `g`.

For factors `F₂, ..., Fℓ` and `g = g₁`, this unfolds to
`g₁ + g₂ < k₂`, `g₁ + g₂ + g₃ < k₃`, and so on. -/
def ChainPrefixBudget : ℤ → List KGeneralChainFactor → Prop
  | _, [] => True
  | g, F :: rest =>
      g + genus F.marked.graph < (F.period : ℤ) ∧
        ChainPrefixBudget (g + genus F.marked.graph) rest

@[simp] theorem chainPrefixBudget_nil (g : ℤ) :
    ChainPrefixBudget g [] := trivial

@[simp] theorem chainPrefixBudget_cons (g : ℤ)
    (F : KGeneralChainFactor) (rest : List KGeneralChainFactor) :
    ChainPrefixBudget g (F :: rest) ↔
      g + genus F.marked.graph < (F.period : ℤ) ∧
        ChainPrefixBudget (g + genus F.marked.graph) rest :=
  Iff.rfl

/-- Inductive engine for Corollary 6.16(1).  The accumulated twice-marked
graph is already once-marked Brill--Noether general at its right mark; attaching
factors whose periods satisfy the successive prefix bounds preserves that
property.

The extra left mark is retained only because Theorem 6.6 uses it to compose
the exact transmission permutations. -/
theorem onceMarkedBrillNoetherGeneral_chain_aux
    (M : MarkedGraph)
    (hMconn : _root_.graph_connected M.graph)
    (hMsub : AllSubmodular (mark M.graph M.left M.right))
    (hMgeneral : OnceMarkedBrillNoetherGeneral M.graph M.right)
    (L : List KGeneralChainFactor)
    (hBudget : ChainPrefixBudget (genus M.graph) L) :
    OnceMarkedBrillNoetherGeneral
      (M.chain (L.map KGeneralChainFactor.marked)).graph
      (M.chain (L.map KGeneralChainFactor.marked)).right := by
  induction L generalizing M with
  | nil => exact hMgeneral
  | cons F rest ih =>
      rw [List.map_cons, MarkedGraph.chain_cons]
      apply ih (M.wedge F.marked)
      · exact graph_connected_vertexWedge
          M.graph F.marked.graph M.right F.marked.left
          hMconn F.connected
      · exact allSubmodular_vertexWedge_opposite
          M.graph F.marked.graph M.right F.marked.left
          hMconn F.connected M.left F.marked.right
          hMsub F.kGeneral.2.1
      · exact onceMarkedBrillNoetherGeneral_vertexWedge_of_kGeneralTransmission
          M.graph F.marked.graph M.left M.right
          F.marked.left F.marked.right hMconn F.connected
          hMsub hMgeneral F.kGeneral hBudget.1
      · simpa only [MarkedGraph.genus_wedge] using hBudget.2

/-- Corollary 6.16(1), the once-marked mixed-torsion chain theorem.

The head inequality is the `i = 1` case of the paper's hypothesis, and
`hTailBudget` contains all later prefix inequalities.  Every factor has its
own period and `k`-general transmission; no common torsion order is assumed. -/
theorem onceMarkedBrillNoetherGeneral_mixedTorsionChain
    (head : KGeneralChainFactor) (tail : List KGeneralChainFactor)
    (hHeadBudget : genus head.marked.graph < (head.period : ℤ))
    (hTailBudget : ChainPrefixBudget (genus head.marked.graph) tail) :
    OnceMarkedBrillNoetherGeneral
      (head.marked.chain (tail.map KGeneralChainFactor.marked)).graph
      (head.marked.chain (tail.map KGeneralChainFactor.marked)).right := by
  apply onceMarkedBrillNoetherGeneral_chain_aux
    head.marked head.connected head.kGeneral.2.1
  · exact onceMarkedBrillNoetherGeneral_of_kGeneralTransmission
      head.marked.left head.marked.right head.connected
      head.kGeneral hHeadBudget
  · exact hTailBudget

end Bananas
