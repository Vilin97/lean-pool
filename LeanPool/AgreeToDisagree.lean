/-
Copyright (c) 2026 Axiom Math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AgreeToDisagree contributors
-/

import LeanPool.AgreeToDisagree.AgreeToDisagree
import LeanPool.AgreeToDisagree.AgreeToDisagreeBeliefs

/-!
# Aumann's Agreement Theorem

Source: url:https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6837298
Authors: Ruiz Chen, Ben Eltschig, Ken Ono, Jujian Zhang
Status: verified
Main declarations: `AgreeToDisagree.agreeToDisagree`, `AgreeToDisagree.agreeToDisagree_beliefs`
Tags: probability, game-theory, epistemic-logic
MSC: 60A10, 91A40
-/

/-!
## Mathematical overview

This project formalizes Aumann's theorem that agents with common prior
probabilities cannot agree to disagree when it is common knowledge that they
assign fixed posterior probabilities to an event.

The first theorem proves equality of the posteriors under common knowledge for
two agents and, more generally, a family of agents. The second develops a
`p`-belief variant, proving that common `p`-belief bounds posterior
disagreement by `2 * (1 - p)`.

## Main results

- `AgreeToDisagree.agreeToDisagree` — two agents with common knowledge of
  their posteriors and equal common prior posterior on the common-knowledge
  cell have equal posteriors.
- `AgreeToDisagree.agreeToDisagree'` — the corresponding finite-family
  formulation.
- `AgreeToDisagree.agreeToDisagree_beliefs` — common `p`-belief bounds
  posterior disagreement by `2 * (1 - p)`.
-/
