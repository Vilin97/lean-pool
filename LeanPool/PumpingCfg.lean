/-
Copyright (c) 2026 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
import LeanPool.PumpingCfg.Pumping

/-!
# Pumping Lemma for Context-Free Grammars

Source: url:https://github.com/AlexLoitzl/pumping_cfg
Authors: Alexander Loitzl, Martin Dvorak
Status: verified
Main declarations: `Language.IsContextFree.pumping`, `ChomskyNormalFormGrammar.pumping`
Tags: formal-languages, context-free-grammars, computability, pumping-lemma
MSC: 68Q45
-/

/-!
## Mathematical overview

Formalizes the pumping lemma for context-free grammars. The development converts
a context-free grammar to Chomsky normal form, introduces parse trees for
Chomsky-normal-form grammars together with their yield and subtree relation, and
uses a pigeonhole argument on a sufficiently tall parse tree to extract a
repeated nonterminal whose subtree can be pumped.

The final theorem, `Language.IsContextFree.pumping`, states that every
context-free language `L` admits a pumping length `p` such that any word `w ∈ L`
of length at least `p` decomposes as `w = u v x y z` with `vy` nonempty,
`vxy` of length at most `p`, and `u vⁱ x yⁱ z ∈ L` for every `i`.

## Provenance

Imported from <https://github.com/AlexLoitzl/pumping_cfg>. Upstream is
Apache-2.0 licensed and contains no `sorry`s.

Upstream imports the modules `Mathlib.Computability.ChomskyNormalForm.*` from
the authors' in-review Mathlib branch (`alex-loitzl-cnf`), which is not part of
the Mathlib release pinned here. Those modules (by the same authors, Apache-2.0)
are vendored under `LeanPool/PumpingCfg/ChomskyNormalForm/` until they land in
a pinned Mathlib release.
-/
