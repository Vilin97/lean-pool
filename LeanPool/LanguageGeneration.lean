/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao, Shuangping Li, Peng Zhang
-/

import LeanPool.LanguageGeneration.FiniteWitness
import LeanPool.LanguageGeneration.FiniteWitness.Simplified
import LeanPool.LanguageGeneration.FiniteWitness.Width

/-!
# Finite witnesses and the width hierarchy for language generation

Source: arxiv:2609.10525, url:https://github.com/xiaoyulics/language-generation-characterization
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao, Shuangping Li, Peng Zhang
Status: verified
Main declarations: `GenLimit.FiniteWitness.Simplified.ordinary_iff_finiteWitnesses`
Tags: language-generation, learning-theory, finite-witnesses, combinatorics
MSC: 68Q32, 68Q45
-/

/-
Attribution and notice retained from the upstream distribution:
Characterizing Language Generation in the Limit — Lean development.

This distribution includes code from generation-in-the-limit-lib,
developed and maintained by Shuangping Li and Peng Zhang.
https://github.com/pengzhang91/generation-in-the-limit-lib
Base revision: de0d70c7e4645bface1d19bded9c8a5ade080fa8.
The original Apache License 2.0 is the repository's LICENSE.

The FiniteWitness extension and focused packaging were added for the manuscript
by Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao.
Source: https://github.com/xiaoyulics/language-generation-characterization
Revision: 4f7d3f2148017ae15135ba39ddc4d655bb175ab6.
The four Core modules derive from the earlier library; the remaining modules
are the manuscript extension. Upstream CREDITS.md and NOTICE record this split.

The earlier library discloses AI-assisted formalization under human direction;
the extension's CREDITS.md and the paper disclose OpenAI Codex assistance with
proof development and Lean formalization. The registry's AI category is an
inference from these disclosures and the released proof history, rather than
a claim that the authors reported a measured share of machine-written Lean.

Modified for Lean Pool: module paths, Lean/Mathlib API repairs, narrow imports,
proof reuse, direct arithmetic proofs, file headers, and generated project card.
Diagnostic audit modules are omitted; their theorem dependencies are retained.
The mathematical statements retain their original scope. The paper's additional
density-one example and computability results in Appendices D and E are outside
this formalization. Both normalization constructions are retained because the
finite-query and executable theorems use the original construction, while the
revised construction supplies the manuscript's checkpoint interface.
-/
