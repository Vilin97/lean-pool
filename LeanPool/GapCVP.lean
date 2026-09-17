/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part18

/-!
# Polynomial-factor hardness of the closest vector problem

Source: url:https://github.com/openai/ten-proofs
Authors: OpenAI, Dean Cureton
Status: verified
Main declarations: `GapCVP.Comparator.gapCVP400IsNPHard`
Tags: computational-complexity, np-hardness, lattice-problems, coding-theory
MSC: 68Q17, 68Q25, 11H06, 94B35
-/

/-! # Polynomial-factor hardness of the closest vector problem -/

/-!
## Maintenance

The split modules are maintained as Lean source. No external certificate generator is required
or supplied: the machine descriptions and their execution/time-bound proofs are part of the
formalization. In particular, the `BitTM` layer uses Mathlib's `TM2ComputableInPolyTime`;
removing that layer would discard the polynomial-time guarantees of the headline reductions.

The import starts from `openai/ten-proofs` commit
`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`, incorporating Dean Cureton's proof refactorings at
`30c21d72a2ee3308d66c945387729d736e0cb305`. Keep the four `GapCVP.Comparator` headline
statements stable when updating the proof modules. Their public `PromiseProblem` and
`PromiseReduction` types provide the downstream interface; encoding and machine implementations
remain behind that interface.

For Mathlib updates, repair the shared trace/composition helpers before individual machine
proofs, then run `lake build LeanPool.GapCVP` and the project linters. The source modules follow
dependency order, so a focused rebuild checks the affected suffix without rebuilding other
pooled projects. The large Turing-machine layer remains a maintenance cost of this import.
-/
