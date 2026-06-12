/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.ConjInvLength.Length
import LeanPool.Polylean.ConjInvLength.LengthBound
import LeanPool.Polylean.ConjInvLength.LengthNode
import LeanPool.Polylean.ConjInvLength.MemoLength
import LeanPool.Polylean.ConjInvLength.ProvedBound

/-!
# Demonstration executable for Polylean length computations
-/

namespace LeanPool.Polylean

open Letter

/-- Demonstration executable for the conjugacy-invariant length computations. -/
def polymathMain : IO Unit := do
  for k in [1, 2, 6] do
    let w := #[α, β, α!, β!]^k ++ #[α]
    IO.println s!"computing length via powers of {w}"
    for n in [1:21] do
      let l ← powerLength w n
      IO.println s!"length of {w} from power {n}: {l}"
  let w := #[α, β, α!, β!]
  IO.println s!"computing length via powers of the commutator {w}"
  for n in [1:21] do
    let l ← powerLength w n
    IO.println s!"length of {w} from power {n}: {l}"
  let l ← lengthNodes w
  IO.println s!"length of {w}: {l}"
  IO.println s!"derived length: {(← derivedLength w)}"
  let (_, ns) ← derivedProof w
  let ns := ns.eraseDups
  let mut j := 0
  for node in ns do
    j := j + 1
    let w := node.top
    let l ← lengthNodes w
    IO.println s!"Lemma {j}: l({w}) ≤ {l}"
    IO.println s!"Proof: apply {node}"
    for w in node.base do
      let l ← lengthNodes w
      IO.println s!"  using l({w}) ≤ {l}"
    IO.println ""

end LeanPool.Polylean
