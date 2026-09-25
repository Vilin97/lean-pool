/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.TreewidthGonality.Gonality.BrambleGonality
import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.SeymourThomas

/-!
# `treewidth ≤ gonality`

The theorem of van Dobben de Bruyn--Gijswijt (arXiv:1407.7055): the treewidth of
a connected graph is at most its divisorial gonality.

The proof is the two-line composition of the repository's two halves:

* `Utilities.Gonality.bramble_order_le_gonality_succ` — Theorem A, the
  divisor-theoretic heart (`#print axioms` reports exactly
  `[propext, Classical.choice, Quot.sound]`);
* `Utilities.Treewidth.exists_bramble_of_treewidth` — Seymour--Thomas duality,
  following Bellenbaum--Diestel's short proof; see
  `TreewidthGonality/Treewidth/SeymourThomas.lean`.

Both halves are unconditional, so `#print axioms` on the theorems below
reports exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Utilities.Gonality

open Utilities.Treewidth

variable {G : CFGraph}

/-- **`treewidth ≤ gonality`** (van Dobben de Bruyn--Gijswijt).  Treewidth is
taken on `underlyingSimpleGraph G`, which is what "the treewidth of a
multigraph" means: parallel edges and loops do not change it. -/
theorem treewidth_le_gonality (h_conn : graphConnected G) :
    treewidth (underlyingSimpleGraph G) ≤ divisorialGonality G := by
  obtain ⟨𝔅, h𝔅⟩ := exists_bramble_of_treewidth (underlyingSimpleGraph G)
  have hA := bramble_order_le_gonality_succ h_conn 𝔅
  omega

/-- The same bound against the dependency's `ℤ`-valued `gonality`. -/
theorem treewidth_le_gonality_int (h_conn : graphConnected G) :
    (treewidth (underlyingSimpleGraph G) : ℤ) ≤ gonality h_conn := by
  rw [gonality_eq_divisorialGonality h_conn]
  exact_mod_cast treewidth_le_gonality h_conn

end Utilities.Gonality
