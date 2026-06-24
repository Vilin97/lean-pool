/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.SATReductionForward
import LeanPool.Sundogcert.SATReductionReverse
import LeanPool.Sundogcert.SATReduction
import LeanPool.Sundogcert.ThreeDMReindex
import LeanPool.Sundogcert.MatchingNPHard
import LeanPool.Sundogcert.DecodingNPHard

/-!
  Sundogcert/SATReductionMain.lean — MILESTONE 9 (CAPSTONE) of the `3SAT ≤ 3DM` marathon: the
  COMPOSITION that closes the full machine-checked reduction-correctness chain.  (Lean 4 /
  mathlib v4.30.0.)

  WHAT THIS FILE PROVES.  It glues the four already-proved pieces into the headline equivalences:
    * `sat_iff_threeDM_I φ : Satisfiable φ ↔ threeDMI (tripleFn φ)`
        — the forward (m8) and reverse (m7) directions packaged as one `Iff` over the structured
          `Fintype` index `TripleIdx n m`.
    * `sat_iff_threeDM   φ : Satisfiable φ ↔ ThreeDM (reduce φ)`
        — transported onto the real `Fin s`-indexed matching problem through the m5 reindexing
          bridge (`threeDM_reindex_comp`; `reduce φ` is defeq to `tripleFn φ ∘ (equivFin _).symm`).
    * `sat_iff_decodes   φ : Satisfiable φ ↔ Decodes (reduce3DM (reduce φ)) (2*m*n)`  — HEADLINE.
        — chained through the m4 data-layer connection (`reduce_chain_connects`) all the way to the
          bounded-weight GF(2) decoding instance.

  THE FULL CHAIN, NOW CLOSED.  Composing these milestones establishes, machine-checked, the
  reduction-correctness chain
        `3SAT ≤ 3DM ≤ X3C ≤ Decodes`,
  i.e. `Satisfiable φ` holds IF AND ONLY IF the reduced bounded-weight GF(2) decoding instance
  `Decodes (reduce3DM (reduce φ)) (2·m·n)` decodes.  Every link is an `Iff` proved in Lean; no link
  relies on `native_decide` (the few `decide`s in the chain are kernel-reduced, not compiled).

  WHAT IS — AND IS NOT — ESTABLISHED.  What is machine-checked here is exactly the REDUCTION
  CORRECTNESS: the logical equivalence between the SAT instance and its decoding image.  This is the
  many-one (Karp) correctness of the map, NOT a hardness theorem.

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity-theory framework):
    * the NP complexity CLASS itself (a machine/resource-bounded notion, not formalized here);
    * the POLY-TIME-NESS of the reductions — the maps `reduce`, `reduce3DM` are built and their
      correctness is verified, but their running time is never modelled or bounded;
    * 3SAT's OWN NP-hardness — Cook–Levin, the deep terminal wall that sources every Karp-reduction
      hardness claim along this chain, and which is formalized in NO proof assistant to date.
  Because of this wall, any "NP-hard" reading of `Decodes` stays CONDITIONAL on `P ≠ NP` and on the
  imported Cook–Levin hardness of 3SAT.  This file does NOT prove that decoding is hard, and makes
  NO claim about P-vs-NP; it proves only that the reduction is faithful (the iff).

  Axiom-clean (no `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`).  Expect
  `[propext, Classical.choice, Quot.sound]` on each audited result.
-/

open Sundog.SATReduction Sundog.SATNPHard Sundog.SATReductionForward
open Sundog.SATReductionReverse Sundog.ThreeDMReindex Sundog.MatchingNPHard

namespace Sundog.SATReductionMain

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- **Packaged correctness over the structured index** (m8 ∧ m7).  A satisfying assignment for `φ`
    exists iff the gadget triple map has a perfect 3-dimensional matching over `TripleIdx n m`. -/
theorem sat_iff_threeDM_I (φ : Formula n m) :
    Satisfiable φ ↔ threeDMI (tripleFn φ) :=
  ⟨forward φ, reverse φ⟩

/-- **Correctness over the real `Fin s`-indexed matching** (through the m5 reindexing bridge).
    `Satisfiable φ ↔ ThreeDM (reduce φ)`; `reduce φ` is defeq to the comp `tripleFn φ ∘ _.symm`. -/
theorem sat_iff_threeDM (φ : Formula n m) :
    Satisfiable φ ↔ ThreeDM (reduce φ) := by
  rw [sat_iff_threeDM_I φ]
  exact threeDM_reindex_comp (tripleFn φ)

/-- **THE HEADLINE.**  Closing the machine-checked reduction-correctness chain
    `3SAT ≤ 3DM ≤ X3C ≤ Decodes`: `Satisfiable φ` holds iff the reduced bounded-weight GF(2)
    decoding instance `Decodes (reduce3DM (reduce φ)) (2·m·n)` decodes.  Reduction CORRECTNESS only
    — hardness (NP class, poly-time-ness, Cook–Levin) is the imported wall, never proved here. -/
theorem sat_iff_decodes (φ : Formula n m) :
    Satisfiable φ ↔ DecodingNPHard.Decodes (reduce3DM (reduce φ)) (2 * m * n) :=
  (sat_iff_threeDM φ).trans (reduce_chain_connects φ)

/-! ### Axiom audit.

    Expect `[propext, Classical.choice, Quot.sound]` (the classical trio) on each — NO `sorryAx`,
    NO `Lean.ofReduceBool` (no `native_decide` anywhere; the only `decide`s are kernel-reduced). -/


end Sundog.SATReductionMain
