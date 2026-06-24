/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.SATNPHard
import LeanPool.Sundogcert.VarWheel
import LeanPool.Sundogcert.ClauseGadget
import LeanPool.Sundogcert.MatchingNPHard
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin

/-!
  Sundogcert/SATReduction.lean — MILESTONE 4 of the `3SAT ≤ 3DM` marathon: the GLOBAL ASSEMBLY
  SCAFFOLDING (the DATA LAYER).  This module fixes the three coordinate types, the triple-index
  type, the reduction function, the cardinality lemmas, and the theorem that `reduce φ` PLUGS INTO
  the already-formalized hardness chain `3DM ≤ X3C ≤ Decodes`.  (Lean 4 / mathlib v4.30.0.)

  THE THREE COORDINATE TYPES (each of cardinality `2·m·n` — the chain weight `q`):
    * `Tip   = Fin n × Fin m × Bool`                       (the W-part: tip = variable·spoke·sign).
    * `XNode = (Fin n × Fin m) ⊕ Fin m ⊕ Fin (m*(n-1))`    (a-nodes ⊕ s1-nodes ⊕ garbage g1).
    * `YNode = (Fin n × Fin m) ⊕ Fin m ⊕ Fin (m*(n-1))`    (b-nodes ⊕ s2-nodes ⊕ garbage g2).
    CARDINALITIES.  `|Tip| = n·m·2 = 2mn`.  `|XNode| = |YNode| = n·m + m + m·(n-1)`; with `n ≥ 1`
    ([NeZero n]) one has `m·(n-1) + m = m·n` in ℕ, so each is `n·m + m·n = 2mn`.  The `[NeZero n]`
    is exactly what makes the garbage count close the books to `2mn`.

  THE TRIPLE-INDEX TYPE (a clean 4-way Sum — avoids any `Fin`-arithmetic decode):
    `TripleIdx = (Fin n × Fin m) ⊕ (Fin n × Fin m) ⊕ (Fin m × Fin 3) ⊕ (Fin (m*(n-1)) × Tip)`
    indexing, in order: the wheel POSITIVE triples, the wheel NEGATIVE triples, the CLAUSE
    slot-triples (clause `k`, slot), and the GARBAGE triples (garbage `g`, any free tip `w`).

  THE TRIPLE FUNCTION `tripleFn φ : TripleIdx → Tip × XNode × YNode` (faithful to m2/m3 gadgets):
    * wheel POS `(i,j)`:  `((i, j, true),  inl (i, j),     inl (i, j))`
        — `posTip(i,j)`; a-node `(i,j)`; b-node `(i,j)`.  Matches `VarWheel` `t_j=(posTip,a j,b j)`.
    * wheel NEG `(i,j)`:  `((i, j, false), inl (i, j+1),   inl (i, j))`
        — `negTip(i,j)`; a-node `(i,j+1)` (`j+1` CYCLIC in `Fin m`); b-node `(i,j)`.  Matches
          `t⁻_j=(negTip, a(j+1), b j)`.
    * CLAUSE `(k,slot)`:  `let l := φ k slot; ((l.1, k, l.2), inr (inl k), inr (inl k))`
        — tip of literal `l` at spoke `k`; `s1_k`; `s2_k`.  Matches the `ClauseGadget` slot-triple
          `(tip(c_k,slot), s1_k, s2_k)`; tip polarity `= l.2` (the literal sign).
    * GARBAGE `(g,w)`:    `(w, inr (inr g), inr (inr g))`
        — any free tip `w`; `g1_g`; `g2_g`.  Garbage absorbs any leftover free tip.

  THE REDUCTION (`Fin s → Tip × XNode × YNode`, `s = card TripleIdx`, via the canonical equiv):
    `reduce φ := fun i => tripleFn φ ((Fintype.equivFin _).symm i)`, where
    `Fintype.equivFin T : T ≃ Fin (card T)` (so `.symm : Fin (card T) → T`).  `equivFin` is
    noncomputable, so `reduce` is `noncomputable` — fine; nothing here is meant to run.

  THE CHAIN-CONNECTION PAYOFF (this milestone's deliverable):
    `reduce_chain_connects φ : ThreeDM (reduce φ) ↔ Decodes (reduce3DM (reduce φ)) (2*m*n)`,
    obtained by feeding `card_tip`/`card_xnode`/`card_ynode` to the already-proved
    `MatchingNPHard.threeDM_iff_Decodes`.  So the SAT-side `reduce` function is now wired onto the
    formalized `3DM ≤ X3C ≤ Decodes` chain.

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity framework):
    * the NP complexity class itself, and poly-time-ness of any reduction;
    * 3SAT's OWN NP-hardness — Cook–Levin, the deep terminal wall sourcing every Karp-reduction
      hardness claim in this `3SAT ≤ 3DM ≤ X3C ≤ Decodes` chain.

  STANDING LIMIT: this module is the DATA LAYER only.  It builds the reduction's TYPES, INDEX, and
  TRIPLE MAP and connects them to the chain by cardinality.  The GADGET CORRECTNESS
  (`Satisfiable φ ↔ ThreeDM (reduce φ)`) — that the wheel + clause + garbage triples actually
  enforce satisfiability — is milestones 5–7.

  Axiom-clean throughout (`decide` is never used here; no `native_decide`).  Expect
  `[propext, Classical.choice, Quot.sound]` on the four audited results.
-/

open Sundog.SATNPHard Sundog.VarWheel Sundog.ClauseGadget Sundog.MatchingNPHard

namespace Sundog.SATReduction

variable {n m : ℕ} [NeZero n] [NeZero m]

/-! ### The three coordinate types (each of cardinality `2·m·n`). -/

/-- The W-part: a tip `= (variable `i`, spoke `j`, polarity)`. -/
abbrev Tip (n m : ℕ) := Fin n × Fin m × Bool

/-- The X-part: a-nodes `(i,j)` ⊕ s1-nodes (one per clause) ⊕ garbage `g1`. -/
abbrev XNode (n m : ℕ) := (Fin n × Fin m) ⊕ Fin m ⊕ Fin (m * (n - 1))

/-- The Y-part (same shape as `XNode`): b-nodes `(i,j)` ⊕ s2-nodes ⊕ garbage `g2`. -/
abbrev YNode (n m : ℕ) := (Fin n × Fin m) ⊕ Fin m ⊕ Fin (m * (n - 1))

/-! ### The triple-index type (a clean 4-way Sum). -/

/-- The reduction's triple index: wheel-positive ⊕ wheel-negative ⊕ clause-slot ⊕ garbage. -/
abbrev TripleIdx (n m : ℕ) :=
    (Fin n × Fin m)            -- wheel POSITIVE triples, indexed by (variable `i`, spoke `j`)
  ⊕ (Fin n × Fin m)            -- wheel NEGATIVE triples, indexed by (i, j)
  ⊕ (Fin m × Fin 3)            -- CLAUSE slot-triples, indexed by (clause `k`, slot)
  ⊕ (Fin (m * (n - 1)) × Tip n m)  -- GARBAGE triples, indexed by (garbage `g`, any tip `w`)

/-- Decidable equality on the 4-way nested `Sum` index type, assembled layer by layer so that
    instance synthesis stays within the default `synthInstance.maxSize` (a blind search over the
    full nesting otherwise overflows it). -/
instance instDecidableEqTripleIdx : DecidableEq (TripleIdx n m) :=
  have _d1 : DecidableEq (Fin n × Fin m) := instDecidableEqProd
  have _d2 : DecidableEq (Fin m × Fin 3) := instDecidableEqProd
  have _dtip : DecidableEq (Tip n m) := instDecidableEqProd
  have _d4 : DecidableEq (Fin (m * (n - 1)) × Tip n m) := instDecidableEqProd
  have _s3 : DecidableEq ((Fin m × Fin 3) ⊕ Fin (m * (n - 1)) × Tip n m) :=
    instDecidableEqSum
  have _s2 :
      DecidableEq ((Fin n × Fin m) ⊕ (Fin m × Fin 3) ⊕ Fin (m * (n - 1)) × Tip n m) :=
    instDecidableEqSum
  instDecidableEqSum

/-! ### The triple function — faithful to the milestone-2/3 gadgets. -/

/-- The triple map `TripleIdx → Tip × XNode × YNode`: each index slot emits its gadget triple. -/
def tripleFn (φ : Formula n m) : TripleIdx n m → Tip n m × XNode n m × YNode n m
  | Sum.inl (i, j)                      => ((i, j, true),  Sum.inl (i, j),       Sum.inl (i, j))
  | Sum.inr (Sum.inl (i, j))            => ((i, j, false), Sum.inl (i, j + 1),   Sum.inl (i, j))
  | Sum.inr (Sum.inr (Sum.inl (k, slot))) =>
      let l := φ k slot
      ((l.1, k, l.2), Sum.inr (Sum.inl k), Sum.inr (Sum.inl k))
  | Sum.inr (Sum.inr (Sum.inr (g, w))) => (w, Sum.inr (Sum.inr g), Sum.inr (Sum.inr g))

/-! ### The reduction (via the canonical `Fin (card TripleIdx) ≃ TripleIdx`). -/

/-- **The reduction.**  Re-index the gadget triple map along the canonical finite equiv, giving the
    `Fin s → Tip × XNode × YNode` shape the matching problem wants (`s = card TripleIdx`).
    `noncomputable` because `Fintype.equivFin` is. -/
noncomputable def reduce (φ : Formula n m) :
    Fin (Fintype.card (TripleIdx n m)) → Tip n m × XNode n m × YNode n m :=
  fun i => tripleFn φ ((Fintype.equivFin _).symm i)

/-! ### Cardinality lemmas — the hypotheses `threeDM_iff_Decodes` needs (`q := 2*m*n`). -/

omit [NeZero n] [NeZero m] in
/-- `|Tip| = n·m·2 = 2mn`.  No `NeZero` needed (pure product of `Fin`/`Bool` cards). -/
theorem card_tip : Fintype.card (Tip n m) = 2 * m * n := by
  unfold Tip
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool]
  ring

omit [NeZero m] in
/-- `|XNode| = n·m + m + m·(n-1) = 2mn` (the `m·(n-1)+m = m·n` step uses `n ≥ 1`). -/
theorem card_xnode : Fintype.card (XNode n m) = 2 * m * n := by
  unfold XNode
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

omit [NeZero m] in
/-- `|YNode| = n·m + m + m·(n-1) = 2mn` (same shape as `XNode`). -/
theorem card_ynode : Fintype.card (YNode n m) = 2 * m * n := by
  unfold YNode
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

/-! ### The chain-connection theorem — the milestone-4 payoff. -/

/-- **THE CHAIN CONNECTION** (the m4 deliverable).  `reduce φ` plugs into the formalized hardness
    chain: `ThreeDM (reduce φ) ↔ Decodes (reduce3DM (reduce φ)) (2mn)`, by feeding the three card
    lemmas to the already-proved `MatchingNPHard.threeDM_iff_Decodes`.  The GADGET correctness
    (`Satisfiable φ ↔ ThreeDM (reduce φ)`) is milestones 5–7. -/
theorem reduce_chain_connects (φ : Formula n m) :
    ThreeDM (reduce φ) ↔
      DecodingNPHard.Decodes (reduce3DM (reduce φ)) (2 * m * n) :=
  threeDM_iff_Decodes (reduce φ) (2 * m * n) card_tip card_xnode card_ynode

/-! ### Axiom audit.

    Expect `[propext, Classical.choice, Quot.sound]` (or a subset) — NO `sorryAx`, and NO
    `Lean.ofReduceBool` (we never use `decide`/`native_decide` in this module). -/


end Sundog.SATReduction
