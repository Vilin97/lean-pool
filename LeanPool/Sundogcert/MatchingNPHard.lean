/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.DecodingNPHard

/-!
  Sundogcert/MatchingNPHard.lean — the KARP-LAYER EXTENSION of the formalized hardness chain:
  3-DIMENSIONAL MATCHING (3DM) reduces to EXACT-COVER-BY-3-SETS (X3C), composed through
  frontier #1's `reduction_iff` into bounded-weight GF(2) decoding.  (Lean 4 / mathlib v4.30.0.)

  WHAT THIS FILE PROVES (pure combinatorics — the reduction CORRECTNESS, no gadgets):
    * `ThreeDM t` — a perfect 3-dimensional matching among the `s` triples `t : Fin s → W×X×Y`:
      a selection `T` of triples covering each W-, X-, and Y-element exactly once.
    * `reduce3DM t` — the Karp reduction: each triple `(w,x,y)` becomes its 3-element set
      `{inl w, inr (inl x), inr (inr y)}` in the X3C universe `W ⊕ X ⊕ Y`.
    * `threeDM_iff_X3C` (THE HEADLINE) — `ThreeDM t ↔ X3C (reduce3DM t)`, machine-checked.  Both
      sides are `∃ T, <cond>`; the X3C exact-cover condition over `W ⊕ X ⊕ Y` decomposes (via
      `Sum.forall`, twice) into exactly the three per-part "covered once" conditions of `ThreeDM`.
      No gadgets — the equivalence is the Sum-universe bookkeeping, nothing more.
    * `reduce3DM_card` — every reduce-set is a genuine 3-set (the three Sum-tagged elements are
      pairwise distinct: `inl ≠ inr`, and the two `inr`-branches differ by `inl ≠ inr` again).
    * `reduce3DM_univ_card` — with `|W| = |X| = |Y| = q`, the universe `W ⊕ X ⊕ Y` has `3q` points.
    * `threeDM_iff_Decodes` (THE COMPOSITION / PAYOFF) — chaining the headline through frontier #1's
      PROVED `reduction_iff` (whose hypotheses `(c i).card = 3` and `|universe| = 3q` are discharged
      by the two card lemmas) yields `ThreeDM t ↔ Decodes (reduce3DM t) q`.  The hardness chain
      `3DM ≤ X3C ≤ Decodes` is now formalized end to end.

  THE IMPORTED WALL (named, NOT proved — mathlib has no complexity framework):
    * the NP complexity class itself, and poly-time-ness of this reduction (it is visibly local —
      each triple maps to one 3-set — but "polynomial" is unformalized);
    * 3DM's OWN NP-hardness (Garey–Johnson problem GT2, via `3SAT ≤ 3DM`, NOT yet formalized — the
      next milestone; this file only relates 3DM to X3C, it does not prove 3DM hard from scratch);
    * the DEEP TERMINAL WALL = SAT's NP-hardness (Cook–Levin), a multi-year formalization, named
      forever as the ultimate source of every Karp-reduction hardness claim in this chain.
  STANDING LIMIT (unchanged): NP-hardness is CONDITIONAL on P≠NP — never absolute.  What this file
  adds is one Karp layer of REACH: it pushes the imported wall outward from "X3C is hard" to
  "3DM is hard", since `3DM ↔ X3C` (the reduction is an equivalence — `reduce3DM` is essentially a
  relabeling).  A small but composable, de-risking step toward the genuine gadget reduction
  `3SAT ≤ 3DM` that would discharge 3DM's hardness internally.
-/

open Finset

namespace Sundog.MatchingNPHard

variable {W X Y : Type*}
variable [Fintype W] [Fintype X] [Fintype Y]
variable [DecidableEq W] [DecidableEq X] [DecidableEq Y]
variable {s : ℕ} (t : Fin s → W × X × Y) (q : ℕ)

/-! ### The two problems and the reduction. -/

/-- **Perfect 3-dimensional matching** among the `s` triples: a selection `T` of triple-indices
    covering each W-element, each X-element, and each Y-element exactly once. -/
def ThreeDM : Prop := ∃ T : Finset (Fin s),
    (∀ w : W, (T.filter (fun i => (t i).1   = w)).card = 1) ∧
    (∀ x : X, (T.filter (fun i => (t i).2.1 = x)).card = 1) ∧
    (∀ y : Y, (T.filter (fun i => (t i).2.2 = y)).card = 1)

/-- **The reduction.**  Each triple `(w, x, y)` becomes its 3-element set in the X3C universe
    `W ⊕ X ⊕ Y`: the W-, X-, Y-coordinates are tagged into the three disjoint summands. -/
def reduce3DM : Fin s → Finset (W ⊕ X ⊕ Y) :=
  fun i => {Sum.inl (t i).1, Sum.inr (Sum.inl (t i).2.1), Sum.inr (Sum.inr (t i).2.2)}

/-! ### Membership lemmas — each Sum-tagged point lands in exactly its coordinate's slot. -/

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- A W-tagged point `inl w` is in the reduce-set of triple `i` iff that triple's W-coordinate is
    `w` (the other two slots are `inr`, never equal to `inl w`). -/
theorem mem_reduce_inl (i : Fin s) (w : W) :
    Sum.inl w ∈ reduce3DM t i ↔ (t i).1 = w := by
  unfold reduce3DM
  simp [eq_comm]

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- An X-tagged point `inr (inl x)` is in the reduce-set of triple `i` iff that triple's
    X-coordinate is `x`. -/
theorem mem_reduce_inr_inl (i : Fin s) (x : X) :
    Sum.inr (Sum.inl x) ∈ reduce3DM t i ↔ (t i).2.1 = x := by
  unfold reduce3DM
  simp [eq_comm]

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- A Y-tagged point `inr (inr y)` is in the reduce-set of triple `i` iff that triple's
    Y-coordinate is `y`. -/
theorem mem_reduce_inr_inr (i : Fin s) (y : Y) :
    Sum.inr (Sum.inr y) ∈ reduce3DM t i ↔ (t i).2.2 = y := by
  unfold reduce3DM
  simp [eq_comm]

/-! ### The cover counts of the reduced instance ARE the per-part filter counts. -/

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- The X3C cover count of a W-tagged point equals the W-part matching count. -/
theorem coverCount_inl (T : Finset (Fin s)) (w : W) :
    DecodingNPHard.coverCount (reduce3DM t) T (Sum.inl w)
      = (T.filter (fun i => (t i).1 = w)).card := by
  unfold DecodingNPHard.coverCount
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i _
  rw [mem_reduce_inl]

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- The X3C cover count of an X-tagged point equals the X-part matching count. -/
theorem coverCount_inr_inl (T : Finset (Fin s)) (x : X) :
    DecodingNPHard.coverCount (reduce3DM t) T (Sum.inr (Sum.inl x))
      = (T.filter (fun i => (t i).2.1 = x)).card := by
  unfold DecodingNPHard.coverCount
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i _
  rw [mem_reduce_inr_inl]

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- The X3C cover count of a Y-tagged point equals the Y-part matching count. -/
theorem coverCount_inr_inr (T : Finset (Fin s)) (y : Y) :
    DecodingNPHard.coverCount (reduce3DM t) T (Sum.inr (Sum.inr y))
      = (T.filter (fun i => (t i).2.2 = y)).card := by
  unfold DecodingNPHard.coverCount
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro i _
  rw [mem_reduce_inr_inr]

/-! ### THE HEADLINE — reduction correctness. -/

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- **THE REDUCTION CORRECTNESS** (machine-checked, pure combinatorics).  `ThreeDM t` holds iff the
    reduced X3C instance `reduce3DM t` has an exact cover.  Both sides are `∃ T, <cond>`; for a
    fixed `T`, the X3C exact-cover condition `∀ u : W ⊕ X ⊕ Y, coverCount … u = 1` decomposes via
    `Sum.forall` (applied twice, for `W ⊕ (X ⊕ Y)`) into the three slots, and the cover-count
    lemmas rewrite each slot into the corresponding per-part matching count.  So the X3C condition
    is EXACTLY `ThreeDM`'s three-fold "covered once" condition — no gadgets, just the Sum
    bookkeeping. -/
theorem threeDM_iff_X3C : ThreeDM t ↔ DecodingNPHard.X3C (reduce3DM t) := by
  unfold ThreeDM DecodingNPHard.X3C
  refine exists_congr (fun T => ?_)
  unfold DecodingNPHard.IsExactCover
  rw [Sum.forall, Sum.forall]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact forall_congr' (fun w => by rw [coverCount_inl])
  · exact forall_congr' (fun x => by rw [coverCount_inr_inl])
  · exact forall_congr' (fun y => by rw [coverCount_inr_inr])

/-! ### Card lemmas — the hypotheses frontier #1 needs. -/

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- Each reduce-set is a genuine 3-set: its three Sum-tagged elements are pairwise distinct. -/
theorem reduce3DM_card (i : Fin s) : (reduce3DM t i).card = 3 := by
  unfold reduce3DM
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp
  · simp

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- With each part of size `q`, the X3C universe `W ⊕ X ⊕ Y` has `3q` points. -/
theorem reduce3DM_univ_card (hW : Fintype.card W = q) (hX : Fintype.card X = q)
    (hY : Fintype.card Y = q) : Fintype.card (W ⊕ X ⊕ Y) = 3 * q := by
  rw [Fintype.card_sum, Fintype.card_sum, hW, hX, hY]
  ring

/-! ### THE COMPOSITION — chain extended to the certificate. -/

/-- **THE COMPOSITION** (the payoff).  Chaining the headline `threeDM_iff_X3C` through frontier
    #1's PROVED `reduction_iff` — whose two hypotheses (each set has card `3`; the universe has
    `3q` points) are discharged by `reduce3DM_card` and `reduce3DM_univ_card` — yields
    `ThreeDM t ↔ Decodes (reduce3DM t) q`.  The formalized hardness chain `3DM ≤ X3C ≤ Decodes`
    is now complete end to end; only the COMPLEXITY WRAPPING (NP class, poly-time-ness, 3DM's own
    NP-hardness Garey–Johnson GT2, ultimately Cook–Levin) stays the named imported wall. -/
theorem threeDM_iff_Decodes (hW : Fintype.card W = q) (hX : Fintype.card X = q)
    (hY : Fintype.card Y = q) :
    ThreeDM t ↔ DecodingNPHard.Decodes (reduce3DM t) q :=
  (threeDM_iff_X3C t).trans
    (DecodingNPHard.reduction_iff (reduce3DM t) q (reduce3DM_card t)
      (reduce3DM_univ_card q hW hX hY))

/-! ### Axiom audit on the two headline theorems (expect propext/Classical.choice/Quot.sound). -/


end Sundog.MatchingNPHard
