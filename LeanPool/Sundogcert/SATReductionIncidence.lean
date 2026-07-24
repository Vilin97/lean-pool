/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.SATReduction

/-!
  Sundogcert/SATReductionIncidence.lean — MILESTONE 6 of the `3SAT ≤ 3DM` marathon: the INCIDENCE
  LEMMAS.  This module answers, for the reduction's triple map `SATReduction.tripleFn`, a single
  purely mechanical question: **which triple-indices cover each X-node and each Y-node?**

  THE SIX INCIDENCE FACTS (each an `↔` characterizing the fibre of one projection over one node):
    * X-projection (`.2.1 = XNode`):
        - an a-node `inl (i₀, j₀)` is hit by exactly the positive triple `posT i₀ j₀` (X-coord
          `inl (i₀,j₀)`) and the negative triple `negT i₀ (j₀-1)` (X-coord `inl (i, j+1)`, equal to
          `inl (i₀,j₀)` iff `i=i₀ ∧ j+1=j₀`, i.e. `j = j₀-1`, the spoke shift CYCLIC in `Fin m`);
        - an s1-node `inr (inl k)` is hit by exactly the clause-`k` slot triples (any `slot`);
        - a g1-node `inr (inr g)` is hit by exactly the garbage-`g` triples (any tip `w`).
    * Y-projection (`.2.2 = YNode`):
        - a b-node `inl (i₀, j₀)` is hit by exactly `posT i₀ j₀` AND `negT i₀ j₀` (both Y-coord
          `inl (i,j)`, NO cyclic shift on the Y side);
        - an s2-node `inr (inl k)` is hit by exactly the clause-`k` slot triples;
        - a g2-node `inr (inr g)` is hit by exactly the garbage-`g` triples.

  WHY THIS MODULE EXISTS.  These six `↔`s are the shared mechanical core consumed by BOTH the
  reverse-direction correctness proof (m7: `ThreeDM (reduce φ) → Satisfiable φ`) and the
  forward-direction proof (m8: `Satisfiable φ → ThreeDM (reduce φ)`).  Both directions reason about
  which triples can land on a given node in a perfect matching; that bookkeeping is exactly these
  fibre characterizations, factored out once.

  STANDING LIMIT.  This module proves ONLY the incidence facts — the combinatorial geometry of
  `tripleFn`.  It does NOT prove the reduction is correct (`Satisfiable φ ↔ ThreeDM (reduce φ)`);
  that is the consuming work of m7/m8.  Pure incidence, nothing more.

  Axiom-clean (no `decide`, no `native_decide`).  Expect `[propext, Quot.sound]` subsets on all six.
-/

open Sundog.SATReduction Sundog.SATNPHard

namespace Sundog.SATReductionIncidence

variable {n m : ℕ} [NeZero n] [NeZero m]

/-! ### Constructor abbreviations (readable names for the four `TripleIdx` slots). -/

/-- The wheel-POSITIVE triple index `(i, j)`. -/
abbrev posT (i : Fin n) (j : Fin m) : TripleIdx n m := Sum.inl (i, j)

/-- The wheel-NEGATIVE triple index `(i, j)`. -/
abbrev negT (i : Fin n) (j : Fin m) : TripleIdx n m := Sum.inr (Sum.inl (i, j))

/-- The CLAUSE slot-triple index `(k, slot)`. -/
abbrev clauseT (k : Fin m) (slot : Fin 3) : TripleIdx n m :=
  Sum.inr (Sum.inr (Sum.inl (k, slot)))

/-- The GARBAGE triple index `(g, w)`. -/
abbrev garbageT (g : Fin (m * (n - 1))) (w : Tip n m) : TripleIdx n m :=
  Sum.inr (Sum.inr (Sum.inr (g, w)))

/-! ### The six incidence lemmas. -/

omit [NeZero n] in
/-- **X-incidence at an a-node.**  The X-coordinate of `tripleFn φ idx` is `inl (i₀, j₀)` iff `idx`
    is the positive triple `posT i₀ j₀` or the negative triple `negT i₀ (j₀-1)` (the negative
    triple's X-coord is `inl (i, j+1)`; the cyclic predecessor `j₀-1` is the spoke that lands it on
    `j₀`). -/
theorem xcoord_inl (φ : Formula n m) (i0 : Fin n) (j0 : Fin m) (idx : TripleIdx n m) :
    (tripleFn φ idx).2.1 = Sum.inl (i0, j0) ↔ idx = posT i0 j0 ∨ idx = negT i0 (j0 - 1) := by
  rcases idx with ⟨i, j⟩ | ⟨i, j⟩ | ⟨k, slot⟩ | ⟨g, w⟩ <;>
    simp only [tripleFn, posT, negT, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, false_or, or_false]
  rw [eq_sub_iff_add_eq]

omit [NeZero n] in
/-- **X-incidence at an s1-node.**  The X-coordinate is `inr (inl k)` iff `idx` is a clause-`k`
    slot triple (for some `slot`). -/
theorem xcoord_s1 (φ : Formula n m) (k : Fin m) (idx : TripleIdx n m) :
    (tripleFn φ idx).2.1 = Sum.inr (Sum.inl k) ↔ ∃ slot, idx = clauseT k slot := by
  rcases idx with ⟨i, j⟩ | ⟨i, j⟩ | ⟨k', slot⟩ | ⟨g, w⟩ <;>
    simp [tripleFn, clauseT, Sum.inr.injEq, Prod.mk.injEq]

omit [NeZero n] in
/-- **X-incidence at a g1-node.**  The X-coordinate is `inr (inr g)` iff `idx` is a garbage-`g`
    triple (for some tip `w`). -/
theorem xcoord_g1 (φ : Formula n m) (g : Fin (m * (n - 1))) (idx : TripleIdx n m) :
    (tripleFn φ idx).2.1 = Sum.inr (Sum.inr g) ↔ ∃ w, idx = garbageT g w := by
  rcases idx with ⟨i, j⟩ | ⟨i, j⟩ | ⟨k, slot⟩ | ⟨g', w⟩ <;>
    simp [tripleFn, garbageT, Sum.inr.injEq, Prod.mk.injEq]

omit [NeZero n] in
/-- **Y-incidence at a b-node.**  The Y-coordinate is `inl (i₀, j₀)` iff `idx` is the positive
    triple `posT i₀ j₀` or the negative triple `negT i₀ j₀` (both have Y-coord `inl (i, j)` — no
    cyclic shift on the Y side). -/
theorem ycoord_inl (φ : Formula n m) (i0 : Fin n) (j0 : Fin m) (idx : TripleIdx n m) :
    (tripleFn φ idx).2.2 = Sum.inl (i0, j0) ↔ idx = posT i0 j0 ∨ idx = negT i0 j0 := by
  rcases idx with ⟨i, j⟩ | ⟨i, j⟩ | ⟨k, slot⟩ | ⟨g, w⟩ <;>
    simp [tripleFn, posT, negT, Sum.inr.injEq, Prod.mk.injEq]

omit [NeZero n] in
/-- **Y-incidence at an s2-node.**  The Y-coordinate is `inr (inl k)` iff `idx` is a clause-`k`
    slot triple (for some `slot`). -/
theorem ycoord_s2 (φ : Formula n m) (k : Fin m) (idx : TripleIdx n m) :
    (tripleFn φ idx).2.2 = Sum.inr (Sum.inl k) ↔ ∃ slot, idx = clauseT k slot := by
  rcases idx with ⟨i, j⟩ | ⟨i, j⟩ | ⟨k', slot⟩ | ⟨g, w⟩ <;>
    simp [tripleFn, clauseT, Sum.inr.injEq, Prod.mk.injEq]

omit [NeZero n] in
/-- **Y-incidence at a g2-node.**  The Y-coordinate is `inr (inr g)` iff `idx` is a garbage-`g`
    triple (for some tip `w`). -/
theorem ycoord_g2 (φ : Formula n m) (g : Fin (m * (n - 1))) (idx : TripleIdx n m) :
    (tripleFn φ idx).2.2 = Sum.inr (Sum.inr g) ↔ ∃ w, idx = garbageT g w := by
  rcases idx with ⟨i, j⟩ | ⟨i, j⟩ | ⟨k, slot⟩ | ⟨g', w⟩ <;>
    simp [tripleFn, garbageT, Sum.inr.injEq, Prod.mk.injEq]

/-! ### Axiom audit.

    Expect `[propext, Quot.sound]` subsets — NO `sorryAx`, NO `Lean.ofReduceBool`. -/


end Sundog.SATReductionIncidence
