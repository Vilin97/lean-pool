/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.SATReductionIncidence
import LeanPool.Sundogcert.ThreeDMReindex

/-!
  Sundogcert/SATReductionReverse.lean — MILESTONE 7 of the `3SAT ≤ 3DM` marathon: the REVERSE
  DIRECTION of the reduction's correctness.

  WHAT THIS FILE PROVES (`reverse`):
      `threeDMI (tripleFn φ) → Satisfiable φ`
  — a perfect 3-dimensional matching of the gadget triple map yields a satisfying assignment for
  the formula `φ`.  This is the analytic crux of the reduction; it does NOT touch the garbage
  triples (their only role is to absorb the unused tips, which a perfect matching handles for free).

  THE PROOF IDEA (pure combinatorics):
    Let `T : Finset (TripleIdx n m)` be the matching selection.
    * Define `σ i j := decide (posT i j ∈ T)` — for each variable `i`, the wheel state read off
      from which positive triples were selected.
    * Each b-node `(i,j)` is covered exactly once (`hY`); the only triples touching it are
      `posT i j` and `negT i j` (incidence `ycoord_inl`).  So EXACTLY ONE of the two is in `T`:
      `posT i j ∈ T ↔ ¬ negT i j ∈ T`  (the helper `card_filter_pair_eq_one`).
    * Each a-node `(i,j)` is covered exactly once (`hX`); the only triples touching it are
      `posT i j` and `negT i (j-1)` (incidence `xcoord_inl`, the CYCLIC spoke shift).  So
      `posT i j ∈ T ↔ ¬ negT i (j-1) ∈ T`.
    * Chaining the two facts forces `σ i j = σ i (j-1)` for every spoke ⟹ `σ i` is a `ValidCover`
      ⟹ by `validCover_iff_const`, `σ i` is CONSTANT (the wheel admits only the all-true / all-false
      covers — the two truth values).  Take the assignment `a i := !(σ i 0)`.
    * Each s1-node `k` is covered exactly once (`hX`), and the only triples touching it are the
      clause-`k` slot triples (`xcoord_s1`).  Hence some `clauseT k slotStar ∈ T`; its W-tip
      `τ = (iS, k, sgn)` (with `(iS, sgn) = φ k slotStar`) is then covered by that clause triple, so
      the matching wheel triple over `τ` (`posT iS k` if `sgn`, else `negT iS k`) is NOT in `T`
      (`hW`: the W-fibre over `τ` has card 1).  Reading this back through `σ` shows the literal
      `φ k slotStar` evaluates to `true`, hence clause `k` is satisfied.

  STANDING LIMIT: this module proves ONLY the reverse direction.  The forward direction
  (`Satisfiable φ → threeDMI (tripleFn φ)` — a matching from an assignment) is milestone 8.

  NOTE on the `synthInstance.maxSize` bump: `DecidableEq (TripleIdx n m)` (a 4-way nested `Sum` of
  products) does not synthesize at the default `maxSize`; the `filter_congr` rewrites whose target
  predicate is `idx = posT i j ∨ idx = negT i j` push the threshold higher still.  A scoped
  `set_option synthInstance.maxSize 512 in` on `reverse` clears it (the generic helper needs none).

  Axiom-clean (no `native_decide`; the only `decide` is the data-level Prop-membership read).
  Expect `[propext, Classical.choice, Quot.sound]` on both `reverse` and the helper.
-/

open Sundog.SATReduction Sundog.SATNPHard Sundog.VarWheel
open Sundog.SATReductionIncidence Sundog.ThreeDMReindex

namespace Sundog.SATReductionReverse

variable {n m : ℕ} [NeZero n] [NeZero m]

/-! ### Helper lemma -/

/-- In a `Finset` `T`, if exactly one of two DISTINCT elements `a`, `b` is present (the `{a,b}`
    fibre of `T` has card `1`), then membership of `a` is the negation of membership of `b`. -/
lemma card_filter_pair_eq_one {α} [DecidableEq α] {T : Finset α} {a b : α}
    (hab : a ≠ b)
    (h : (T.filter (fun x => x = a ∨ x = b)).card = 1) :
    (a ∈ T) ↔ ¬ (b ∈ T) := by
  rw [Finset.filter_or, Finset.filter_eq', Finset.filter_eq'] at h
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> simp_all

/-! ### The reverse theorem -/

omit [NeZero n] in
/-- **Reverse correctness.**  A perfect 3-dimensional matching of the gadget triple map yields a
    satisfying assignment: the wheel triples force each variable's selection constant (a truth
    value), and each clause's selected slot triple frees its literal's wheel triple, making the
    literal true.  (One direction only; the forward direction is milestone 8.) -/
theorem reverse (φ : Formula n m) (h : threeDMI (tripleFn φ)) :
    Satisfiable φ := by
  obtain ⟨T, hW, hX, hY⟩ := h
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set σ : Fin n → Fin m → Bool := fun i j => decide (posT i j ∈ T) with hσ
  -- b-node exactly-one fact
  have hb : ∀ i j, (posT i j ∈ T) ↔ ¬ (negT i j ∈ T) := by
    intro i j
    have hc := hY (Sum.inl (i, j))
    have heq : (T.filter (fun idx => (tripleFn φ idx).2.2 = Sum.inl (i, j)))
        = (T.filter (fun idx => idx = posT i j ∨ idx = negT i j)) :=
      Finset.filter_congr (fun idx _ => ycoord_inl φ i j idx)
    rw [heq] at hc
    exact card_filter_pair_eq_one (by simp [posT, negT]) hc
  -- a-node exactly-one fact
  have ha : ∀ i j, (posT i j ∈ T) ↔ ¬ (negT i (j - 1) ∈ T) := by
    intro i j
    have hc := hX (Sum.inl (i, j))
    have heq : (T.filter (fun idx => (tripleFn φ idx).2.1 = Sum.inl (i, j)))
        = (T.filter (fun idx => idx = posT i j ∨ idx = negT i (j - 1))) :=
      Finset.filter_congr (fun idx _ => xcoord_inl φ i j idx)
    rw [heq] at hc
    exact card_filter_pair_eq_one (by simp [posT, negT]) hc
  -- each spoke is a valid cover
  have hvalid : ∀ i, ValidCover (σ i) := by
    intro i j
    rw [aCoveredOnce_iff]
    change decide (posT i j ∈ T) = decide (posT i (j - 1) ∈ T)
    have h1 := ha i j
    have h2 := hb i (j - 1)
    by_cases hp : posT i j ∈ T <;> by_cases hq : posT i (j - 1) ∈ T <;>
      simp_all
  -- each spoke is constant
  have hconst : ∀ i, σ i = (fun _ => σ i ⟨0, hm0⟩) := by
    intro i
    rcases (validCover_iff_const hm0 (σ i)).mp (hvalid i) with hh | hh <;>
      rw [hh]
  -- the assignment
  refine ⟨fun i => !(σ i ⟨0, hm0⟩), ?_⟩
  intro k
  -- extract a clause-k triple in T
  have hs1 := hX (Sum.inr (Sum.inl k))
  have heqs : (T.filter (fun idx => (tripleFn φ idx).2.1 = Sum.inr (Sum.inl k)))
      = (T.filter (fun idx => ∃ slot, idx = clauseT k slot)) :=
    Finset.filter_congr (fun idx _ => xcoord_s1 φ k idx)
  rw [heqs] at hs1
  obtain ⟨idx0, hidx0⟩ := Finset.card_pos.mp (by rw [hs1]; norm_num)
  rw [Finset.mem_filter] at hidx0
  obtain ⟨hmem, slotStar, hslot⟩ := hidx0
  have hmemC : clauseT k slotStar ∈ T := hslot ▸ hmem
  -- tip data
  set iS : Fin n := (φ k slotStar).1 with hiSdef
  set sgn : Bool := (φ k slotStar).2 with hsgndef
  -- the clause triple's W-coord equals the tip τ = (iS, k, sgn)
  have htipC : (tripleFn φ (clauseT k slotStar)).1 = (iS, k, sgn) := by
    simp [tripleFn, hiSdef, hsgndef]
  -- the W-fibre over τ has card 1
  have hWk := hW (iS, k, sgn)
  -- clauseT k slotStar is in that fibre
  have hCin : clauseT k slotStar ∈
      T.filter (fun i => (tripleFn φ i).1 = (iS, k, sgn)) := by
    rw [Finset.mem_filter]; exact ⟨hmemC, htipC⟩
  refine ⟨slotStar, ?_⟩
  -- split on the literal sign
  cases hs : sgn with
  | true =>
    -- wtri = posT iS k; show posT iS k ∉ T
    have htipP : (tripleFn φ (posT iS k)).1 = (iS, k, sgn) := by
      rw [hs]; simp [tripleFn]
    have hne : posT iS k ≠ clauseT k slotStar := by simp [posT, clauseT]
    have hpos_not : posT iS k ∉ T := by
      intro hpin
      have hPin : posT iS k ∈
          T.filter (fun i => (tripleFn φ i).1 = (iS, k, sgn)) := by
        rw [Finset.mem_filter]; exact ⟨hpin, htipP⟩
      have : 1 < (T.filter (fun i => (tripleFn φ i).1 = (iS, k, sgn))).card :=
        Finset.one_lt_card.mpr ⟨posT iS k, hPin, clauseT k slotStar, hCin, hne⟩
      omega
    -- σ iS k = false
    have hσk : σ iS k = false := by
      rw [hσ]; simp only [decide_eq_false_iff_not]; exact hpos_not
    have hck : σ iS ⟨0, hm0⟩ = false := by
      rw [← congrFun (hconst iS) k]; exact hσk
    simp only [evalLiteral, ← hiSdef, ← hsgndef, hs]
    rw [hck]; rfl
  | false =>
    -- wtri = negT iS k; show negT iS k ∉ T, hence posT iS k ∈ T
    have htipN : (tripleFn φ (negT iS k)).1 = (iS, k, sgn) := by
      rw [hs]; simp [tripleFn]
    have hne : negT iS k ≠ clauseT k slotStar := by simp [negT, clauseT]
    have hneg_not : negT iS k ∉ T := by
      intro hnin
      have hNin : negT iS k ∈
          T.filter (fun i => (tripleFn φ i).1 = (iS, k, sgn)) := by
        rw [Finset.mem_filter]; exact ⟨hnin, htipN⟩
      have : 1 < (T.filter (fun i => (tripleFn φ i).1 = (iS, k, sgn))).card :=
        Finset.one_lt_card.mpr ⟨negT iS k, hNin, clauseT k slotStar, hCin, hne⟩
      omega
    have hpos_in : posT iS k ∈ T := (hb iS k).mpr hneg_not
    have hσk : σ iS k = true := by
      rw [hσ]; simp only [decide_eq_true_iff]; exact hpos_in
    have hck : σ iS ⟨0, hm0⟩ = true := by
      rw [← congrFun (hconst iS) k]; exact hσk
    simp only [evalLiteral, ← hiSdef, ← hsgndef, hs]
    rw [hck]; rfl

/-! ### Axiom audit.

    Expect `[propext, Classical.choice, Quot.sound]` — NO `sorryAx`, NO `Lean.ofReduceBool`. -/


end Sundog.SATReductionReverse
