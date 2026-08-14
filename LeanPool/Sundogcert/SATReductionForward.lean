/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.SATReductionIncidence
import LeanPool.Sundogcert.ThreeDMReindex

/-!
  Sundogcert/SATReductionForward.lean — MILESTONE 8 of the `3SAT ≤ 3DM` marathon: the FORWARD
  DIRECTION of the reduction's correctness, and the analytic crux of the whole reduction.

  WHAT THIS FILE PROVES (`forward`):
      `Satisfiable φ → threeDMI (tripleFn φ)`
  — a satisfying assignment for the formula `φ` yields a perfect 3-dimensional matching of the
  gadget triple map.  This is the hard direction: it must EXHIBIT the matching explicitly and then
  verify all three cover conditions (each W-, X-, and Y-element hit exactly once).

  THE CONSTRUCTION (pure combinatorics, all inside the proof).  From a satisfying assignment `a` and
  a per-clause witness slot `slotStar k` (`choose` from sat), build three triple families:
    * WHEEL triples — one per `(i, j)`: `wheelTriple ij = negT i j` if `a i`, else `posT i j`.  The
      tip it consumes is `(i, j, !(a i))`; so a tip `(i, j, s)` is FREE (unconsumed) iff `s = a i`.
    * CLAUSE triples — one per clause `k`: `clauseT k (slotStar k)`, whose W-tip
      `((φ k (slotStar k)).1, k, (φ k (slotStar k)).2)` is a free tip (the witness literal is true,
      so its sign matches `a` at its variable — `hlitfree`).  These `m` tips are the CLAIMED tips.
    * GARBAGE triples — one per `g : Fin (m·(n-1))`: `garbageT g (β g)`, where `β` bijects
      `Fin (m·(n-1))` onto the UNCLAIMED free tips (`freeTips \ claimedTips`; the count
      `n·m − m = m·(n−1)` uses `n ≥ 1`, and the bijection comes from `Fintype.equivFinOfCardEq`).
  The matching `T` is the union of the three image families.

  THE THREE COVER CONDITIONS.  Because the three families live in DISJOINT `Sum` summands of
  `TripleIdx`, any predicate's filtered count over `T` splits as wheel + clause + garbage
  (`hsplit`), and each part — an image of an injective map over `univ` — reduces to a `univ`-filter
  count (`hredWheel`/`hredClause`/`hredGarbage`).  Then:
    * W-condition: each tip `(i, j, s)` is hit once — CONSUMED → (1,0,0); free & CLAIMED → (0,1,0);
      free & UNCLAIMED → (0,0,1).
    * X-condition: an a-node is hit by exactly one wheel triple (the CYCLIC spoke shift, via
      `xcoord_inl`); an s1/g1-node by exactly the matching clause/garbage triple (`xcoord_s1/g1`).
    * Y-condition: a b-node by exactly the single wheel triple at `(i, j)` (NO cyclic shift,
      `ycoord_inl`); an s2/g2-node by the matching clause/garbage triple (`ycoord_s2/g2`).

  STANDING LIMIT: this module proves ONLY the forward direction.  The reverse direction
  (`threeDMI (tripleFn φ) → Satisfiable φ`) is milestone 7 (`Sundogcert/SATReductionReverse.lean`),
  and the index-bridge to the `Fin s`-indexed `MatchingNPHard.ThreeDM` is milestone 5
  (`Sundogcert/ThreeDMReindex.lean`).  Nothing here is claimed about NP-hardness itself.

  NOTE on `synthInstance.maxSize`: `DecidableEq (TripleIdx n m)` (a 4-way nested `Sum` of products)
  does not synthesize at the default `maxSize` inside this large proof context; a scoped
  `set_option synthInstance.maxSize 512 in` on `forward` clears it (as in m7).

  Axiom-clean (no `native_decide`, no `decide`).  Expect `[propext, Classical.choice, Quot.sound]`.
-/

open Sundog.SATReduction Sundog.SATNPHard Sundog.VarWheel
open Sundog.SATReductionIncidence Sundog.ThreeDMReindex

namespace Sundog.SATReductionForward

variable {n m : ℕ} [NeZero n] [NeZero m]

omit [NeZero n] in
/-- The **W-fibre (tip) cover condition** of the forward matching, factored out of `forward`.

Given the disjoint-split reduction `hsplit`, the per-family `univ`-filter reductions `hred*`,
and the per-family tip characterizations `h*tip`, every tip `w` is covered exactly once by the
matching: consumed → wheel hits it once; free & claimed → the clause triple; free & unclaimed →
the garbage triple. -/
theorem wfibre_cover (φ : Formula n m) (a : Assignment n)
    (slotStar : Fin m → Fin 3)
    (wheelTriple : Fin n × Fin m → TripleIdx n m)
    (beta : Fin (m * (n - 1)) → Tip n m)
    (freeTips claimedTips unclaimed : Finset (Tip n m))
    (T : Finset (TripleIdx n m))
    (hsplit : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (T.filter P).card
        = (Finset.univ.filter (fun ij => P (wheelTriple ij))).card
          + (Finset.univ.filter (fun k => P (clauseT k (slotStar k)))).card
          + (Finset.univ.filter (fun g => P (garbageT g (beta g)))).card)
    (hwheeltip : ∀ ij : Fin n × Fin m,
      (tripleFn φ (wheelTriple ij)).1 = (ij.1, ij.2, !(a ij.1)))
    (hclausetip : ∀ k : Fin m,
      (tripleFn φ (clauseT k (slotStar k))).1
        = ((φ k (slotStar k)).1, k, (φ k (slotStar k)).2))
    (hgarbagetip : ∀ g, (tripleFn φ (garbageT g (beta g))).1 = beta g)
    (hbeta_mem : ∀ g, beta g ∈ unclaimed)
    (hbeta_inj : Function.Injective beta)
    (hbeta_surj : ∀ w ∈ unclaimed, ∃ g, beta g = w)
    (hsub : claimedTips ⊆ freeTips)
    (hfreeTips : freeTips = Finset.univ.filter (fun tau : Tip n m => tau.2.2 = a tau.1))
    (hclaimedTips : claimedTips = Finset.univ.image
      (fun k : Fin m => ((φ k (slotStar k)).1, k, (φ k (slotStar k)).2)))
    (hunclaimed : unclaimed = freeTips \ claimedTips) :
    ∀ w : Tip n m, (T.filter (fun idx => (tripleFn φ idx).1 = w)).card = 1 := by
  intro w
  obtain ⟨wi, wj, ws⟩ := w
  rw [hsplit (fun idx => (tripleFn φ idx).1 = (wi, wj, ws))]
  have hWwheel_consumed : ws = !(a wi) →
      (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).1 = (wi, wj, ws))).card = 1 := by
    intro hcons
    rw [Finset.card_eq_one]
    refine ⟨(wi, wj), ?_⟩
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      hwheeltip, Prod.mk.injEq]
    constructor
    · rintro ⟨hi, hj, _⟩; exact Prod.ext hi hj
    · rintro rfl; exact ⟨rfl, rfl, hcons.symm⟩
  have hWwheel_free : ws = a wi →
      (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).1 = (wi, wj, ws))).card = 0 := by
    intro hfree
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ij _
    simp only [hwheeltip, Prod.mk.injEq, not_and]
    rintro rfl _
    rw [hfree]; simp
  have hWclause_in : ((wi, wj, ws) : Tip n m) ∈ claimedTips →
      (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).1 = (wi, wj, ws))).card = 1 := by
    intro hin
    rw [hclaimedTips] at hin
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hin
    obtain ⟨k0, hk0⟩ := hin
    rw [Finset.card_eq_one]
    refine ⟨k0, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      hclausetip]
    constructor
    · intro hk
      have h2 : k = wj := by
        have := congrArg (fun t : Tip n m => t.2.1) hk; simpa using this
      have h2' : k0 = wj := by
        have := congrArg (fun t : Tip n m => t.2.1) hk0; simpa using this
      rw [h2, ← h2']
    · rintro rfl; exact hk0
  have hWclause_out : ((wi, wj, ws) : Tip n m) ∉ claimedTips →
      (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).1 = (wi, wj, ws))).card = 0 := by
    intro hout
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    simp only [hclausetip]
    intro hk
    apply hout
    rw [hclaimedTips]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨k, hk⟩
  have hWgarbage_in : ((wi, wj, ws) : Tip n m) ∈ unclaimed →
      (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).1 = (wi, wj, ws))).card = 1 := by
    intro hin
    obtain ⟨g0, hg0⟩ := hbeta_surj _ hin
    rw [Finset.card_eq_one]
    refine ⟨g0, ?_⟩
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      hgarbagetip]
    constructor
    · intro hg; exact hbeta_inj (hg.trans hg0.symm)
    · rintro rfl; exact hg0
  have hWgarbage_out : ((wi, wj, ws) : Tip n m) ∉ unclaimed →
      (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).1 = (wi, wj, ws))).card = 0 := by
    intro hout
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g _
    simp only [hgarbagetip]
    intro hg
    apply hout
    rw [← hg]; exact hbeta_mem g
  have hwfree : ((wi, wj, ws) : Tip n m) ∈ freeTips ↔ ws = a wi := by
    rw [hfreeTips]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hfree : ws = a wi
  · rw [hWwheel_free hfree]
    by_cases hcl : ((wi, wj, ws) : Tip n m) ∈ claimedTips
    · have hncl : ((wi, wj, ws) : Tip n m) ∉ unclaimed := by
        rw [hunclaimed]
        simp only [Finset.mem_sdiff, not_and, not_not]
        intro _; exact hcl
      rw [hWclause_in hcl, hWgarbage_out hncl]
    · have hunc' : ((wi, wj, ws) : Tip n m) ∈ unclaimed := by
        rw [hunclaimed]
        simp only [Finset.mem_sdiff]
        exact ⟨hwfree.mpr hfree, hcl⟩
      rw [hWclause_out hcl, hWgarbage_in hunc']
  · have hcons : ws = !(a wi) := Bool.eq_not.mpr hfree
    have hncl : ((wi, wj, ws) : Tip n m) ∉ claimedTips := by
      intro hc
      exact hfree (hwfree.mp (hsub hc))
    have hnunc : ((wi, wj, ws) : Tip n m) ∉ unclaimed := by
      rw [hunclaimed]
      simp only [Finset.mem_sdiff, not_and, not_not]
      intro hcontra; exact absurd (hwfree.mp hcontra) hfree
    rw [hWwheel_consumed hcons, hWclause_out hncl, hWgarbage_out hnunc]

omit [NeZero n] in
/-- The **X-node cover condition** of the forward matching, factored out of `forward`.

Each a-node `inl (i,j)` is hit by exactly one wheel triple (the cyclic spoke shift); each
s1-node by exactly its clause triple; each g1-node by exactly its garbage triple. -/
theorem xnode_cover (φ : Formula n m) (a : Assignment n)
    (slotStar : Fin m → Fin 3)
    (wheelTriple : Fin n × Fin m → TripleIdx n m)
    (beta : Fin (m * (n - 1)) → Tip n m)
    (T : Finset (TripleIdx n m))
    (hsplit : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (T.filter P).card
        = (Finset.univ.filter (fun ij => P (wheelTriple ij))).card
          + (Finset.univ.filter (fun k => P (clauseT k (slotStar k)))).card
          + (Finset.univ.filter (fun g => P (garbageT g (beta g)))).card)
    (hwheelDef : ∀ ij : Fin n × Fin m,
      wheelTriple ij = if a ij.1 then negT ij.1 ij.2 else posT ij.1 ij.2)
    (hwheel_form : ∀ ij,
      wheelTriple ij = negT ij.1 ij.2 ∨ wheelTriple ij = posT ij.1 ij.2) :
    ∀ x : XNode n m, (T.filter (fun idx => (tripleFn φ idx).2.1 = x)).card = 1 := by
  intro x
  rw [hsplit (fun idx => (tripleFn φ idx).2.1 = x)]
  match x with
  | Sum.inl (i0, j0) =>
    have hc0 : (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).2.1 = Sum.inl (i0, j0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [xcoord_inl]
      rintro (h | h) <;> simp [clauseT, posT, negT] at h
    have hg0 : (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).2.1 = Sum.inl (i0, j0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro g _
      rw [xcoord_inl]
      rintro (h | h) <;> simp [garbageT, posT, negT] at h
    have hw1 : (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).2.1 = Sum.inl (i0, j0))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨if a i0 then (i0, j0 - 1) else (i0, j0), ?_⟩
      ext ij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [xcoord_inl]
      obtain ⟨i, j⟩ := ij
      constructor
      · rintro (h | h)
        · rw [hwheelDef] at h
          split at h
          · simp [negT, posT] at h
          · rename_i hai
            simp only [posT, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨hi, hj⟩ := h; subst hi; subst hj
            simp only [Bool.not_eq_true] at hai
            rw [ite_eq_right (by simp [hai])]
        · rw [hwheelDef] at h
          split at h
          · rename_i hai
            simp only [negT, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
            obtain ⟨hi, hj⟩ := h; subst hi; subst hj
            rw [ite_eq_left hai]
          · simp [posT, negT] at h
      · intro h
        by_cases hai : a i0 = true
        · rw [ite_eq_left hai] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨hi, hj⟩ := h; subst hi; subst hj
          right
          rw [hwheelDef]
          rw [ite_eq_left hai]
        · rw [ite_eq_right hai] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨hi, hj⟩ := h; subst hi; subst hj
          left
          rw [hwheelDef]
          rw [ite_eq_right hai]
    rw [hc0, hg0, hw1]
  | Sum.inr (Sum.inl k0) =>
    have hw0 : (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).2.1 = Sum.inr (Sum.inl k0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ij _
      rw [xcoord_s1]
      rintro ⟨slot, hs⟩
      rcases hwheel_form ij with hf | hf <;>
        (rw [hf] at hs; simp [negT, posT, clauseT] at hs)
    have hg0 : (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).2.1 = Sum.inr (Sum.inl k0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro g _
      rw [xcoord_s1]
      rintro ⟨slot, hs⟩
      simp [garbageT, clauseT] at hs
    have hc1 : (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).2.1 = Sum.inr (Sum.inl k0))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨k0, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [xcoord_s1]
      constructor
      · rintro ⟨slot, hs⟩
        simp only [clauseT, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hs
        exact hs.1
      · rintro rfl; exact ⟨slotStar k, rfl⟩
    rw [hw0, hg0, hc1]
  | Sum.inr (Sum.inr g0) =>
    have hw0 : (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).2.1 = Sum.inr (Sum.inr g0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ij _
      rw [xcoord_g1]
      rintro ⟨w, hw⟩
      rcases hwheel_form ij with hf | hf <;>
        (rw [hf] at hw; simp [negT, posT, garbageT] at hw)
    have hc0 : (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).2.1 = Sum.inr (Sum.inr g0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [xcoord_g1]
      rintro ⟨w, hw⟩
      simp [clauseT, garbageT] at hw
    have hg1 : (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).2.1 = Sum.inr (Sum.inr g0))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨g0, ?_⟩
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [xcoord_g1]
      constructor
      · rintro ⟨w, hw⟩
        simp only [garbageT, Sum.inr.injEq, Prod.mk.injEq] at hw
        exact hw.1
      · rintro rfl; exact ⟨beta g, rfl⟩
    rw [hw0, hc0, hg1]

omit [NeZero n] in
/-- The **Y-node cover condition** of the forward matching, factored out of `forward`.

Each b-node `inl (i,j)` is hit by exactly one wheel triple (no cyclic shift on the Y side); each
s2-node by exactly its clause triple; each g2-node by exactly its garbage triple. -/
theorem ynode_cover (φ : Formula n m)
    (slotStar : Fin m → Fin 3)
    (wheelTriple : Fin n × Fin m → TripleIdx n m)
    (beta : Fin (m * (n - 1)) → Tip n m)
    (T : Finset (TripleIdx n m))
    (hsplit : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (T.filter P).card
        = (Finset.univ.filter (fun ij => P (wheelTriple ij))).card
          + (Finset.univ.filter (fun k => P (clauseT k (slotStar k)))).card
          + (Finset.univ.filter (fun g => P (garbageT g (beta g)))).card)
    (hwheel_form : ∀ ij,
      wheelTriple ij = negT ij.1 ij.2 ∨ wheelTriple ij = posT ij.1 ij.2) :
    ∀ y : YNode n m, (T.filter (fun idx => (tripleFn φ idx).2.2 = y)).card = 1 := by
  intro y
  rw [hsplit (fun idx => (tripleFn φ idx).2.2 = y)]
  match y with
  | Sum.inl (i0, j0) =>
    have hc0 : (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).2.2 = Sum.inl (i0, j0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [ycoord_inl]
      rintro (h | h) <;> simp [clauseT, posT, negT] at h
    have hg0 : (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).2.2 = Sum.inl (i0, j0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro g _
      rw [ycoord_inl]
      rintro (h | h) <;> simp [garbageT, posT, negT] at h
    have hw1 : (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).2.2 = Sum.inl (i0, j0))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨(i0, j0), ?_⟩
      ext ij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [ycoord_inl]
      constructor
      · rintro (h | h) <;>
          (rcases hwheel_form ij with hf | hf <;>
            (rw [hf] at h; simp only [negT, posT, Sum.inl.injEq, Sum.inr.injEq,
              Prod.mk.injEq, reduceCtorEq] at h <;> try exact Prod.ext h.1 h.2))
      · rintro rfl
        rcases hwheel_form (i0, j0) with hf | hf <;> rw [hf]
        · right; rfl
        · left; rfl
    rw [hc0, hg0, hw1]
  | Sum.inr (Sum.inl k0) =>
    have hw0 : (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).2.2 = Sum.inr (Sum.inl k0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ij _
      rw [ycoord_s2]
      rintro ⟨slot, hs⟩
      rcases hwheel_form ij with hf | hf <;>
        (rw [hf] at hs; simp [negT, posT, clauseT] at hs)
    have hg0 : (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).2.2 = Sum.inr (Sum.inl k0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro g _
      rw [ycoord_s2]
      rintro ⟨slot, hs⟩
      simp [garbageT, clauseT] at hs
    have hc1 : (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).2.2 = Sum.inr (Sum.inl k0))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨k0, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [ycoord_s2]
      constructor
      · rintro ⟨slot, hs⟩
        simp only [clauseT, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hs
        exact hs.1
      · rintro rfl; exact ⟨slotStar k, rfl⟩
    rw [hw0, hg0, hc1]
  | Sum.inr (Sum.inr g0) =>
    have hw0 : (Finset.univ.filter (fun ij =>
        (tripleFn φ (wheelTriple ij)).2.2 = Sum.inr (Sum.inr g0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro ij _
      rw [ycoord_g2]
      rintro ⟨w, hw⟩
      rcases hwheel_form ij with hf | hf <;>
        (rw [hf] at hw; simp [negT, posT, garbageT] at hw)
    have hc0 : (Finset.univ.filter (fun k =>
        (tripleFn φ (clauseT k (slotStar k))).2.2 = Sum.inr (Sum.inr g0))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [ycoord_g2]
      rintro ⟨w, hw⟩
      simp [clauseT, garbageT] at hw
    have hg1 : (Finset.univ.filter (fun g =>
        (tripleFn φ (garbageT g (beta g))).2.2 = Sum.inr (Sum.inr g0))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨g0, ?_⟩
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [ycoord_g2]
      constructor
      · rintro ⟨w, hw⟩
        simp only [garbageT, Sum.inr.injEq, Prod.mk.injEq] at hw
        exact hw.1
      · rintro rfl; exact ⟨beta g, rfl⟩
    rw [hw0, hc0, hg1]

theorem forward (φ : Formula n m) (h : Satisfiable φ) :
    threeDMI (tripleFn φ) := by
  obtain ⟨a, hsat⟩ := h
  choose slotStar hslotStar using hsat
  let wheelTriple : Fin n × Fin m → TripleIdx n m :=
    fun ij => if a ij.1 then negT ij.1 ij.2 else posT ij.1 ij.2
  let freeTips : Finset (Tip n m) :=
    Finset.univ.filter (fun tau => tau.2.2 = a tau.1)
  let claimedTips : Finset (Tip n m) :=
    Finset.univ.image
      (fun k : Fin m => ((φ k (slotStar k)).1, k, (φ k (slotStar k)).2))
  let unclaimed : Finset (Tip n m) := freeTips \ claimedTips
  have hfreeEq : freeTips = Finset.univ.image (fun ij : Fin n × Fin m =>
      ((ij.1, ij.2, a ij.1) : Tip n m)) := by
    apply Finset.ext
    intro tau
    obtain ⟨i, j, s⟩ := tau
    simp only [freeTips, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro hs
      exact ⟨(i, j), by simp [hs.symm]⟩
    · rintro ⟨⟨i', j'⟩, h⟩
      obtain ⟨hi, hj, hsgn⟩ := h
      subst hi; subst hj; rw [hsgn]
  have hfinj : Function.Injective
      (fun ij : Fin n × Fin m => ((ij.1, ij.2, a ij.1) : Tip n m)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2.1
  have hfree : freeTips.card = n * m := by
    rw [hfreeEq, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hcinj : Function.Injective
      (fun k : Fin m => (((φ k (slotStar k)).1, k, (φ k (slotStar k)).2) : Tip n m)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.2.1
  have hclaim : claimedTips.card = m := by
    change (Finset.univ.image
      (fun k : Fin m => (((φ k (slotStar k)).1, k, (φ k (slotStar k)).2) : Tip n m))).card = m
    rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_fin]
  have hlitfree : ∀ k : Fin m, (φ k (slotStar k)).2 = a (φ k (slotStar k)).1 := by
    intro k
    have he := hslotStar k
    unfold evalLiteral at he
    cases hsgn : (φ k (slotStar k)).2 with
    | true =>
      rw [hsgn] at he; simp only [ite_true] at he; exact he.symm
    | false =>
      rw [hsgn] at he
      simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true'] at he
      exact he.symm
  have hsub : claimedTips ⊆ freeTips := by
    intro tau htau
    simp only [claimedTips, Finset.mem_image, Finset.mem_univ, true_and] at htau
    obtain ⟨k, hk⟩ := htau
    simp only [freeTips, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hk]
    exact (hlitfree k)
  have hunc : unclaimed.card = m * (n - 1) := by
    change (freeTips \ claimedTips).card = m * (n - 1)
    rw [Finset.card_sdiff_of_subset hsub, hfree, hclaim]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
    rw [Nat.succ_sub_one, Nat.succ_mul, Nat.add_sub_cancel, Nat.mul_comm]
  have hcard : Fintype.card { x : Tip n m // x ∈ unclaimed } = m * (n - 1) := by
    rw [Fintype.card_coe]; exact hunc
  let e : { x : Tip n m // x ∈ unclaimed } ≃ Fin (m * (n - 1)) :=
    Fintype.equivFinOfCardEq hcard
  let beta : Fin (m * (n - 1)) → Tip n m := fun g => (e.symm g).val
  have hbeta_mem : ∀ g, beta g ∈ unclaimed := fun g => (e.symm g).property
  have hbeta_inj : Function.Injective beta := by
    intro x y hxy
    have : e.symm x = e.symm y := Subtype.ext hxy
    exact e.symm.injective this
  have hbeta_surj : ∀ w ∈ unclaimed, ∃ g, beta g = w := by
    intro w hw
    refine ⟨e ⟨w, hw⟩, ?_⟩
    simp only [beta, Equiv.symm_apply_apply]
  let Twheel : Finset (TripleIdx n m) := Finset.univ.image wheelTriple
  let Tclause : Finset (TripleIdx n m) :=
    Finset.univ.image (fun k : Fin m => clauseT k (slotStar k))
  let Tgarbage : Finset (TripleIdx n m) :=
    Finset.univ.image (fun g : Fin (m * (n - 1)) => garbageT g (beta g))
  let T : Finset (TripleIdx n m) := Twheel ∪ Tclause ∪ Tgarbage
  have hmemWheel : ∀ idx, idx ∈ Twheel ↔ ∃ ij, wheelTriple ij = idx := by
    intro idx; simp only [Twheel, Finset.mem_image, Finset.mem_univ, true_and]
  have hmemClause : ∀ idx, idx ∈ Tclause ↔ ∃ k, clauseT k (slotStar k) = idx := by
    intro idx; simp only [Tclause, Finset.mem_image, Finset.mem_univ, true_and]
  have hmemGarbage : ∀ idx, idx ∈ Tgarbage ↔ ∃ g, garbageT g (beta g) = idx := by
    intro idx; simp only [Tgarbage, Finset.mem_image, Finset.mem_univ, true_and]
  have hwheel_form : ∀ ij,
      wheelTriple ij = negT ij.1 ij.2 ∨ wheelTriple ij = posT ij.1 ij.2 := by
    intro ij; simp only [wheelTriple]; split <;> [left; right] <;> rfl
  have hdisj_wc : Disjoint Twheel Tclause := by
    rw [Finset.disjoint_left]
    intro idx hw hc
    rw [hmemWheel] at hw; rw [hmemClause] at hc
    obtain ⟨ij, hij⟩ := hw; obtain ⟨k, hk⟩ := hc
    rcases hwheel_form ij with hf | hf <;>
      (rw [hf] at hij; rw [← hij] at hk; simp [negT, posT, clauseT] at hk)
  have hdisj_wg : Disjoint Twheel Tgarbage := by
    rw [Finset.disjoint_left]
    intro idx hw hg
    rw [hmemWheel] at hw; rw [hmemGarbage] at hg
    obtain ⟨ij, hij⟩ := hw; obtain ⟨g, hg'⟩ := hg
    rcases hwheel_form ij with hf | hf <;>
      (rw [hf] at hij; rw [← hij] at hg'; simp [negT, posT, garbageT] at hg')
  have hdisj_cg : Disjoint Tclause Tgarbage := by
    rw [Finset.disjoint_left]
    intro idx hc hg
    rw [hmemClause] at hc; rw [hmemGarbage] at hg
    obtain ⟨k, hk⟩ := hc; obtain ⟨g, hg'⟩ := hg
    rw [← hk] at hg'; simp [clauseT, garbageT] at hg'
  have hsplit : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (T.filter P).card
        = (Twheel.filter P).card + (Tclause.filter P).card + (Tgarbage.filter P).card := by
    intro P _
    change ((Twheel ∪ Tclause ∪ Tgarbage).filter P).card = _
    rw [Finset.filter_union, Finset.filter_union]
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter hdisj_wc (p := P) (q := P))]
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter_filter hdisj_wg (p := P) (q := P),
      Finset.disjoint_filter_filter hdisj_cg (p := P) (q := P)⟩
  have hwinj : Function.Injective wheelTriple := by
    intro x y hxy
    simp only [wheelTriple] at hxy
    obtain ⟨xi, xj⟩ := x; obtain ⟨yi, yj⟩ := y
    revert hxy; split <;> split <;> intro hxy <;>
      simp_all [negT, posT, Prod.ext_iff]
  have hclinj : Function.Injective
      (fun k : Fin m => (clauseT k (slotStar k) : TripleIdx n m)) := by
    intro x y hxy
    simp only [clauseT, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at hxy
    exact hxy.1
  have hginj : Function.Injective
      (fun g : Fin (m * (n - 1)) => (garbageT g (beta g) : TripleIdx n m)) := by
    intro x y hxy
    simp only [garbageT, Sum.inr.injEq, Prod.mk.injEq] at hxy
    exact hxy.1
  have hredWheel : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (Twheel.filter P).card = (Finset.univ.filter (fun ij => P (wheelTriple ij))).card := by
    intro P _
    change (Finset.filter P (Finset.univ.image wheelTriple)).card = _
    rw [Finset.filter_image, Finset.card_image_of_injective _ hwinj]
  have hredClause : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (Tclause.filter P).card
        = (Finset.univ.filter (fun k => P (clauseT k (slotStar k)))).card := by
    intro P _
    change (Finset.filter P (Finset.univ.image (fun k => clauseT k (slotStar k)))).card = _
    rw [Finset.filter_image, Finset.card_image_of_injective _ hclinj]
  have hredGarbage : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (Tgarbage.filter P).card
        = (Finset.univ.filter (fun g => P (garbageT g (beta g)))).card := by
    intro P _
    change (Finset.filter P (Finset.univ.image (fun g => garbageT g (beta g)))).card = _
    rw [Finset.filter_image, Finset.card_image_of_injective _ hginj]
  have hwheeltip : ∀ ij : Fin n × Fin m,
      (tripleFn φ (wheelTriple ij)).1 = (ij.1, ij.2, !(a ij.1)) := by
    intro ij
    simp only [wheelTriple]
    split
    · rename_i h; simp [tripleFn, h]
    · rename_i h; simp only [Bool.not_eq_true] at h; simp [tripleFn, h]
  have hclausetip : ∀ k : Fin m,
      (tripleFn φ (clauseT k (slotStar k))).1
        = ((φ k (slotStar k)).1, k, (φ k (slotStar k)).2) := by
    intro k; simp [tripleFn]
  have hgarbagetip : ∀ g, (tripleFn φ (garbageT g (beta g))).1 = beta g := by
    intro g; simp [tripleFn]
  -- Combine the disjoint-split with the three image reductions into one univ-filter split.
  have hsplitFull : ∀ (P : TripleIdx n m → Prop) [DecidablePred P],
      (T.filter P).card
        = (Finset.univ.filter (fun ij => P (wheelTriple ij))).card
          + (Finset.univ.filter (fun k => P (clauseT k (slotStar k)))).card
          + (Finset.univ.filter (fun g => P (garbageT g (beta g)))).card := by
    intro P _
    rw [hsplit P, hredWheel P, hredClause P, hredGarbage P]
  exact ⟨T,
    wfibre_cover φ a slotStar wheelTriple beta freeTips claimedTips unclaimed T
      hsplitFull hwheeltip hclausetip hgarbagetip hbeta_mem hbeta_inj hbeta_surj hsub
      rfl rfl rfl,
    xnode_cover φ a slotStar wheelTriple beta T hsplitFull (fun _ => rfl) hwheel_form,
    ynode_cover φ slotStar wheelTriple beta T hsplitFull hwheel_form⟩

end Sundog.SATReductionForward
