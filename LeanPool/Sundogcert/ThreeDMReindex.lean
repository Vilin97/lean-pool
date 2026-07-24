/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.MatchingNPHard
import Mathlib.Data.Fintype.EquivFin

/-!
  Sundogcert/ThreeDMReindex.lean — MILESTONE 5 of the `3SAT ≤ 3DM` marathon: the GENERIC
  REINDEXING BRIDGE.  (Lean 4 / mathlib v4.30.0.)

  WHAT THIS FILE PROVIDES (pure index bookkeeping — NOT reduction correctness):
    * `threeDMI t` — perfect 3-dimensional matching stated over an ARBITRARY `Fintype` index `I`
      (a selection `T : Finset I` covering each W-, X-, and Y-element exactly once).  This mirrors
      `MatchingNPHard.ThreeDM` verbatim, except the index is a clean `Fintype` rather than `Fin s`.
    * `threeDM_reindex` (THE BRIDGE) — `threeDMI t ↔ ThreeDM (fun i => t (e.symm i))` with
      `e := Fintype.equivFin I : I ≃ Fin (card I)`.  This connects the natural-index matching
      to the real `Fin s`-indexed `MatchingNPHard.ThreeDM` (with `s = Fintype.card I`).  The RHS
      triple-function is EXACTLY the shape `SATReduction.reduce` produces.
    * `threeDM_reindex_comp` — the point-free restatement `threeDMI t ↔ ThreeDM (t ∘ e.symm)`,
      which reads cleanly when `t = SATReduction.tripleFn φ` in m8 (defeq to the above).
    * `map_filter_card_eq` — the load-bearing helper: pushing a `Finset` through an equiv-embedding
      and re-filtering by a transported predicate preserves the filtered cardinality.  Generic over
      an ARBITRARY equiv `e : J ≃ K` and an arbitrary projection — one helper serves BOTH the
      forward direction (`e := equivFin I`) and the reverse (`e := (equivFin I).symm`).

  WHY THIS EXISTS: the heavy forward/reverse gadget counting (milestones 6/7) is far cleaner over a
  structured `Fintype` index `I = SATReduction.TripleIdx n m` (a 4-way `Sum`) than over the opaque
  `Fin (card I)`.  This bridge lets that counting be done over `I` and then transported, for free,
  onto the `Fin s`-indexed `MatchingNPHard.ThreeDM` that the formalized hardness chain consumes.

  THE STANDING LIMIT (named): this module is INDEX BOOKKEEPING ONLY.  It proves that re-indexing a
  triple map along a finite equivalence does not change whether a perfect matching exists — a
  relabeling fact, nothing about the gadgets.  The REDUCTION CORRECTNESS
  (`Satisfiable φ ↔ threeDMI (tripleFn φ)`) — that the wheel + clause + garbage triples actually
  enforce satisfiability — is milestones 6/7, and is NOT touched here.

  Axiom-clean (`decide`/`native_decide` never used).  Expect the standard classical trio.
-/

open Finset
open Sundog.MatchingNPHard

namespace Sundog.ThreeDMReindex

variable {W X Y : Type*}
variable [Fintype W] [Fintype X] [Fintype Y]
variable [DecidableEq W] [DecidableEq X] [DecidableEq Y]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ### The matching predicate over an arbitrary `Fintype` index. -/

/-- **Perfect 3-dimensional matching over an arbitrary `Fintype` index `I`** — a selection
    `T : Finset I` covering each W-element, each X-element, and each Y-element exactly once.
    Mirrors `MatchingNPHard.ThreeDM` exactly, but indexed by `I` rather than `Fin s`. -/
def threeDMI (t : I → W × X × Y) : Prop := ∃ T : Finset I,
    (∀ w : W, (T.filter (fun i => (t i).1   = w)).card = 1) ∧
    (∀ x : X, (T.filter (fun i => (t i).2.1 = x)).card = 1) ∧
    (∀ y : Y, (T.filter (fun i => (t i).2.2 = y)).card = 1)

/-! ### The load-bearing card-preservation helper (generic over an arbitrary equiv). -/

omit [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq W] [DecidableEq X] [DecidableEq Y] in
/-- Pushing a `Finset` through an equiv-embedding and re-filtering by the transported predicate
    preserves the filtered cardinality.  Generic over an arbitrary equiv `e : J ≃ K` and an
    arbitrary projection `proj` — this one helper serves both the forward (`e := equivFin I`) and
    reverse (`e := (equivFin I).symm`) directions of `threeDM_reindex`. -/
theorem map_filter_card_eq {J K : Type*}
    (e : J ≃ K) (T : Finset J)
    {Z : Type*} [DecidableEq Z] (proj : (W × X × Y) → Z)
    (t : J → W × X × Y) (z : Z) :
    ((T.map e.toEmbedding).filter
        (fun i => proj (t (e.symm i)) = z)).card
      = (T.filter (fun a => proj (t a) = z)).card := by
  rw [Finset.filter_map, Finset.card_map]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro a _
  simp only [Function.comp, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]

/-! ### The reindexing bridge. -/

omit [Fintype W] [Fintype X] [Fintype Y] [DecidableEq I] in
/-- **The reindexing bridge.**  A perfect matching over the arbitrary `Fintype` index `I` exists iff
    one exists for the `Fin (card I)`-reindexed triple map (along `e := Fintype.equivFin I`).  This
    is the bridge from `threeDMI` to the real `Fin s`-indexed `MatchingNPHard.ThreeDM`. -/
theorem threeDM_reindex (t : I → W × X × Y) :
    threeDMI t ↔
      ThreeDM (fun i : Fin (Fintype.card I) => t ((Fintype.equivFin I).symm i)) := by
  set e := Fintype.equivFin I with he
  unfold threeDMI ThreeDM
  constructor
  · rintro ⟨T, hW, hX, hY⟩
    refine ⟨T.map e.toEmbedding, ?_, ?_, ?_⟩
    · intro w
      rw [map_filter_card_eq e T (fun p => p.1) t w]; exact hW w
    · intro x
      rw [map_filter_card_eq e T (fun p => p.2.1) t x]; exact hX x
    · intro y
      rw [map_filter_card_eq e T (fun p => p.2.2) t y]; exact hY y
  · rintro ⟨T, hW, hX, hY⟩
    refine ⟨T.map e.symm.toEmbedding, ?_, ?_, ?_⟩
    · intro w
      have h := map_filter_card_eq e.symm T (fun p => p.1) (fun i => t (e.symm i)) w
      simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at h
      rw [h]; exact hW w
    · intro x
      have h := map_filter_card_eq e.symm T (fun p => p.2.1) (fun i => t (e.symm i)) x
      simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at h
      rw [h]; exact hX x
    · intro y
      have h := map_filter_card_eq e.symm T (fun p => p.2.2) (fun i => t (e.symm i)) y
      simp only [Equiv.symm_symm, Equiv.symm_apply_apply] at h
      rw [h]; exact hY y

omit [Fintype W] [Fintype X] [Fintype Y] [DecidableEq I] in
/-- **Point-free restatement** of the bridge: `threeDMI t ↔ ThreeDM (t ∘ (equivFin I).symm)`.
    Defeq to `threeDM_reindex`; reads cleanly when `t = SATReduction.tripleFn φ` in m8. -/
theorem threeDM_reindex_comp (t : I → W × X × Y) :
    threeDMI t ↔ ThreeDM (t ∘ (Fintype.equivFin I).symm) :=
  threeDM_reindex t


end Sundog.ThreeDMReindex
