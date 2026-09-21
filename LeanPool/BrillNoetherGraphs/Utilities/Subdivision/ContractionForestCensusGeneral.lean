/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotential
import Mathlib.Tactic

/-!
# Equal-genus contractions of an arbitrary `n`-vertex, `p`-slot core

`Certificate/ContractionForestCensus.lean` builds the union-find census
machinery (`compFold`, `compFold_iff`, `IsForest`, `IsLoopy`) for the one fixed
shape `ExplicitPotential.Core 8 12`, the shape of every genus-five AR row core.
This file lifts the *same* machinery, verbatim in argument, to an arbitrary
`ExplicitPotential.Core n p`, so that a row of any shape — not just the two
eight-vertex, twelve-slot rows 11/15 — can use the census, and so that
`Certificate/DegenerateSpecCensus.lean` can turn a forest into the `DegSpec`
face datum (`rep`, `rep_idem`, `rep_zero`, `rep_loopless`, `forest`) generically.

Nothing in `ContractionForestCensus.lean` is modified; that file, and
`Generated/GenusFiveARRow1115ContractionCensus.lean`, keep working untouched.
`§4` below checks — cheaply, by `rfl` — that specializing this file's
definitions at `n = 8, p = 12` recovers the *fixed-shape* file's definitions
exactly, so row 11/15's already-landed 2656/2686-target census is literally an
instance of this one, not a parallel development.

## Two additions beyond a straight generalization

The fixed-shape file stops at `compFold`/`IsForest`/`IsLoopy`: enough to
classify contraction targets, but not enough to *emit* a `DegSpec` face datum.
Two more facts are needed for that (`DegenerateSpecCensus.lean` consumes both):

* **`compFold` is idempotent** (`compFold_idem`): the union-find fold, folded
  again through itself, is a no-op. This is what makes `compFold core F`
  usable as `DegSpec.rep` directly — `DegSpec.rep_idem` is exactly this fact.
  Proved by induction on the edge list, carrying idempotence of the
  accumulator as the loop invariant (`unionStep_idem`); no `decide`, no
  per-shape work.
* **A contracted edge really does identify its endpoints**
  (`compFold_tail_eq_head_of_mem`) and **`compFold` reaches every vertex from
  itself along `F`** (`reachIn_self_compFold`): together with
  `compFold_iff`, the second is what lets `DegenerateSpecCensus.lean` produce
  the `ZeroReach` witness the interpolated layer needs, straight from the
  spanning-forest structure that already defines `rep` — no separate search.
-/

namespace Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate

open Utilities

open ExplicitPotential

variable {n p : ℕ} (core : ExplicitPotential.Core n p)

/-! ## Direct adjacency along an explicit list of edge slots -/

/-- `u` and `v` are joined by one edge slot drawn from the list `l` (in
either reading direction). -/
def AdjInList (l : List (Fin p)) (u v : Fin n) : Prop :=
  ∃ e ∈ l, (core.tail e = u ∧ core.head e = v) ∨ (core.head e = u ∧ core.tail e = v)

instance decidableAdjInList (l : List (Fin p)) (u v : Fin n) :
    Decidable (AdjInList core l u v) := by
  unfold AdjInList; infer_instance

theorem AdjInList.symm {l : List (Fin p)} {u v : Fin n}
    (h : AdjInList core l u v) : AdjInList core l v u := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨e, he, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

theorem adjInList_symmetric (l : List (Fin p)) :
    ∀ ⦃u v⦄, AdjInList core l u v → AdjInList core l v u :=
  fun _ _ h => h.symm (core := core)

/-- v4.33 note: `Relation.ReflTransGen.symmetric` is now a deprecated alias for the
*instance* `Relation.ReflTransGen.stdSymm`, which takes its hypothesis as a
type-class argument `[Std.Symm r]` rather than as an explicit `Symmetric r` term
(`Std.Symm` is a genuine structure/class with field `symm`, not the old `Prop`
abbreviation), so the old `Relation.ReflTransGen.symmetric hr` call pattern no
longer elaborates. Proved directly by induction instead of bridging through the
new class. -/
private theorem symmetric_reflTransGen {r : Fin n → Fin n → Prop}
    (hr : ∀ ⦃x y⦄, r x y → r y x) :
    ∀ ⦃x y⦄, Relation.ReflTransGen r x y → Relation.ReflTransGen r y x := by
  intro x y h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact (Relation.ReflTransGen.single (hr hbc)).trans ih

/-- One new edge appended at the end joins the list's adjacency relation with
one literal pair. -/
theorem adjInList_snoc (l : List (Fin p)) (e : Fin p) (x y : Fin n) :
    AdjInList core (l ++ [e]) x y ↔
      AdjInList core l x y ∨ (x = core.tail e ∧ y = core.head e) ∨
        (x = core.head e ∧ y = core.tail e) := by
  unfold AdjInList
  constructor
  · rintro ⟨e', he', h⟩
    rcases List.mem_append.mp he' with he' | he'
    · exact Or.inl ⟨e', he', h⟩
    · rw [List.mem_singleton] at he'
      subst he'
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)
      · exact Or.inr (Or.inr ⟨h1.symm, h2.symm⟩)
  · rintro (⟨e', he', h⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨e', List.mem_append_left _ he', h⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), Or.inr ⟨h1.symm, h2.symm⟩⟩

/-- The reachability relation generated by a list of edge slots: the
reflexive-transitive closure of direct adjacency. Symmetric because
`AdjInList` already is. -/
def ReachInList (l : List (Fin p)) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (AdjInList core l)

theorem reachInList_symmetric (l : List (Fin p)) :
    ∀ ⦃u v⦄, ReachInList core l u v → ReachInList core l v u :=
  symmetric_reflTransGen (adjInList_symmetric core l)

theorem reachInList_equivalence (l : List (Fin p)) :
    Equivalence (ReachInList core l) where
  refl _ := Relation.ReflTransGen.refl
  symm h := reachInList_symmetric core l h
  trans h1 h2 := Relation.ReflTransGen.trans h1 h2

/-! ## Merging one related pair into an equivalence relation -/

/-- `R` extended by declaring `u` and `v` related (and closing under the
equivalence-relation axioms already available from `R`). -/
def mergePair (R : Fin n → Fin n → Prop) (u v x y : Fin n) : Prop :=
  R x y ∨ (R x u ∧ R y v) ∨ (R x v ∧ R y u)

theorem mergePair_equivalence {R : Fin n → Fin n → Prop} (hR : Equivalence R) (u v : Fin n) :
    Equivalence (mergePair R u v) where
  refl x := Or.inl (hR.refl x)
  symm {x y} h := by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hR.symm h)
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  trans {x y z} hxy hyz := by
    rcases hxy with hxy | ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩ <;>
      rcases hyz with hyz | ⟨hyu2, hzv⟩ | ⟨hyv2, hzu⟩
    · exact Or.inl (hR.trans hxy hyz)
    · exact Or.inr (Or.inl ⟨hR.trans hxy hyu2, hzv⟩)
    · exact Or.inr (Or.inr ⟨hR.trans hxy hyv2, hzu⟩)
    · exact Or.inr (Or.inl ⟨hxu, hR.symm (hR.trans (hR.symm hyv) hyz)⟩)
    · exact Or.inl (hR.trans (hR.trans hxu (hR.symm (hR.trans (hR.symm hyv) hyu2))) (hR.symm hzv))
    · exact Or.inl (hR.trans hxu (hR.symm hzu))
    · exact Or.inr (Or.inr ⟨hxv, hR.symm (hR.trans (hR.symm hyu) hyz)⟩)
    · exact Or.inl (hR.trans hxv (hR.symm hzv))
    · exact Or.inr (Or.inr ⟨hxv, hzu⟩)

/-! ## Reflexive-transitive closure of a one-pair extension -/

private def joinPair (r : Fin n → Fin n → Prop) (p' q x y : Fin n) : Prop :=
  r x y ∨ (x = p' ∧ y = q) ∨ (x = q ∧ y = p')

private theorem reflTransGen_joinPair_closure {r : Fin n → Fin n → Prop} (p' q x y : Fin n) :
    Relation.ReflTransGen (joinPair r p' q) x y ↔
      Relation.ReflTransGen (joinPair (Relation.ReflTransGen r) p' q) x y := by
  constructor
  · -- v4.33 note: `Relation.ReflTransGen.mono` now concludes `≤` between whole
    -- relations (`r ≤ p → ReflTransGen r ≤ ReflTransGen p`) rather than being
    -- auto-bound at implicit points, so it must be applied to the two explicit
    -- points (`x y`) before it can be used as an implication.
    exact Relation.ReflTransGen.mono
      (fun a b hab => hab.imp Relation.ReflTransGen.single id) x y
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
        refine ih.trans ?_
        rcases hbc with hbc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Relation.ReflTransGen.mono (fun a b h => Or.inl h) b c hbc
        · exact Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · exact Relation.ReflTransGen.single (Or.inr (Or.inr ⟨rfl, rfl⟩))

private theorem reflTransGen_joinPair {R : Fin n → Fin n → Prop} (hEquiv : Equivalence R)
    (p' q x y : Fin n) :
    Relation.ReflTransGen (joinPair R p' q) x y ↔ mergePair R p' q x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (hEquiv.refl _)
    | @tail b c _ hbc ih =>
        rcases ih with ih | ⟨ihp, ihq⟩ | ⟨ihq, ihp⟩ <;>
          rcases hbc with hbc | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (hEquiv.trans ih hbc)
        · exact Or.inr (Or.inl ⟨ih, hEquiv.refl _⟩)
        · exact Or.inr (Or.inr ⟨ih, hEquiv.refl _⟩)
        · exact Or.inr (Or.inl ⟨ihp, hEquiv.trans (hEquiv.symm hbc) ihq⟩)
        · exact Or.inl (hEquiv.trans ihp ihq)
        · exact Or.inl ihp
        · exact Or.inr (Or.inr ⟨ihq, hEquiv.trans (hEquiv.symm hbc) ihp⟩)
        · exact Or.inl ihq
        · exact Or.inr (Or.inr ⟨ihq, hEquiv.refl _⟩)
  · rintro (h | ⟨hxp, hyq⟩ | ⟨hxq, hyp⟩)
    · exact Relation.ReflTransGen.single (Or.inl h)
    · have h1 : Relation.ReflTransGen (joinPair R p' q) x p' :=
        Relation.ReflTransGen.mono (fun a b hab => Or.inl hab) x p'
          (Relation.ReflTransGen.single hxp)
      have h2 : Relation.ReflTransGen (joinPair R p' q) p' q :=
        Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have h3 : Relation.ReflTransGen (joinPair R p' q) q y :=
        Relation.ReflTransGen.mono (fun a b hab => Or.inl hab) q y
          (Relation.ReflTransGen.single (hEquiv.symm hyq))
      exact h1.trans (h2.trans h3)
    · have h1 : Relation.ReflTransGen (joinPair R p' q) x q :=
        Relation.ReflTransGen.mono (fun a b hab => Or.inl hab) x q
          (Relation.ReflTransGen.single hxq)
      have h2 : Relation.ReflTransGen (joinPair R p' q) q p' :=
        Relation.ReflTransGen.single (Or.inr (Or.inr ⟨rfl, rfl⟩))
      have h3 : Relation.ReflTransGen (joinPair R p' q) p' y :=
        Relation.ReflTransGen.mono (fun a b hab => Or.inl hab) p' y
          (Relation.ReflTransGen.single (hEquiv.symm hyp))
      exact h1.trans (h2.trans h3)

private theorem reflTransGen_joinPair_general {r : Fin n → Fin n → Prop}
    (hr : ∀ ⦃x y⦄, r x y → r y x)
    (p' q x y : Fin n) :
    Relation.ReflTransGen (joinPair r p' q) x y ↔
      mergePair (Relation.ReflTransGen r) p' q x y := by
  rw [reflTransGen_joinPair_closure]
  exact reflTransGen_joinPair
    ⟨fun _ => Relation.ReflTransGen.refl, fun h => symmetric_reflTransGen hr h,
      fun h1 h2 => Relation.ReflTransGen.trans h1 h2⟩ p' q x y

theorem reachInList_snoc (l : List (Fin p)) (e : Fin p) (x y : Fin n) :
    ReachInList core (l ++ [e]) x y ↔
      mergePair (ReachInList core l) (core.tail e) (core.head e) x y := by
  have hpt : ∀ a b, AdjInList core (l ++ [e]) a b ↔
      joinPair (AdjInList core l) (core.tail e) (core.head e) a b :=
    adjInList_snoc core l e
  have hrel : (AdjInList core (l ++ [e])) =
      joinPair (AdjInList core l) (core.tail e) (core.head e) := by
    funext a b; exact propext (hpt a b)
  unfold ReachInList
  rw [hrel]
  exact reflTransGen_joinPair_general (adjInList_symmetric core l) (core.tail e) (core.head e) x y

/-! ## `unionStep` matches `mergePair` exactly -/

/-- Merge the `rep`-class of `u` into the `rep`-class of `v`. See
`ContractionForestCensus.unionStep`'s docstring for the sharing discipline
this `let`-binding shape enforces. -/
def unionStep (rep : Fin n → Fin n) (u v : Fin n) : Fin n → Fin n :=
  let ru := rep u
  let rv := rep v
  fun x => if rep x = ru then rv else rep x

theorem unionStep_iff {rep : Fin n → Fin n} {R : Fin n → Fin n → Prop}
    (hIff : ∀ a b, rep a = rep b ↔ R a b) (hR : Equivalence R) (u v x y : Fin n) :
    unionStep rep u v x = unionStep rep u v y ↔ mergePair R u v x y := by
  unfold unionStep mergePair
  by_cases hx : rep x = rep u <;> by_cases hy : rep y = rep u
  · have hxu : R x u := (hIff x u).mp hx
    have hyu : R y u := (hIff y u).mp hy
    rw [if_pos hx, if_pos hy]
    exact iff_of_true rfl (Or.inl (hR.trans hxu (hR.symm hyu)))
  · have hxu : R x u := (hIff x u).mp hx
    have hnyu : ¬ R y u := fun h => hy ((hIff y u).mpr h)
    rw [if_pos hx, if_neg hy, hIff]
    constructor
    · intro hvy; exact Or.inr (Or.inl ⟨hxu, hR.symm hvy⟩)
    · rintro (hxy | ⟨_, hyv⟩ | ⟨_, hyu⟩)
      · exact absurd (hR.symm (hR.trans (hR.symm hxu) hxy)) hnyu
      · exact hR.symm hyv
      · exact absurd hyu hnyu
  · have hyu : R y u := (hIff y u).mp hy
    have hnxu : ¬ R x u := fun h => hx ((hIff x u).mpr h)
    rw [if_neg hx, if_pos hy, hIff]
    constructor
    · intro hxv; exact Or.inr (Or.inr ⟨hxv, hyu⟩)
    · rintro (hxy | ⟨hxu, _⟩ | ⟨hxv, _⟩)
      · exact absurd (hR.trans hxy hyu) hnxu
      · exact absurd hxu hnxu
      · exact hxv
  · have hnxu : ¬ R x u := fun h => hx ((hIff x u).mpr h)
    have hnyu : ¬ R y u := fun h => hy ((hIff y u).mpr h)
    rw [if_neg hx, if_neg hy, hIff]
    constructor
    · intro hxy; exact Or.inl hxy
    · rintro (hxy | ⟨hxu, _⟩ | ⟨_, hyu⟩)
      · exact hxy
      · exact absurd hxu hnxu
      · exact absurd hyu hnyu

/-- **New.** `unionStep` preserves idempotence of the accumulator: if `rep` is
already a retraction onto its own fixed points, so is `unionStep rep u v`.
This is the loop invariant `foldRep_idem` inducts on. -/
theorem unionStep_idem {rep : Fin n → Fin n} (hidem : ∀ x, rep (rep x) = rep x)
    (u v x : Fin n) :
    unionStep rep u v (unionStep rep u v x) = unionStep rep u v x := by
  show (if rep (unionStep rep u v x) = rep u then rep v else rep (unionStep rep u v x))
      = unionStep rep u v x
  by_cases hx : rep x = rep u
  · have hux : unionStep rep u v x = rep v := by
      show (if rep x = rep u then rep v else rep x) = rep v
      rw [if_pos hx]
    rw [hux]
    have hrv : rep (rep v) = rep v := hidem v
    by_cases hcase : rep v = rep u
    · rw [if_pos (by rw [hrv]; exact hcase)]
    · rw [if_neg (by rw [hrv]; exact hcase)]
      exact hrv
  · have hux : unionStep rep u v x = rep x := by
      show (if rep x = rep u then rep v else rep x) = rep x
      rw [if_neg hx]
    rw [hux]
    have hrx : rep (rep x) = rep x := hidem x
    rw [if_neg (by rw [hrx]; exact hx)]
    exact hrx

/-- **New.** One `unionStep` merges at most two classes, so it destroys at
most one element of the image: `image rep ⊆ insert (rep u) (image (unionStep …))`,
because the only vertices whose value changes are those already sent to
`rep u`. This is the inductive heart of the graphic-matroid rank inequality
`card_le_card_image_compFold_add_card`. -/
theorem card_image_le_card_image_unionStep_succ (rep : Fin n → Fin n) (u v : Fin n) :
    (Finset.image rep Finset.univ).card
      ≤ (Finset.image (unionStep rep u v) Finset.univ).card + 1 := by
  have hsub : Finset.image rep Finset.univ ⊆
      insert (rep u) (Finset.image (unionStep rep u v) Finset.univ) := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    by_cases hx : rep x = rep u
    · exact Finset.mem_insert.mpr (Or.inl hx)
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, ?_⟩))
      show (if rep x = rep u then rep v else rep x) = rep x
      rw [if_neg hx]
  calc (Finset.image rep Finset.univ).card
      ≤ (insert (rep u) (Finset.image (unionStep rep u v) Finset.univ)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.image (unionStep rep u v) Finset.univ).card + 1 := Finset.card_insert_le _ _

/-! ## Folding over a list of edges: union-find, and its correctness -/

/-- Union-find over a list of edge slots, applied in order. -/
def foldRep (l : List (Fin p)) : Fin n → Fin n :=
  l.foldl (fun rep e => unionStep rep (core.tail e) (core.head e)) id

theorem foldRep_nil : foldRep core [] = id := rfl

theorem foldRep_snoc (l : List (Fin p)) (e : Fin p) :
    foldRep core (l ++ [e]) = unionStep (foldRep core l) (core.tail e) (core.head e) := by
  unfold foldRep
  rw [List.foldl_append]
  rfl

/-- **Union-find correctness.** `foldRep`-equality exactly characterizes
reachability via the processed edge list. -/
theorem foldRep_iff (l : List (Fin p)) : ∀ x y : Fin n,
    foldRep core l x = foldRep core l y ↔ ReachInList core l x y := by
  induction l using List.reverseRecOn with
  | nil =>
      intro x y
      have hFalse : ∀ b, ¬ AdjInList core [] x b := by
        rintro b ⟨e, he, -⟩
        exact List.not_mem_nil he
      unfold ReachInList
      rw [Relation.reflTransGen_iff_eq hFalse]
      show foldRep core [] x = foldRep core [] y ↔ y = x
      rw [foldRep_nil]
      exact eq_comm
  | append_singleton l e ih =>
      intro x y
      rw [foldRep_snoc, reachInList_snoc]
      exact unionStep_iff ih (reachInList_equivalence core l) (core.tail e) (core.head e) x y

/-- **New.** The union-find fold is idempotent: refolding through itself is a
no-op. Proved by induction on the edge list, carrying `unionStep_idem` as the
loop invariant — no `decide`, and independent of `n`/`p`. This is exactly
`DegSpec.rep_idem` once `compFold` is used as `rep`. -/
theorem foldRep_idem (l : List (Fin p)) : ∀ x : Fin n,
    foldRep core l (foldRep core l x) = foldRep core l x := by
  induction l using List.reverseRecOn with
  | nil => intro x; rfl
  | append_singleton l e ih =>
      intro x
      rw [foldRep_snoc]
      exact unionStep_idem ih (core.tail e) (core.head e) x

/-- **New.** The graphic-matroid rank inequality, at list level: folding `k`
edges can cut the number of vertex classes by at most `k`. Induction on the
edge list, with `card_image_le_card_image_unionStep_succ` as the step. -/
theorem card_le_card_image_foldRep_add_length (l : List (Fin p)) :
    n ≤ (Finset.image (foldRep core l) Finset.univ).card + l.length := by
  induction l using List.reverseRecOn with
  | nil =>
      rw [foldRep_nil]
      simp
  | append_singleton l e ih =>
      have h := card_image_le_card_image_unionStep_succ (foldRep core l)
        (core.tail e) (core.head e)
      rw [foldRep_snoc]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-! ## The census-facing interface: a specific contracted edge set `F` -/

/-- The edge slots of the core belonging to a finite set `F`, listed in the
fixed canonical order `0, 1, …, p - 1`. -/
def edgeList (F : Finset (Fin p)) : List (Fin p) :=
  (List.finRange p).filter (fun e => decide (e ∈ F))

theorem mem_edgeList (F : Finset (Fin p)) (e : Fin p) : e ∈ edgeList F ↔ e ∈ F := by
  unfold edgeList
  simp [List.mem_filter, List.mem_finRange]

/-- **New.** `edgeList` lists each slot of `F` exactly once, so its length is
`F.card`. This is what converts the list-level rank inequality into the
`Finset`-level one. -/
theorem length_edgeList (F : Finset (Fin p)) : (edgeList (p := p) F).length = F.card := by
  have hnd : (edgeList (p := p) F).Nodup := (List.nodup_finRange p).filter _
  have hto : (edgeList (p := p) F).toFinset = F := by
    ext e
    simp [List.mem_toFinset, mem_edgeList]
  have hcard := List.toFinset_card_of_nodup hnd
  rw [hto] at hcard
  exact hcard.symm

/-- The vertex partition induced by contracting the edge set `F`: each
vertex's canonical representative under the union-find fold. -/
def compFold (F : Finset (Fin p)) : Fin n → Fin n := foldRep core (edgeList F)

@[simp] theorem compFold_empty : compFold core ∅ = id := by
  simp [compFold, edgeList, foldRep]

/-- The reachability relation actually induced by contracting `F`. -/
def ReachIn (F : Finset (Fin p)) : Fin n → Fin n → Prop := ReachInList core (edgeList F)

theorem reachIn_equivalence (F : Finset (Fin p)) : Equivalence (ReachIn core F) :=
  reachInList_equivalence core (edgeList F)

/-- **The main correctness theorem.** `compFold`-equality exactly
characterizes vertex reachability through the contracted edge set `F`. -/
theorem compFold_iff (F : Finset (Fin p)) (x y : Fin n) :
    compFold core F x = compFold core F y ↔ ReachIn core F x y :=
  foldRep_iff core (edgeList F) x y

instance decidableReachIn (F : Finset (Fin p)) : DecidableRel (ReachIn core F) :=
  fun x y => decidable_of_iff _ (compFold_iff core F x y)

/-- **New.** `compFold` is idempotent: refolding a class through `compFold`
again does nothing. This is exactly `DegSpec.rep_idem`. -/
theorem compFold_idem (F : Finset (Fin p)) (x : Fin n) :
    compFold core F (compFold core F x) = compFold core F x :=
  foldRep_idem core (edgeList F) x

/-- **New.** A contracted edge's two endpoints land in the same class: this
is exactly `DegSpec.rep_zero` for `e ∈ F`. -/
theorem compFold_tail_eq_head_of_mem {F : Finset (Fin p)} {e : Fin p} (he : e ∈ F) :
    compFold core F (core.tail e) = compFold core F (core.head e) :=
  (compFold_iff core F (core.tail e) (core.head e)).mpr
    (Relation.ReflTransGen.single ⟨e, (mem_edgeList F e).mpr he, Or.inl ⟨rfl, rfl⟩⟩)

/-- **New.** Every vertex reaches its own `compFold` representative through
`F` — trivial from idempotence, but this is precisely the fact
`DegenerateSpecCensus.lean` transports into a `ZeroReach` witness. -/
theorem reachIn_self_compFold (F : Finset (Fin p)) (v : Fin n) :
    ReachIn core F v (compFold core F v) :=
  (compFold_iff core F v (compFold core F v)).mp (compFold_idem core F v).symm

/-! ## Genus preservation: the graphic-matroid rank equation -/

/-- `F` is a *forest* of the core: contracting it is an equal-genus
topological contraction. -/
def IsForest (F : Finset (Fin p)) : Prop :=
  F.card = n - (Finset.image (compFold core F) Finset.univ).card

instance decidableIsForest (F : Finset (Fin p)) : Decidable (IsForest core F) := by
  unfold IsForest; infer_instance

/-- The image of `compFold core F` has at most `n` elements — trivial, but
what `forest_image_add_card_eq` needs to turn the truncated-subtraction
`IsForest` equation into the additive `DegSpec.forest` equation. -/
theorem card_image_compFold_le (F : Finset (Fin p)) :
    (Finset.image (compFold core F) Finset.univ).card ≤ n := by
  calc (Finset.image (compFold core F) Finset.univ).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- **New. The graphic-matroid rank inequality.** Contracting `F` cuts the
number of vertex classes by at most `F.card`, for *every* slot set `F` — each
contracted slot merges at most two classes. `IsForest core F` is precisely the
equality case (see `forest_image_add_card_eq`), so this is the inequality whose
saturation "contracting `F` preserves the genus" means.

Consequence used by the split-loop analysis: a slot set carrying a cycle
cannot be a forest, because deleting a redundant slot from it leaves the
partition — hence the image cardinality — unchanged while dropping `F.card`
by one, which would violate this bound. -/
theorem card_le_card_image_compFold_add_card (F : Finset (Fin p)) :
    n ≤ (Finset.image (compFold core F) Finset.univ).card + F.card := by
  have h := card_le_card_image_foldRep_add_length core (edgeList F)
  rwa [length_edgeList F] at h

/-- **New.** Two idempotent representative maps with the *same fibres* have
images of the same size; only the `≤` direction is stated, since the converse
is the same lemma with the arguments swapped. The injection is `r₂` itself:
idempotence of `r₁` makes `r₂ (r₁ x) = r₂ x`, so `r₂` separates distinct
`r₁`-classes. Used to compare `compFold core F` with `compFold core F'` when
`F` and `F'` induce the same reachability relation. -/
theorem card_image_le_of_rep_iff {m : ℕ} {r₁ r₂ : Fin m → Fin m}
    (h₁ : ∀ x, r₁ (r₁ x) = r₁ x) (hiff : ∀ x y, r₁ x = r₁ y ↔ r₂ x = r₂ y) :
    (Finset.image r₁ Finset.univ).card ≤ (Finset.image r₂ Finset.univ).card := by
  refine Finset.card_le_card_of_injOn r₂
    (fun a _ => Finset.mem_image_of_mem r₂ (Finset.mem_univ a)) ?_
  intro a ha b hb hab
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
  have hx : r₂ (r₁ x) = r₂ x := (hiff (r₁ x) x).mp (h₁ x)
  have hy : r₂ (r₁ y) = r₂ y := (hiff (r₁ y) y).mp (h₁ y)
  exact (hiff x y).mpr (by rw [← hx, ← hy]; exact hab)

/-- **New.** `IsForest`, stated additively: exactly the `DegSpec.forest`
field, once `rep := compFold core F` and `F` is the zero-length slot set. -/
theorem forest_image_add_card_eq {F : Finset (Fin p)} (hForest : IsForest core F) :
    (Finset.univ.image (compFold core F)).card + F.card = n := by
  have hle := card_image_compFold_le core F
  unfold IsForest at hForest
  omega

/-- Every forest of an `n`-vertex graph has at most `n - 1` edges: the
vertex-partition image is nonempty (given `n > 0`), so `n - image.card ≤ n - 1`. -/
theorem forest_card_lt {F : Finset (Fin p)} (hn : 0 < n) (h : IsForest core F) :
    F.card ≤ n - 1 := by
  unfold IsForest at h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Finset.image (compFold core F) Finset.univ).Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  have hpos : 0 < (Finset.image (compFold core F) Finset.univ).card := hne.card_pos
  omega

/-- `F` leaves a semantic loop: some uncontracted edge slot has both
endpoints identified by the contraction. Exactly the negation of
`core_loopless`/`rep_loopless` for the contraction target. -/
def IsLoopy (F : Finset (Fin p)) : Prop :=
  let g := compFold core F
  ∃ e : Fin p, e ∉ F ∧ g (core.tail e) = g (core.head e)

instance decidableIsLoopy (F : Finset (Fin p)) : Decidable (IsLoopy core F) := by
  unfold IsLoopy; infer_instance

/-- **New.** The `rep_loopless` reading of `¬ IsLoopy`, stated pointwise: a
surviving slot (`e ∉ F`) is not a loop after contracting `F`. -/
theorem rep_loopless_of_not_isLoopy {F : Finset (Fin p)} (hNotLoopy : ¬ IsLoopy core F) :
    ∀ e : Fin p, e ∉ F → compFold core F (core.tail e) ≠ compFold core F (core.head e) :=
  fun e he heq => hNotLoopy ⟨e, he, heq⟩

end Utilities.Certificate.ContractionForestCensusGeneral
