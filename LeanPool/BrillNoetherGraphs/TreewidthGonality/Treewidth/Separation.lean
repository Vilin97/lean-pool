/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.TreePath
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.Bramble

/-!
# Separation: Bellenbaum--Diestel's Lemma 1 and Lemma 4, and components

Three independent ingredients of the Seymour--Thomas induction:

* `separates_of_mem_anc` — **Lemma 1** in the shape the proof uses: if `t` lies
  on the tree path from a node holding `a` to the distinguished node `s`, while
  no node holding `b` is below `t`, then every walk from `a` to `b` inside `U`
  meets `bag t`.
* `Bramble.isHittingSet_of_separates` — **Lemma 4**: a set separating two covers
  of a bramble covers it.  (One line on paper; the Lean proof has to produce the
  walk inside a member.)
* `awayGraph`, `compOf`, `IsComponent` — the components of `H − X`, kept on the
  ambient vertex type `V` so that no subtype coercion enters the recursion.
  There is deliberately **no** "finset of all components": the gluing induction
  of `SeymourThomasInduction.lean` peels one component off a closed set at a
  time.
-/

@[expose] public section

namespace Utilities.Treewidth

open Finset SimpleGraph

universe u

variable {V : Type u} {H : SimpleGraph V}

/-! ### Lemma 1 -/

/-- **Bellenbaum--Diestel Lemma 1**, in the only shape the duality proof uses.

`na` is a node holding `a` and lying below `t` (that is, `t` is on the tree path
from `na` to `s`); `nb` is a node holding `b` and *not* below `t`.  Then `bag t`
separates `a` from `b` inside `U`.

Note that no `t ≠ s` hypothesis is needed: `s ∈ Anc hT s nb` always, so `h2`
already forces `t ≠ s`.

Discharge plan (the σ-colouring argument of the blueprint §3.4).  For `u ∈ U`
with `u ∉ bag t`, `D.coherent` makes `S u := {n | u ∈ bag n}` connected and it
misses `t`, so `subset_below_or_disjoint` puts it wholly inside `Below` or
wholly outside.  Along an `H`-edge inside `U`, `D.cover_edge` supplies a node in
both `S u` and `S u'`, so the side is the same at both ends; induct along the
walk.  The two endpoints have opposite sides by `h1`/`h2`. -/
theorem separates_of_mem_anc {U : Finset V} (D : PartialDecomposition H U)
    (s t : D.Node) {a b : V} (ha : a ∈ U) (_hb : b ∈ U)
    {na nb : D.Node} (hna : a ∈ D.bag na) (hnb : b ∈ D.bag nb)
    (h1 : t ∈ Anc D.isTree s na) (h2 : t ∉ Anc D.isTree s nb)
    (p : H.Walk a b) (hp : ∀ x ∈ p.support, x ∈ U) :
    ∃ x ∈ p.support, x ∈ D.bag t := by
  classical
  by_contra hcon
  push Not at hcon
  have mono : ∀ u : V, u ∈ U → u ∉ D.bag t → ∀ n : D.Node, u ∈ D.bag n →
      n ∈ Below D.isTree s t → {n : D.Node | u ∈ D.bag n} ⊆ Below D.isTree s t := by
    intro u hu hut n hun hnB
    rcases subset_below_or_disjoint D.isTree (D.coherent u hu) hut with h | h
    · exact h
    · exact absurd hnB (Set.disjoint_left.mp h hun)
  have step : ∀ (x y : V) (q : H.Walk x y), (∀ z ∈ q.support, z ∈ U) →
      (∀ z ∈ q.support, z ∉ D.bag t) →
      ({n : D.Node | x ∈ D.bag n} ⊆ Below D.isTree s t ↔
        {n : D.Node | y ∈ D.bag n} ⊆ Below D.isTree s t) := by
    intro x y q
    induction q with
    | nil => intro _ _; exact Iff.rfl
    | @cons u v w hadj r ih =>
        intro hU hT
        have hmemu : u ∈ (SimpleGraph.Walk.cons hadj r).support :=
          SimpleGraph.Walk.start_mem_support _
        have hmemv : v ∈ (SimpleGraph.Walk.cons hadj r).support :=
          List.mem_cons_of_mem u r.start_mem_support
        have huU : u ∈ U := hU u hmemu
        have hvU : v ∈ U := hU v hmemv
        have hut : u ∉ D.bag t := hT u hmemu
        have hvt : v ∉ D.bag t := hT v hmemv
        obtain ⟨n, hnu, hnv⟩ := D.cover_edge u huU v hvU hadj
        have huv : ({n : D.Node | u ∈ D.bag n} ⊆ Below D.isTree s t ↔
            {n : D.Node | v ∈ D.bag n} ⊆ Below D.isTree s t) := by
          constructor
          · exact fun hpu => mono v hvU hvt n hnv (hpu hnu)
          · exact fun hpv => mono u huU hut n hnu (hpv hnv)
        refine huv.trans (ih (fun z hz => hU z (List.mem_cons_of_mem u hz))
          (fun z hz => hT z (List.mem_cons_of_mem u hz)))
  have hat : a ∉ D.bag t := hcon a p.start_mem_support
  have hPa := mono a ha hat na hna h1
  exact h2 ((step a b p hp hcon).mp hPa hnb)

/-! ### Lemma 4 -/

namespace Bramble

variable [DecidableEq V]

/-- **Bellenbaum--Diestel Lemma 4.**  Any set separating two covers of a bramble
also covers that bramble.

"Separating" is spelled walk-wise, which is the form
`SeymourThomasInduction.lean` produces and the form that avoids introducing a
separator predicate.

Discharge plan: for `M ∈ 𝔅.members`, `hA`/`hB` give `a ∈ M ∩ A` and `b ∈ M ∩ B`;
`𝔅.connected_mem M` gives a walk between them in `H.induce ↑M`, which maps down
to an `H`-walk with support inside `M` (`SimpleGraph.Embedding.induce`); `hsep`
puts a vertex of `S` on it, and that vertex is in `M`. -/
theorem isHittingSet_of_separates (𝔅 : Bramble H) {A B S : Finset V}
    (hA : 𝔅.IsHittingSet A) (hB : 𝔅.IsHittingSet B)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ∀ p : H.Walk a b, ∃ x ∈ p.support, x ∈ S) :
    𝔅.IsHittingSet S := by
  classical
  intro M hM
  obtain ⟨a, ha⟩ := hA M hM
  obtain ⟨b, hb⟩ := hB M hM
  have haM : a ∈ M := (Finset.mem_inter.mp ha).1
  have haA : a ∈ A := (Finset.mem_inter.mp ha).2
  have hbM : b ∈ M := (Finset.mem_inter.mp hb).1
  have hbB : b ∈ B := (Finset.mem_inter.mp hb).2
  obtain ⟨q⟩ := (𝔅.connected_mem M hM).preconnected
    ⟨a, Finset.mem_coe.mpr haM⟩ ⟨b, Finset.mem_coe.mpr hbM⟩
  have key : ∀ (u v : ↥(↑M : Set V)) (r : (H.induce (↑M : Set V)).Walk u v),
      ∀ x ∈ (r.map (SimpleGraph.Embedding.induce (↑M : Set V)).toHom).support, x ∈ M := by
    intro u v r x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Finset.mem_coe.mp y.2
  obtain ⟨x, hxp, hxS⟩ :=
    hsep a haA b hbB (q.map (SimpleGraph.Embedding.induce (↑M : Set V)).toHom)
  exact ⟨x, Finset.mem_inter.mpr ⟨key _ _ q x hxp, hxS⟩⟩

end Bramble

/-! ### Components of `H − X` -/

/-- `H` with every vertex of `X` isolated.  Its connected components on `V \ X`
are the components of `H − X`, but the construction never leaves the type `V`. -/
def awayGraph (H : SimpleGraph V) (X : Finset V) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∉ X ∧ b ∉ X
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

theorem awayGraph_le (H : SimpleGraph V) (X : Finset V) : awayGraph H X ≤ H :=
  fun _ _ h => h.1

/-- `C` is a **connected component of `H − X`**: nonempty, disjoint from `X`,
inducing a connected subgraph of `H`, and closed under taking `H`-neighbours
outside `X`. -/
structure IsComponent (H : SimpleGraph V) (X C : Finset V) : Prop where
  /-- No vertex of `C` lies in `X`. -/
  notMem : ∀ v ∈ C, v ∉ X
  /-- `C` is nonempty. -/
  nonempty : C.Nonempty
  /-- `C` induces a connected subgraph of `H`. -/
  connected : (H.induce (↑C : Set V)).Connected
  /-- Every `H`-neighbour of a vertex of `C` lies in `C` or in `X`; that is,
  `N(C) ⊆ X`. -/
  closed : ∀ a ∈ C, ∀ b, H.Adj a b → b ∉ X → b ∈ C

/-- The component of `v` inside a set `R`.  `R` is intended to be closed under
`awayGraph H X`-adjacency, in which case the filter by `R` is vacuous and this
is the full component of `v`. -/
noncomputable def compOf (H : SimpleGraph V) (X R : Finset V) (v : V) : Finset V :=
  @Finset.filter _ (fun w => (awayGraph H X).Reachable v w) (Classical.decPred _) R

theorem mem_compOf_iff (H : SimpleGraph V) (X R : Finset V) (v w : V) :
    w ∈ compOf H X R v ↔ w ∈ R ∧ (awayGraph H X).Reachable v w :=
  @Finset.mem_filter _ (fun w => (awayGraph H X).Reachable v w) (Classical.decPred _) R w

theorem compOf_subset (H : SimpleGraph V) (X R : Finset V) (v : V) :
    compOf H X R v ⊆ R := fun _ hw => ((mem_compOf_iff H X R v _).mp hw).1

theorem mem_compOf_self {H : SimpleGraph V} {X R : Finset V} {v : V} (hv : v ∈ R) :
    v ∈ compOf H X R v :=
  (mem_compOf_iff H X R v v).mpr ⟨hv, SimpleGraph.Reachable.refl v⟩

/-- A set of vertices outside `X` closed under `awayGraph`-adjacency. -/
def IsClosedAway (H : SimpleGraph V) (X R : Finset V) : Prop :=
  (∀ v ∈ R, v ∉ X) ∧ ∀ a ∈ R, ∀ b, (awayGraph H X).Adj a b → b ∈ R

/-- Inside a closed set, `compOf` really is a component.

Discharge plan: `notMem` from `IsClosedAway.1` and `compOf_subset`; `nonempty`
from `mem_compOf_self`; `closed` because an `H`-edge out of `C` to a vertex
outside `X` is an `awayGraph` edge, so the target is reachable and (by closure of
`R`) in `R`; `connected` by transporting `awayGraph`-walks with
`SimpleGraph.Walk.mapLe (awayGraph_le H X)` and then `SimpleGraph.Walk.induce`,
the support staying inside `C` because reachability is transitive. -/
theorem isComponent_compOf {H : SimpleGraph V} {X R : Finset V}
    (hR : IsClosedAway H X R) {v : V} (hv : v ∈ R) :
    IsComponent H X (compOf H X R v) := by
  classical
  have hreach : ∀ (x y : V) (q : (awayGraph H X).Walk x y), x ∈ R → y ∈ R := by
    intro x y q
    induction q with
    | nil => exact id
    | @cons c d e hadj r ih => exact fun hc => ih (hR.2 c hc d hadj)
  have hmemC : ∀ w : V, w ∈ compOf H X R v ↔ (awayGraph H X).Reachable v w := by
    intro w
    rw [mem_compOf_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.elim fun q => hreach v w q hv, h⟩⟩
  refine ⟨fun w hw => hR.1 w (compOf_subset H X R v hw), ⟨v, mem_compOf_self hv⟩, ?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨v, Finset.mem_coe.mpr (mem_compOf_self hv)⟩, ?_⟩
    rintro ⟨w, hw⟩
    obtain ⟨q⟩ := (hmemC w).mp (Finset.mem_coe.mp hw)
    have hsupp : ∀ x ∈ (q.mapLe (awayGraph_le H X)).support,
        x ∈ (↑(compOf H X R v) : Set V) := by
      intro x hx
      rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
      exact Finset.mem_coe.mpr ((hmemC x).mpr ⟨q.takeUntil x hx⟩)
    exact ⟨SimpleGraph.Walk.induce _ (q.mapLe (awayGraph_le H X)) hsupp⟩
  · intro a haC b hadj hbX
    have haX : a ∉ X := hR.1 a (compOf_subset H X R v haC)
    have hway : (awayGraph H X).Adj a b := ⟨hadj, haX, hbX⟩
    exact (hmemC b).mpr (((hmemC a).mp haC).trans hway.reachable)

/-- Removing a component from a closed set leaves a closed set. -/
theorem isClosedAway_sdiff [DecidableEq V] {H : SimpleGraph V} {X R : Finset V}
    (hR : IsClosedAway H X R) (v : V) :
    IsClosedAway H X (R \ compOf H X R v) := by
  refine ⟨fun w hw => hR.1 w (Finset.mem_sdiff.mp hw).1, ?_⟩
  intro a ha b hab
  have ha' := Finset.mem_sdiff.mp ha
  refine Finset.mem_sdiff.mpr ⟨hR.2 a ha'.1 b hab, ?_⟩
  intro hb
  exact ha'.2 ((mem_compOf_iff H X R v a).mpr
    ⟨ha'.1, ((mem_compOf_iff H X R v b).mp hb).2.trans hab.symm.reachable⟩)

/-- A component is nonempty, so removing it strictly shrinks the set. -/
theorem card_sdiff_compOf_lt [DecidableEq V] {H : SimpleGraph V} {X R : Finset V}
    {v : V} (hv : v ∈ R) :
    (R \ compOf H X R v).card < R.card := by
  refine Finset.card_lt_card ⟨Finset.sdiff_subset, fun hcon => ?_⟩
  exact (Finset.mem_sdiff.mp (hcon hv)).2 (mem_compOf_self hv)

end Utilities.Treewidth
