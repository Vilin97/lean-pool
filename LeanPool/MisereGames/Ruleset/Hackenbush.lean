/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.GameGraph
public import LeanPool.MisereGames.Misere.Stride
public import LeanPool.MisereGames.Mathlib.SimpleGraph
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum
import Mathlib.Order.RelClasses

/-!
Misere combinatorial games.
-/

namespace MisereGames

/-!
# Hackenbush

Hackenbush is played on a connected graph with a designated "ground" vertex.
All edges are coloured either Left (bLue) or Right (Red). On their turn, a
player removes one of their coloured edges. The resulting position is the
connected component containing the ground vertex.
-/

attribute [local instance] Classical.propDecidable

public noncomputable section

open Form
open GameForm

variable {V : Type}

/-- A Hackenbush position on a finite supported graph with a ground vertex. -/
structure Hackenbush (V : Type) where
  /-- The underlying graph. -/
  graph : SimpleGraph V
  /-- The ground vertex. -/
  ground : V
  /--
  Edge colouring: assigns a colour/player (Left or Right) to each pair of
  vertices.
  -/
  coloring : Sym2 V → Player
  /-- Every vertex incident to an edge is reachable from the ground vertex. -/
  connected : ∀ v ∈ graph.support, graph.Reachable v ground
  /-- A finset witnessing the finiteness of the graph's support. -/
  supportFinset : Finset V
  /-- The supportFinset coerces to exactly the graph's support. -/
  supportFinset_coe : ↑supportFinset = graph.support

namespace Hackenbush

/--
The edge set of a Hackenbush position is finite.
-/
theorem edgeSetFinite (hack : Hackenbush V) : hack.graph.edgeSet.Finite :=
  SimpleGraph.edgeSet_finite_of_support_finite
    (hack.supportFinset_coe ▸ hack.supportFinset.finite_toSet)

/--
The edge finset of a Hackenbush position's graph, derived from support finiteness.
-/
def edgeFinset (hack : Hackenbush V) : Finset (Sym2 V) :=
  hack.edgeSetFinite.toFinset

@[simp]
theorem mem_edgeFinset {hack : Hackenbush V} {e : Sym2 V} :
    e ∈ hack.edgeFinset ↔ e ∈ hack.graph.edgeSet :=
  Set.Finite.mem_toFinset _

/--
The number of edges in a Hackenbush position.
-/
def edgeCard (hack : Hackenbush V) : ℕ := hack.edgeFinset.card

/-!
### Ground component
-/

/--
The ground component after removing an edge: the subgraph of `G.deleteEdges
{e}` restricted to vertices reachable from the ground vertex. An edge `{u, v}`
is kept iff it was in `G`, it is not the removed edge, and both `u` and `v` are
still reachable from `ground`.
-/
def groundComp (graph : SimpleGraph V) (ground : V) (e : Sym2 V) : SimpleGraph V where
  Adj u v := (graph.deleteEdges {e}).Adj u v ∧
    (graph.deleteEdges {e}).Reachable u ground ∧
    (graph.deleteEdges {e}).Reachable v ground
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := (graph.deleteEdges {e}).loopless.irrefl v h.1

theorem groundComp_adj_iff {graph : SimpleGraph V} {ground : V} {e : Sym2 V} {u v : V} :
    (groundComp graph ground e).Adj u v ↔
    (graph.deleteEdges {e}).Adj u v ∧
    (graph.deleteEdges {e}).Reachable u ground ∧
    (graph.deleteEdges {e}).Reachable v ground := Iff.rfl

theorem groundComp_le (graph : SimpleGraph V) (ground : V) (e : Sym2 V) :
    groundComp graph ground e ≤ graph := by
  intro u v h
  exact SimpleGraph.deleteEdges_le (s := ({e} : Set (Sym2 V))) h.1

theorem groundComp_edgeSet_subset (graph : SimpleGraph V) (ground : V) (e : Sym2 V) :
    (groundComp graph ground e).edgeSet ⊆ graph.edgeSet :=
  SimpleGraph.edgeSet_mono (groundComp_le graph ground e)

theorem groundComp_edgeSet_ssubset {graph : SimpleGraph V} {ground : V}
    {e : Sym2 V} (he : e ∈ graph.edgeSet) :
    (groundComp graph ground e).edgeSet ⊂ graph.edgeSet := by
  constructor
  · exact groundComp_edgeSet_subset graph ground e
  · intro h
    have hmem := h he
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at hmem
      exact (SimpleGraph.deleteEdges_adj.mp hmem.1).2 (Set.mem_singleton _)

/--
The support of a ground component is a subset of the original graph's support.
-/
theorem groundComp_support_subset (graph : SimpleGraph V) (ground : V) (e : Sym2 V) :
    (groundComp graph ground e).support ⊆ graph.support := by
  intro v hv
  rw [SimpleGraph.mem_support] at hv ⊢
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, groundComp_le graph ground e hw⟩

/--
Reachability in `G.deleteEdges {e}` from ground implies reachability in the
ground component.
-/
theorem reach_deleteEdges_imp_reach_groundComp {graph : SimpleGraph V} {ground : V} {e : Sym2 V}
    {v : V} (hv : (graph.deleteEdges {e}).Reachable v ground) :
    (groundComp graph ground e).Reachable v ground := by
  rcases hv with ⟨walk⟩
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h walk ih =>
    refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) ih
    rw [groundComp_adj_iff]
    exact
      ⟨h, SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable h)
        (SimpleGraph.Walk.reachable walk), ⟨walk⟩⟩

/--
The ground component is connected.
-/
theorem groundComp_connected (graph : SimpleGraph V) (ground : V) (e : Sym2 V) :
    ∀ v ∈ (groundComp graph ground e).support, (groundComp graph ground e).Reachable v ground := by
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨_, h_adj⟩ := hv
  rw [groundComp_adj_iff] at h_adj
  obtain ⟨_, h_v_g, _⟩ := h_adj
  exact reach_deleteEdges_imp_reach_groundComp h_v_g

/--
Remove an edge from a Hackenbush position and take the ground component.
-/
def remove (hack : Hackenbush V) (e : Sym2 V) : Hackenbush V where
  graph := groundComp hack.graph hack.ground e
  ground := hack.ground
  coloring := hack.coloring
  connected := groundComp_connected hack.graph hack.ground e
  supportFinset := hack.supportFinset.filter
    (fun v => v ∈ (groundComp hack.graph hack.ground e).support)
  supportFinset_coe := by
    ext v
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · exact fun ⟨_, hv⟩ => hv
    · intro hv
      refine ⟨?_, hv⟩
      rw [← Finset.mem_coe, hack.supportFinset_coe]
      exact groundComp_support_subset _ _ _ hv

@[simp]
theorem remove_graph (hack : Hackenbush V) (e : Sym2 V) :
    (hack.remove e).graph = groundComp hack.graph hack.ground e := by rw [remove]

@[simp]
theorem remove_ground (hack : Hackenbush V) (e : Sym2 V) :
    (hack.remove e).ground = hack.ground := by rw [remove]

@[simp]
theorem remove_coloring (hack : Hackenbush V) (e : Sym2 V) :
    (hack.remove e).coloring = hack.coloring := by rw [remove]

/--
Removing an edge strictly decreases the edge count.
-/
theorem edgeCard_remove_lt (hack : Hackenbush V) (e : Sym2 V) (he : e ∈ hack.graph.edgeSet) :
    (hack.remove e).edgeCard < hack.edgeCard := by
  unfold edgeCard edgeFinset
  exact Finset.card_lt_card
    (Set.Finite.toFinset_ssubset_toFinset.mpr (groundComp_edgeSet_ssubset he))

/-!
### Ground edges
-/

/--
The set of p-coloured ground edges (edges incident with the ground vertex).
-/
def groundEdges (hack : Hackenbush V) (p : Player) : Finset (Sym2 V) :=
  hack.edgeFinset.filter fun e => hack.ground ∈ e ∧ hack.coloring e = p

/--
The number of p-coloured edges incident with ground vertex.
-/
def groundCount (hack : Hackenbush V) (p : Player) : ℕ :=
  (hack.groundEdges p).card

/--
A ground edge (other than the removed one) survives in the ground component.
-/
theorem groundEdge_mem_groundComp {graph : SimpleGraph V}
    {ground : V} {e e' : Sym2 V}
    (he' : e' ∈ graph.edgeSet) (hne : e' ≠ e) (hgnd : ground ∈ e')
    (hconn : ∀ v ∈ graph.support, graph.Reachable v ground) :
    e' ∈ (groundComp graph ground e).edgeSet := by
  obtain ⟨u, v, h1, h2, h3 | h3⟩ : ∃ u v, e' = s(u,
    v) ∧ graph.Adj u v ∧ (u = ground ∨ v = ground) := by
    obtain ⟨u, v⟩ := e'
    simp only [SimpleGraph.mem_edgeSet, ne_eq, Sym2.mem_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
               Prod.swap_prod_mk] at he' hne hgnd ⊢
    obtain hgnd | hgnd := hgnd
    · subst hgnd
      use v, ground, Or.inr ⟨rfl, rfl⟩
      exact ⟨he'.symm, Or.inr rfl⟩
    · subst hgnd
      use u, ground, Or.inl ⟨rfl, rfl⟩
      exact ⟨he', Or.inr rfl⟩
  · subst h3
    simp only [h1, ne_eq] at hne
    simp only [groundComp, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, h1,
               SimpleGraph.mem_edgeSet, h2, hne, not_false_eq_true, and_self,
               SimpleGraph.Reachable.rfl, true_and]
    apply SimpleGraph.Reachable.symm
    apply SimpleGraph.Adj.reachable
    subst h1
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, not_false_eq_true, and_self, h2,
      hne]
  · subst h3
    simp only [h1, ne_eq] at hne
    simp only [groundComp, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, h1,
               SimpleGraph.mem_edgeSet, h2, hne, not_false_eq_true, and_self,
               SimpleGraph.Reachable.rfl, true_and, and_true]
    apply SimpleGraph.Adj.reachable
    subst h1
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, not_false_eq_true, and_self, h2,
      hne]

/--
Ground edges of the removed position = ground edges of original minus the
removed edge.
-/
theorem groundEdges_remove_eq (hack : Hackenbush V) (e : Sym2 V)
    (p : Player) :
    (hack.groundEdges p).erase e = (hack.remove e).groundEdges p := by
  ext e'
  simp only [Finset.mem_erase, groundEdges, Finset.mem_filter, mem_edgeFinset,
             remove_graph, remove_ground, remove_coloring]
  constructor
  · intro ⟨hne, he'_mem, hgnd, hcol⟩
    exact ⟨groundEdge_mem_groundComp he'_mem hne hgnd hack.connected, hgnd, hcol⟩
  · intro ⟨he'_gc, hgnd, hcol⟩
    refine ⟨?_, groundComp_edgeSet_subset _ _ _ he'_gc, hgnd, hcol⟩
    intro heq
    rw [heq] at he'_gc
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he'_gc
      exact (SimpleGraph.deleteEdges_adj.mp he'_gc.1).2 (Set.mem_singleton _)

/-!
### Ground count properties under edge removal
-/

/--
Ground count after removing a ground p-edge decreases by 1.
-/
theorem groundCount_remove_ground {hack : Hackenbush V} {e : Sym2 V} {p : Player}
    (he : e ∈ hack.graph.edgeSet) (hg : hack.ground ∈ e) (hc : hack.coloring e = p) :
    (hack.remove e).groundCount p = hack.groundCount p - 1 := by
  unfold groundCount
  rw [← hack.groundEdges_remove_eq e p, Finset.card_erase_of_mem]
  simp only [groundEdges, Finset.mem_filter, mem_edgeFinset]
  exact ⟨he, hg, hc⟩

/--
Ground count is preserved when removing an edge of different colour.
-/
theorem groundCount_remove_neg {hack : Hackenbush V} {e : Sym2 V} {p : Player}
    (hc : hack.coloring e = -p) :
    (hack.remove e).groundCount p = hack.groundCount p := by
  unfold groundCount
  rw [← hack.groundEdges_remove_eq e p, Finset.erase_eq_of_notMem]
  simp only [groundEdges, Finset.mem_filter, mem_edgeFinset, not_and]
  intro _ _ hnc
  exact Player.absurd hnc hc

/--
Ground count is preserved when removing a non-ground edge.
-/
theorem groundCount_remove_non_ground {hack : Hackenbush V} {e : Sym2 V} {p : Player}
    (hng : hack.ground ∉ e) :
    (hack.remove e).groundCount p = hack.groundCount p := by
  unfold groundCount
  rw [← hack.groundEdges_remove_eq e p, Finset.erase_eq_of_notMem]
  simp only [groundEdges, Finset.mem_filter, mem_edgeFinset, not_and]
  intro _ hg
  exact absurd hg hng

/--
Removing a p-coloured edge preserves (-p)-coloured ground count.
-/
theorem groundCount_neg_remove {hack : Hackenbush V} {e : Sym2 V} {p : Player}
    (hc : hack.coloring e = p) :
    (hack.remove e).groundCount (-p) = hack.groundCount (-p) :=
  groundCount_remove_neg (by rw [hc, neg_neg])

/--
For any p-move, the groundCount p of the result is ≥ groundCount p - 1.
-/
theorem groundCount_move {hack : Hackenbush V} {e : Sym2 V} {p : Player}
    (he : e ∈ hack.graph.edgeSet) (hc : hack.coloring e = p) :
    (hack.remove e).groundCount p ≥ hack.groundCount p - 1 := by
  by_cases hg : hack.ground ∈ e
  · simp [groundCount_remove_ground he hg hc]
  · simp [groundCount_remove_non_ground hg]

/-!
### Hackenbush game structure
-/

/--
Moves in Hackenbush: remove an edge of your colour and take the ground
component.
-/
protected def moves (p : Player) (hack : Hackenbush V) : Set (Hackenbush V) :=
  {hack' | ∃ e ∈ hack.graph.edgeSet, hack.coloring e = p ∧ hack' = hack.remove e}

theorem mem_moves_iff {p : Player} {hack hack' : Hackenbush V} :
    hack' ∈ hack.moves p ↔
    ∃ e ∈ hack.graph.edgeSet, hack.coloring e = p ∧ hack' = hack.remove e := Iff.rfl

/-- The game graph whose moves are Hackenbush edge removals. -/
def _root_.GameGraph.hackenbush : GameGraph (Hackenbush V) where
  moves := Hackenbush.moves

private theorem edgeCard_le_of_mem_moves {a b : Hackenbush V} {p : Player}
    (h : a ∈ GameGraph.hackenbush.moves p b) :
    a.edgeCard < b.edgeCard := by
  simp only [GameGraph.hackenbush] at h
  obtain ⟨e, he, _, rfl⟩ := mem_moves_iff.mp h
  exact edgeCard_remove_lt b e he

instance : GameGraph.IsWellFounded (GameGraph.hackenbush (V := V)) :=
  GameGraph.IsWellFounded.of_subrelation
    (InvImage (· < ·) (fun hack : Hackenbush V => hack.edgeCard))
    (fun _ _ _ h => edgeCard_le_of_mem_moves h)

/--
Convert a Hackenbush position to a GameForm.
-/
def toGameForm (hack : Hackenbush V) : GameForm :=
  GameGraph.toForm (g := GameGraph.hackenbush) hack

@[simp]
theorem moves_toGameForm (p : Player) (hack : Hackenbush V) :
    Form.moves p hack.toGameForm = toGameForm '' (hack.moves p) := by
  simp only [toGameForm]
  rw [GameGraph.moves_toForm]
  rfl

theorem mem_moves_toGameForm_iff {p : Player} {hack : Hackenbush V} {g : GameForm} :
    g ∈ Form.moves p hack.toGameForm ↔
    ∃ (e : Sym2 V) (_ : e ∈ hack.graph.edgeSet),
      hack.coloring e = p ∧ g = (hack.remove e).toGameForm := by
  rw [moves_toGameForm]
  constructor
  · rintro ⟨hack', h_hack', rfl⟩
    obtain ⟨e, he, hc, rfl⟩ := mem_moves_iff.mp h_hack'
    exact ⟨e, he, hc, rfl⟩
  · rintro ⟨e, he, hc, rfl⟩
    exact ⟨hack.remove e, mem_moves_iff.mpr ⟨e, he, hc, rfl⟩, rfl⟩

theorem toGameForm_remove_mem_moves {hack : Hackenbush V} {e : Sym2 V}
    (he : e ∈ hack.graph.edgeSet) :
    (hack.remove e).toGameForm ∈ Form.moves (hack.coloring e) hack.toGameForm := by
  rw [mem_moves_toGameForm_iff]
  exact ⟨e, he, rfl, rfl⟩

/--
The game form is zero iff the graph has no edges.
-/
theorem toGameForm_eq_zero_iff {hack : Hackenbush V} :
    hack.toGameForm = 0 ↔ hack.graph = ⊥ := by
  refine ⟨ ?_, ?_ ⟩
  · intro h
    contrapose! h
    obtain ⟨e, he⟩ : ∃ e : Sym2 V, e ∈ hack.graph.edgeSet := by
      refine Set.nonempty_iff_ne_empty.mpr fun h' => h <| ?_
      ext
      simp only [SimpleGraph.edgeSet_eq_empty, h] at h'
    intro h
    have := toGameForm_remove_mem_moves he
    simp only [h, moves_zero, Set.mem_empty_iff_false] at this
  · intro h
    have h_empty_moves : ∀ p : Player, hack.moves p = ∅ := by
      intro p
      ext hack'
      simp only [Hackenbush.moves, h, SimpleGraph.edgeSet_bot,
                 Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false]
    apply GameForm.leftEnd_rightEnd_eq_zero
    · rw [isEnd_def, moves_toGameForm, Set.image_eq_empty]
      exact h_empty_moves .left
    · rw [isEnd_def, moves_toGameForm, Set.image_eq_empty]
      exact h_empty_moves .right

/-!
### Existence of ground edges
-/

/-
If the graph has edges, there is a ground edge.
-/
theorem exists_ground_edge {hack : Hackenbush V} (h_ne : hack.graph ≠ ⊥) :
    ∃ e ∈ hack.graph.edgeSet, hack.ground ∈ e := by
  obtain ⟨v, h1, h2, h3⟩ :
      ∃ w ∈ hack.graph.support, hack.graph.Reachable w hack.ground ∧ w ≠ hack.ground := by
    obtain ⟨v, w, hvw⟩ : ∃ v w, hack.graph.Adj v w := SimpleGraph.ne_bot_iff_exists_adj.mp h_ne
    by_cases h : v = hack.ground
    <;> by_cases h' : w = hack.ground
    <;> simp_all only [ne_eq, SimpleGraph.support, SetRel.mem_dom, Set.mem_setOf_eq,
      SimpleGraph.irrefl]
    · exact ⟨w, ⟨hack.ground, hvw.symm⟩, hvw.symm.reachable, h'⟩
    · exact ⟨v, ⟨hack.ground, hvw⟩, hvw.reachable, h⟩
    · exact ⟨v, ⟨w, hvw ⟩, hack.connected v ⟨w, hvw⟩, h⟩
  apply SimpleGraph.Reachable.elim h2
  exact SimpleGraph.exist_edge_end_walk h3

/-
If position is nonempty and groundCount p = 0, then all ground edges are
(-p)-coloured.
-/
theorem exists_neg_ground_edge {hack : Hackenbush V} {p : Player}
    (h_ne : hack.graph ≠ ⊥) (hgc : hack.groundCount p = 0) :
    ∃ e, e ∈ hack.graph.edgeSet ∧ hack.ground ∈ e ∧ hack.coloring e = -p := by
  obtain ⟨ e, he₁, he₂ ⟩ := hack.exists_ground_edge h_ne
  by_cases he₃ : hack.coloring e = p
  · absurd hgc
    apply Nat.ne_of_gt
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨hack.mem_edgeFinset.mpr he₁, he₂, he₃⟩⟩
  · use e
    refine ⟨?_, ?_, ?_⟩
    · exact he₁
    · exact he₂
    · simp only [Player.ne_iff_eq_neg] at he₃
      exact he₃

/--
A p-move cannot lead to the zero game when groundCount p = 0.
-/
theorem move_not_zero_of_groundCount_zero {hack : Hackenbush V} {p : Player} {e : Sym2 V}
    (he : e ∈ hack.graph.edgeSet) (hc : hack.coloring e = p) (hgc : hack.groundCount p = 0) :
    (hack.remove e).graph ≠ ⊥ := by
  have h_ne : hack.graph ≠ ⊥ := by
    intro hbot
    simp [hbot] at he
  obtain ⟨e', he'_mem, he'_gnd, he'_col⟩ := hack.exists_neg_ground_edge h_ne hgc
  have hne : e' ≠ e := by
    intro heq
    subst heq
    cases p
    <;> simp_all only [ne_eq, Player.neg_right, reduceCtorEq]
  have h_survive : e' ∈ (hack.remove e).graph.edgeSet := by
    simp only [remove_graph]
    exact groundEdge_mem_groundComp he'_mem hne he'_gnd hack.connected
  intro hbot
  rw [hbot] at h_survive
  simp only [SimpleGraph.edgeSet, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] at h_survive

/--
Removing any edge preserves the zero-ness of groundCount p.
-/
theorem groundCount_zero_of_option {hack : Hackenbush V} {p : Player} {e : Sym2 V}
    (hgc : hack.groundCount p = 0) :
    (hack.remove e).groundCount p = 0 := by
  rw [groundCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro e' he'
  simp only [groundEdges, Finset.mem_filter, mem_edgeFinset,
    remove_graph, remove_ground, remove_coloring] at he'
  obtain ⟨he'_gc, he'_gnd, he'_col⟩ := he'
  have he'_G : e' ∈ hack.graph.edgeSet :=
    groundComp_edgeSet_subset _ _ _ he'_gc
  have : e' ∈ hack.groundEdges p := by
    simp only [groundEdges, Finset.mem_filter, mem_edgeFinset]
    exact ⟨he'_G, he'_gnd, he'_col⟩
  rw [groundCount, Finset.card_eq_zero] at hgc
  rw [hgc] at this
  exact absurd this (Finset.notMem_empty _)

/-!
### Stride theory
-/

/--
When p has no ground edges, the position is solved for p.
-/
theorem isSolved_of_groundCount_zero {hack : Hackenbush V} {p : Player}
    (hgc : hack.groundCount p = 0) :
    GameForm.IsSolved p hack.toGameForm := by
  induction m : hack.edgeCard using Nat.strong_induction_on generalizing hack p with
  | h m ih =>
    -- IH: for positions with fewer edges and groundCount p = 0, the position is solved.
    have ih_remove : ∀ (e : Sym2 V) (he : e ∈ hack.graph.edgeSet),
        (hack.remove e).groundCount p = 0 →
        GameForm.IsSolved p (hack.remove e).toGameForm := by
      intro e he hgc'
      refine ih _ ?_ hgc' rfl
      subst m
      exact hack.edgeCard_remove_lt e he
    rw [GameForm.isSolved_def]
    refine ⟨?_, ?_, ?_⟩
    · -- (i): p has no moves to 0
      intro h_mem
      obtain ⟨e, he, hc, heq⟩ := mem_moves_toGameForm_iff.mp h_mem
      have := move_not_zero_of_groundCount_zero he hc hgc
      exact this (toGameForm_eq_zero_iff.mp heq.symm)
    · -- (ii): Game is not a (-p)-end
      intro hne0 h_end
      have hne : hack.graph ≠ ⊥ := fun h => hne0 (toGameForm_eq_zero_iff.mpr h)
      obtain ⟨e, he_mem, he_gnd, he_col⟩ := exists_neg_ground_edge hne hgc
      have hmove : (hack.remove e).toGameForm ∈ Form.moves (-p) hack.toGameForm := by
        rw [← he_col]
        exact toGameForm_remove_mem_moves he_mem
      rw [Form.isEnd_def] at h_end
      rwa [h_end] at hmove
    · -- (iii): All options are solved for p
      intro gp hopt
      rw [Form.isOption_iff_mem_union] at hopt
      obtain hopt | hopt := hopt
      all_goals
      · obtain ⟨e, he, hc, rfl⟩ := mem_moves_toGameForm_iff.mp hopt
        exact ih_remove e he (groundCount_zero_of_option hgc)

/--
When `groundCount` p ≥ 1, the position is not solved for p.
-/
theorem not_isSolved_of_groundCount_pos {hack : Hackenbush V} {p : Player}
    (hgc : 1 ≤ hack.groundCount p) :
    ¬GameForm.IsSolved p hack.toGameForm := by
  induction n : hack.edgeCard using Nat.strong_induction_on generalizing hack p with
  | h n ih =>
    intro h_solved
    have hne : hack.graph ≠ ⊥ := by
      intro hbot
      have : hack.edgeFinset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e
        simp only [mem_edgeFinset, hbot, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false,
                  not_false_eq_true]
      simp [groundCount, groundEdges, this] at hgc
    have hne0 : hack.toGameForm ≠ 0 :=
      fun h => hne (toGameForm_eq_zero_iff.mp h)
    -- Case split: does (-p) have any edges?
    by_cases h_neg : ∃ e ∈ hack.graph.edgeSet, hack.coloring e = -p
    · -- Case A: (-p) has an edge e₁
      obtain ⟨e₁, he₁, hc₁⟩ := h_neg
      have hmove : (hack.remove e₁).toGameForm ∈ Form.moves (-p) hack.toGameForm := by
        rw [← hc₁]
        exact toGameForm_remove_mem_moves he₁
      have h_solved' := GameForm.isSolved_of_mem_moves h_solved hmove
      have hgc' : (hack.remove e₁).groundCount p ≥ 1 := by
        rw [groundCount_remove_neg hc₁]
        exact hgc
      refine ih _ ?_ hgc' rfl h_solved'
      subst n
      exact hack.edgeCard_remove_lt e₁ he₁
    · -- Case B: all edges are p-coloured, so (-p)-end
      push Not at h_neg
      refine absurd ?_ (GameForm.isSolved_not_isEnd h_solved hne0)
      rw [isEnd_def, moves_toGameForm, Set.image_eq_empty]
      ext
      simp only [Hackenbush.moves, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨e, he, hc, _⟩
      exact absurd hc (h_neg e he)

/--
The p-stride of a Hackenbush position equals the number of p-coloured ground
edges.
-/
theorem hasStride_groundCount (hack : Hackenbush V) (p : Player) :
    GameForm.HasStride p hack.toGameForm (hack.groundCount p) := by
  induction n : hack.edgeCard using Nat.strong_induction_on generalizing hack p with
  | h n ih =>
    have ih_remove : ∀ (e : Sym2 V) (he : e ∈ hack.graph.edgeSet) (q : Player),
        GameForm.HasStride q (hack.remove e).toGameForm
          ((hack.remove e).groundCount q) := by
      intro e he q
      refine ih _ ?_ _ _ rfl
      subst n
      exact hack.edgeCard_remove_lt e he
    by_cases h_groundCount : hack.groundCount p = 0
    · rw [h_groundCount, hasStride_eq_zero_iff]
      exact isSolved_of_groundCount_zero h_groundCount
    · obtain ⟨k, hk⟩ : ∃ k, hack.groundCount p = k + 1 :=
        ⟨hack.groundCount p - 1, Eq.symm (Nat.succ_pred_eq_of_ne_zero h_groundCount)⟩
      rw [hk]
      have ⟨e₀, he₀_filt⟩ : (hack.groundEdges p).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        simp only [groundCount, hempty, Finset.card_empty, Nat.zero_ne_add_one] at hk
      simp only [groundEdges, Finset.mem_filter, mem_edgeFinset] at he₀_filt
      obtain ⟨he₀_mem, he₀_gnd, he₀_col⟩ := he₀_filt
      rw [GameForm.hasStride_succ_iff]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- (i) : Game is not solved
        exact not_isSolved_of_groundCount_pos (by omega)
      · -- (ii): Own support
        intro g' hg'
        obtain ⟨e, he, hc, rfl⟩ := mem_moves_toGameForm_iff.mp hg'
        have hge := groundCount_move he hc
        exact ⟨(hack.remove e).groundCount p, by omega, ih_remove e he p⟩
      · -- (iii): Own best response
        refine ⟨(hack.remove e₀).toGameForm,
          (by rw [← he₀_col]; exact toGameForm_remove_mem_moves he₀_mem), ?_, ?_⟩
        · have : (hack.remove e₀).groundCount p = k := by
            rw [groundCount_remove_ground he₀_mem he₀_gnd he₀_col, hk, Nat.add_sub_self_right]
          rw [← this]
          exact ih_remove e₀ he₀_mem p
        · intro g'' hg'' m hm
          obtain ⟨e', he', hc', rfl⟩ := mem_moves_toGameForm_iff.mp hg''
          have hs1 := ih_remove e' he' (-p)
          rw [groundCount_neg_remove hc'] at hs1
          rw [GameForm.hasStride_unique hm hs1]
          have hs2 := ih_remove e₀ he₀_mem (-p)
          rw [groundCount_neg_remove he₀_col] at hs2
          exact ⟨hack.groundCount (-p), le_refl _, hs2⟩
      · -- (iv): Opponent support
        intro g' hg'
        obtain ⟨e, he, hc, rfl⟩ := mem_moves_toGameForm_iff.mp hg'
        use (hack.remove e).groundCount p
        have hgc_eq : (hack.remove e).groundCount p = k + 1 := by
          rw [groundCount_remove_neg hc, hk]
        rw [← hgc_eq]
        exact ⟨le_refl _, ih_remove e he p⟩
      · -- (v): Opponent best response
        intro hne
        obtain ⟨g', hg'⟩ := Set.nonempty_iff_ne_empty.mpr hne
        obtain ⟨e, he, hc, rfl⟩ := mem_moves_toGameForm_iff.mp hg'
        use (hack.remove e).toGameForm, mem_moves_toGameForm_iff.mpr ⟨e, he, hc, rfl⟩
        have hgc_eq : (hack.remove e).groundCount p = k + 1 := by
          rw [groundCount_remove_neg hc, hk]
        rw [← hgc_eq]
        exact ih_remove e he p

instance : Ruleset (Hackenbush V) where
  toGameForm := toGameForm
  moves_toGameForm p r g' h_g' := by
    simp only [moves_toGameForm, Set.mem_image] at h_g'
    obtain ⟨r', _, h_r'⟩ := h_g'
    use r'

/--
The underlying star graph for Hackenbush: ground vertex `0` connected to
vertices `1, ..., n`.
-/
private def starGraph (n : ℕ) : SimpleGraph ℕ where
  Adj u v := (u = 0 ∧ 1 ≤ v ∧ v ≤ n) ∨ (1 ≤ u ∧ u ≤ n ∧ v = 0)
  symm.symm u v h := by
    cases h with
    | inl h => exact Or.inr ⟨h.2.1, h.2.2, h.1⟩
    | inr h => exact Or.inl ⟨h.2.2, h.1, h.2.1⟩
  loopless.irrefl v h := by
    cases h with
    | inl h => omega
    | inr h => omega

/--
A star Hackenbush position over ℕ with `l` left ground edges and `r` right
ground edges. Ground vertex is `0`. Left edges connect `0` to `1, ..., l`.
Right edges connect `0` to `l+1, ..., l+r`. The colouring uses `max u v` (the
non-zero endpoint of each star edge) to determine colour.
-/
def starPos (l r : ℕ) : Hackenbush ℕ where
  graph := Hackenbush.starGraph (l + r)
  ground := 0
  coloring := fun e =>
    Sym2.lift ⟨fun u v =>
      if max u v ≤ l then Player.left else Player.right,
      by intro u v; simp [max_comm]⟩ e
  connected := fun v hv => by
    simp only [starGraph, SimpleGraph.mem_support] at hv
    obtain ⟨w, hw⟩ := hv
    cases hw with
    | inl h => exact h.1 ▸ SimpleGraph.Reachable.refl _
    | inr h => exact SimpleGraph.Adj.reachable (Or.inr ⟨h.1, h.2.1, rfl⟩)
  supportFinset := (Finset.range (l + r + 1)).filter (fun v =>
    v ∈ (Hackenbush.starGraph (l + r)).support)
  supportFinset_coe := by
    ext v
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, SimpleGraph.mem_support,
      starGraph]
    constructor
    · intro ⟨_, hv⟩; exact hv
    · intro ⟨w, hw⟩
      refine ⟨?_, ⟨w, hw⟩⟩
      cases hw with
      | inl h => omega
      | inr h => omega

theorem starPos_groundCount_left (l r : ℕ) :
    (Hackenbush.starPos l r).groundCount .left = l := by
  have h_groundEdges_left :
      (Hackenbush.starPos l r).groundEdges Player.left =
    Finset.image (fun i => s(0, i)) (Finset.Icc 1 l) := by
      ext e
      simp only [groundEdges, Finset.mem_filter, mem_edgeFinset, Finset.mem_image, Finset.mem_Icc]
      constructor <;> intro h <;> rcases e with ⟨u, v⟩
      · simp only [starPos, sup_le_iff, SimpleGraph.mem_edgeSet, Sym2.mem_iff, Sym2.lift_mk,
                   ite_eq_left_iff, not_and, not_le, reduceCtorEq, imp_false, Classical.not_imp,
                   not_lt, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h ⊢
        apply Or.elim h.left
        · intro ⟨h1, _, _⟩
          simp only [h1, zero_le, true_and] at h ⊢
          use v
          omega
        · intro ⟨_, _, h3⟩
          simp only [h3, zero_le, true_and] at h ⊢
          obtain ⟨left, right⟩ := h
          use u
          omega
      · simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, starPos,
          sup_le_iff, SimpleGraph.mem_edgeSet, Sym2.mem_iff, Sym2.lift_mk,
          ite_eq_left_iff, not_and, not_le, reduceCtorEq, imp_false, Classical.not_imp,
          not_lt] at h ⊢
        rcases h with ⟨a, ⟨ha₁, ha₂⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        <;> simp only [and_false, and_true, false_and, false_or,
                       nonpos_iff_eq_zero, one_ne_zero, or_false, or_true,
                       starGraph, true_and, true_or, zero_le]
        <;> omega
  unfold groundCount
  rw [h_groundEdges_left, Finset.card_image_of_injective] <;> norm_num [Function.Injective]
  omega

theorem starPos_groundCount_right (l r : ℕ) :
    (Hackenbush.starPos l r).groundCount .right = r := by
  have h_groundEdges_right :
      (Hackenbush.starPos l r).groundEdges Player.right =
      Finset.image (fun v => s(v, 0)) (Finset.Icc (l + 1) (l + r)) := by
    ext e
    simp only [groundEdges, starPos, sup_le_iff, Finset.mem_filter, mem_edgeFinset,
      Finset.mem_image, Finset.mem_Icc, Order.add_one_le_iff]
    rcases e with ⟨u, v⟩
    rcases u with (_ | u)
    <;> rcases v with (_ | v)
    <;> simp [starGraph]
    · tauto
    · tauto
  unfold groundCount
  rw [h_groundEdges_right, Finset.card_image_of_injOn] <;> norm_num [Function.Injective]
  omega

instance : GameForm.Strided (Ruleset.Forms (Hackenbush ℕ)) where
  mk_with_strides l r := by
    use toGameForm (starPos l r)
    refine ⟨?_, ?_, ?_⟩
    · apply Ruleset.Forms.position_mem
    · convert hasStride_groundCount (starPos l r) .left
      rw [starPos_groundCount_left l r]
    · convert hasStride_groundCount (starPos l r) .right
      rw [starPos_groundCount_right l r]
  has_stride p g hg := by
    have ⟨r, h_r⟩ := Ruleset.Forms.exists hg
    simp only [Ruleset.toGameForm] at h_r
    have := hasStride_groundCount r p
    use r.groundCount p
    convert this

/-- The misère quotient of finite-star Hackenbush positions is equivalent to `ℤ`. -/
protected noncomputable def equivInt : MisereQuotient (Ruleset.Forms (Hackenbush ℕ)) ≃ ℤ :=
  MisereQuotient.stridedEquivInt

protected theorem le_iff_equiv_ge (a b : MisereQuotient (Ruleset.Forms (Hackenbush ℕ))) :
    a ≤ b ↔
    MisereQuotient.stridedEquivInt a ≥ MisereQuotient.stridedEquivInt b :=
    MisereQuotient.le_iff_equiv_ge a b

/-- The additive closure of Hackenbush positions has quotient equivalent to `ℤ`. -/
protected noncomputable def closure.equivInt :
    MisereQuotient (ClosedUnderAdd.closure (Ruleset.Forms (Hackenbush ℕ))) ≃ ℤ :=
  MisereQuotient.stridedEquivInt

protected theorem closure.le_iff_equiv_ge
    (a b : MisereQuotient (ClosedUnderAdd.closure (Ruleset.Forms (Hackenbush ℕ)))) :
    a ≤ b ↔
    MisereQuotient.stridedEquivInt a ≥ MisereQuotient.stridedEquivInt b :=
    MisereQuotient.le_iff_equiv_ge a b

end Hackenbush

end

end MisereGames
