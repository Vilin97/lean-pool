/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Push

/-!
# Chordal graphs

A simple graph is **chordal** if every cycle of length at least four has a *chord* — an edge of the
graph joining two vertices of the cycle that is not itself one of the cycle's edges.

This module is a reusable byproduct extracted from the verified formalization accompanying Paper II,
*Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs*. It is
self-contained and depends only on Mathlib.

## Main definitions
* `SimpleGraph.IsChordal`
* `SimpleGraph.IsSimplicial`
* `SimpleGraph.Separates`, `SimpleGraph.IsMinimalSeparator`

## Main results
* `SimpleGraph.IsChordal.comap` — chordality pulls back along an injective vertex map
* `SimpleGraph.IsChordal.minimalSeparator_isClique` — finite minimal separators of fixed vertex
  pairs are cliques
* `SimpleGraph.IsChordal.exists_isSimplicial` — Dirac (1961): a nonempty finite chordal graph has a
  simplicial vertex
* `SimpleGraph.IsChordal.exists_two_nonadj_isSimplicial` — a connected non-complete finite chordal
  graph has two non-adjacent simplicial vertices
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A graph is **chordal** if every cycle of length `≥ 4` has a chord: an adjacency between two
vertices of the cycle whose edge is not one of the cycle's own edges. -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges

/-- A vertex is **simplicial** if its neighbourhood induces a clique. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop := G.IsClique (G.neighborSet v)

/-- `S` **separates** `a` from `b` if neither lies in `S` and every walk `a → b` meets `S`. -/
def Separates (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ ¬ Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ G.Adj p q) a b

/-- `S` is a **minimal** `a`–`b` separator: it separates them and no proper subset does. -/
def IsMinimalSeparator (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  G.Separates S a b ∧ ∀ T ⊂ S, ¬ G.Separates T a b

/-- Chordality pulls back along an injective vertex map. In particular, every induced subgraph of
a chordal graph is chordal. -/
theorem IsChordal.comap {W : Type*} (hG : G.IsChordal) (f : W ↪ V) :
    (G.comap f).IsChordal := by
  intro v c hc hlen
  let φ : G.comap f ↪g G := SimpleGraph.Embedding.comap f G
  obtain ⟨x, y, hx, hy, hadj, hchord⟩ :=
    hG (c.map φ.toHom) (hc.map φ.injective) (by rwa [Walk.length_map])
  rw [Walk.support_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  refine ⟨x', y', hx', hy', φ.map_adj_iff.mp hadj, fun hmem => hchord ?_⟩
  rw [Walk.edges_map]
  exact List.mem_map.2 ⟨s(x', y'), hmem, rfl⟩

/-- Every induced subgraph of a chordal graph is chordal. -/
theorem IsChordal.induce (hG : G.IsChordal) (W : Set V) : (G.induce W).IsChordal :=
  hG.comap (Function.Embedding.subtype (· ∈ W))


/-! ### Private helpers (ported from a verified development; self-contained). -/

section DiracPort

/-- `a` reaches `b` avoiding `S` (Finset form). -/
private def AvoidReach (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (fun p q => p ∉ S ∧ q ∉ S ∧ G.Adj p q) a b

/-- `S` separates `a` from `b` (Finset form). -/
private def SeparatesF (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ ¬ AvoidReach G S a b

/-- `S` is a minimal `a`–`b` separator (Finset form). -/
private def IsMinimalSeparatorF (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  SeparatesF G S a b ∧ ∀ T : Finset V, T ⊂ S → ¬ SeparatesF G T a b

/-- Relative simpliciality: the neighbors of `a` lying inside `S` form a clique. -/
private def RSimplicial (H : SimpleGraph V) (S : Finset V) (a : V) : Prop :=
  H.IsClique {b | b ∈ S ∧ H.Adj a b}

/-- One step of relative reachability inside `S`. -/
private def RStep (H : SimpleGraph V) (S : Finset V) (p q : V) : Prop := p ∈ S ∧ q ∈ S ∧ H.Adj p q

/-- Relative reachability inside `S`. -/
private def RReach (H : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  Relation.ReflTransGen (RStep H S) a b

/-- `S` induces a connected subgraph. -/
private def RConn (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, RReach H S a b

/-- A relatively-simplicial vertex whose neighbors all lie in `S` is genuinely simplicial. -/
private theorem isSimplicial_of_rsimplicial (H : SimpleGraph V) {S : Finset V} {a : V}
    (hsub : ∀ b, H.Adj a b → b ∈ S) (h : RSimplicial H S a) : IsSimplicial H a := by
  intro b hb c hc
  exact h ⟨hsub b hb, hb⟩ ⟨hsub c hc, hc⟩

/-- `RStep` is symmetric. -/
private theorem rstep_symm (H : SimpleGraph V) (S : Finset V) {p q : V} (h : RStep H S p q) :
    RStep H S q p := ⟨h.2.1, h.1, h.2.2.symm⟩

/-- `RReach` is symmetric. -/
private theorem rreach_symm (H : SimpleGraph V) (S : Finset V) {a b : V} (h : RReach H S a b) :
    RReach H S b a := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact (Relation.ReflTransGen.single (rstep_symm H S hstep)).trans ih

/-- A vertex reached relatively inside `S` is either the starting vertex or lies in `S`. -/
private theorem eq_or_mem_of_rreach (H : SimpleGraph V) (S : Finset V) {a b : V}
    (h : RReach H S a b) : b = a ∨ b ∈ S := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep _ => exact Or.inr hstep.2.1

/-- Relative reachability inside `S.erase v` from a vertex other than `v` never reaches `v`. -/
private theorem ne_of_rreach_erase [DecidableEq V] (H : SimpleGraph V) {S : Finset V} {v a b : V}
    (h : RReach H (S.erase v) a b) (ha : a ≠ v) : b ≠ v := by
  rcases eq_or_mem_of_rreach H _ h with rfl | hb
  · exact ha
  · exact Finset.ne_of_mem_erase hb

/-- Shortcut lemma: reachability that may pass through a relatively-simplicial vertex `v` can be
rerouted to avoid `v` (endpoints distinct from `v`). -/
private theorem rreach_erase [DecidableEq V] (H : SimpleGraph V) {S : Finset V} {v : V}
    (hv : RSimplicial H S v) {a b : V} (hab : RReach H S a b) (ha : a ≠ v) (hb : b ≠ v) :
    RReach H (S.erase v) a b := by
  -- Reaching `c` inside `S` either avoids `v` altogether, or `c = v` and the last vertex before
  -- `v` is reached while avoiding `v`.
  have key : ∀ c, RReach H S a c → RReach H (S.erase v) a c ∨
      (c = v ∧ ∃ n, n ∈ S ∧ H.Adj n v ∧ RReach H (S.erase v) a n) := by
    intro c hc
    induction hc with
    | refl => exact Or.inl .refl
    | @tail p q _ hstep ih =>
      obtain ⟨hpS, hqS, hpq⟩ := hstep
      rcases ih with hp | ⟨rfl, n, hnS, hnv, hn⟩
      · have hpv : p ≠ v := ne_of_rreach_erase H hp ha
        by_cases hqv : q = v
        · exact Or.inr ⟨hqv, p, hpS, hqv ▸ hpq, hp⟩
        · exact Or.inl (hp.tail ⟨Finset.mem_erase.2 ⟨hpv, hpS⟩,
            Finset.mem_erase.2 ⟨hqv, hqS⟩, hpq⟩)
      · -- Here the previous vertex is `v` itself: reroute through the clique of `v`'s neighbors.
        rcases eq_or_ne n q with rfl | hnq
        · exact Or.inl hn
        · exact Or.inl (hn.tail ⟨Finset.mem_erase.2 ⟨hnv.ne, hnS⟩,
            Finset.mem_erase.2 ⟨hpq.ne', hqS⟩, hv ⟨hnS, hnv.symm⟩ ⟨hqS, hpq⟩ hnq⟩)
  rcases key b hab with h | ⟨rfl, -⟩
  · exact h
  · exact absurd rfl hb

/-- Removing a relatively-simplicial vertex from a connected `S` keeps it connected. -/
private theorem rconn_erase [DecidableEq V] (H : SimpleGraph V) {S : Finset V} {v : V}
    (hv : RSimplicial H S v) (hconn : RConn H S) : RConn H (S.erase v) := fun a ha b hb =>
  rreach_erase H hv (hconn a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb))
    (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb)

/-- The connected component of `u` inside `S` (characterized by `hDdef`) is itself connected. -/
private theorem rconn_component (H : SimpleGraph V) {S : Finset V} {u : V} {D : Finset V}
    (hDdef : ∀ w, w ∈ D ↔ (w ∈ S ∧ RReach H S u w)) : RConn H D := by
  have haux : ∀ w, RReach H S u w → RReach H D u w := by
    intro w hw
    induction hw with
    | refl => exact .refl
    | @tail p q hup hstep ih =>
      exact ih.tail ⟨(hDdef p).2 ⟨hstep.1, hup⟩, (hDdef q).2 ⟨hstep.2.1, hup.tail hstep⟩,
        hstep.2.2⟩
  exact fun a ha b hb =>
    (rreach_symm H D (haux a ((hDdef a).1 ha).2)).trans (haux b ((hDdef b).1 hb).2)

/-- The component of `u` inside `S` is separated from the rest: any `S`-neighbor of a component
vertex is again in the component. -/
private theorem component_sep (H : SimpleGraph V) {S : Finset V} {u : V} {D : Finset V}
    (hDdef : ∀ w, w ∈ D ↔ (w ∈ S ∧ RReach H S u w)) :
    ∀ d ∈ D, ∀ w, w ∈ S → H.Adj d w → w ∈ D := by
  intro d hd w hw hadj
  rw [hDdef] at hd ⊢
  exact ⟨hw, hd.2.tail ⟨hd.1, hw, hadj⟩⟩

/-- `AvoidReach` is symmetric (the underlying step relation is symmetric). -/
private theorem avoidReach_symm (G : SimpleGraph V) (S : Finset V) {a b : V}
    (h : AvoidReach G S a b) : AvoidReach G S b a := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, hstep.2.2.symm⟩ ih

/-- `SeparatesF` is symmetric in the two endpoints. -/
private theorem separates_symm (G : SimpleGraph V) {S : Finset V} {a b : V}
    (h : SeparatesF G S a b) : SeparatesF G S b a :=
  ⟨h.2.1, h.1, fun h' => h.2.2 (avoidReach_symm G S h')⟩

/-- Every vertex reachable from `a` while avoiding `S` (with `a ∉ S`) is itself outside `S`. -/
private theorem avoidReach_notMem (G : SimpleGraph V) {S : Finset V} {a b : V}
    (h : AvoidReach G S a b) (ha : a ∉ S) : b ∉ S := by
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.1

/-- An `S`-avoiding reach `p → q` is witnessed by an actual walk all of whose vertices are
`S`-avoidingly reachable from `p`. -/
private theorem avoidReach_walk (G : SimpleGraph V) (S : Finset V) {p q : V}
    (h : AvoidReach G S p q) :
    ∃ P : G.Walk p q, ∀ w ∈ P.support, AvoidReach G S p w := by
  induction h with
  | refl =>
    refine ⟨Walk.nil, fun w hw => ?_⟩
    simp only [Walk.support_nil, List.mem_singleton] at hw
    exact hw ▸ .refl
  | @tail c d hpc hstep ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P.append (Walk.cons hstep.2.2 Walk.nil), fun w hw => ?_⟩
    rw [Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    · exact hP w hw
    · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hw
      rcases hw with rfl | rfl
      · exact hpc
      · exact hpc.tail hstep

/-- **Minimality neighbour lemma.** If `S` is a minimal `a`–`b` separator and `x ∈ S`, then `x`
has a neighbour on the `a`-side (reachable from `a` avoiding `S`). -/
private theorem sep_exists_aside_nbr (G : SimpleGraph V) {S : Finset V} {a b : V}
    (hS : IsMinimalSeparatorF G S a b) {x : V} (hx : x ∈ S) :
    ∃ u, AvoidReach G S a u ∧ G.Adj u x := by
  classical
  obtain ⟨haS, hbS, hab⟩ := hS.1
  -- By minimality, `S.erase x` fails to separate `a` from `b`.
  have hpath : AvoidReach G (S.erase x) a b := by
    by_contra hcon
    exact hS.2 (S.erase x) (Finset.erase_ssubset hx)
      ⟨fun h => haS (Finset.mem_of_mem_erase h), fun h => hbS (Finset.mem_of_mem_erase h), hcon⟩
  -- Following such a walk, either it never meets `S`, or it produces a neighbour of `x`.
  have hclaim : ∀ c, AvoidReach G (S.erase x) a c →
      AvoidReach G S a c ∨ ∃ u, AvoidReach G S a u ∧ G.Adj u x := by
    intro c hc
    induction hc with
    | refl => exact Or.inl .refl
    | @tail p q _ hstep ih =>
      obtain ⟨_, hqe, hpq⟩ := hstep
      rcases ih with hp | hfound
      · have hpS : p ∉ S := avoidReach_notMem G hp haS
        by_cases hqS : q ∈ S
        · have hqx : q = x := by
            by_contra hne
            exact hqe (Finset.mem_erase.2 ⟨hne, hqS⟩)
          exact Or.inr ⟨p, hp, hqx ▸ hpq⟩
        · exact Or.inl (hp.tail ⟨hpS, hqS, hpq⟩)
      · exact Or.inr hfound
  rcases hclaim b hpath with hreach | hfound
  · exact absurd hreach hab
  · exact hfound

/-- A `G`-walk `x → y` all of whose vertices lie in `K` lifts to a walk in `G.induce K`, giving
reachability there. -/
private theorem reachable_induce_of_walk (G : SimpleGraph V) (K : Set V) {x y : V}
    (hy : y ∈ K) (P : G.Walk x y) (hsupp : ∀ w ∈ P.support, w ∈ K) (hx : x ∈ K) :
    (G.induce K).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction P with
  | nil => exact Reachable.refl _
  | @cons c d _ hadj Q ih =>
    have hdK : d ∈ K := hsupp d (by simp)
    have hQ : ∀ w ∈ Q.support, w ∈ K := fun w hw => hsupp w (by simp [hw])
    exact (Adj.reachable (show (G.induce K).Adj ⟨c, hx⟩ ⟨d, hdK⟩ from hadj)).trans (ih hy hQ hdK)

/-- A walk between distinct endpoints that does not use the edge joining them has length `≥ 2`. -/
private theorem two_le_length_of_notMem_edges {W : Type*} {G' : SimpleGraph W} {x y : W}
    (w : G'.Walk x y) (hxy : x ≠ y) (hmem : s(x, y) ∉ w.edges) : 2 ≤ w.length := by
  cases w with
  | nil => exact absurd rfl hxy
  | cons _ w' =>
    cases w' with
    | nil => exact absurd (by simp) hmem
    | cons _ w'' =>
      simp only [Walk.length_cons]
      omega

/-- **Geodesics are chordless.** On a shortest walk, any two adjacent support vertices are joined by
an edge of the walk. -/
private theorem geodesic_adj_imp_edge {W : Type*} {G' : SimpleGraph W} {u v : W}
    (p : G'.Walk u v) (hp : p.length = G'.dist u v)
    {s t : W} (hs : s ∈ p.support) (ht : t ∈ p.support) (hadj : G'.Adj s t) :
    s(s, t) ∈ p.edges := by
  classical
  by_contra hmem
  -- Split the walk at `s`.
  obtain ⟨A, B, rfl⟩ : ∃ (A : G'.Walk u s) (B : G'.Walk s v), p = A.append B :=
    ⟨p.takeUntil s hs, p.dropUntil s hs, (p.take_spec hs).symm⟩
  rw [Walk.length_append] at hp
  rcases (Walk.mem_support_append_iff A B).1 ht with ht₁ | ht₂
  · -- `t` occurs before `s`: rerouting through the chord shortens the walk.
    obtain ⟨C, D, rfl⟩ : ∃ (C : G'.Walk u t) (D : G'.Walk t s), A = C.append D :=
      ⟨A.takeUntil t ht₁, A.dropUntil t ht₁, (A.take_spec ht₁).symm⟩
    rw [Walk.length_append] at hp
    have hdist : G'.dist u v ≤ C.length + (B.length + 1) := by
      simpa [Walk.length_append, Walk.length_cons] using
        G'.dist_le (C.append (Walk.cons hadj.symm B))
    have hedges : s(t, s) ∉ D.edges := fun he => hmem <| by
      rw [Sym2.eq_swap, Walk.edges_append, Walk.edges_append]
      exact List.mem_append_left _ (List.mem_append_right _ he)
    have h2 : 2 ≤ D.length := two_le_length_of_notMem_edges D hadj.ne' hedges
    omega
  · -- `t` occurs after `s`.
    obtain ⟨E, F, rfl⟩ : ∃ (E : G'.Walk s t) (F : G'.Walk t v), B = E.append F :=
      ⟨B.takeUntil t ht₂, B.dropUntil t ht₂, (B.take_spec ht₂).symm⟩
    rw [Walk.length_append] at hp
    have hdist : G'.dist u v ≤ A.length + (F.length + 1) := by
      simpa [Walk.length_append, Walk.length_cons] using
        G'.dist_le (A.append (Walk.cons hadj F))
    have hedges : s(s, t) ∉ E.edges := fun he => hmem <| by
      rw [Walk.edges_append, Walk.edges_append]
      exact List.mem_append_right _ (List.mem_append_left _ he)
    have h2 : 2 ≤ E.length := two_le_length_of_notMem_edges E hadj.ne hedges
    omega

/-- From a `G`-walk `x → y` staying inside `K`, extract an induced (chordless) `G`-path `x → y`
staying inside `K`. -/
private theorem exists_induced_path_of_walk (G : SimpleGraph V) (K : Set V) {x y : V}
    (hx : x ∈ K) (hy : y ∈ K) (P : G.Walk x y) (hsupp : ∀ w ∈ P.support, w ∈ K) :
    ∃ Q : G.Walk x y, Q.IsPath ∧ (∀ w ∈ Q.support, w ∈ K) ∧
      (∀ s ∈ Q.support, ∀ t ∈ Q.support, G.Adj s t → s(s, t) ∈ Q.edges) := by
  obtain ⟨Q, hQpath, hQdist⟩ :
      ∃ Q : (G.induce K).Walk ⟨x, hx⟩ ⟨y, hy⟩,
        Q.IsPath ∧ Q.length = (G.induce K).dist ⟨x, hx⟩ ⟨y, hy⟩ :=
    (reachable_induce_of_walk G K hy P hsupp hx).exists_path_of_dist
  let f : (G.induce K) →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  refine ⟨Q.map f, hQpath.map Subtype.val_injective, ?_, ?_⟩
  · intro w hw
    have hwMap : w ∈ List.map (⇑f) Q.support := by
      rw [← SimpleGraph.Walk.support_map f Q]
      exact hw
    obtain ⟨wPre, _, hfw⟩ := List.mem_map.1 hwMap
    dsimp only [f] at hfw
    have hwEq : w = (wPre : V) := hfw.symm
    subst w
    exact wPre.property
  · intro s hs t ht hst
    have hsMap : s ∈ List.map (⇑f) Q.support := by
      rw [← SimpleGraph.Walk.support_map f Q]
      exact hs
    have htMap : t ∈ List.map (⇑f) Q.support := by
      rw [← SimpleGraph.Walk.support_map f Q]
      exact ht
    obtain ⟨sPre, hsPre, hfs⟩ := List.mem_map.1 hsMap
    obtain ⟨tPre, htPre, hft⟩ := List.mem_map.1 htMap
    dsimp only [f] at hfs hft
    have hsEq : s = (sPre : V) := hfs.symm
    have htEq : t = (tPre : V) := hft.symm
    subst s
    subst t
    have hstPre : (G.induce K).Adj sPre tPre := hst
    have he := geodesic_adj_imp_edge Q hQdist hsPre htPre hstPre
    have he' : Sym2.map (⇑f) s(sPre, tPre) ∈ List.map (Sym2.map ⇑f) Q.edges :=
      List.mem_map.2 ⟨s(sPre, tPre), he, rfl⟩
    rw [← SimpleGraph.Walk.edges_map f Q] at he'
    dsimp only [f] at he'
    rw [Sym2.map_mk] at he'
    exact he'

/-- **Cycle contradiction.** Two internally-disjoint induced `x`–`y` paths (each of length `≥ 2`,
no cross edges except through the endpoints) form a chordless cycle of length `≥ 4`, contradicting
chordality. -/
private theorem two_induced_paths_not_chordal (G : SimpleGraph V) (hG : IsChordal G) {x y : V}
    (P Q : G.Walk x y) (hP : P.IsPath) (hQ : Q.IsPath)
    (hPlen : 2 ≤ P.length) (hQlen : 2 ≤ Q.length)
    (hPind : ∀ s ∈ P.support, ∀ t ∈ P.support, G.Adj s t → s(s, t) ∈ P.edges)
    (hQind : ∀ s ∈ Q.support, ∀ t ∈ Q.support, G.Adj s t → s(s, t) ∈ Q.edges)
    (hdisj : ∀ w, w ∈ P.support → w ∈ Q.support → w = x ∨ w = y)
    (hcross : ∀ s ∈ P.support, ∀ t ∈ Q.support, G.Adj s t →
        (s = x ∨ s = y) ∨ (t = x ∨ t = y)) :
    False := by
  -- The start of a path does not occur again in the tail of its support.
  have hstart : ∀ {u v : V} {p : G.Walk u v}, p.IsPath → u ∉ p.support.tail := by
    intro u v p hp hmem
    have hnd := hp.support_nodup
    rw [← Walk.cons_tail_support] at hnd
    exact (List.nodup_cons.1 hnd).1 hmem
  have hmemrev : ∀ {w : V}, w ∈ Q.reverse.support → w ∈ Q.support := by
    intro w hw
    rwa [Walk.support_reverse, List.mem_reverse] at hw
  -- `P` followed by `Q` reversed is a cycle of length at least four.
  have hdisjtails : P.support.tail.Disjoint Q.reverse.support.tail := by
    intro w hwP hwQ
    rcases hdisj w (List.mem_of_mem_tail hwP) (hmemrev (List.mem_of_mem_tail hwQ)) with rfl | rfl
    · exact hstart hP hwP
    · exact hstart hQ.reverse hwQ
  have hcyc : (P.append Q.reverse).IsCycle :=
    hP.isCycle_append hQ.reverse hdisjtails (Or.inl (by omega))
  have hlen : 4 ≤ (P.append Q.reverse).length := by
    rw [Walk.length_append, Walk.length_reverse]
    omega
  obtain ⟨s, t, hs, ht, hadj, hchord⟩ := hG (P.append Q.reverse) hcyc hlen
  -- Every adjacency between vertices of the cycle is already one of its edges.
  refine hchord ?_
  have hedgeP : ∀ {u w : V}, u ∈ P.support → w ∈ P.support → G.Adj u w →
      s(u, w) ∈ (P.append Q.reverse).edges := by
    intro u w hu hw huw
    rw [Walk.edges_append]
    exact List.mem_append_left _ (hPind u hu w hw huw)
  have hedgeQ : ∀ {u w : V}, u ∈ Q.support → w ∈ Q.support → G.Adj u w →
      s(u, w) ∈ (P.append Q.reverse).edges := by
    intro u w hu hw huw
    rw [Walk.edges_append, Walk.edges_reverse]
    exact List.mem_append_right _ (List.mem_reverse.2 (hQind u hu w hw huw))
  rcases (Walk.mem_support_append_iff _ _).1 hs with hsP | hsQ
  · rcases (Walk.mem_support_append_iff _ _).1 ht with htP | htQ
    · exact hedgeP hsP htP hadj
    · rcases hcross s hsP t (hmemrev htQ) hadj with hsxy | htxy
      · have hsQ : s ∈ Q.support := by
          rcases hsxy with rfl | rfl
          exacts [Q.start_mem_support, Q.end_mem_support]
        exact hedgeQ hsQ (hmemrev htQ) hadj
      · have htP : t ∈ P.support := by
          rcases htxy with rfl | rfl
          exacts [P.start_mem_support, P.end_mem_support]
        exact hedgeP hsP htP hadj
  · rcases (Walk.mem_support_append_iff _ _).1 ht with htP | htQ
    · rw [Sym2.eq_swap]
      rcases hcross t htP s (hmemrev hsQ) hadj.symm with htxy | hsxy
      · have htQ : t ∈ Q.support := by
          rcases htxy with rfl | rfl
          exacts [Q.start_mem_support, Q.end_mem_support]
        exact hedgeQ htQ (hmemrev hsQ) hadj.symm
      · have hsP : s ∈ P.support := by
          rcases hsxy with rfl | rfl
          exacts [P.start_mem_support, P.end_mem_support]
        exact hedgeP htP hsP hadj.symm
    · exact hedgeQ (hmemrev hsQ) (hmemrev htQ) hadj

/-! ### Dirac helpers (private) -/

/-
A simplicial vertex of the induced subgraph on `↑T` is relatively simplicial in `T`.
-/
private theorem rsimplicial_of_induce_simplicial (G : SimpleGraph V) (T : Finset V)
    (z : (T : Set V)) (hz : IsSimplicial (G.induce (T : Set V)) z) :
    RSimplicial G T z.val := by
  rintro a ⟨haT, haz⟩ b ⟨hbT, hbz⟩ hab
  have haT' : a ∈ (T : Set V) := haT
  have hbT' : b ∈ (T : Set V) := hbT
  exact hz (show (G.induce (T : Set V)).Adj z ⟨a, haT'⟩ from haz)
    (show (G.induce (T : Set V)).Adj z ⟨b, hbT'⟩ from hbz)
    (by simpa [Subtype.ext_iff] using hab)

/-
A simplicial vertex of `G.induce W` whose `G`-neighbours all lie in `W` is simplicial in `G`.
-/
private theorem isSimplicial_of_induce (G : SimpleGraph V) (W : Set V) (z : W)
    (hz : IsSimplicial (G.induce W) z) (hsub : ∀ w, G.Adj z.val w → w ∈ W) :
    IsSimplicial G z.val := by
  intro p hp q hq hpq
  exact hz (show (G.induce W).Adj z ⟨p, hsub p hp⟩ from hp)
    (show (G.induce W).Adj z ⟨q, hsub q hq⟩ from hq)
    (by simpa [Subtype.ext_iff] using hpq)

/-
`S`-avoiding reachability equals relative reachability inside the complement of `S`.
-/
private theorem avoidReach_iff_rreach_compl [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (a b : V) :
    AvoidReach G S a b ↔ RReach G (Finset.univ \ S) a b := by
  have hstep : ∀ p q : V, (p ∉ S ∧ q ∉ S ∧ G.Adj p q) ↔ RStep G (Finset.univ \ S) p q := by
    intro p q
    simp only [RStep, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · exact fun h => Relation.ReflTransGen.mono (fun p q hpq => (hstep p q).1 hpq) a b h
  · exact fun h => Relation.ReflTransGen.mono (fun p q hpq => (hstep p q).2 hpq) a b h

/-
The complement of a nonadjacent pair `{a,b}` separates them.
-/
private theorem separates_compl_pair [Fintype V] [DecidableEq V] (G : SimpleGraph V) {a b : V}
    (hab : a ≠ b)
    (hnadj : ¬ G.Adj a b) :
    SeparatesF G ((Finset.univ.erase a).erase b) a b := by
  refine ⟨by simp, by simp, ?_⟩
  -- Every vertex reachable from `a` while avoiding the complement of `{a, b}` equals `a`.
  have h_ind : ∀ c, AvoidReach G ((Finset.univ.erase a).erase b) a c → c = a := by
    intro c hc
    induction hc with
    | refl => rfl
    | @tail c' c _ hstep ih =>
      have hadj : G.Adj a c := ih ▸ hstep.2.2
      have hcS : c ∉ (Finset.univ.erase a).erase b := hstep.2.1
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at hcS
      by_cases hcb : c = b
      · subst hcb
        exact absurd hadj hnadj
      · exact hcS hcb
  exact fun h => hab (h_ind b h).symm

/-
From any separating set, a minimal separator exists.
-/
private theorem exists_minimal_separator (G : SimpleGraph V) {a b : V} (S₀ : Finset V)
    (h : SeparatesF G S₀ a b) : ∃ S, IsMinimalSeparatorF G S a b := by
  classical
  -- Pick a separating set of least cardinality.
  have hex : ∃ n, ∃ S : Finset V, SeparatesF G S a b ∧ S.card = n := ⟨S₀.card, S₀, h, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hS, fun T hT hTsep => ?_⟩
  have hle : Nat.find hex ≤ T.card := Nat.find_le ⟨T, hTsep, rfl⟩
  have hlt : T.card < S.card := Finset.card_lt_card hT
  omega

/-
Dirac-2, restricted form of `PaperII.rdirac2` with `hRSH` only required on subsets of `U`.
-/
private theorem rdirac2U (H : SimpleGraph V) (U : Finset V)
    (hRSH : ∀ T : Finset V, T ⊆ U → T.Nonempty → ∃ a ∈ T, RSimplicial H T a) :
    ∀ (n : ℕ) (S : Finset V), S ⊆ U → S.card = n → RConn H S →
      (¬ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b) →
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ¬ H.Adj a b ∧ RSimplicial H S a ∧ RSimplicial H S b := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hSU hSn hSconn hSnotcomplete
    have hSne : S.Nonempty := by
      rcases Finset.eq_empty_or_nonempty S with rfl | h
      · exact (hSnotcomplete (by simp)).elim
      · exact h
    obtain ⟨v, hv, hv'⟩ := hRSH S hSU hSne
    by_cases hS'complete : ∀ a ∈ S.erase v, ∀ b ∈ S.erase v, a ≠ b → H.Adj a b
    · -- `S` minus the relatively simplicial vertex `v` is complete, so `v` is one of the
      -- two nonadjacent vertices we are after.
      obtain ⟨p, hp, q, hq, hpq, hnpq⟩ : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ ¬ H.Adj p q := by
        by_contra hcon
        push Not at hcon
        exact hSnotcomplete hcon
      have hRS : ∀ w ∈ S, ¬ H.Adj v w → RSimplicial H S w := by
        intro w _ hvw y hy z hz hyz
        have hyv : y ≠ v := by
          rintro rfl
          exact hvw hy.2.symm
        have hzv : z ≠ v := by
          rintro rfl
          exact hvw hz.2.symm
        exact hS'complete y (Finset.mem_erase.mpr ⟨hyv, hy.1⟩) z
          (Finset.mem_erase.mpr ⟨hzv, hz.1⟩) hyz
      have hkey : p = v ∨ q = v := by
        by_contra hcon
        push Not at hcon
        exact hnpq (hS'complete p (Finset.mem_erase.mpr ⟨hcon.1, hp⟩) q
          (Finset.mem_erase.mpr ⟨hcon.2, hq⟩) hpq)
      rcases hkey with hpv | hqv
      · refine ⟨p, hp, q, hq, hpq, hnpq, ?_, hRS q hq ?_⟩
        · rw [hpv]
          exact hv'
        · rw [← hpv]
          exact hnpq
      · refine ⟨p, hp, q, hq, hpq, hnpq, hRS p hp ?_, ?_⟩
        · rw [← hqv]
          exact fun hadj => hnpq hadj.symm
        · rw [hqv]
          exact hv'
    · obtain ⟨a, ha, b, hb, hab, hnab, haSimp, hbSimp⟩ :=
        ih (n - 1)
          (Nat.sub_lt (by have hpos := Finset.card_pos.mpr ⟨v, hv⟩; omega) zero_lt_one)
          (S.erase v) (Finset.Subset.trans (Finset.erase_subset _ _) hSU)
          (by rw [Finset.card_erase_of_mem hv, hSn]) (rconn_erase H hv' hSconn)
          hS'complete
      have haS : a ∈ S := Finset.mem_of_mem_erase ha
      have hbS : b ∈ S := Finset.mem_of_mem_erase hb
      have liftRSimplicial (x : V) (hxv : ¬ H.Adj x v)
          (hx : RSimplicial H (S.erase v) x) : RSimplicial H S x := by
        intro y hy z hz hyz
        apply hx
        · exact ⟨Finset.mem_erase.mpr ⟨fun hyv => hxv (hyv ▸ hy.2), hy.1⟩, hy.2⟩
        · exact ⟨Finset.mem_erase.mpr ⟨fun hzv => hxv (hzv ▸ hz.2), hz.1⟩, hz.2⟩
        · exact hyz
      by_cases hav : H.Adj a v
      · by_cases hbv : H.Adj b v
        · exact False.elim (hnab (hv' ⟨haS, hav.symm⟩ ⟨hbS, hbv.symm⟩ hab))
        · exact ⟨b, hbS, v, hv, Finset.ne_of_mem_erase hb, hbv,
            liftRSimplicial b hbv hbSimp, hv'⟩
      · by_cases hbv : H.Adj b v
        · exact ⟨a, haS, v, hv, Finset.ne_of_mem_erase ha, hav,
            liftRSimplicial a hav haSimp, hv'⟩
        · exact ⟨a, haS, b, hbS, hab, hnab, liftRSimplicial a hav haSimp,
            liftRSimplicial b hbv hbSimp⟩

/-
Restricted form of `PaperII.exists_rsimplicial_outside_clique`.
-/
private theorem exists_rsimplicial_outside_cliqueU [DecidableEq V] (H : SimpleGraph V)
    (U : Finset V)
    (hRSH : ∀ T : Finset V, T ⊆ U → T.Nonempty → ∃ a ∈ T, RSimplicial H T a)
    {K S : Finset V} (hSU : S ⊆ U) (hK : H.IsClique (K : Set V))
    (hne : (S \ K).Nonempty) (hconn : RConn H S) :
    ∃ z ∈ S \ K, RSimplicial H S z := by
  by_cases hcomp : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b
  · obtain ⟨z, hz⟩ := hne
    refine ⟨z, hz, ?_⟩
    intro x hx y hy hxy
    exact hcomp x hx.1 y hy.1 hxy
  · obtain ⟨a, ha, b, hb, hab, hnab, hRSa, hRSb⟩ :=
      rdirac2U H U hRSH _ _ hSU rfl hconn hcomp
    by_cases haK : a ∈ K
    · by_cases hbK : b ∈ K
      · exact absurd (hK (Finset.mem_coe.mpr haK) (Finset.mem_coe.mpr hbK) hab) hnab
      · exact ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbK⟩, hRSb⟩
    · exact ⟨a, Finset.mem_sdiff.mpr ⟨ha, haK⟩, hRSa⟩
/-
Restricted form of `PaperII.exists_simplicial_in_component`: only needs `hRSH` on subsets of
`U ⊇ C ∪ D`, and returns a genuinely simplicial vertex of `H` inside `D`.
-/
private theorem exists_simplicial_in_componentU [DecidableEq V] (H : SimpleGraph V)
    (U : Finset V)
    (hRSH : ∀ T : Finset V, T ⊆ U → T.Nonempty → ∃ a ∈ T, RSimplicial H T a)
    (C : Finset V) (hCclique : H.IsClique (C : Set V))
    (D : Finset V) (hCDU : C ∪ D ⊆ U)
    (hDC : ∀ d ∈ D, d ∉ C) (hDne : D.Nonempty) (hDconn : RConn H D)
    (hsep : ∀ d ∈ D, ∀ w, H.Adj d w → w ∈ C ∨ w ∈ D) :
    ∃ z ∈ D, IsSimplicial H z := by
  -- By `hRSH`, we can get a relatively-simplicial `s ∈ D`.
  obtain ⟨s, hsD, hs⟩ : ∃ s ∈ D, RSimplicial H D s :=
    hRSH D (Finset.subset_union_right.trans hCDU) hDne
  by_cases hcase : ∀ w, H.Adj s w → w ∈ D
  · exact ⟨s, hsD, isSimplicial_of_rsimplicial H hcase hs⟩
  · -- Otherwise `s` has a neighbour `x ∈ C`, and `C ∪ D` is relatively connected.
    obtain ⟨x, hxC, hsx⟩ : ∃ x ∈ C, H.Adj s x := by
      push Not at hcase
      obtain ⟨w, hw, hwD⟩ := hcase
      exact ⟨w, (hsep s hsD w hw).resolve_right hwD, hw⟩
    have hxCD : x ∈ C ∪ D := Finset.mem_union_left _ hxC
    have hreach : ∀ a ∈ C ∪ D, RReach H (C ∪ D) a x := by
      intro a ha
      by_cases haC : a ∈ C
      · by_cases hax : a = x
        · subst hax
          exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single
            ⟨ha, hxCD, hCclique (Finset.mem_coe.mpr haC) (Finset.mem_coe.mpr hxC) hax⟩
      · have haD : a ∈ D := (Finset.mem_union.mp ha).resolve_left haC
        have hrel : RStep H D ≤ RStep H (C ∪ D) := fun p q hpq =>
          ⟨Finset.mem_union_right _ hpq.1, Finset.mem_union_right _ hpq.2.1, hpq.2.2⟩
        have has : RReach H (C ∪ D) a s :=
          Relation.ReflTransGen.mono hrel a s (hDconn a haD s hsD)
        exact has.tail ⟨Finset.mem_union_right _ hsD, hxCD, hsx⟩
    have hRConn : RConn H (C ∪ D) := fun a ha b hb =>
      (hreach a ha).trans (rreach_symm _ _ (hreach b hb))
    -- By `hRSH`, we can get a relatively-simplicial `z ∈ (C ∪ D) \ C`.
    obtain ⟨z, hzD, hz⟩ : ∃ z ∈ (C ∪ D) \ C, RSimplicial H (C ∪ D) z := by
      refine exists_rsimplicial_outside_cliqueU H U hRSH hCDU hCclique ?_ hRConn
      obtain ⟨d, hd⟩ := hDne
      exact ⟨d, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hd, hDC d hd⟩⟩
    have hzsd := Finset.mem_sdiff.mp hzD
    have hzmem : z ∈ D := (Finset.mem_union.mp hzsd.1).resolve_left hzsd.2
    refine ⟨z, hzmem, isSimplicial_of_rsimplicial H (fun w hw => ?_) hz⟩
    rcases hsep z hzmem w hw with hwC | hwD
    · exact Finset.mem_union_left _ hwC
    · exact Finset.mem_union_right _ hwD

/-
A walk from `x` to `y` all of whose interior vertices avoid `S`, built from two `S`-avoiding
reaches out of a common root `c` ending at neighbours of `x` and `y`.
-/
private theorem exists_walk_avoiding (G : SimpleGraph V) (S : Finset V) {c x y u v : V}
    (hu : AvoidReach G S c u) (hv : AvoidReach G S c v)
    (hux : G.Adj u x) (hvy : G.Adj v y) :
    ∃ P : G.Walk x y, ∀ w ∈ P.support, AvoidReach G S c w ∨ w = x ∨ w = y := by
  obtain ⟨R, hR⟩ := avoidReach_walk G S ((avoidReach_symm G S hu).trans hv)
  refine ⟨Walk.cons hux.symm (R.append (Walk.cons hvy Walk.nil)), ?_⟩
  intro w hw
  rw [Walk.support_cons, List.mem_cons] at hw
  rcases hw with rfl | hw
  · exact Or.inr (Or.inl rfl)
  rw [Walk.support_append, List.mem_append] at hw
  rcases hw with hw | hw
  · exact Or.inl (hu.trans (hR w hw))
  · simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    exact Or.inr (Or.inr hw)

/-
**Engine.** In a chordal graph, every minimal `a`–`b` separator is a clique.
Proof: for nonadjacent `x, y ∈ S`, minimality gives neighbours of each in both
components; shortest `x→y` paths through the `a`-component and the `b`-component form an induced
cycle of length `≥ 4` with no chord, contradicting `IsChordal`.
-/
private theorem minimal_separator_isClique (G : SimpleGraph V) (hG : IsChordal G)
    {S : Finset V} {a b : V} (hS : IsMinimalSeparatorF G S a b) :
    G.IsClique (S : Set V) := by
  intro x hxS y hyS hxy
  by_contra hnadjxy
  have hxS' : x ∈ S := hxS
  have hyS' : y ∈ S := hyS
  have hSba : IsMinimalSeparatorF G S b a :=
    ⟨separates_symm G hS.1, fun T hT hT' => hS.2 T hT (separates_symm G hT')⟩
  obtain ⟨ux, haux, hadjux⟩ := sep_exists_aside_nbr G hS hxS'
  obtain ⟨uy, hauy, hadjuy⟩ := sep_exists_aside_nbr G hS hyS'
  obtain ⟨wx, hbwx, hadjwx⟩ := sep_exists_aside_nbr G hSba hxS'
  obtain ⟨wy, hbwy, hadjwy⟩ := sep_exists_aside_nbr G hSba hyS'
  obtain ⟨Pw, hPw⟩ := exists_walk_avoiding G S haux hauy hadjux hadjuy
  obtain ⟨Qw, hQw⟩ := exists_walk_avoiding G S hbwx hbwy hadjwx hadjwy
  obtain ⟨P, hPpath, hPsupp, hPind⟩ :=
    exists_induced_path_of_walk G {w | AvoidReach G S a w ∨ w = x ∨ w = y}
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) Pw hPw
  obtain ⟨Q, hQpath, hQsupp, hQind⟩ :=
    exists_induced_path_of_walk G {w | AvoidReach G S b w ∨ w = x ∨ w = y}
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) Qw hQw
  -- Since `x ≠ y` are nonadjacent, every `x`–`y` walk has length at least two.
  have hlen : ∀ R : G.Walk x y, 2 ≤ R.length := by
    intro R
    cases R with
    | nil => exact absurd rfl hxy
    | cons hadj R' =>
      cases R' with
      | nil => exact absurd hadj hnadjxy
      | cons hadj' R'' =>
        simp only [Walk.length_cons]
        omega
  have hdisj : ∀ w, w ∈ P.support → w ∈ Q.support → w = x ∨ w = y := by
    intro w hwP hwQ
    rcases hPsupp w hwP with hwa | hwxy
    · rcases hQsupp w hwQ with hwb | hwxy
      · exact absurd (hwa.trans (avoidReach_symm G S hwb)) hS.1.2.2
      · exact hwxy
    · exact hwxy
  have hcross : ∀ s ∈ P.support, ∀ t ∈ Q.support, G.Adj s t →
      (s = x ∨ s = y) ∨ (t = x ∨ t = y) := by
    intro s hs t ht hst
    rcases hPsupp s hs with hsa | hsxy
    · rcases hQsupp t ht with htb | htxy
      · have hsS : s ∉ S := avoidReach_notMem G hsa hS.1.1
        have htS : t ∉ S := avoidReach_notMem G htb hS.1.2.1
        refine absurd ?_ hS.1.2.2
        exact hsa.trans
          ((Relation.ReflTransGen.single ⟨hsS, htS, hst⟩).trans (avoidReach_symm G S htb))
      · exact Or.inr htxy
    · exact Or.inl hsxy
  exact two_induced_paths_not_chordal G hG P Q hPpath hQpath (hlen P) (hlen Q) hPind hQind
    hdisj hcross

/-
Disconnected case of the Dirac induction: recurse into the connected component of some `a`.
-/
private theorem dirac_step_disconnected [Fintype V] (G : SimpleGraph V)
    (hnconn : ¬ G.Connected) (hne : Nonempty V)
    (ih_ind : ∀ (W : Finset V), W.card < Fintype.card V → W.Nonempty →
        ∃ z : (↑W : Set V), IsSimplicial (G.induce (↑W : Set V)) z) :
    ∃ v : V, IsSimplicial G v := by
  classical
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hnconn
  push Not at hnconn
  obtain ⟨v0, hv0⟩ := hnconn hne.some
  -- The connected component of `hne.some` is a proper nonempty subset of the vertex set.
  set W : Finset V := Finset.univ.filter (fun w => G.Reachable hne.some w) with hW
  have hmemW : ∀ w, w ∈ W ↔ G.Reachable hne.some w := by
    intro w
    simp [hW]
  have hWlt : W.card < Fintype.card V := by
    refine Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => ?_)
    exact hv0 ((hmemW v0).1 (by rw [h]; exact Finset.mem_univ v0))
  have hWne : W.Nonempty := ⟨hne.some, (hmemW _).2 (SimpleGraph.Reachable.refl _)⟩
  obtain ⟨z, hz⟩ := ih_ind W hWlt hWne
  refine ⟨z.val, isSimplicial_of_induce G _ z hz fun w hw => ?_⟩
  have hzW : G.Reachable hne.some z.val := (hmemW _).1 (Finset.mem_coe.mp z.2)
  exact Finset.mem_coe.mpr ((hmemW w).2 (hzW.trans hw.reachable))

/-- Connected non-complete case: a minimal separator is a clique, and a component `D` of `G - S`
contains a simplicial vertex. -/
private theorem dirac_step_separator [Fintype V] (G : SimpleGraph V) (hG : IsChordal G)
    {a b : V} (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (ih_ind : ∀ (W : Finset V), W.card < Fintype.card V → W.Nonempty →
        ∃ z : (↑W : Set V), IsSimplicial (G.induce (↑W : Set V)) z) :
    ∃ v : V, IsSimplicial G v := by
  classical
  obtain ⟨S, hS⟩ := exists_minimal_separator G _ (separates_compl_pair G hab hnadj)
  obtain ⟨haS, hbS, hnr⟩ := hS.1
  have hCclique := minimal_separator_isClique G hG hS
  set Sc : Finset V := Finset.univ \ S with hSc
  set D : Finset V := Finset.univ.filter (fun w => w ∈ Sc ∧ RReach G Sc a w) with hD
  have hDdef : ∀ w, w ∈ D ↔ (w ∈ Sc ∧ RReach G Sc a w) := by
    intro w; simp [hD, Finset.mem_filter]
  have haSc : a ∈ Sc := by simp [hSc, Finset.mem_sdiff, haS]
  have haD : a ∈ D := (hDdef a).2 ⟨haSc, Relation.ReflTransGen.refl⟩
  have hDne : D.Nonempty := ⟨a, haD⟩
  have hbD : b ∉ D := by
    intro hbd
    rw [hDdef] at hbd
    exact hnr ((avoidReach_iff_rreach_compl G S a b).2 hbd.2)
  have hDconn : RConn G D := rconn_component G hDdef
  have hDC : ∀ d ∈ D, d ∉ S := by
    intro d hd
    have h1 := ((hDdef d).1 hd).1
    rw [hSc] at h1
    exact (Finset.mem_sdiff.mp h1).2
  have hsep' : ∀ d ∈ D, ∀ w, G.Adj d w → w ∈ S ∨ w ∈ D := by
    intro d hd w hadj
    by_cases hwS : w ∈ S
    · exact Or.inl hwS
    · refine Or.inr (component_sep G hDdef d hd w ?_ hadj)
      simp [hSc, Finset.mem_sdiff, hwS]
  have hbU : b ∉ S ∪ D := by simp [Finset.mem_union, hbS, hbD]
  have hUlt : (S ∪ D).card < Fintype.card V := by
    rw [← Finset.card_univ]
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨b, Finset.mem_univ b, hbU⟩
  have hRSH : ∀ T : Finset V, T ⊆ S ∪ D → T.Nonempty → ∃ a ∈ T, RSimplicial G T a := by
    intro T hTU hTne
    have hTlt : T.card < Fintype.card V := lt_of_le_of_lt (Finset.card_le_card hTU) hUlt
    obtain ⟨z, hz⟩ := ih_ind T hTlt hTne
    refine ⟨z.val, ?_, rsimplicial_of_induce_simplicial G T z hz⟩
    have hzmem := z.property
    rwa [Finset.mem_coe] at hzmem
  obtain ⟨z, hzD, hzS⟩ := exists_simplicial_in_componentU G (S ∪ D) hRSH S hCclique D
    (Finset.Subset.refl _) hDC hDne hDconn hsep'
  exact ⟨z, hzS⟩

/-- **Dirac-1**, general (polymorphic) form, proved by strong induction on `Fintype.card`. -/
private theorem dirac_gen :
    ∀ (n : ℕ) {U : Type*} [Fintype U] (G : SimpleGraph U),
      Fintype.card U = n → IsChordal G → Nonempty U → ∃ v : U, IsSimplicial G v := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U _ G hcard hG hne
    have ih_ind : ∀ (W : Finset U), W.card < Fintype.card U → W.Nonempty →
        ∃ z : (↑W : Set U), IsSimplicial (G.induce (↑W : Set U)) z := by
      intro W hW hWne
      obtain ⟨w0, hw0⟩ := hWne
      exact ih W.card (by rw [hcard] at hW; exact hW)
        (G.induce (↑W : Set U)) (Fintype.card_coe W) (hG.induce _) ⟨⟨w0, hw0⟩⟩
    by_cases hcomp : ∀ u w : U, u ≠ w → G.Adj u w
    · obtain ⟨v0⟩ := hne
      exact ⟨v0, fun p _ q _ hpq => hcomp p q hpq⟩
    · by_cases hconn : G.Connected
      · push Not at hcomp
        obtain ⟨a, b, hab, hnadj⟩ := hcomp
        exact dirac_step_separator G hG hab hnadj ih_ind
      · exact dirac_step_disconnected G hconn hne ih_ind


/-- **Dirac-1 (A3a).** A nonempty chordal graph has a simplicial vertex.
Proof: induction on `|V|`; complete graph — any vertex; disconnected — recurse into a
component; connected non-complete — a minimal separator `S` (a clique by the engine) and a component
`C`, the standard argument yields a simplicial vertex of `G` inside `C`. -/
private theorem dirac_simplicial [Finite V] (G : SimpleGraph V) (hG : IsChordal G)
    (hne : Nonempty V) : ∃ v : V, IsSimplicial G v := by
  have := Fintype.ofFinite V
  exact dirac_gen (Fintype.card V) G rfl hG hne


/-! ### Bridges between the `Finset`-based and `Set`-based separator notions. -/

private theorem avoidReach_iff_set (G : SimpleGraph V) (S : Finset V) (a b : V) :
    AvoidReach G S a b ↔
      Relation.ReflTransGen (fun p q => p ∉ (↑S : Set V) ∧ q ∉ (↑S : Set V) ∧ G.Adj p q) a b := by
  constructor
  · intro h
    have hrel : (fun p q : V => p ∉ S ∧ q ∉ S ∧ G.Adj p q) ≤
        (fun p q : V => p ∉ (↑S : Set V) ∧ q ∉ (↑S : Set V) ∧ G.Adj p q) := by
      intro p q hpq
      simpa using hpq
    exact (Relation.ReflTransGen.mono hrel) a b h
  · intro h
    have hrel : (fun p q : V => p ∉ (↑S : Set V) ∧ q ∉ (↑S : Set V) ∧ G.Adj p q) ≤
        (fun p q : V => p ∉ S ∧ q ∉ S ∧ G.Adj p q) := by
      intro p q hpq
      simpa using hpq
    exact (Relation.ReflTransGen.mono hrel) a b h

private theorem separatesF_iff_set (G : SimpleGraph V) (S : Finset V) (a b : V) :
    SeparatesF G S a b ↔ G.Separates (↑S) a b := by
  unfold SeparatesF Separates
  rw [avoidReach_iff_set]
  simp

private theorem isMinimalSeparatorF_of_set (G : SimpleGraph V) {S : Finset V} {a b : V}
    (hS : G.IsMinimalSeparator (↑S) a b) : IsMinimalSeparatorF G S a b := by
  refine ⟨(separatesF_iff_set G S a b).2 hS.1, ?_⟩
  intro T hT hsep
  exact hS.2 (↑T) (Finset.coe_ssubset.2 hT) ((separatesF_iff_set G T a b).1 hsep)

end DiracPort


/-- In a chordal graph, every finite minimal separator of two fixed vertices is a clique. -/
theorem IsChordal.minimalSeparator_isClique (hG : G.IsChordal)
    {S : Finset V} {a b : V} (hS : G.IsMinimalSeparator (S : Set V) a b) :
    G.IsClique (S : Set V) :=
  minimal_separator_isClique G hG (isMinimalSeparatorF_of_set G hS)

/-- **Dirac's theorem (1961).** A nonempty finite chordal graph has a simplicial vertex. -/
theorem IsChordal.exists_isSimplicial [Finite V] [Nonempty V]
    (hG : G.IsChordal) : ∃ v : V, G.IsSimplicial v :=
  dirac_simplicial G hG inferInstance

/-- Relative reachability on `Finset.univ` follows from ordinary reachability. -/
private theorem rreach_univ_of_reachable [Fintype V] {a b : V} (h : G.Reachable a b) :
    RReach G Finset.univ a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons hadj p ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨Finset.mem_univ _, Finset.mem_univ _, hadj⟩) ih

/-- **Connected case of Dirac's two-vertex conclusion.** A connected non-complete finite chordal
graph has two distinct non-adjacent simplicial vertices. -/
theorem IsChordal.exists_two_nonadj_isSimplicial [Finite V]
    (hG : G.IsChordal) (hconn : G.Connected) (hnc : ¬ ∀ u v : V, u ≠ v → G.Adj u v) :
    ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y ∧ G.IsSimplicial x ∧ G.IsSimplicial y := by
  classical
  have := Fintype.ofFinite V
  -- Every nonempty subset has a relatively-simplicial vertex, via Dirac-1 on the induced subgraph.
  have hRSH : ∀ T : Finset V, T ⊆ Finset.univ → T.Nonempty →
      ∃ a ∈ T, RSimplicial G T a := by
    intro T _ hTne
    obtain ⟨w0, hw0⟩ := hTne
    obtain ⟨z, hz⟩ := dirac_simplicial (G.induce (↑T : Set V)) (hG.induce _)
      ⟨⟨w0, hw0⟩⟩
    refine ⟨z.val, ?_, rsimplicial_of_induce_simplicial G T z hz⟩
    have hzmem := z.property
    rwa [Finset.mem_coe] at hzmem
  -- `Finset.univ` is relatively connected.
  have hRConn : RConn G Finset.univ := by
    intro a _ b _
    exact rreach_univ_of_reachable (hconn a b)
  -- Non-completeness in the relative sense.
  have hnc' : ¬ ∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ, a ≠ b → G.Adj a b := by
    intro h; exact hnc (fun u v huv => h u (Finset.mem_univ _) v (Finset.mem_univ _) huv)
  obtain ⟨a, _, b, _, hab, hnadj, ha, hb⟩ :=
    rdirac2U G Finset.univ hRSH (Fintype.card V) Finset.univ (Finset.subset_univ _)
      (Finset.card_univ) hRConn hnc'
  refine ⟨a, b, hab, hnadj, ?_, ?_⟩
  · exact isSimplicial_of_rsimplicial G (fun c _ => Finset.mem_univ _) ha
  · exact isSimplicial_of_rsimplicial G (fun c _ => Finset.mem_univ _) hb

end SimpleGraph
