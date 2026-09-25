/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Config
import Mathlib.Data.DFinsupp.Multiset

/-! # Orientation -/
open Multiset Finset

/-!
## Orientations of chip-firing graphs

This file defines orientations of chip-firing graphs and establishes their relationship to
divisors, configurations, and the Riemann-Roch theorem.

An *orientation* (`CFOrientation G`) assigns a direction to each edge of $G$. The key
objects are:
- `indeg G O v`: the in-degree of vertex $v$ under orientation $\mathcal{O}$.
- `ordiv G O`: the divisor $D(\mathcal{O})$ assigning $\mathrm{indeg}(v) - 1$ to each vertex.
- `orientationToConfig G O q`: the configuration $c(\mathcal{O})$ for acyclic orientations
  with unique source $q$.

The main results are:
- **Theorem 4.8**: There is a bijection between acyclic orientations
  with unique source $q$ and maximal superstable configurations
  (`orientation_superstable_bijection`).
- The divisor of an acyclic orientation is unwinnable (`ordiv_unwinnable`).
- The canonical divisor $K_G = D(\mathcal{O}) + D(\overline{\mathcal{O}})$ where
  $\overline{\mathcal{O}}$ is the reverse orientation (`divisor_reverse_orientation`).
- The degree of the canonical divisor is $2g-2$ (`degree_of_canonical_divisor`).

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8.
-/

/-- An *orientation* of $G$ assigns a direction to each edge.

The field `directedEdges` is a multiset of directed pairs. The `count_preserving` field
ensures that the total flow between $v$ and $w$ equals the edge multiplicity, and
-/
structure CFOrientation (G : CFGraph) where
  /-- The multiset of directed edges in the orientation. -/
  directedEdges : Multiset (G.V × G.V)
  /-- The total directed flow between two vertices preserves the graph's edge multiplicity. -/
  count_preserving : ∀ v w,
    numEdges G v w =
    Multiset.count (v, w) directedEdges + Multiset.count (w, v) directedEdges

/-- The flow from $u$ to $v$ under an orientation $\mathcal{O}$ is the multiplicity of
the directed edge $(u,v)$. -/
abbrev flow {G: CFGraph} (O : CFOrientation G) (u v : G.V) : ℕ :=
  Multiset.count (u,v) O.directedEdges

/-- The total flow on an undirected edge equals its multiplicity. -/
private lemma opp_flow {G : CFGraph} (O : CFOrientation G) (u v : G.V) :
  flow O u v + flow O v u= (numEdges G u v) := by
  rw[O.count_preserving u v]

/-- Two orientations are equal if and only if they assign the same flow to every directed pair. -/
private lemma eq_orient {G : CFGraph} (O1 O2 : CFOrientation G) : O1 = O2 ↔ ∀ (u v : G.V), flow O1 u v = flow O2 u v := by
  constructor
  · intro h_eq u v
    rw [h_eq]
  -- Converse
  · intro h_flow_eq
    have h_directed_edges_eq : O1.directedEdges = O2.directedEdges := by
      apply Multiset.ext.mpr
      intro ⟨u,v⟩
      specialize h_flow_eq u v
      exact h_flow_eq
    cases O1
    cases O2
    cases h_directed_edges_eq
    rfl

/-- Rewrites a double sum over a finite type as a sum over ordered pairs. -/
private lemma double_sum {T : Type*} [DecidableEq T] [Fintype T] (f : T × T → ℕ) :
    ∑ (u : T), ∑ (v : T), f ⟨u, v⟩ = ∑ (e : T × T), f e := by
  rw [← Finset.sum_product]
  simp only [univ_product_univ]

/-- The multiset of directed edges in an orientation has the same cardinality as the
underlying multiset of graph edges. -/
private lemma card_directed_edges_eq_card_edges {G : CFGraph} (O : CFOrientation G) : Multiset.card  O.directedEdges = Multiset.card G.edges := by
  have hms (M : Multiset (G.V × G.V)): ∀ e ∈ M, e ∈ univ := by
      intro e _
      exact mem_univ e

  let f (u v : G.V) := flow O u v
  let g (u v : G.V) := Multiset.count ⟨u,v⟩ G.edges
  have h_uv (u v : G.V) : f u v + f v u = g u v + g v u := by
    have h := O.count_preserving u v
    dsimp only [flow, f, g]
    dsimp only [numEdges] at h
    rw [← h]
    rw [← Multiset.sum_count_eq_card (hms ((Multiset.filter (fun e ↦ e = (u, v) ∨ e = (v, u)) G.edges)))]
    -- Now simplify the count of a in the filtered multiset
    have h_msum (u v : G.V) : Multiset.filter (λ e => e = (u, v) ∨ e = (v, u)) G.edges = Multiset.filter (λ e => e = ⟨u,v⟩) G.edges + Multiset.filter (λ e => e = ⟨v,u⟩) G.edges := by
      apply Multiset.ext.mpr
      intro e
      simp only [count_add]
      repeat rw [Multiset.count_filter]
      by_cases h_e : e = ⟨u,v⟩
      · -- case: e = ⟨u,v⟩
        simp only [h_e, Prod.mk.injEq, true_or, ↓reduceIte, Nat.left_eq_add, ite_eq_right_iff,
            count_eq_zero, and_imp]
        intro h_eq _
        rw [h_eq]
        exact G.loopless v
      · -- case: e ≠ ⟨u,v⟩
        by_cases h_e' : e = ⟨v,u⟩
        · -- case: e = ⟨v,u⟩
          simp only [h_e', Prod.mk.injEq, or_true, ↓reduceIte, Nat.right_eq_add, ite_eq_right_iff,
              count_eq_zero, and_imp]
          intro h_eq _
          rw [h_eq]
          exact G.loopless u
        · -- case: e ≠ ⟨v,u⟩
          simp only [h_e, h_e', or_self, ↓reduceIte, add_zero]
    rw [h_msum]
    simp only [count_add]
    rw [sum_add_distrib]
    simp only [count_filter, sum_ite_eq', mem_univ, ↓reduceIte]
  have lhs : ∑ u: G.V, ∑ v : G.V, (f u v + f v u)= 2 * Multiset.card O.directedEdges := by
    simp only [sum_add_distrib]
    dsimp only [flow, f]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← two_mul]
    have h_replace := double_sum (λ e : G.V × G.V => Multiset.count e O.directedEdges)
    simp only [h_replace]
    simp only [mem_univ, implies_true, sum_count_eq_card]
  have rhs : ∑ u : G.V, ∑ v : G.V, (g u v + g v u) = 2 * Multiset.card G.edges := by
    simp only [sum_add_distrib]
    dsimp only [g]
    nth_rewrite 2 [Finset.sum_comm]
    rw [← two_mul]
    have h_replace := double_sum (λ e : G.V × G.V => Multiset.count e G.edges)
    simp only [h_replace]
    simp only [mem_univ, implies_true, sum_count_eq_card]
  simp only [h_uv] at lhs
  rw [lhs] at rhs
  linarith

/-- The number of edges directed into a vertex under an orientation. -/
def indeg (G : CFGraph) (O : CFOrientation G) (v : G.V) : ℕ :=
  Multiset.card (O.directedEdges.filter (λ e => e.snd = v))

/-- The in-degree of $v$ equals the sum of flows into $v$ from all vertices. -/
private lemma indeg_eq_sum_flow {G : CFGraph} (O : CFOrientation G) (v : G.V) :
  indeg G O v = ∑ w : G.V, flow O w v := by
  dsimp only [indeg, flow]
  suffices h_eq : (∀ S : Multiset (G.V × G.V) , ∀ v : G.V,
    Multiset.card (S.filter (λ e => e.snd = v)) = ∑ u : G.V, Multiset.count (u, v) S) by
    exact h_eq O.directedEdges v
  -- Prove by induction on the set of directed edges, following the pattern of the proof of
  -- degree_eq_total_flow in Basic.lean. I suspect the two can be unified.
  intro S v
  induction S using Multiset.induction_on with
  | empty =>
    simp only [filter_zero, Multiset.card_zero]
    simp only [notMem_zero, not_false_eq_true, count_eq_zero_of_notMem, sum_const_zero]
  | cons e S ih =>
    simp only [Multiset.filter_cons, card_add, count_cons, sum_add_distrib]
    rw [ih]
    nth_rewrite 1 [add_comm]
    apply add_left_cancel_iff.mpr
    obtain ⟨eu,ev⟩ := e
    by_cases h_ev_eq_v : ev = v
    · -- Case ev = v
      rw [h_ev_eq_v]
      simp only [↓reduceIte, Multiset.card_singleton, Prod.mk.injEq, and_true, sum_ite_eq',
          mem_univ]
    · -- Case ev ≠ v
      rw [ite_eq_right h_ev_eq_v, Multiset.card_zero]
      -- Flip the sides of the equation in the goal
      have : ∑ x : G.V, (if (x, v) = (eu, ev) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Prod.mk.injEq, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
        intro _
        contrapose! h_ev_eq_v
        rw [h_ev_eq_v]
      -- refine Finset.sum_eq_zero ?_
      rw [this]


/-- The number of edges directed out of a vertex under an orientation. -/
def outdeg (G : CFGraph) (O : CFOrientation G) (v : G.V) : ℕ :=
  Multiset.card (O.directedEdges.filter (λ e => e.fst = v))

/-- A vertex is a source if it has no incoming edges. -/
def isSource (G : CFGraph) (O : CFOrientation G) (v : G.V) : Prop :=
  indeg G O v = 0

/-- The proposition `directedEdge G O u v` holds when there is a directed edge from $u$
to $v$ in orientation $\mathcal{O}$. -/
def directedEdge (G : CFGraph) (O : CFOrientation G) (u v : G.V) : Prop :=
  (u, v) ∈ O.directedEdges

/-- A directed path in a graph under an orientation. -/
structure DirectedPath {G : CFGraph} (O : CFOrientation G) where
  /-- The sequence of vertices in the path. -/
  vertices : List G.V
  /-- The path is nonempty. -/
  non_empty : vertices.length > 0
  /-- Every consecutive pair forms a directed edge. -/
  valid_edges : List.IsChain (directedEdge G O) vertices

/-- A directed path is *non-repeating* if its vertex list has no duplicates. -/
def nonRepeating {G: CFGraph} {O : CFOrientation G} (p : DirectedPath O) : Prop :=
  p.vertices.Nodup

/-- A non-repeating directed path has length at most $|V(G)|$. -/
private lemma path_length_bound {G : CFGraph} {O : CFOrientation G} (p : DirectedPath O) :
  nonRepeating p → p.vertices.length ≤ Fintype.card G.V := by
  intro h_distinct
  exact List.Nodup.length_le_card h_distinct

/-- An orientation is acyclic if every directed path has no repeated vertices. -/
def isAcyclic (G : CFGraph) (O : CFOrientation G) : Prop :=
  ∀ (p : DirectedPath O), nonRepeating p

/-- Vertices that are not sources must have at least one incoming edge. -/
private lemma indeg_ge_one_of_not_source (G : CFGraph) (O : CFOrientation G) (v : G.V) :
    ¬ isSource G O v → indeg G O v ≥ 1 := by
  intro h_not_source -- h_not_source : isSource G O v = false
  unfold isSource at h_not_source -- h_not_source : (decide (indeg G O v = 0)) = false
  apply Nat.one_le_iff_ne_zero.mpr -- Goal is indeg G O v ≠ 0
  intro h_eq_zero -- Assume indeg G O v = 0
  exact h_not_source h_eq_zero

/-- For vertices that are not sources, $\mathrm{indeg}(v)-1$ is nonnegative. -/
private lemma indeg_minus_one_nonneg_of_not_source (G : CFGraph) (O : CFOrientation G) (v : G.V) :
    ¬ isSource G O v → 0 ≤ (indeg G O v : ℤ) - 1 := by
  intro h_not_source
  have h_indeg_ge_1 : indeg G O v ≥ 1 := indeg_ge_one_of_not_source G O v h_not_source
  apply Int.sub_nonneg_of_le
  exact Nat.cast_le.mpr h_indeg_ge_1


/-- In an acyclic orientation, every nonempty subset of vertices contains a vertex with no
incoming flow from within the subset (a relative source). -/
private lemma subset_source (G : CFGraph) (O : CFOrientation G) (S : Finset G.V):
  S.Nonempty → isAcyclic G O → ∃ v ∈ S, ∀ w ∈ S, flow O w v = 0 := by
  intro S_nonempty h_acyclic
  by_contra! no_sourceless

  let S_path (p : DirectedPath O) : Prop :=
    ∀ v ∈ p.vertices, v ∈ S

  have arb_path (n : ℕ) : ∃ (p : DirectedPath O), S_path p ∧ p.vertices.length = n + 1:= by
    induction n with
    | zero =>
    · -- Base case: n = 0
      -- Create a list consisting of v only
      rcases S_nonempty with ⟨v, h_v_in_S⟩
      use {
        vertices := [v],
        non_empty := by
          simp only [List.length_cons, List.length_nil, zero_add, gt_iff_lt, Order.lt_one_iff],
        valid_edges := List.isChain_singleton v
      }
      simp only [List.length_cons, List.length_nil, zero_add, and_true]
      intro u h_u_in_path
      rw [List.mem_singleton] at h_u_in_path
      rw [h_u_in_path]
      exact h_v_in_S
    | succ n ih =>
    · -- Inductive step: assume true for n, prove for n + 1
      rcases ih with ⟨p, h_len⟩
      cases hp: p.vertices with
      | nil =>
        -- This case should not happen since p.vertices has length n + 1 ≥ 1
        exfalso
        rw [hp] at h_len
        simp only [List.length_nil, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero,
            and_false] at h_len
      | cons v p' =>
        specialize no_sourceless v
        have v_S : v ∈ S := h_len.1 v (by simp only [hp, List.mem_cons, true_or])
        rcases (no_sourceless v_S) with h_no_parent
        rcases h_no_parent with ⟨u, h_u⟩
        let new_path : List G.V := u :: p.vertices
        use {
          vertices := new_path,
          non_empty := by
            rw [List.length_cons]
            exact Nat.succ_pos _,
          valid_edges := by
            dsimp only [new_path]
            cases h_case : p.vertices with
            | nil =>
              -- Path was just [v], so new path is [u, v]
              simp only [List.IsChain.singleton]
            | cons v' vs =>
              have eq_vv': v = v' := by
                rw [h_case] at hp
                simp only [List.cons.injEq] at hp
                obtain ⟨h,_⟩ := hp
                rw [h]
              rw [← eq_vv']
              constructor
              -- Show the new first link is a directed edge
              have := h_u.2
              dsimp only [flow, ne_eq] at this
              contrapose! this with h_no_edge
              simp only [count_eq_zero]
              exact h_no_edge
              -- Now show the rest of the path is valid
              have h_rec := p.valid_edges
              rw [h_case] at h_rec
              rw [← eq_vv'] at h_rec
              exact h_rec
        }
        -- Show that the path lies in S
        constructor
        intro v h_v_in_path
        simp only at h_v_in_path
        dsimp only [new_path] at h_v_in_path
        cases h_v_in_path with
        | head h_eq_v =>
          exact h_u.1
        | tail _ h_v_in_tail =>
          exact h_len.1 v h_v_in_tail
        -- Show the length is n + 2
        rw [List.length_cons]
        rw [h_len.2]
  specialize arb_path (Fintype.card G.V)
  rcases arb_path with ⟨p, h_len⟩
  have ineq := path_length_bound p (h_acyclic p)
  linarith

/-- A nonempty graph with an acyclic orientation has at least one source. -/
private lemma acyclic_has_source (G : CFGraph) (O : CFOrientation G) :
  isAcyclic G O → ∃ v : G.V, isSource G O v := by
  intro h_acyclic
  have h := subset_source G O Finset.univ Finset.univ_nonempty h_acyclic
  rcases h with ⟨v, _, h_source⟩
  use v
  dsimp only [isSource]
  rw [indeg_eq_sum_flow]
  apply Finset.sum_eq_zero
  exact h_source

/-- If every source of an acyclic orientation must equal $q$, then $q$ is itself a source. -/
private lemma is_source_of_unique_source {G : CFGraph} (O : CFOrientation G) {q : G.V} (h_acyclic : isAcyclic G O)
    (h_unique_source : ∀ w, isSource G O w → w = q) :
  isSource G O q := by
  rcases acyclic_has_source G O h_acyclic with ⟨q', h_q'⟩
  specialize h_unique_source q'
  have := h_unique_source h_q'
  rw [this] at h_q'
  exact h_q'

/-- The proposition `acyclicWithUniqueSource G O q` means that $\mathcal{O}$ is acyclic
and every source of $\mathcal{O}$ is equal to $q$. -/
def acyclicWithUniqueSource (G : CFGraph) (O : CFOrientation G) (q : G.V) : Prop :=
  isAcyclic G O ∧ ∀ w, isSource G O w → w = q

/-- In an acyclic orientation with unique source $q$, the vertex $q$ is a source. -/
private lemma source_of_acyclic_with_unique_source {G : CFGraph} {O : CFOrientation G} {q : G.V}
    (hO : acyclicWithUniqueSource G O q) : isSource G O q :=
  is_source_of_unique_source O hO.1 hO.2


/-- The configuration associated to an acyclic orientation with unique source $q$ assigns
$\mathrm{indeg}(v)-1$ chips to each vertex $v \ne q$, and $0$ at $q$. -/
def configOfSource {G : CFGraph} {O : CFOrientation G} {q : G.V}
    (hO : acyclicWithUniqueSource G O q) : Config G q :=
  { chips := λ v => if v = q then 0 else (indeg G O v : ℤ) - 1,
    q_zero := by simp only [↓reduceIte]
    non_negative := by
      intro v
      simp only [ge_iff_le]
      split_ifs with h_eq
      · linarith
      · have h_not_source : ¬ isSource G O v := by
          intro hs_v
          exact h_eq (hO.2 v hs_v)
        exact indeg_minus_one_nonneg_of_not_source G O v h_not_source
  }

/-!
## Orientation divisors and configurations

For an orientation $\mathcal{O}$ of $G$, the *orientation divisor* `ordiv G O` is
$D(\mathcal{O})(v) = \mathrm{indeg}_{\mathcal{O}}(v) - 1$.

For an acyclic orientation $\mathcal{O}$ with unique source $q$, the associated
*configuration* `orientationToConfig G O q` assigns $\mathrm{indeg}(v) - 1$ chips to
each vertex $v \ne q$. An acyclic orientation is uniquely determined by its in-degree
sequence (`orientation_determined_by_indegrees`), and the divisor of an acyclic orientation
is always $q$-reduced and unwinnable.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 4.7.
-/

/-- The divisor associated with an orientation assigns $\mathrm{indeg}(v)-1$ to each vertex.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 4.7,
part 1; written $D(\mathcal{O})$ there. -/
def ordiv (G : CFGraph) (O : CFOrientation G) : CFDiv G :=
  λ v => indeg G O v - 1

/-- The orientation divisor `ordiv G O` bundled as a $q$-effective divisor, using
acyclicity to prove $q$-effectivity. -/
def orqed {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclicWithUniqueSource G O q) : qEffectiveDivisor G q := {
      D := ordiv G O,
      h_eff := by
        intro v v_ne_q
        dsimp only [ordiv]
        contrapose! v_ne_q with v_q
        have h_indeg : indeg G O v = 0 := by
          linarith
        rw [indeg_eq_sum_flow] at h_indeg
        -- Sum of non-negative terms is zero, so each term is zero
        apply hO.2
        contrapose! h_indeg with h_not_source
        dsimp only [isSource] at h_not_source
        rw [indeg_eq_sum_flow] at h_not_source
        intro h_bad
        rw [h_bad] at h_not_source
        simp only [not_true_eq_false] at h_not_source
    }

/-- The configuration $c(\mathcal{O})$ associated to an acyclic orientation $\mathcal{O}$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 4.7
(part 2). -/
def orientationToConfig (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclicWithUniqueSource G O q) : Config G q :=
  configOfSource hO

/-- The configuration associated to an orientation records the expected in-degree data. -/
private lemma orientation_to_config_indeg (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclicWithUniqueSource G O q) (v : G.V) :
    (orientationToConfig G O q hO).chips v =
    if v = q then 0 else (indeg G O v : ℤ) - 1 := by
  -- This follows directly from the definition of configOfSource
  simp only [orientationToConfig] at *
  -- Use the definition of configOfSource
  exact rfl



/-- The configuration associated to an orientation agrees with the configuration obtained
from its orientation divisor. -/
lemma config_and_divisor_from_O {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclicWithUniqueSource G O q) :
  orientationToConfig G O q hO = toConfig (orqed O hO) := by
  let c := orientationToConfig G O q hO
  let D := orqed O hO
  rw [eq_config_iff_eq_chips]
  funext v
  by_cases h_v: v = q
  · -- Case v = q
    rw [h_v]
    have (c d : Config G q) : c.chips q = d.chips q := by
      rw [c.q_zero, d.q_zero]
    rw [this]
  · -- Case v ≠ q
    dsimp only [orientationToConfig, configOfSource, orqed, toConfig, ordiv, Pi.sub_apply,
        Pi.smul_apply, Int.zsmul_eq_mul]
    simp only [h_v, ↓reduceIte, ne_eq, not_false_eq_true, one_chip_apply_other', mul_zero, sub_zero]


-- The double-counting lemmas `sum_filter_eq_map` and `sum_card_filter_eq_mul` used below
-- are proved at the end of Basic.lean.




/-- An acyclic orientation is uniquely determined by its in-degree sequence.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Lemma 4.3. -/
lemma orientation_determined_by_indegrees {G : CFGraph}
  (O O' : CFOrientation G) :
  isAcyclic G O → isAcyclic G O' →
  (∀ v : G.V, indeg G O v = indeg G O' v) →
  O = O' := by
  intro h_acyc h_acyc' h_indeg_eq

  let S := { e : G.V × G.V | O.directedEdges.count e > O'.directedEdges.count e }
  have suff_S_empty : S = ∅ → O = O' := by
    intro h_S_empty
    have h_ineq (u v : G.V) : flow O u v ≤ flow O' u v := by
      have h_nin: ⟨u,v⟩ ∉ S := by
        rw [h_S_empty]
        simp only [Set.mem_empty_iff_false, not_false_eq_true]
      dsimp only [Set.mem_ofPred_eq, S] at h_nin
      linarith
    simp only [eq_orient O O']
    intro u v
    by_contra h_neq
    have h_uv_le := h_ineq u v
    have h_lt : flow O u v < flow O' u v := lt_of_le_of_ne h_uv_le h_neq
    have h_indeg_contra : indeg G O v < indeg G O' v := by
      rw [indeg_eq_sum_flow O v, indeg_eq_sum_flow O' v]
      apply Finset.sum_lt_sum
      intro x hx
      exact h_ineq x v
      use u
      simp only [mem_univ, h_lt, and_self]
    linarith [h_indeg_eq v]
  apply suff_S_empty

  -- A small helper we'll need a couple time later
  have directed_edge_of_S (e : G.V × G.V) : e ∈ S → directedEdge G O e.1 e.2 :=  by
    dsimp only [directedEdge]
    intro h
    dsimp only [Set.mem_ofPred_eq, S] at h
    have h_pos_count : count e O.directedEdges > 0 := by
      omega
    apply Multiset.count_pos.mp
    exact h_pos_count

  -- We now must show that S is empty.
  -- Do so by showing any element in S belongs to an infinite directed path
  have going_up : ∀ e ∈ S, ∃ f ∈ S, f.2 = e.1 := by
    intro e h_e_in_S
    obtain ⟨u,v⟩ := e
    by_contra! h_no_parent
    have all_flow_le : ∀ (w : G.V) , flow O w u ≤ flow O' w u := by
      intro w
      by_contra h_flow_gt
      apply lt_of_not_ge at h_flow_gt
      specialize h_no_parent ⟨w,u⟩
      simp only [ne_eq, not_true_eq_false, imp_false] at h_no_parent
      exact h_no_parent h_flow_gt
    have one_flow_lt : ∃ (w : G.V), flow O w u < flow O' w u := by
      contrapose! h_e_in_S
      dsimp only [Set.mem_ofPred_eq, S]
      suffices flow O u v ≤ flow O' u v by linarith
      specialize h_e_in_S v
      by_contra flow_lt
      apply lt_of_not_ge at flow_lt
      have edges_lt := add_lt_add_of_le_of_lt h_e_in_S flow_lt
      rw [opp_flow O v u, opp_flow O' v u] at edges_lt
      linarith

    have h: ∑ (w : G.V), flow O w u < ∑ (w : G.V), flow O' w u := by
      apply Finset.sum_lt_sum
      intro i _
      exact all_flow_le i
      rcases one_flow_lt with ⟨w, h_flow_lt⟩
      use w
      constructor
      simp only [mem_univ]
      exact h_flow_lt

    repeat rw [← indeg_eq_sum_flow] at h
    specialize h_indeg_eq u
    linarith

  -- Suppose S is nonempty, and consider the set T of vertices where an edge of S
  -- originates. By going_up, every vertex of T receives positive flow from another
  -- vertex of T, contradicting the relative source provided by subset_source.
  by_contra! h_S_nonempty
  rcases h_S_nonempty with ⟨e_start, h_e_start_in_S⟩
  classical
  let T : Finset G.V := Finset.univ.filter (fun v => ∃ e ∈ S, e.1 = v)
  have h_mem_T : ∀ v : G.V, v ∈ T ↔ ∃ e ∈ S, e.1 = v := by
    intro v
    simp only [Prod.exists, exists_and_right, exists_eq_right, Finset.mem_filter, mem_univ,
        true_and, T]
  have h_T_nonempty : T.Nonempty :=
    ⟨e_start.1, (h_mem_T e_start.1).mpr ⟨e_start, h_e_start_in_S, rfl⟩⟩
  obtain ⟨v, h_v_T, h_v_source⟩ := subset_source G O T h_T_nonempty h_acyc
  obtain ⟨e, h_e_S, h_e_fst⟩ := (h_mem_T v).mp h_v_T
  obtain ⟨f, h_f_S, h_f_snd⟩ := going_up e h_e_S
  have h_flow_pos : 0 < flow O f.1 v := by
    rw [← h_e_fst, ← h_f_snd]
    exact Multiset.count_pos.mpr (directed_edge_of_S f h_f_S)
  have h_flow_zero : flow O f.1 v = 0 :=
    h_v_source f.1 ((h_mem_T f.1).mpr ⟨f, h_f_S, rfl⟩)
  omega

/-- Two acyclic orientations with unique source $q$ that give the same configuration are equal. -/
private theorem config_to_orientation_unique (G : CFGraph) (q : G.V)
    (c : Config G q)
    (O₁ O₂ : CFOrientation G)
    (hO₁ : acyclicWithUniqueSource G O₁ q)
    (hO₂ : acyclicWithUniqueSource G O₂ q)
    (h_eq₁ : orientationToConfig G O₁ q hO₁ = c)
    (h_eq₂ : orientationToConfig G O₂ q hO₂ = c) :
    O₁ = O₂ := by
  apply orientation_determined_by_indegrees O₁ O₂ hO₁.1 hO₂.1
  intro v

  have h_deg₁ := orientation_to_config_indeg G O₁ q hO₁ v
  have h_deg₂ := orientation_to_config_indeg G O₂ q hO₂ v

  have h_config_eq : (orientationToConfig G O₁ q hO₁).chips v =
                     (orientationToConfig G O₂ q hO₂).chips v := by
    rw [h_eq₁, h_eq₂]

  by_cases hv : v = q
  · -- Case v = q: Both vertices are sources, so indegree is 0
    rw [hv]
    rw [source_of_acyclic_with_unique_source hO₁, source_of_acyclic_with_unique_source hO₂]
  · -- Case v ≠ q: use vertex degree equality
    rw [h_deg₁, h_deg₂] at h_config_eq
    simp only [ite_eq_right hv] at h_config_eq
    -- From config degrees being equal, show indegrees are equal
    have h := congr_arg (fun x => x + 1) h_config_eq
    simp only [sub_add_cancel] at h
    -- Use nat cast injection
    exact (Nat.cast_inj.mp h)

/-- The degree of an orientation divisor equals $g - 1$, where $g$ is the genus of $G$. -/
lemma degree_ordiv {G : CFGraph} (O : CFOrientation G) :
  deg (ordiv G O) = (genus G) - 1 := by
  have flow_sum : deg (ordiv G O) = (∑ v : G.V, ∑ w : G.V, ↑(flow O w v)) - (Fintype.card G.V) := by
    calc
      deg (ordiv G O)
        = ∑ v : G.V, ordiv G O v := by rfl
      _ = ∑ v : G.V, (∑ w : G.V, ↑(flow O w v) - 1) := by
        apply Finset.sum_congr rfl
        intro x _
        dsimp only [ordiv]
        rw [indeg_eq_sum_flow O x]
        simp only [Nat.cast_sum]
      _ = (∑ v : G.V, ∑ w : G.V, ↑(flow O w v)) - (Fintype.card G.V) := by
        rw [Finset.sum_sub_distrib]
        simp only [sum_const, card_univ, Int.nsmul_eq_mul, mul_one]
  dsimp only [genus]
  rw [flow_sum]
  suffices h : (∑ v : G.V, ∑ w : G.V, ↑(flow O w v)) = ↑(Multiset.card G.edges) by linarith [h]
  calc
    ∑ v : G.V, ∑ w : G.V, ↑(flow O w v)
      = ∑ v : G.V, (indeg G O v) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [indeg_eq_sum_flow]
    _ = ∑ v : G.V, Multiset.card (O.directedEdges.filter (λ e => e.snd = v)) := by
      dsimp only [indeg]
    _ = ↑(Multiset.card O.directedEdges) := by
      -- Each directed edge points into exactly one vertex
      rw [sum_card_filter_eq_mul G O.directedEdges (λ v e => e.snd = v) 1 ?_, one_mul]
      intro e _
      refine Finset.card_eq_one.mpr ⟨e.2, ?_⟩
      ext x
      simp only [eq_comm, Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
    _ = ↑(Multiset.card G.edges) := by
      exact card_directed_edges_eq_card_edges O
    _ = Multiset.card G.edges := by
      rfl

/-- The configuration degree of an acyclic orientation with unique source equals the genus. -/
lemma config_degree_from_O {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclicWithUniqueSource G O q) :
  configDegree (orientationToConfig G O q hO) = genus G := by
  rw [config_and_divisor_from_O O hO]
  -- Use config_degree_div_degree to relate configDegree to deg of the underlying divisor.
  have h_q_source : indeg G O q = 0 := source_of_acyclic_with_unique_source hO
  have h1 := config_degree_div_degree (orqed O hO)
  -- (orqed O ...).D = ordiv G O definitionally, so:
  have h2 : (orqed O hO).D q = (indeg G O q : ℤ) - 1 := rfl
  have h3 : deg (orqed O hO).D = (genus G : ℤ) - 1 := degree_ordiv O
  have h4 : (indeg G O q : ℤ) = 0 := by exact_mod_cast h_q_source
  linarith

/-- The orientation divisor $D(\mathcal{O})$ of an acyclic orientation $\mathcal{O}$ is not
winnable.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Proposition 4.11. -/
lemma ordiv_unwinnable (G : CFGraph) (O : CFOrientation G) :
  isAcyclic G O → ¬ winnable G (ordiv G O) := by
  intro h_acyclic
  by_contra h_win
  let D := ordiv G O
  rcases h_win with ⟨E, E_eff, E_equiv⟩
  dsimp only [Eff] at E_eff
  dsimp only [linearEquiv] at E_equiv
  rw [principal_iff_eq_prin] at E_equiv
  rcases E_equiv with ⟨σ, h_σ⟩
  apply eq_add_of_sub_eq at h_σ

  obtain ⟨v_max, -, h_max⟩ := Finset.exists_max_image Finset.univ σ Finset.univ_nonempty
  have h_max : ∀ w : G.V, σ w ≤ σ v_max := fun w => h_max w (Finset.mem_univ w)
  let S := {v : G.V | σ v = σ v_max}
  have S_nonempty : S.Nonempty := by
    use v_max
    simp only [Set.mem_ofPred_eq, S]

  have h_lt (u : G.V) (h_u : u ∉ S):  σ u ≤ σ v_max - 1 := by
    specialize h_max u
    suffices σ u < σ v_max by linarith
    apply lt_of_le_of_ne h_max
    simp only [Set.mem_ofPred_eq, S] at h_u
    exact h_u

  suffices h_v : ∃ v ∈ S, ∀ w : G.V, flow O w v > 0 → w ∉ S by
    rcases h_v with ⟨v, h_v, h_flow⟩
    have h_prin : (prin G) σ v + indeg G O v ≤ 0 := by
      rw [prin_apply]
      rw [indeg_eq_sum_flow O v]
      have h_diff : ∀ u : G.V, σ u - σ v ≤ if u ∈ S then 0 else -1 := by
        intro u
        by_cases h_u_in_S : u ∈ S
        · simp only [h_u_in_S, ↓reduceIte, tsub_le_iff_right, zero_add]
          -- Goal is now: σ u ≤ σ v
          dsimp only [Set.mem_ofPred_eq, S] at h_u_in_S h_v
          rw [h_u_in_S,h_v]
        · simp only [h_u_in_S, ↓reduceIte, Int.reduceNeg, tsub_le_iff_right, le_neg_add_iff_add_le]
          -- Goal is now: σ u - σ v ≤ -1
          dsimp only [Set.mem_ofPred_eq, S] at h_u_in_S h_v
          have := h_lt u h_u_in_S
          rw [h_v]
          linarith [this]
      have h_diff_mul : ∀ u : G.V, (σ u - σ v) * ↑(numEdges G v u) ≤ if u ∈ S then 0 else -↑(numEdges G v u) := by
        intro u
        by_cases h_u_in_S : u ∈ S
        · simp only [h_u_in_S, ↓reduceIte]
          dsimp only [Set.mem_ofPred_eq, S] at h_u_in_S h_v
          rw [h_u_in_S,h_v]
          simp only [sub_self, zero_mul, Std.le_refl]
        · simp only [h_u_in_S, ↓reduceIte]
          have ineq := h_lt u h_u_in_S
          rw [← h_v] at ineq
          apply le_of_sub_nonneg
          rw [neg_eq_neg_one_mul, ← sub_mul]
          apply mul_nonneg
          linarith
          exact Nat.cast_nonneg _
      have h_sum : ∑ w : G.V, (σ w - σ v) * ↑(numEdges G v w) ≤ ∑ w : G.V, if w ∈ S then 0 else -↑(numEdges G v w) := by
        apply Finset.sum_le_sum
        intro u _
        specialize h_diff_mul u

        exact h_diff_mul
      suffices ∑ u : G.V, ((σ u - σ v) * ↑(numEdges G v u)) ≤ -↑ (∑ u: G.V, (flow O u v)) by linarith
      refine le_trans h_sum ?_
      apply le_of_neg_le_neg
      rw [neg_neg, Nat.cast_sum, neg_eq_neg_one_mul, mul_comm (-1), Finset.sum_mul]


      apply sum_le_sum

      intro u _
      by_cases h_u_in_S : u ∈ S
      · -- Case: u ∈ S. No edges from u to v.
        simp only [h_u_in_S]
        rw [ite_true]
        contrapose! h_flow
        use u
        norm_num at h_flow
        exact ⟨h_flow, h_u_in_S⟩
      · -- Case : u ∉ S.
        simp only [h_u_in_S, ↓reduceIte, Int.reduceNeg, mul_neg, mul_one, neg_neg, Nat.cast_le]
        -- Goal: flow O u v ≤ numEdges G v u
        rw [← opp_flow O v u]
        linarith
    specialize E_eff v
    rw [h_σ] at E_eff
    rw [Pi.add_apply] at E_eff
    dsimp only [ordiv] at E_eff
    linarith
  -- Now we must find a source of O relative to S
  let S' := Finset.filter (λ v => v ∈ S) Finset.univ
  have S'_nonempty : S'.Nonempty := by
    rcases S_nonempty with ⟨v, h_v_in_S⟩
    use v
    simp only [Finset.mem_filter, mem_univ, true_and, S']
    exact h_v_in_S
  have h := subset_source G O S' S'_nonempty h_acyclic
  rcases h with ⟨v, h_v_in_S', h_flow⟩
  use v
  simp only [Finset.mem_filter, mem_univ, true_and, S'] at h_v_in_S'
  constructor
  · exact h_v_in_S'
  · intro w h_flow_w_v
    specialize h_flow w
    by_contra!
    have : w ∈ S' := by
      simp only [Finset.mem_filter, mem_univ, true_and, S']
      exact this
    apply h_flow at this
    linarith

/-- The orientation divisor $D(\mathcal{O})$ of an acyclic orientation with unique source $q$
is $q$-reduced.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Proposition 4.11, which
asserts that $D(\mathcal{O})$ is maximal unwinnable; this lemma and `ordiv_unwinnable`
supply the unwinnability, while maximality is established in `RRGHelpers.lean`. -/
private lemma ordiv_q_reduced {G : CFGraph} (O : CFOrientation G) {q : G.V}
    (hO : acyclicWithUniqueSource G O q) : qReduced G q (ordiv G O) := by
  constructor
  · -- Show ordiv is effective away from q
    intro v h_v_ne_q
    simp only [ne_eq] at h_v_ne_q -- Now just ¬ v = q
    dsimp only [ordiv]
    suffices indeg G O v > 0  by
      linarith
    contrapose! h_v_ne_q with indeg_zero
    apply hO.2
    apply Nat.eq_zero_of_le_zero at indeg_zero
    dsimp only [isSource]
    simp only [indeg_zero]
  · -- Show no valid firing move exists for subsets not containing q
    intro S h_q_S S_nonempty hlegal
    have h_source := subset_source G O S S_nonempty hO.1
    rcases h_source with ⟨v, h_v_S, h_flow⟩
    apply (not_lt_of_ge (hlegal v h_v_S))
    dsimp only [ordiv]
    -- Cancel -1 from both sides
    apply Int.lt_of_le_sub_one
    apply sub_le_sub_right
    -- Expand indeg and compare terms
    rw [indeg_eq_sum_flow O v, Nat.cast_sum]
    -- Split the LHS sum into the x ∈ S part and the x ∉ S part
    have flow_bound (w : G.V) : flow O w v ≤ if w ∈ S then 0 else numEdges G w v := by
      by_cases h_w_in_S : w ∈ S
      · -- Case: w ∈ S
        simp only [h_w_in_S, ↓reduceIte, nonpos_iff_eq_zero, count_eq_zero]
        specialize h_flow w
        apply h_flow at h_w_in_S
        dsimp only [flow] at h_w_in_S
        -- Now deduce (w,v) ∉ O.directedEdges from count = 0.
        exact  Multiset.count_eq_zero.mp h_w_in_S
      · -- Case: w ∉ S
        simp only [h_w_in_S, ↓reduceIte]
        rw [← opp_flow O w v]
        linarith
    have sum_flow_bound : ∑ w : G.V, ↑(flow O w v) ≤ ∑ w : G.V, if w ∈ S then 0 else ↑(numEdges G w v) := by
      apply Finset.sum_le_sum
      intro u _
      specialize flow_bound u
      exact flow_bound
    rw [Finset.sum_ite, sum_const,smul_zero, zero_add] at sum_flow_bound
    -- Do some annoying casting business to remove ↑.
    rw [outdeg_S_eq_sum_filter]
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    apply Nat.cast_le.mpr
    apply le_trans sum_flow_bound
    -- Final step: we have numEdges G _ v on LHS and G v _ on the right. Use symmetry.
    simp only [num_edges_symmetric, Std.le_refl]

/-- The configuration associated to an acyclic orientation with unique source $q$ is
superstable. -/
private lemma orientation_config_superstable (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclicWithUniqueSource G O q) :
    superstable G q (orientationToConfig G O q hO) := by
    let c := orientationToConfig G O q hO
    apply (superstable_iff_q_reduced G q (genus G -1) c).mpr

    have h_c := config_and_divisor_from_O O hO
    dsimp only [c]
    rw [h_c]
    have : genus G - 1 = deg ((orqed O hO).D) := by
      simpa only [orqed] using (degree_ordiv O).symm
    rw [this]
    rw [div_of_config_of_div (orqed O hO)]
    exact ordiv_q_reduced O hO



/-!
## The canonical divisor and reverse orientations

The *canonical divisor* of $G$ is $K_G(v) = \deg(v) - 2$ for each vertex $v$.
The *reverse orientation* $\overline{\mathcal{O}}$
of an orientation $\mathcal{O}$ is obtained by reversing all edge directions. The key
identity is $D(\mathcal{O}) + D(\overline{\mathcal{O}}) = K_G$ (`divisor_reverse_orientation`).

Combining the handshaking theorem (`sum_vertex_degree_eq_twice_card_edges`, proved at the
end of `Basic.lean`) with the definition of the genus shows that $\deg(K_G) = 2g - 2$
(`degree_of_canonical_divisor`).

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 5.7.
-/

/-- The canonical divisor assigns $\deg(v)-2$ to each vertex $v$.

It is independent of orientation and equals
$D(\mathcal{O}) + D(\overline{\mathcal{O}})$. -/
def canonicalDivisor (G : CFGraph) : CFDiv G :=
  λ v => (vertexDegree G v) - 2

/-- Counting a pair in a multiset mapped by `Prod.swap` counts the swapped pair in the
original multiset. Specialization of `Multiset.count_map_eq_count'` to `Prod.swap`. -/
private lemma count_map_swap {G : CFGraph} (M : Multiset (G.V × G.V)) (v w : G.V) :
  Multiset.count (v, w) (M.map Prod.swap) = Multiset.count (w, v) M :=
  Multiset.count_map_eq_count' Prod.swap M Prod.swap_injective (w, v)

/-- The *reverse orientation* $\overline{\mathcal{O}}$ obtained by reversing all edge directions.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 5.7. -/
def CFOrientation.reverse (G : CFGraph) (O : CFOrientation G) : CFOrientation G where
  directedEdges := O.directedEdges.map Prod.swap
  count_preserving v w := by
    rw [count_map_swap, count_map_swap, add_comm]
    exact O.count_preserving v w

/-- The flow of the reverse orientation $\overline{\mathcal{O}}$ from $v$ to $w$ equals the
flow of $\mathcal{O}$ from $w$ to $v$. -/
private lemma flow_reverse {G : CFGraph} (O : CFOrientation G) (v w : G.V) :
  flow (O.reverse G) v w = flow O w v :=
  count_map_swap O.directedEdges v w

/-- The in-degree of $v$ in the reverse orientation $\overline{\mathcal{O}}$ equals the
out-degree of $v$ in $\mathcal{O}$. -/
private lemma indeg_reverse_eq_outdeg (G : CFGraph) (O : CFOrientation G) (v : G.V) :
  indeg G (O.reverse G) v = outdeg G O v := by
  classical
  simp only [indeg, outdeg]
  rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
  let O_rev_edges_def : (CFOrientation.reverse G O).directedEdges = O.directedEdges.map Prod.swap := by rfl
  conv_lhs => rw [O_rev_edges_def]
  rw [Multiset.countP_map]
  simp only [Prod.snd_swap]
  simp only [countP_eq_card_filter]

/-- The reverse of an acyclic orientation is also acyclic. -/
lemma is_acyclic_reverse_of_is_acyclic (G : CFGraph) (O : CFOrientation G)
    (h_acyclic : isAcyclic G O) :
  isAcyclic G (O.reverse G) := by
  intro p
  let q : DirectedPath O := {
    vertices := p.vertices.reverse,
    non_empty := by
      rw [List.length_reverse]
      exact p.non_empty,
    valid_edges := by
      have p_valid := p.valid_edges
      have hyp := List.isChain_reverse.mpr p_valid
      -- hyp : List.IsChain (flip (directedEdge G (CFOrientation.reverse G O))) p.vertices
      -- Need to show: List.IsChain (directedEdge G (CFOrientation.reverse G O)) p.vertices.reverse
      -- Since isChain_reverse gives us the flipped relation, we need to show
      -- flip (directedEdge G (CFOrientation.reverse G O)) = directedEdge G O
      convert hyp using 2
      ext a
      simp only [directedEdge, CFOrientation.reverse, Multiset.mem_map, Prod.exists,
          Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq, true_and, exists_eq_right]
  }
  have h_non_repeating_q : nonRepeating q := h_acyclic q
  exact List.nodup_reverse.mp h_non_repeating_q


/-- The orientation divisors of $\mathcal{O}$ and its reverse sum to the canonical divisor:
$D(\mathcal{O}) + D(\overline{\mathcal{O}}) = K_G$. -/
lemma divisor_reverse_orientation {G : CFGraph} (O : CFOrientation G)  : ordiv G O + ordiv G (O.reverse) = canonicalDivisor G := by
  let O' := O.reverse
  funext v
  rw [Pi.add_apply]
  dsimp only [ordiv, canonicalDivisor]
  suffices indeg G O v + indeg G O' v = vertexDegree G v by
    dsimp only [vertexDegree] at this ⊢
    rw [← this]
    ring
  rw [indeg_eq_sum_flow, indeg_eq_sum_flow, Nat.cast_sum, Nat.cast_sum]
  dsimp only [vertexDegree]
  rw [← sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [← opp_flow O v w]
  rw [Nat.cast_add, add_comm]
  simp only [add_left_inj, Nat.cast_inj]
  -- Goal is now: flow O' w v = flow O v w
  rw [flow_reverse O w v]

/-- The degree of the canonical divisor is $2g - 2$, where $g$ is the genus of $G$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Exercise 5.8. -/
theorem degree_of_canonical_divisor (G : CFGraph) :
    deg (canonicalDivisor G) = 2 * genus G - 2 := by
  -- Use sum_sub_distrib to split the sum
  have h1 : ∑ v, (canonicalDivisor G v) =
            ∑ v, vertexDegree G v - 2 * Fintype.card G.V := by
    unfold canonicalDivisor
    rw [sum_sub_distrib]
    simp only [sum_const, card_univ, Int.nsmul_eq_mul, sub_right_inj]
    ring
  dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [h1]

  -- Use the fact that sum of vertex degrees = 2|E|
  have h2 : ∑ v, vertexDegree G v = 2 * Multiset.card G.edges := by
    exact sum_vertex_degree_eq_twice_card_edges G
  rw [h2]

  -- Use genus definition: g = |E| - |G.V| + 1
  rw [genus]

  ring

/-!
## Orientations from burn lists

Given a complete burn list $L$ for a superstable configuration $c$, the function
`burnOrientation L h_full` constructs an acyclic orientation of $G$ with unique source $q$
(`burn_acyclic`, `burn_unique_source`). Acyclicity is proved by showing that position in
the burn list gives a strictly decreasing labeling along any directed path (`dp_dec`).

The key lemma `dp_dec` formalizes this as a strict chain of natural numbers, and
`orientationFromFlow` constructs a `CFOrientation` from an explicit flow function.
-/

/-- Create a multiset with a given count function. This is a thin wrapper around
`DFinsupp.toMultiset` specialized to a finite type. -/
def multisetOfCount {T : Type*} [DecidableEq T] [Fintype T] (f : T → ℕ) : Multiset T :=
  DFinsupp.toMultiset (DFinsupp.equivFunOnFintype.symm f)

@[simp] private lemma count_of_multiset_of_count {T : Type*} [DecidableEq T] [Fintype T]
    (f : T → ℕ) : ∀ e : T, Multiset.count e (multisetOfCount f) = f e := by
  intro e
  rw [← Multiset.toDFinsupp_apply]
  calc
    (Multiset.toDFinsupp (multisetOfCount f)) e = (DFinsupp.equivFunOnFintype.symm f) e := by
      simp only [multisetOfCount, DFinsupp.toMultiset_toDFinsupp]
    _ = f e := by
      simpa only [DFinsupp.equivFunOnFintype_apply]
          using congrFun (Equiv.apply_symm_apply DFinsupp.equivFunOnFintype f) e

/-- Constructs a `CFOrientation` from an explicit flow function, given proofs that it respects
edge multiplicities and has no bidirectional edges. -/
def orientationFromFlow {G : CFGraph} (f : G.V × G.V → ℕ) (h_count_preserving : ∀ v w : G.V, f (v,w) + f (w,v) = numEdges G v w) : CFOrientation G :=
  {
    directedEdges := multisetOfCount f,
    count_preserving := by
      intro v w
      simpa only [count_of_multiset_of_count] using (h_count_preserving v w).symm
  }

/-- The orientation constructed from a complete burn list $L$ for a superstable configuration,
via `burnFlow`. This is shown to be acyclic with unique source $q$ by `burn_acyclic` and
`burn_unique_source`. -/
def burnOrientation {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ (v :G.V), v ∈ L.list): CFOrientation G := orientationFromFlow (burnFlow L) (burn_flow_reverse L h_full)

/-- Along any directed path in `burnOrientation L`, the positions of vertices in the burn list
are strictly decreasing. This is the key lemma for proving acyclicity. -/
private lemma dp_dec {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ (v :G.V), v ∈ L.list) (p : DirectedPath (burnOrientation L h_full)) :
  List.IsChain (· > ·) (p.vertices.map (λ v => List.idxOf v L.list)) := by
  refine List.isChain_map_of_isChain (f := fun v => List.idxOf v L.list) ?_ p.valid_edges
  intro v v' h_edge
  dsimp only [directedEdge] at h_edge
  simp only [burnOrientation] at h_edge
  dsimp only [orientationFromFlow] at h_edge
  have h_count : Multiset.count ⟨v,v'⟩ (multisetOfCount (burnFlow L)) > 0 := by
    contrapose! h_edge with h_zero
    apply Nat.eq_zero_of_le_zero at h_zero
    exact Multiset.count_eq_zero.mp h_zero
  simp only [count_of_multiset_of_count, gt_iff_lt] at h_count
  dsimp only [burnFlow] at h_count
  by_contra! h_not_gt
  have : ¬ (v ∈ L.list ∧ List.idxOf v' L.list < List.idxOf v L.list) := by
    intro ⟨_, h_lt⟩
    omega
  simp only [this, ↓reduceIte, lt_self_iff_false] at h_count

/-- Every directed path in `burnOrientation L` has no repeated vertices. -/
private lemma burn_nodup {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ (v :G.V), v ∈ L.list) (p : DirectedPath (burnOrientation L h_full)) : p.vertices.Nodup := by
  let q : List ℕ := p.vertices.map (λ v => List.idxOf v L.list)
  have h_sorted : q.SortedGT := (List.sortedGT_iff_isChain).2 (dp_dec L h_full p)
  exact List.Nodup.of_map (λ v => List.idxOf v L.list) h_sorted.nodup

/-- The orientation constructed from a complete burn list is acyclic. -/
private lemma burn_acyclic {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ (v :G.V), v ∈ L.list) :
  isAcyclic G (burnOrientation L h_full) := by
  dsimp only [isAcyclic]
  intro p
  dsimp only [nonRepeating]
  exact burn_nodup L h_full p

/-- The orientation constructed from a complete burn list has $q$ as its unique source. -/
private lemma burn_unique_source {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ (v :G.V), v ∈ L.list) :
  ∀ w, isSource G (burnOrientation L h_full) w → w = q := by
  intro w h_source
  dsimp only [isSource] at h_source
  rw [indeg_eq_sum_flow (burnOrientation L h_full) w] at h_source
  dsimp only [burnOrientation, orientationFromFlow, flow] at h_source
  simp only [count_of_multiset_of_count] at h_source
  -- Remove the decide and true parts
  contrapose! h_source with h_ne
  have ineq := burnin_degree L w (h_full w) h_ne
  -- rw [Nat.cast_sum] at ineq
  have : c.chips w ≥ 0 := by
    apply c.non_negative w
  let ineq := lt_of_le_of_lt this ineq
  apply ne_of_lt at ineq
  contrapose! ineq
  rw [Nat.cast_sum]
  simp only [Finset.sum_eq_zero_iff, mem_univ, forall_const] at ineq
  simp only [ineq, CharP.cast_eq_zero, sum_const_zero]

/-- The orientation constructed from a complete burn list is acyclic with unique source $q$. -/
private lemma burn_acyclic_with_unique_source {G : CFGraph} {q : G.V} {c : Config G q}
    (L : burnList G c) (h_full : ∀ (v : G.V), v ∈ L.list) :
    acyclicWithUniqueSource G (burnOrientation L h_full) q :=
  ⟨burn_acyclic L h_full, burn_unique_source L h_full⟩



/-!
## The bijection between orientations and maximal superstable configurations

This section establishes Theorem 4.8: there is a bijection between
acyclic orientations with unique source $q$ and maximal superstable configurations.

- `superstable_dhar`: given a superstable configuration $c$, Dhar's algorithm produces an
  acyclic orientation whose associated configuration dominates $c$.
- `orientation_config_maximal`: Every acyclic orientation with unique source $q$ gives a
  maximal superstable configuration.
- `maximal_superstable_orientation`: Every maximal superstable configuration arises from
  some acyclic orientation.
- `orientation_superstable_bijection`: The full bijection statement.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8.
-/

/-- Dhar's burning algorithm produces, from a superstable configuration, an orientation whose
associated configuration dominates it. -/
theorem superstable_dhar {G : CFGraph} {q : G.V} {c : Config G q} (h_ss : superstable G q c) :
    ∃ (O : CFOrientation G) (hO : acyclicWithUniqueSource G O q),
      c ≤ orientationToConfig G O q hO := by
  rcases superstable_burn_list G c h_ss with ⟨L, h_full⟩
  let O := burnOrientation L h_full
  have hO : acyclicWithUniqueSource G O q := burn_acyclic_with_unique_source L h_full
  use O, hO
  intro v
  dsimp only [orientationToConfig, configOfSource]
  by_cases h_vq : v = q
  · -- Case: v = q
    rw [h_vq]
    simp only [↓reduceIte]
    linarith [c.q_zero]
  · -- Case: v ≠ q
    simp only [h_vq, ↓reduceIte]
    rw [indeg_eq_sum_flow O v]
    dsimp only [flow]
    dsimp only [burnOrientation, orientationFromFlow, O]
    simp only [count_of_multiset_of_count]
    have ineq := burnin_degree L v (h_full v) h_vq
    linarith

/-- The configuration associated to an acyclic orientation with unique source is maximal
superstable.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8,
part 1 ($c(\mathcal{O})$ is maximal superstable). -/
theorem orientation_config_maximal (G : CFGraph) (O : CFOrientation G) (q : G.V)
    (hO : acyclicWithUniqueSource G O q) :
    maximalSuperstable G (orientationToConfig G O q hO) := by
  dsimp only [maximalSuperstable]
  let cO := orientationToConfig G O q hO
  have h_ssO : superstable G q cO := orientation_config_superstable G O q hO
  refine ⟨h_ssO, ?_⟩
  -- Goal is now just maximality of cO.
  -- Suppose another divisor is bigger. There's an orientation divisor yet above that one.
  intro c h_ss h_ge
  rcases superstable_dhar h_ss with ⟨O', hO', h_ge'⟩
  let c' := orientationToConfig G O' q hO'
  -- Sandwich c between cO and c', which have the same degree
  have h_deg_le : configDegree cO ≤ configDegree c := config_degree_mono h_ge
  have h_deg_le' : configDegree c ≤ configDegree c' := config_degree_mono h_ge'
  rw [config_degree_from_O O hO] at h_deg_le
  rw [config_degree_from_O O' hO'] at h_deg_le'
  have h_deg : configDegree c = genus G := by
    linarith
  have h_deg : configDegree c = configDegree cO := by
    rw [config_degree_from_O O hO]
    exact h_deg
  -- Now apply config equality from degree and ge
  exact config_eq_of_le_and_degree h_ge h_deg

/-- Every superstable configuration extends to a maximal superstable configuration. -/
theorem maximal_superstable_exists (G : CFGraph) (q : G.V) (c : Config G q)
    (h_super : superstable G q c) :
    ∃ c' : Config G q, maximalSuperstable G c' ∧ c ≤ c' := by
    rcases superstable_dhar h_super with ⟨O, hO, h_ge⟩
    let c' := orientationToConfig G O q hO
    use c'
    refine ⟨?_, h_ge⟩
    -- Remains to show c' is maximal superstable
    exact orientation_config_maximal G O q hO

/-- Every maximal superstable configuration comes from an acyclic orientation.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8,
part 2 (surjectivity). -/
theorem maximal_superstable_orientation (G : CFGraph) (q : G.V) (c : Config G q)
    (h_max : maximalSuperstable G c) :
    ∃ (O : CFOrientation G) (hO : acyclicWithUniqueSource G O q),
      orientationToConfig G O q hO = c := by
  rcases superstable_dhar h_max.1 with ⟨O, hO, h_ge⟩
  use O, hO
  let c' := orientationToConfig G O q hO
  have h_eq := h_max.2 c' (orientation_config_superstable G O q hO) h_ge
  exact h_eq

/-- The bijection between acyclic orientations with unique source $q$ and maximal
superstable configurations.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 4.8,
part 3 (bijection). -/
theorem orientation_superstable_bijection (G : CFGraph) (q : G.V) :
    let α := {O : CFOrientation G // acyclicWithUniqueSource G O q};
    let β := {c : Config G q // maximalSuperstable G c};
    let f_raw : α → Config G q := λ O_sub => orientationToConfig G O_sub.val q O_sub.prop;
    let f : α → β := λ O_sub => ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop⟩;
    Function.Bijective f := by
  -- Define the domain and codomain types explicitly (can be removed if using let like above)
  let α := {O : CFOrientation G // acyclicWithUniqueSource G O q}
  let β := {c : Config G q // maximalSuperstable G c}
  -- Define the function f_raw : α → Config G q
  let f_raw : α → Config G q := λ O_sub => orientationToConfig G O_sub.val q O_sub.prop
  -- Define the function f : α → β, showing the result is maximal superstable
  let f : α → β := λ O_sub =>
    ⟨f_raw O_sub, orientation_config_maximal G O_sub.val q O_sub.prop⟩

  constructor
  -- Injectivity
  { -- Prove injective f using injective f_raw
    intros O₁_sub O₂_sub h_f_eq -- h_f_eq : f O₁_sub = f O₂_sub
    have h_f_raw_eq : f_raw O₁_sub = f_raw O₂_sub := by
      simp only [Subtype.mk.injEq] at h_f_eq; exact h_f_eq

    -- Reuse original injectivity proof structure, ensuring types match
    let ⟨O₁, h₁⟩ := O₁_sub
    let ⟨O₂, h₂⟩ := O₂_sub
    -- Define c, h_eq₁, h_eq₂ based on orientationToConfig directly
    let c := orientationToConfig G O₁ q h₁
    have h_eq₁ : orientationToConfig G O₁ q h₁ = c := rfl
    have h_eq₂ : orientationToConfig G O₂ q h₂ = c := by
      exact h_f_raw_eq.symm.trans h_eq₁

    apply Subtype.ext
    exact config_to_orientation_unique G q c O₁ O₂ h₁ h₂ h_eq₁ h_eq₂
  }

  -- Surjectivity
  { -- Prove Function.Surjective f
    unfold Function.Surjective
    intro y -- y should now have type β
    -- Access components using .val and .property
    let c_target : Config G q := y.val -- Explicitly type c_target
    let h_target_max_superstable := y.property

    -- Use the fact that every maximal superstable config comes from an orientation.
    rcases maximal_superstable_orientation G q c_target h_target_max_superstable with
      ⟨O, hO, h_config_eq_target⟩

    -- Construct the required subtype element x : α (the pre-image)
    let x : α := ⟨O, hO⟩

    -- Show that this x exists
    use x

    -- Show f x = y using Subtype.eq
    apply Subtype.ext
    -- Goal: (f x).val = y.val
    -- Need to show: f_raw x = c_target
    -- This is exactly h_config_eq_target
    exact h_config_eq_target
    -- Proof irrelevance handles the equality of the property components.
  }
