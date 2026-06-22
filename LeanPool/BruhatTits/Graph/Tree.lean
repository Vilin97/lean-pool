/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Graph.GroupAction

/-!
# Proof that the Bruhat-Tits graph is a tree

Let `R` be a discrete valuation ring and `K` its fraction field.

In this file we show that the Bruhat-Tits graph associated to `R` is acyclic (i.e. without loops)
and conclude that it is a tree. The connectedness was already shown in `BruhatTits.Graph.Graph`
(see `BruhatTits.BTGraph_connected`).

The strategy for proving acyclicity is as follows:

- Show that every trail (i.e. a walk that has no self-intersections in the interior, but possibly
  at the ends) can be transformed into a standard walk by the action of `GL₂(K)`. Here a standard
  walk is a walk that is represented by a standard sequence of lattices (see `List.IsBTStandard`).
- The length of a standard walk is the distance (in the sense of `inv`) of the endpoints, so
  by the first point, this also holds for every trail.
- In particular, the second point holds for a circle at `x`, but a circle always has length at least
  `3 > 0 = inv x x`, so no circles exist.

-/

open Module


namespace BruhatTits

variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]

section «Action»

/-- Any walk is representable by a chain of lattices. If the walk is a trail,
the chain is simple (see `BruhatTits.exists_repr_isSimpleChain_of_isTrail`). -/
lemma _root_.SimpleGraph.Walk.exists_repr_isChain {x y : Vertices R} (p : BTgraph.Walk x y) :
    ∃ (l : List (Lattice R)), l.IsBTChain ∧ l.map (fun L ↦ ⟦L⟧) = p.support := by
  induction p using SimpleGraph.Walk.rec with
  | nil =>
    rename_i u
    refine Quotient.inductionOn' u (fun L ↦ ?_)
    refine ⟨[L], singleton_isChain L, by rfl⟩
  | @cons u v w hadj p ih =>
    obtain ⟨l, hchain, hl⟩ := ih
    have lnenil : l ≠ [] := hchain.ne_nil
    match l with
    | (L :: l) =>
    have hLv : ⟦L⟧ = v := by
      rw [← p.cons_tail_support] at hl
      exact (List.cons.inj hl).1
    subst hLv
    obtain ⟨M, rfl, hstd⟩ := exists_repr_isStandardNeighbour_of_isNeighbour L u hadj.symm
    refine ⟨M :: L :: l, ?_, ?_⟩
    · exact cons_isChain_of hchain hstd
    · rw [SimpleGraph.Walk.support_cons, ← hl]
      rfl

/-- A non-empty chain of lattices defines a walk on the Bruhat-Tits graph. -/
noncomputable def chainToWalk (l : List (Lattice R)) (hl : l ≠ []) (hc : l.IsBTChain) :
    BTgraph.Walk ⟦l.head hl⟧ ⟦l.getLast hl⟧ := match l with
  | [L] => SimpleGraph.Walk.nil' ⟦L⟧
  | L₁ :: L₂ :: l =>
      have p : BTgraph.Adj ⟦L₁⟧ ⟦L₂⟧ := by
        apply isNeighbour_of_isStandardNeighbour
        have := hc.isStandardNeighbour
        rw [List.isChain_cons_cons] at this
        exact this.1
      let q : BTgraph.Walk ⟦L₂⟧ ⟦(L₁ :: L₂ :: l).getLast hl⟧ :=
        chainToWalk (L₂ :: l) (by simp) (isChain_of_cons_isChain (List.cons_ne_nil L₂ l) hc)
      q.cons p

lemma isSimpleChain_of_isTrail_aux {x y : Vertices R} (p : BTgraph.Walk x y)
    (hp : p.IsTrail) (l : List (Lattice R)) (hl : l.map (fun L ↦ ⟦L⟧) = p.support) :
    (List.zipWith₃ (fun L₁ _ L₃ ↦ ¬ Lattice.IsSimilar R L₁ L₃) l l.tail l.tail.tail).Forall id := by
  match p, l with
  | .nil, [L] => simp [List.zipWith₃]
  | .cons _ .nil, [_, _] => simp [List.zipWith₃]
  | .cons' _ v _ adj (.cons' _ _ _ adj' .nil), [M, L, Q] =>
      simp only [List.map_cons, List.map_nil, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil] at hl
      have hfirst : (⟦M⟧ : Vertices R) = x := (List.cons.inj hl).1
      have htail := (List.cons.inj hl).2
      have htailtail := (List.cons.inj htail).2
      have hthird : (⟦Q⟧ : Vertices R) = y := (List.cons.inj htailtail).1
      simp only [List.tail_cons, List.zipWith₃, List.forall_cons, id_eq, List.Forall, and_true]
      intro h
      have : (⟦M⟧ : Vertices R) = ⟦Q⟧ := Quotient.sound h
      simp only [SimpleGraph.Walk.isTrail_cons, SimpleGraph.Walk.IsTrail.nil,
        SimpleGraph.Walk.edges_nil, List.not_mem_nil, not_false_eq_true, and_self,
        SimpleGraph.Walk.edges_cons, List.mem_singleton, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, and_true, not_or, not_and, true_and] at hp
      apply hp.right
      rw [← hfirst, ← hthird]
      exact this
  | .cons' _ v₂ _ adj (.cons' _ v₁ _ adj' <| .cons' _ _ _ adj'' q),
      (L₁ :: L₂ :: L₃ :: l) =>
      simp only [List.map_cons, SimpleGraph.Walk.support_cons] at hl
      have hfirst : (⟦L₁⟧ : Vertices R) = x := (List.cons.inj hl).1
      have htail := (List.cons.inj hl).2
      have hsecond : (⟦L₂⟧ : Vertices R) = v₂ := (List.cons.inj htail).1
      have htailtail := (List.cons.inj htail).2
      have hthird : (⟦L₃⟧ : Vertices R) = v₁ := (List.cons.inj htailtail).1
      simp only [SimpleGraph.Walk.isTrail_cons, SimpleGraph.Walk.edges_cons, List.mem_cons,
        Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_true, not_or, not_and] at hp
      simp only [List.tail_cons, List.zipWith₃, List.forall_cons, id_eq]
      refine ⟨?_, ?_⟩
      · intro h
        have hx : x = v₁ := by
          rw [← hfirst, ← hthird]
          exact Quotient.sound h
        exact hp.2.1.2 hx
      · apply isSimpleChain_of_isTrail_aux (.cons adj' <| .cons adj'' q)
        · simpa [SimpleGraph.Walk.isTrail_cons, SimpleGraph.Walk.edges_cons, List.mem_cons,
            Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, not_or, not_and] using hp.1
        · exact htail

/-- If `p` is a trail in the Bruhat-Tits graph, it is representable by
  a simple chain of lattices. -/
lemma exists_repr_isSimpleChain_of_isTrail {x y : Vertices R} (p : BTgraph.Walk x y)
    (hp : p.IsTrail) :
    ∃ (l : List (Lattice R)), l.IsBTSimpleChain ∧ l.map (fun L ↦ ⟦L⟧) = p.support := by
  obtain ⟨l, hl, heq⟩ := p.exists_repr_isChain
  refine ⟨l, ⟨hl, ?_⟩, heq⟩
  apply isSimpleChain_of_isTrail_aux p hp _ heq

/-- A walk on the Bruhat-Tits graph is a standard walk, if there exists a sequence
of representing lattices `(Lᵢ)` with `pᵢ = ⟦Lᵢ⟧` such that the sequence `(Lᵢ)` is
  a standard sequence (see `List.IsBTStandard`). -/
def _root_.SimpleGraph.Walk.IsStandard {x y : Vertices R} (p : BTgraph.Walk x y) : Prop :=
  ∃ (l : List (Lattice R)), l.map (fun L ↦ ⟦L⟧) = p.support ∧ l.IsBTStandard

lemma isStandard_of_list_isStandard {x y : Vertices R} {p : BTgraph.Walk x y}
    (l : List (Lattice R)) (hleq : l.map (fun L ↦ ⟦L⟧) = p.support) (hl : l.IsBTStandard) :
    p.IsStandard := by
  use l

/-- If `p` is a standard walk from `x` to `y`, the length of `p` is the distance `inv x y`. -/
lemma length_eq_inv_of_isStandard {x y : Vertices R} {p : BTgraph.Walk x y} (h : p.IsStandard) :
    p.length = inv x y := by
  obtain ⟨l, hleq, hl⟩ := h
  have hlen := length_eq_dist_add_one_of_isStandard hl
  have : p.support.length = dist (l.head hl.ne_nil) (l.getLast hl.ne_nil) + 1 := by
    rw [← hleq]
    exact (List.length_map (fun L ↦ (⟦L⟧ : Vertices R))).trans hlen
  simp only [SimpleGraph.Walk.length_support, add_left_inj] at this
  have : x = ⟦l.head hl.ne_nil⟧ := by
    match l with
    | L :: l =>
    rw [List.map_cons] at hleq
    have hx := p.cons_tail_support
    rw [← hleq] at hx
    exact (List.cons.inj hx).1
  subst this
  have : y = ⟦l.getLast hl.ne_nil⟧ := by
    have hmap_ne_nil : List.map (fun L ↦ (⟦L⟧ : Vertices R)) l ≠ [] := by
      intro hnil
      exact hl.ne_nil (List.map_eq_nil_iff.mp hnil)
    have hlast_eq := List.getLast_congr hmap_ne_nil p.support_ne_nil hleq
    simpa [Vertices, List.getLast_map] using (hlast_eq.trans p.getLast_support).symm
  subst this
  assumption

/-- Given two vertices and a trail `p` from `x` to `y`, there exists a `g : GL₂(K)`
such that `g • p` is a standard walk. -/
lemma exists_map_isStandard {x y : Vertices R} {p : BTgraph.Walk x y} (hp : p.IsTrail) :
    ∃ (g : GL (Fin 2) K), (p.map (g.toGraphIso (R := R))).IsStandard (R := R) := by
  obtain ⟨l, hlsimple, heq⟩ := exists_repr_isSimpleChain_of_isTrail p hp
  obtain ⟨g, hg⟩ := exists_trafo_to_isStandard l hlsimple
  use g
  refine isStandard_of_list_isStandard (g • l) ?_ hg
  simp only [List.smul_lattice_def, List.map_map, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, SimpleGraph.Walk.support_map]
  change List.map (fun L ↦ ⟦g • L⟧) l = _
  simp_rw [← smulGL_mk, ← Vertices.smul_def]
  change List.map ((fun x : Vertices R ↦ g • x) ∘ (fun L ↦ ⟦L⟧)) l = _
  rw [List.comp_map, ← heq]
  rfl

end «Action»

section «Acyclic»

/-- The length of a trail is equal to the distance of the endpoints. -/
lemma length_eq_inv {x y : Vertices R} {p : BTgraph.Walk x y} (hp : p.IsTrail) :
    p.length = inv x y := by
  -- transform chain to standard one by a graph isomorphism, then apply the result for
  -- standard walks
  obtain ⟨g, hg⟩ := exists_map_isStandard hp
  have : (p.map (g.toGraphIso (R := R)).toHom).length = inv (g • x) (g • y) :=
    length_eq_inv_of_isStandard hg
  simpa using this

/-- The graph-theoretic distance agrees with our constructed `inv` function. -/
lemma dist_BTgraph_eq_inv : (BTgraph (R := R)).dist = inv := by
  ext x y
  obtain ⟨p, hp, hlen⟩ := (BTgraph_connected (R := R)).exists_path_of_dist x y
  rw [← hlen, length_eq_inv hp.isTrail]

/-- The Bruhat-Tits graph has no loops, i.e. it is acyclic. -/
lemma BTgraph_isAcyclic : (BTgraph (R := R)).IsAcyclic := by
  -- suppose `c` is a circle
  intro x c h
  -- then `c` is a trail, but the length of such a chain is the distance
  -- of the endpoints, which yields a contradiction
  have hlen : c.length = inv x x := length_eq_inv h.isCircuit.isTrail
  rw [inv_self] at hlen
  have : 3 ≤ 0 := hlen ▸ SimpleGraph.Walk.IsCycle.three_le_length h
  contradiction

end «Acyclic»

/-- The Bruhat-Tits graph is a tree. -/
theorem BTtree : SimpleGraph.IsTree (BTgraph (R := R)) where
  preconnected := BTgraph_connected.preconnected
  isAcyclic := BTgraph_isAcyclic

end BruhatTits
