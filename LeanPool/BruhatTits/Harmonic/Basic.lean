/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import LeanPool.BruhatTits.Utils.GraphAction

/-!
# Definition and Surjectivity of Laplacian

In this file we define the Laplacian of a simple graph `X` and the notion of harmonic functions.
We show that if `X` is a tree, with the property that each vertex has at least two and only
finitely many neighbours, then the Laplacian is surjective.

-/

open Module


suppress_compilation

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]

open BigOperators

namespace SimpleGraph

section «Incidence»

variable {X : SimpleGraph V}

/-- Edges containing `v` are equivalent to the incidence set at `v`. -/
def incidenceEquiv (v : V) : { e : X.edgeSet | v ∈ e.val } ≃ X.incidenceSet v where
  toFun e := ⟨e.val.val, ⟨e.val.property, e.property⟩⟩
  invFun e := ⟨⟨e.val, e.property.left⟩, e.property.right⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (v : V) [Finite (X.incidenceSet v)] : Finite { e : X.edgeSet | v ∈ e.val } :=
  Finite.of_equiv _ (incidenceEquiv v).symm

/-- The finset of the edges of `X` consisting of all edges connected to `v`. -/
def incidenceFinset' (v : V) [Fintype (X.neighborSet v)] : Finset X.edgeSet :=
  (Set.toFinite { e : X.edgeSet | v ∈ e.val }).toFinset

lemma mem_incidenceFinset' (v : V) [Fintype (X.neighborSet v)] (e : X.edgeSet) :
    e ∈ incidenceFinset' v ↔ v ∈ e.val := by
  simp [incidenceFinset']

/-- The Laplacian of an `M`-valued function on the set of edges of `X` as an `M`-valued function
on the vertices of `X`. -/
def laplace [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : X.edgeSet → M) (v : V) : M :=
  w v • ∑ e ∈ X.incidenceFinset' v, f e

/-- A function on the edges of `X` is called harmonic, if the Laplacian of it is zero. -/
def IsHarmonic [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : X.edgeSet → M) : Prop :=
  X.laplace w f = 0

end «Incidence»

section «Surjectivity»

/-- A simple graph equipped with a proof that it is a tree. -/
structure Tree (V : Type*) extends SimpleGraph V where
  isTree : IsTree toSimpleGraph

namespace Tree

variable {X : Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)

variable (v₀ : V)

section «API»

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma exists_path_eq_append_of_isPath_of_mem_support {v w x : V} (p : X.Walk v w) (hp : p.IsPath)
    (hx : x ∈ p.support) :
    ∃ (r : X.Walk v x) (s : X.Walk x w), r.IsPath ∧ s.IsPath ∧ p = r.append s := by
  rw [p.mem_support_iff_exists_append] at hx
  obtain ⟨r, s, hrs⟩ := hx
  have : (r.append s).IsPath := by rwa [← hrs]
  exact ⟨r, s, this.of_append_left, this.of_append_right, hrs⟩

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma exists_path_eq_cons_of_isPath_of_mem_support {v w : V} (h : X.Adj w v) (p : X.Walk w v₀)
    (hv : v ∈ p.support) (hpath : p.IsPath) : ∃ (r : X.Walk v v₀), r.IsPath ∧ p = r.cons h := by
  obtain ⟨r, s, hr, hs, hrs⟩ := exists_path_eq_append_of_isPath_of_mem_support p hpath hv
  let r' : X.Walk w v := h.toWalk
  have hr' : r'.IsPath := by simpa [r'] using h.ne
  let pr' : X.Path w v := ⟨r', hr'⟩
  let pr : X.Path w v := ⟨r, hr⟩
  have : pr = pr' := X.isTree.isAcyclic.path_unique _ _
  have hrr' : r = r' := by rwa [Subtype.ext_iff] at this
  use s, hs
  rw [hrs, hrr']
  simp [r']

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma dist_ne_of_of_adj {v w : V} (h : X.Adj v w) : X.dist v₀ v ≠ X.dist v₀ w := by
  obtain ⟨pv, hpvpath, hpvlength⟩ := X.isTree.connected.exists_path_of_dist v v₀
  obtain ⟨pw, hpwpath, hpwlength⟩ := X.isTree.connected.exists_path_of_dist w v₀
  let q : X.Walk v v₀ := pw.cons' _ _ _ h
  intro hdist
  let pv' : X.Path v v₀ := ⟨pv, hpvpath⟩
  have hlen : pv.length = pw.length := by
    rw [hpvlength, dist_comm, hdist, dist_comm, ← hpwlength]
  have hqpath : q.IsPath := by
    simp only [Walk.cons_isPath_iff, hpwpath, true_and, q]
    intro hc
    obtain ⟨r, hr, hpr⟩ := X.exists_path_eq_cons_of_isPath_of_mem_support v₀ h.symm pw hc hpwpath
    let r' : X.Path v v₀ := ⟨r, hr⟩
    have : pv' = r' := X.isTree.isAcyclic.path_unique _ _
    have : pv = r := by rwa [Subtype.ext_iff] at this
    have : pw.length = pv.length + 1 := by simp [this, hpr]
    omega
  let q' : X.Path v v₀ := ⟨q, hqpath⟩
  have hpeq : pv' = q' := X.isTree.isAcyclic.path_unique _ _
  have heq : pv = q := congrArg Subtype.val hpeq
  have : q.length = pw.length + 1 := by simp [q]
  rw [← heq, hpvlength, dist_comm, hdist, dist_comm, ← hpwlength] at this
  omega

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma exists_ordered (e : X.edgeSet) :
    ∃ p : V × V, X.dist v₀ p.1 < X.dist v₀ p.2 ∧ s(p.1, p.2) = e.val := by
  obtain ⟨p, hp⟩ := Quot.exists_rep e.val
  if h : X.dist v₀ p.1 < X.dist v₀ p.2
  then exact ⟨p, h, hp⟩
  else
    use (p.2, p.1)
    simp only
    constructor
    · by_contra hc
      have hdist : X.dist v₀ p.1 = X.dist v₀ p.2 := by omega
      have hadj : s(p.1, p.2) ∈ X.edgeSet := by
        change Quot.mk (Sym2.Rel V) p ∈ _
        rw [hp]
        exact e.property
      rw [mem_edgeSet] at hadj
      apply dist_ne_of_of_adj v₀ hadj hdist
    · rw [Sym2.eq_swap]
      exact hp

/-- Given an edge `e` of `X`, the source is the vertex of `e` closer to `v₀`. -/
def source (e : X.edgeSet) : V :=
  (X.exists_ordered v₀ e).choose.1

/-- Given an edge `e` of `X`, the target is the vertex of `e` farther from `v₀`. -/
def target (e : X.edgeSet) : V :=
  (X.exists_ordered v₀ e).choose.2

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma norm_source_lt_norm_target (e : X.edgeSet) :
    X.dist v₀ (X.source v₀ e) < X.dist v₀ (X.target v₀ e) :=
  (X.exists_ordered v₀ e).choose_spec.left

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma edge_eq_mk_source_target (e : X.edgeSet) :
    e.val = s(source v₀ e, target v₀ e) :=
  (exists_ordered v₀ e).choose_spec.right.symm

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma source_mem (e : X.edgeSet) : X.source v₀ e ∈ e.val := by
  simp [edge_eq_mk_source_target v₀]

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma target_mem (e : X.edgeSet) : X.target v₀ e ∈ e.val := by
  simp [edge_eq_mk_source_target v₀]

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma source_adj_target (e : X.edgeSet) :
    X.Adj (X.source v₀ e) (X.target v₀ e) := by
  rw [adj_iff_exists_edge]
  refine ⟨fun hc ↦ ?_, e, e.property, source_mem v₀ e, target_mem v₀ e⟩
  have := norm_source_lt_norm_target v₀ e
  simp [hc] at this

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma norm_target_eq_norm_source_add_one (e : X.edgeSet) :
    X.dist v₀ (X.target v₀ e) = X.dist v₀ (X.source v₀ e) + 1 := by
  apply le_antisymm
  · have h := X.source_adj_target v₀ e
    rw [← dist_eq_one_iff_adj] at h
    rw [← h]
    apply X.isTree.connected.dist_triangle
  · have := norm_source_lt_norm_target v₀ e
    omega

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma eq_source_or_eq_target_of_mem (e : X.edgeSet) (v : V) (hv : v ∈ e.val) :
    X.source v₀ e = v ∨ X.target v₀ e = v := by
  rw [edge_eq_mk_source_target v₀, Sym2.mem_iff] at hv
  tauto

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma zero_lt_norm_target (e : X.edgeSet) : 0 < X.dist v₀ (X.target v₀ e) := by
  rw [norm_target_eq_norm_source_add_one]
  omega

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma source_eq_origin_of_mem (e : X.edgeSet) (h : v₀ ∈ e.val) :
    X.source v₀ e = v₀ := by
  rcases eq_source_or_eq_target_of_mem v₀ e v₀ h with hm | hm
  · exact hm
  · have : 0 < X.dist v₀ v₀ := by
      nth_rw 2 [← hm]
      exact zero_lt_norm_target v₀ e
    simp [dist_self] at this

/-- The outward cone of a vertex `w` wrt. `v₀` is the finset of neighbors that has
a bigger distance to `v₀` than `w`. -/
def outwardCone (w : V) : Finset V :=
  let s : Set V := { v : V | X.Adj w v ∧ X.dist v₀ w < X.dist v₀ v }
  have hs : s.Finite := (Set.toFinite (X.neighborSet w)).subset fun _ ha ↦ ha.left
  hs.toFinset

omit [DecidableEq V] in
/-- A vertex `a` is in the outward cone of a vertex `w`, iff `a` is a neighbour and has
bigger distance to `v₀` than `w`. -/
lemma mem_outwardCone_iff (w a : V) :
    a ∈ X.outwardCone v₀ w ↔ (X.Adj w a ∧ X.dist v₀ w < X.dist v₀ a) := by
  simp [outwardCone]

omit [DecidableEq V] in
lemma not_mem_outwardCone (w : V) : w ∉ X.outwardCone v₀ w := by
  simp [mem_outwardCone_iff]

/-- The outward edge cone of a vertex `w` wrt. `v₀` is the finset of neighboring edges
where `w` is the source vertex wrt. to `v₀`. -/
def outwardEdgeCone (w : V) : Finset X.edgeSet :=
  let s : Set X.edgeSet := { e | w ∈ e.val ∧ X.source v₀ e = w }
  have hs : s.Finite := (Finset.finite_toSet (incidenceFinset' w)).subset fun e he ↦ by
    simpa only [Finset.mem_coe, mem_incidenceFinset'] using he.left
  hs.toFinset

lemma mem_outwardEdgeCone_iff (w : V) (e : X.edgeSet) :
    e ∈ X.outwardEdgeCone v₀ w ↔ w ∈ e.val ∧ X.source v₀ e = w := by
  simp [outwardEdgeCone]

lemma outwardEdgeCone_nonempty_of_source (e : X.edgeSet) :
    (X.outwardEdgeCone v₀ (X.source v₀ e)).Nonempty := by
  use e
  rw [mem_outwardEdgeCone_iff]
  simp

/-- The outward edge cone of the origin `v₀` is the finset of all neighboring edges. -/
lemma outwardEdgeCone_origin_eq : X.outwardEdgeCone v₀ v₀ = X.incidenceFinset' v₀ := by
  ext e
  simp only [mem_outwardEdgeCone_iff, mem_incidenceFinset', and_iff_left_iff_imp]
  intro h
  exact source_eq_origin_of_mem v₀ e h

/-- An arbitrary choice of a distinguished edge pointing away from `v₀`. -/
def distinguishedEdge (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) : X.edgeSet :=
  hw.choose

lemma distinguishedEdge_mem (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) :
    X.distinguishedEdge v₀ w hw ∈ X.outwardEdgeCone v₀ w :=
  hw.choose_spec

@[simp]
lemma source_distinguishedEdge (v : V) (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    X.source v₀ (distinguishedEdge v₀ v hnonempty) = v := by
  have := distinguishedEdge_mem v₀ v hnonempty
  rw [mem_outwardEdgeCone_iff] at this
  exact this.right

lemma outwardEdgeCone_eq_union (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) :
    X.outwardEdgeCone v₀ w = { X.distinguishedEdge v₀ w hw } ∪
        { e | e ∈ X.outwardEdgeCone v₀ w ∧ X.distinguishedEdge v₀ w hw ≠ e } := by
  ext e
  simp_rw [Finset.mem_coe, ne_eq, Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    by_cases hde : e = distinguishedEdge v₀ w hw
    · exact Or.inl hde
    · exact Or.inr ⟨h, fun a ↦ hde a.symm⟩
  · rintro (rfl | ⟨h, _⟩)
    · exact distinguishedEdge_mem v₀ w hw
    · exact h

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
/-- For every vertex `w` different from the root vertex `v₀` there exists an edge `e`, whose
target is `w`. -/
lemma exists_edge_dist_source_lt (w : V) (hw : 0 < X.dist v₀ w) :
    ∃ (e : X.edgeSet), X.target v₀ e = w := by
  obtain ⟨p, hp, hplen⟩ := X.isTree.connected.exists_path_of_dist w v₀
  revert hp hplen
  induction p using Walk.rec with
  | nil =>
    intro hp hplen
    simp_rw [Walk.length_nil] at hplen
    omega
  | @cons x y z hadj p ih =>
    intro hp hplen
    rw [adj_iff_exists_edge_coe] at hadj
    obtain ⟨e, he⟩ := hadj
    use e
    have hx : x ∈ e.val := by simp [he]
    have hy : y ∈ e.val := by simp [he]
    have hp' : p.IsPath := by
      simp only [Walk.cons_isPath_iff] at hp
      exact hp.left
    obtain ⟨q, hq, hqlen⟩ := X.isTree.connected.exists_path_of_dist y z
    let p' : X.Path y z := ⟨p, hp'⟩
    let q' : X.Path y z := ⟨q, hq⟩
    have : p' = q' := X.isTree.isAcyclic.path_unique _ _
    have hpq : p = q := by rwa [Subtype.ext_iff] at this
    have hdist : X.dist z y < X.dist z x := by
      rw [dist_comm, ← hqlen, ← hpq, dist_comm, ← hplen]
      simp
    rcases eq_source_or_eq_target_of_mem z e x hx with hsource | h
    · have hsec : target z e = y := by
        rcases eq_source_or_eq_target_of_mem z e y hy with h' | h'
        · rw [h'] at hsource
          absurd hsource.symm
          exact hadj.ne
        · assumption
      rw [← hsource, ← hsec, norm_target_eq_norm_source_add_one] at hdist
      omega
    · assumption

/-- If `w` is not the origin, then this is the unique edge pointing towards the origin.
For uniqueness, see `eq_edgeTowardsOrigin_iff_of_mem`. -/
def edgeTowardsOrigin (w : V) (hw : 0 < X.dist v₀ w) : X.edgeSet :=
  (X.exists_edge_dist_source_lt v₀ w hw).choose

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma edgeTowardsOrigin_target_eq (w : V) (hw : 0 < X.dist v₀ w) :
    X.target v₀ (X.edgeTowardsOrigin v₀ w hw) = w :=
  (X.exists_edge_dist_source_lt v₀ w hw).choose_spec

omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma eq_of_isPath {x y : V} {p q : X.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q :=
  congrArg Subtype.val (X.isTree.isAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩)

omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)] in
lemma dist_eq_of_isPath {x y : V} (p : X.Walk x y) (hp : p.IsPath) :
    X.dist x y = p.length := by
  obtain ⟨q, hq, hqlen⟩ := X.isTree.connected.exists_path_of_dist x y
  rw [eq_of_isPath hp hq, hqlen]

omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)] in
lemma source_eq_of_target_eq (e f : X.edgeSet) (h : X.target v₀ e = X.target v₀ f) :
    X.source v₀ e = X.source v₀ f := by
  obtain ⟨p, hp, hplen⟩ := X.isTree.connected.exists_path_of_dist (X.source v₀ e) v₀
  let headj : X.Adj (source v₀ e) (target v₀ e) := source_adj_target v₀ e
  obtain ⟨q, hq, hqlen⟩ := X.isTree.connected.exists_path_of_dist (X.source v₀ f) v₀
  let hfadj : X.Adj (source v₀ f) (target v₀ e) := by
    rw [h]
    exact source_adj_target v₀ f
  let p' : X.Walk (target v₀ e) v₀ := p.cons headj.symm
  have hp' : p'.IsPath := by
    simp only [Walk.cons_isPath_iff, hp, true_and, p']
    intro hc
    obtain ⟨r, hr, hpr⟩ := exists_path_eq_cons_of_isPath_of_mem_support v₀ headj p hc hp
    have : X.dist v₀ (source v₀ e) = X.dist v₀ (target v₀ e) + 1 := by
      rw [dist_comm, ← hplen, hpr, dist_comm, dist_eq_of_isPath r hr]
      simp
    rw [norm_target_eq_norm_source_add_one] at this
    omega
  let q' : X.Walk (target v₀ e) v₀ := q.cons hfadj.symm
  have hq' : q'.IsPath := by
    simp only [Walk.cons_isPath_iff, hq, true_and, q']
    intro hc
    obtain ⟨r, hr, hpr⟩ := exists_path_eq_cons_of_isPath_of_mem_support v₀ hfadj q hc hq
    have : X.dist v₀ (source v₀ f) = X.dist v₀ (target v₀ f) + 1 := by
      rw [← h]
      rw [dist_comm, ← hqlen, hpr, dist_comm, dist_eq_of_isPath r hr]
      simp
    rw [norm_target_eq_norm_source_add_one] at this
    omega
  let p'' : X.Path (target v₀ e) v₀ := ⟨p', hp'⟩
  let q'' : X.Path (target v₀ e) v₀ := ⟨q', hq'⟩
  have : p'' = q'' := X.isTree.isAcyclic.path_unique _ _
  simp only [Subtype.mk.injEq, Walk.cons.injEq, p'', p', q'', q'] at this
  exact this.left

omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)] in
lemma eq_of_target_eq (e f : X.edgeSet) (h : X.target v₀ e = X.target v₀ f) : e = f := by
  ext : 1
  rw [edge_eq_mk_source_target v₀, edge_eq_mk_source_target v₀, h, source_eq_of_target_eq v₀ e f h]

omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)] in
lemma eq_edgeTowardsOrigin_iff_of_mem (w : V) (hw : 0 < X.dist v₀ w) (e : X.edgeSet)
    (hmem : w ∈ e.val) :
    e = X.edgeTowardsOrigin v₀ w hw ↔ X.target v₀ e = w := by
  constructor
  · rintro rfl
    apply edgeTowardsOrigin_target_eq
  · intro h
    exact eq_of_target_eq v₀ _ _ (by simpa)

omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)] in
lemma vertex_mem_edgeTowardsOrigin (w : V) (hw : 0 < X.dist v₀ w) :
    w ∈ (edgeTowardsOrigin v₀ w hw).val := by
  nth_rw 2 [← edgeTowardsOrigin_target_eq v₀ w hw]
  exact target_mem v₀ (edgeTowardsOrigin v₀ w hw)

lemma edgeTowardsOrigin_not_mem_outwardEdgeCone (v : V) (hdist : 0 < X.dist v₀ v) :
    edgeTowardsOrigin v₀ v hdist ∉ outwardEdgeCone v₀ v := by
  intro hc
  rw [mem_outwardEdgeCone_iff] at hc
  have := edgeTowardsOrigin_target_eq v₀ v hdist
  nth_rw 4 [← this] at hc
  have := source_adj_target v₀ (edgeTowardsOrigin v₀ v hdist)
  apply this.ne
  exact hc.right

lemma outwardEdgeCone_nonempty_of_two_le_degree {v : V} (hv : 2 ≤ X.degree v) :
    (X.outwardEdgeCone v₀ v).Nonempty := by
  have : 1 < (X.neighborFinset v).card := by simpa
  rw [Finset.one_lt_card] at this
  obtain ⟨a, ha, b, hb, hne⟩ := this
  rw [mem_neighborFinset] at ha hb
  let ea : X.edgeSet := ⟨s(v, a), ha⟩
  let eb : X.edgeSet := ⟨s(v, b), hb⟩
  have hvea : v ∈ ea.val := by simp [ea]
  have hveb : v ∈ eb.val := by simp [eb]
  rcases eq_source_or_eq_target_of_mem v₀ ea v hvea with h | has
  · use ea
    rw [mem_outwardEdgeCone_iff]
    simpa [h]
  rcases eq_source_or_eq_target_of_mem v₀ eb v hveb with h | hbs
  · use eb
    rw [mem_outwardEdgeCone_iff]
    simpa [h]
  have : ea = eb := by
    apply eq_of_target_eq v₀
    rw [has, hbs]
  absurd hne
  simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
    ea, eb] at this
  rcases this with h | h
  · exact h
  · rw [← h.left, h.right]

end «API»

section «Construction»

variable (n : ℕ) (g : X.edgeSet → M)

/-- Boundary value used in the recursive construction of a preimage of the Laplacian. -/
def auxBorder (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) = n + 1) : M :=
  match n with
  | 0 =>
    let d : V := X.source v₀ e
    have hd : (X.outwardEdgeCone v₀ d).Nonempty := by
      use e
      rw [mem_outwardEdgeCone_iff]
      simpa only [d, and_true] using source_mem v₀ e
    if X.distinguishedEdge v₀ d hd = e
      then (w d)⁻¹ • f d
      else 0
  | n + 1 =>
    let d : V := X.source v₀ e
    have hd : (X.outwardEdgeCone v₀ d).Nonempty := by
      use e
      rw [mem_outwardEdgeCone_iff]
      simpa only [d, and_true] using source_mem v₀ e
    have hd2 : 0 < X.dist v₀ d := by
      rw [norm_target_eq_norm_source_add_one] at he
      rw [add_left_inj] at he
      simp_rw [d]
      omega
    let q : X.edgeSet := X.edgeTowardsOrigin v₀ d hd2
    if X.distinguishedEdge v₀ d hd = e
      then (w d)⁻¹ • f d - g q
      else 0

/-- Recursive auxiliary function assigning values to edges at bounded distance from the root. -/
def aux (n : ℕ) : X.edgeSet → M := match n with
  /- arbitrary value in step zero. -/
  | 0 => fun _ ↦ 0
  | n + 1 => fun e ↦
      /- if the norm of the edge is `> n + 1`, we give a trash value -/
      if h₁ : n + 1 < X.dist v₀ (X.target v₀ e) then 0
      else
        /- if the norm of the edge is `≤ n`, we use the induction hypothesis -/
        if h₂ : X.dist v₀ (X.target v₀ e) ≤ n then aux n e
        else
          /- if the norm of the edge is `n + 1`, it is on the current border, so we compute -/
          have he : X.dist v₀ (X.target v₀ e) = n + 1 := by omega
          auxBorder w f v₀ n (aux n) e he

lemma aux_zero_of_gt (n : ℕ) (e : X.edgeSet) (h : n + 1 < X.dist v₀ (X.target v₀ e)) :
    aux w f v₀ n e = 0 := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [aux, dite_eq_left_iff, not_lt]
    intro h
    omega

lemma aux_extends (n : ℕ) (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) ≤ n) :
    aux w f v₀ (n + 1) e = aux w f v₀ n e := by
  simp_rw [aux]
  split_ifs
  · rwa [aux_zero_of_gt]
  · rfl

lemma aux_extends' (n : ℕ) (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) ≤ n) :
    aux w f v₀ (X.dist v₀ (X.target v₀ e)) e = aux w f v₀ n e := by
  match n with
  | 0 =>
    have : (X.dist v₀ (target v₀ e)) = 0 := by omega
    simp only [aux, this]
  | n + 1 =>
    simp only [aux]
    split_ifs
    · next h => omega
    · next h => apply aux_extends' n e h
    · next h₁ h₂ =>
      have : X.dist v₀ (target v₀ e) = n + 1 := by omega
      simp_rw [this]
      simp only [aux]
      split_ifs
      · rfl

lemma incidenceFinset_eq_union (v : V) (hv : 0 < X.dist v₀ v) :
    X.incidenceFinset' v = { edgeTowardsOrigin v₀ v hv } ∪ X.outwardEdgeCone v₀ v := by
  ext e
  constructor
  · intro h
    simp only [Finset.mem_union, Finset.mem_singleton]
    by_cases heq : edgeTowardsOrigin v₀ v hv = e
    · exact Or.inl heq.symm
    · apply Or.inr
      rw [mem_incidenceFinset'] at h
      rw [mem_outwardEdgeCone_iff]
      constructor
      · exact h
      · /- conclude using that `e` is not the edge towards the origin. -/
        rcases eq_source_or_eq_target_of_mem v₀ e v h with h₂ | h₂
        · exact h₂
        · rw [← eq_edgeTowardsOrigin_iff_of_mem v₀ v hv e h] at h₂
          absurd h₂
          exact fun hc ↦ heq hc.symm
  · intro h
    simp only [Finset.mem_union, Finset.mem_singleton] at h
    cases h
    · next h =>
      subst h
      rw [mem_incidenceFinset']
      apply vertex_mem_edgeTowardsOrigin
    · next h =>
      rw [mem_incidenceFinset']
      rw [mem_outwardEdgeCone_iff] at h
      exact h.left

lemma aux_spec_origin_distinguishedEdge (hnonempty : (X.outwardEdgeCone v₀ v₀).Nonempty) :
    aux w f v₀ 1 (distinguishedEdge v₀ v₀ hnonempty) = (w v₀)⁻¹ • f v₀ := by
  have : X.dist v₀ v₀ = 0 := by simp
  simp [aux, norm_target_eq_norm_source_add_one, auxBorder]

lemma aux_spec₀ (e : X.edgeSet) (n : ℕ) (he : X.dist v₀ (X.target v₀ e) ≤ n)
    (hnotdist : X.distinguishedEdge v₀ (X.source v₀ e)
        (outwardEdgeCone_nonempty_of_source v₀ e) ≠ e) :
    aux w f v₀ n e = 0 := by
  match n with
  | 0 => rw [aux]
  | n + 1 =>
    simp only [aux, dite_eq_left_iff, not_lt]
    split_ifs
    · intro _
      apply aux_spec₀ _ _ _ hnotdist
      assumption
    intro h'
    simp only [auxBorder, Nat.reduceAdd]
    match n with
    | 0 | n + 1 =>
      rw [ite_eq_right_iff]
      intro hc
      contradiction

lemma aux_spec_outwardEdgeCone_erase (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    ∑ x ∈ (outwardEdgeCone v₀ v).erase (X.distinguishedEdge v₀ v hnonempty),
    aux w f v₀ n x = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_erase, ne_eq, mem_outwardEdgeCone_iff] at he
  apply aux_spec₀
  · rw [norm_target_eq_norm_source_add_one, he.right.right]
    omega
  · simp_rw [he.right.right]
    symm
    exact he.left

lemma aux_spec_distinguishedEdge (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n) (hlt : 0 < X.dist v₀ v)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    aux w f v₀ n (X.distinguishedEdge v₀ v hnonempty) =
      (w v)⁻¹ • f v - aux w f v₀ n (X.edgeTowardsOrigin v₀ v hlt) := by
  match n with
  | 0 => simp at hv
  | 1 =>
    /- Then `v = v₀`, but this is excluded. -/
    simp only [add_eq_right] at hv
    simp [hv] at hlt
  | n + 2 =>
      conv_lhs => rw [aux]
      simp only
      split_ifs
      · next h =>
        /- causes contradiction since `X.dist v₀ v + 1 = n + 1` -/
        rw [← hv] at h
        have : X.dist v₀ (source v₀ (distinguishedEdge v₀ v hnonempty)) + 1 <
            X.dist v₀ (target v₀ (distinguishedEdge v₀ v hnonempty)) := by
          simpa
        rw [norm_target_eq_norm_source_add_one] at this
        omega
      · next h₁ h₂ =>
        rw [aux]
        rw [add_left_inj, ← source_distinguishedEdge v₀ v hnonempty] at hv
        rw [← hv] at h₂
        have := norm_source_lt_norm_target v₀ (distinguishedEdge v₀ v hnonempty)
        omega
      · rw [auxBorder]
        simp only [source_distinguishedEdge, ↓reduceIte, sub_right_inj]
        rw [← aux_extends]
        simp only [edgeTowardsOrigin_target_eq]
        rw [add_left_inj] at hv
        rw [hv]

lemma aux_spec (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    w v • ∑ e ∈ X.incidenceFinset' v, aux w f v₀ n e = f v := by
  match n with
  | 0 =>
    /- the impossible case -/
    simp at hv
  | 1 =>
    /- the case `v = v₀` -/
    simp_rw [add_eq_right, dist_eq_zero_iff_eq_or_not_reachable] at hv
    have : X.Reachable v₀ v := X.isTree.connected.preconnected v₀ v
    have : v₀ = v := by tauto
    subst this
    simp_rw [← outwardEdgeCone_origin_eq]
    let ed : X.edgeSet := X.distinguishedEdge v₀ v₀ hnonempty
    have hed : ed ∈ X.outwardEdgeCone v₀ v₀ := distinguishedEdge_mem v₀ v₀ hnonempty
    rw [← Finset.insert_erase hed]
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.sum_insert]
    rw [aux_spec_outwardEdgeCone_erase]
    · simp_rw [add_zero, ed]
      rw [aux_spec_origin_distinguishedEdge]
      simp
    · simp
  | n + 2 =>
    /- the case `v ≠ v₀` -/
    have hdist : 0 < X.dist v₀ v := by
      rw [add_left_inj] at hv
      omega
    simp_rw [incidenceFinset_eq_union v₀ v hdist]
    rw [Finset.sum_union]
    · simp only [Finset.sum_singleton]
      let ed : X.edgeSet := X.distinguishedEdge v₀ v hnonempty
      have hed : ed ∈ X.outwardEdgeCone v₀ v := distinguishedEdge_mem v₀ v hnonempty
      rw [← Finset.insert_erase hed]
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
        Finset.sum_insert]
      rw [aux_spec_outwardEdgeCone_erase]
      · simp only [add_zero, smul_add, ed]
        rw [aux_spec_distinguishedEdge _ _ _ _ _ hv hdist, smul_sub]
        simp
      · simpa using hv
    · simp only [Finset.disjoint_singleton_left]
      apply edgeTowardsOrigin_not_mem_outwardEdgeCone

/-- The constructed preimage of a vertex function under the Laplacian. -/
def preimage (e : X.edgeSet) : M :=
  aux w f v₀ (X.dist v₀ (X.target v₀ e)) e

/-- The constructed preimage is indeed a preimage of the Laplacian. -/
lemma laplace_preimage (hinfinite : ∀ v, (X.outwardEdgeCone v₀ v).Nonempty) :
    X.laplace w (preimage w f v₀) = f := by
  ext v
  simp_rw [laplace, preimage]
  have : ∀ e ∈ incidenceFinset' v, aux w f v₀ (X.dist v₀ (X.target v₀ e)) e =
      aux w f v₀ (X.dist v₀ v + 1) e := by
    intro e he
    rw [mem_incidenceFinset'] at he
    have : X.dist v₀ (X.target v₀ e) ≤ X.dist v₀ v + 1 := by
      rcases eq_source_or_eq_target_of_mem v₀ e v he with h | h
      · subst h
        rw [norm_target_eq_norm_source_add_one]
      · subst h
        simp
    rwa [aux_extends' w f v₀ (X.dist v₀ v + 1)]
  simp_rw [Finset.sum_congr rfl this]
  rw [aux_spec]
  · simp
  · exact hinfinite v

end «Construction»

end Tree

end «Surjectivity»

/-- If `X` is a tree, the Laplacian on `X` is surjective. -/
lemma laplace_surjective {X : SimpleGraph V} (htree : IsTree X) [∀ v, Fintype (X.neighborSet v)]
    (w : V → Aˣ) (hmindeg : ∀ v, 2 ≤ X.degree v) : Function.Surjective (X.laplace (M := M) w) := by
  intro f
  let X : Tree V := ⟨X, htree⟩
  obtain ⟨v₀⟩ := X.isTree.connected.nonempty
  use X.preimage w f v₀
  apply X.laplace_preimage
  intro v
  exact X.outwardEdgeCone_nonempty_of_two_le_degree v₀ (hmindeg v)

section «Hom»

variable {X : SimpleGraph V}
variable [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ)

lemma laplace_apply (f : X.edgeSet → M) (v : V) :
    laplace w f v = w v • ∑ e ∈ X.incidenceFinset' v, f e :=
  rfl

@[simp]
lemma laplace_zero : X.laplace w (M := M) 0 = 0 := by
  ext x
  simp [laplace_apply]

@[simp]
lemma laplace_add (f g : X.edgeSet → M) : X.laplace w (f + g) = X.laplace w f + X.laplace w g := by
  ext x
  simp [laplace_apply, Finset.sum_add_distrib]

/-- The Laplacian of `X` as a group homomorphism. -/
@[simps]
def laplaceHom : (X.edgeSet → M) →+ (V → M) where
  toFun := X.laplace w
  map_zero' := laplace_zero w
  map_add' := laplace_add w

lemma laplaceHom_surjective (htree : X.IsTree) (hdeg : ∀ (v : V), 2 ≤ X.degree v) :
    Function.Surjective (X.laplaceHom (M := M) w) :=
  laplace_surjective htree w hdeg

@[simp]
lemma laplace_ASmul (a : A) (f : X.edgeSet → M) : X.laplace w (a • f) = a • X.laplace w f := by
  ext v
  simp [laplace_apply ,smul_comm a (w v), Finset.smul_sum]

lemma isLinearMap_laplace : IsLinearMap A (X.laplace (M := M) w) where
  map_add := laplace_add w
  map_smul := laplace_ASmul w

/-- The Laplacian of `X` as an `A`-linear map. -/
def laplaceLinearMap : (X.edgeSet → M) →ₗ[A] (V → M) := (isLinearMap_laplace w).mk'

@[simp]
lemma coe_laplaceLinearMap : ⇑(laplaceLinearMap w) = laplace (X := X) (M := M) w :=
  rfl

end «Hom»

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {V : Type*} [DecidableEq V]
variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]

/- We let `G` act on functions `V → R` and `X.edgeSet → R` on the left. -/
attribute [instance] arrowAction

section «ArrowAction»

variable {G A B : Type*} [DivisionMonoid G] [MulAction G A]

@[simp]
lemma arrowAction_apply (g : G) (f : A → B) (a : A) : (g • f) a = f (g⁻¹ • a) :=
  rfl

instance arrowDistribMulAction [AddMonoid B] : DistribMulAction G (A → B) where
  smul_zero g := by ext; simp
  smul_add g x y := by ext; simp

end «ArrowAction»

/- Act trivially on `Rˣ`. -/
instance instSMulUnitsLeanPool : SMul G Rˣ where
  smul _ x := x

omit [Group G] in
@[simp]
lemma smul_units (g : G) (x : Rˣ) : g • x = x := rfl

variable {G} {X}
variable [∀ v, Fintype (X.neighborSet v)] (w : V →[G] Rˣ)

@[simp]
lemma laplace_smul (g : G) (f : X.edgeSet → M) :
    laplace w (g • f) = g • laplace w f := by
  ext v
  simp only [laplace_apply, arrowAction_apply, map_smul, smul_units, smul_left_cancel_iff]
  let eq : X.edgeSet ≃ X.edgeSet := {
    toFun := fun e ↦ g⁻¹ • e
    invFun := fun e ↦ g • e
    left_inv := fun e ↦ by simp
    right_inv := fun e ↦ by simp
  }
  refine Finset.sum_equiv eq (fun e ↦ ?_) (fun e _ ↦ ?_)
  · simp [mem_incidenceFinset', eq]
  · simp [eq]

/-- The Laplacian of `X` as a `G`-module homomorphism. -/
noncomputable
def laplaceSMulHom : (X.edgeSet → M) →+[G] (V → M) where
  toFun := X.laplace w
  map_smul' := laplace_smul w
  map_zero' := laplace_zero w
  map_add' := laplace_add w

lemma laplaceSMulHom_surjective (htree : X.IsTree) (hdeg : ∀ (v : V), 2 ≤ X.degree v) :
    Function.Surjective (laplaceSMulHom (M := M) (X := X) w) :=
  laplace_surjective htree w hdeg

end SimpleGraph
