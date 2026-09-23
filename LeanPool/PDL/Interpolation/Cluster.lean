/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.FinePath
public import LeanPool.PDL.Interpolation.Local

/-! # Loaded Clusters (start of Section 9)

Note that we skip much of Subsection 8.2 because we worked already with split tableaux anyway.

This file covers Definitions 9.6 to 9.13 and Lemma 9.14. What comes after it is in
separate files: `Pdl.Interpolation.QFormula` has Definitions 9.15 and 9.16 and Fact 9.17,
`Pdl.PreInterpolant` has Definition 9.18, and `Pdl.ClusterInterpolation` has Lemma 9.3,
i.e. the interpolant for the root of a proper cluster. Counterexamples to Lemma 9.12 (c)
and (d) as stated in the paper are in `Pdl.ClusterCorrection`.
-/

@[expose] public section

namespace PDL

variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Collecting Cluster Nodes in a Finset

We define the finite sets `loadedBelow` and `loadedAbove` of nodes that are reachable from /
can reach a given node via `◃` *by filtering `allPaths`*: a tableau has only finitely many
nodes and `PathIn.elem_allPaths` says that `allPaths tab` contains all of them, so we can
simply keep those nodes that are `◃`-related to `p` in the desired direction.
Then `clusterListOf_spec` is immediate. -/

/-- Loaded nodes "below" the given one, also allowing ♥ steps. Includes the node itself. -/
def loadedBelow (p : PathIn tab) : Finset (PathIn tab) :=
  insert p ((allPaths tab).filter (fun q => ((p ◃⁺ q) ∧ (nodeAt q).isLoaded)))

/-- Loaded nodes "above" the given one, also allowing *backwards* ♥ steps.
Includes the node itself. -/
def loadedAbove (p : PathIn tab) : Finset (PathIn tab) :=
  insert p ((allPaths tab).filter (fun q => ((q ◃⁺ p) ∧ (nodeAt q).isLoaded)))

@[simp]
lemma mem_loadedBelow {p q : PathIn tab} :
    q ∈ loadedBelow p  ↔  q = p ∨ ((p ◃⁺ q) ∧ (nodeAt q).isLoaded) := by
  simp [loadedBelow, PathIn.elem_allPaths]

@[simp]
lemma mem_loadedAbove {p q : PathIn tab} :
    q ∈ loadedAbove p  ↔  q = p ∨ ((q ◃⁺ p) ∧ (nodeAt q).isLoaded) := by
  simp [loadedAbove, PathIn.elem_allPaths]

/-- A free node is alone in its cluster (cf. Remark 4.18 in the paper). -/
lemma eq_of_cEquiv_of_isFree {p q : PathIn tab}
    (p_free : (nodeAt p).isFree) (p_q : p ≡ᶜ q) : q = p := by
  rcases p_q with ⟨p_to_q, q_to_p⟩
  rcases Relation.ReflTransGen.cases_head p_to_q with p_eq_q | ⟨l, p_l, l_to_q⟩
  · exact p_eq_q.symm
  · exfalso
    have l_to_p : l ◃* p := Relation.ReflTransGen.trans l_to_q q_to_p
    cases p_l
    case inl p_edge_l =>
      have p_lt_l := ePropB.c_single p l p_free p_edge_l
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp l_to_p with l_eq_p | l_c_p
      · subst l_eq_p
        exact path_is_irreflexive (Relation.TransGen.single p_edge_l)
      · exact p_lt_l.2 l_c_p
    case inr p_heart_l =>
      have := (companion_loaded p_heart_l).1
      simp only [Sequent.isFree, this] at p_free
      simp at p_free

/-- The set of all other nodes in the same cluster, essentially a constructive version of
`clusterOf`. Computed as the intersection of `loadedAbove` and `loadedBelow`. -/
def clusterListOf (p : PathIn tab) : Finset (PathIn tab) :=
  loadedBelow p  ∩  loadedAbove p

lemma clusterListOf_spec {q : PathIn tab} (p : PathIn tab) :
    q ∈ clusterListOf p  ↔  p ≡ᶜ q := by
  rw [clusterListOf, Finset.mem_inter, mem_loadedBelow, mem_loadedAbove]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | ⟨p_q, -⟩
    · exact (eProp tab).1.refl _
    · rcases h2 with rfl | ⟨q_p, -⟩
      · exact (eProp tab).1.refl _
      · exact ⟨p_q.to_reflTransGen, q_p.to_reflTransGen⟩
  · intro p_c_q
    rcases eq_or_ne q p with rfl | q_ne_p
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · have q_loaded : (nodeAt q).isLoaded := by
        by_contra q_not_loaded
        exact q_ne_p (eq_of_cEquiv_of_isFree
          (by simp_all [Sequent.isFree]) ((cEquiv.symm p q).mp p_c_q)).symm
      exact ⟨ Or.inr ⟨Relation.TransGen_of_ReflTransGen p_c_q.1 (Ne.symm q_ne_p), q_loaded⟩
            , Or.inr ⟨Relation.TransGen_of_ReflTransGen p_c_q.2 q_ne_p, q_loaded⟩ ⟩

/-! ## Cluster roots -/

/-- Being a *cluster root*: there is no `◃` path from `s` back to a parent of `s`.
As a parent `p` of `s` always has a `◃` path to `s`, this says that no parent of `s` is
`≡ᶜ` to `s` (see `PathIn.isClusterRoot_iff`), i.e. that `s` is the first node of its own
cluster along the branch leading to `s`.

Note that this is *vacuously true* for `.nil`, the root of the whole tableau, which has no
parent at all. This is why we quantify over all parents instead of demanding that a parent
exists: the root of a tableau may already be loaded. -/
def PathIn.isClusterRoot (s : PathIn tab) : Prop :=
  ∀ p : PathIn tab, p ⋖_ s → ¬ s ◃* p

lemma PathIn.isClusterRoot_flip {p : PathIn tab}
    (h : p.isClusterRoot) : (p.flip).isClusterRoot := by
  intro q q_edge
  rw [← PathIn.flip_unflip q] at q_edge ⊢
  rw [edge_flip] at q_edge
  rw [cReach_flip]
  exact h _ q_edge

/-- The root of the whole tableau is a cluster root, because it has no parent. -/
lemma PathIn.isClusterRoot_nil :
    (PathIn.nil : PathIn tab).isClusterRoot := by
  intro p p_nil
  exfalso
  have := edge_then_length_lt p_nil
  simp at this

/-- Equivalent formulation of `PathIn.isClusterRoot` using `≡ᶜ`. -/
lemma PathIn.isClusterRoot_iff {s : PathIn tab} :
    s.isClusterRoot ↔ ∀ p : PathIn tab, p ⋖_ s → ¬ p ≡ᶜ s := by
  unfold PathIn.isClusterRoot cEquiv
  constructor
  · rintro h p p_s ⟨-, s_p⟩
    exact h p p_s s_p
  · intro h p p_s s_p
    exact h p p_s ⟨Relation.ReflTransGen.single (Or.inl p_s), s_p⟩

/-- If the parent of `t` is free, then `t` is a cluster root.
This is the case for all children of free nodes in the recursion of `tabToIntAt`. -/
lemma PathIn.isClusterRoot_of_edge_from_free {s t : PathIn tab}
    (s_free : (nodeAt s).isFree) (s_t : s ⋖_ t) : t.isClusterRoot := by
  rw [PathIn.isClusterRoot_iff]
  intro p p_t
  have p_eq_s : p = s := edge_leftInjective _ _ _ p_t s_t
  subst p_eq_s
  exact ePropB.h _ _ (ePropB.c_single _ _ s_free s_t)

/-- Def 8.14: `e` is an *exit* of the cluster of `s`, i.e. `e ∈ C⁺ \ C` where `C` is the
cluster of `s`: it is not in the cluster of `s`, but it is a child of a node in it. -/
def isExitOf (s e : PathIn tab) : Prop :=
  ¬ (e ≡ᶜ s)  ∧  ∃ t : PathIn tab, (t ≡ᶜ s) ∧ t ⋖_ e

lemma isExitOf_flip {s e : PathIn tab} :
    isExitOf s.flip e.flip ↔ isExitOf s e := by
  unfold isExitOf
  rw [cEquiv_flip]
  constructor
  · rintro ⟨no, t, t_s, t_e⟩
    refine ⟨no, t.unflip, ?_, ?_⟩
    · rw [← cEquiv_flip, PathIn.flip_unflip]
      exact t_s
    · rw [← edge_flip, PathIn.flip_unflip]
      exact t_e
  · rintro ⟨no, t, t_s, t_e⟩
    exact ⟨no, t.flip, cEquiv_flip.mpr t_s, edge_flip.mpr t_e⟩

/-- Exits of a cluster are cluster roots.
This is one of the two things needed to keep the `tabToIntAt` recursion going. -/
lemma isClusterRoot_of_isExitOf {s e : PathIn tab}
    (h : isExitOf s e) : e.isClusterRoot := by
  rcases h with ⟨e_not_s, t, t_s, t_e⟩
  rw [PathIn.isClusterRoot_iff]
  intro p p_e p_e_equiv
  absurd e_not_s
  have p_eq_t : p = t := edge_leftInjective _ _ _ p_e t_e
  subst p_eq_t
  exact ⟨p_e_equiv.2.trans t_s.1, t_s.2.trans p_e_equiv.1⟩

/-- If `u < s` then some parent of `s` is reachable from `u` (possibly `u` itself). -/
lemma exists_parent_of_lt {u s : PathIn tab} (h : u < s) :
    ∃ p : PathIn tab, u ≤ p ∧ p ⋖_ s := by
  cases h with
  | single u_s => exact ⟨u, Relation.ReflTransGen.refl, u_s⟩
  | tail u_d d_s => exact ⟨_, u_d.to_reflTransGen, d_s⟩

/-- Lemma 8.15 (a): clusters are subtrees. Here in the form we need it: the root of a
cluster is `≤` all nodes of its cluster. -/
lemma PathIn.le_of_cEquiv_of_isClusterRoot {s t : PathIn tab}
    (s_cr : s.isClusterRoot) (h : s ≡ᶜ t) : s ≤ t := by
  -- No node of the cluster of `s` is a proper ancestor of `s`:
  have not_lt : ∀ u : PathIn tab, u < s → s ◃* u → False := by
    intro u u_lt_s s_to_u
    obtain ⟨p, u_le_p, p_s⟩ := exists_parent_of_lt u_lt_s
    exact s_cr p p_s (s_to_u.trans (cReach_of_le u_le_p))
  -- Now walk along the `◃` path from `s`, staying inside the cluster.
  have key : ∀ u : PathIn tab, s ◃* u → u ◃* s → s ≤ u := by
    intro u s_to_u
    induction s_to_u with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail v u s_v v_u ih =>
      intro u_to_s
      have s_to_u : s ◃* u := s_v.tail v_u
      have s_le_v : s ≤ v := ih (Relation.ReflTransGen.head v_u u_to_s)
      rcases v_u with v_e_u | v_h_u
      · -- A child step goes down, so we can just extend the path.
        exact s_le_v.tail v_e_u
      · -- A companion step goes up, so we must use that `s` is a cluster root.
        have u_lt_v : u < v := companion_lt v_h_u
        rcases eq_or_ne s v with s_eq_v | s_ne_v
        · exact absurd (s_eq_v ▸ u_lt_v) (fun h => (not_lt u h s_to_u).elim)
        · have s_lt_v : s < v := Relation.TransGen_of_ReflTransGen s_le_v s_ne_v
          rcases path_revEuclidean' s u v s_lt_v u_lt_v with s_le_u | u_le_s
          · exact s_le_u
          · rcases eq_or_ne u s with u_eq_s | u_ne_s
            · exact u_eq_s ▸ Relation.ReflTransGen.refl
            · exact absurd (Relation.TransGen_of_ReflTransGen u_le_s u_ne_s)
                (fun h => (not_lt u h s_to_u).elim)
  exact key t h.1 h.2

/-- Exits of the cluster of a cluster root `s` are proper descendants of `s`.
This is the second thing needed to keep the `tabToIntAt` recursion going, and it needs
that clusters are subtrees, i.e. Lemma 8.15 (a). -/
lemma lt_of_isExitOf {s e : PathIn tab}
    (s_cr : s.isClusterRoot) (h : isExitOf s e) : s < e := by
  obtain ⟨-, t, t_s, t_e⟩ := h
  have s_le_t : s ≤ t := PathIn.le_of_cEquiv_of_isClusterRoot s_cr ((cEquiv.symm t s).mp t_s)
  exact Relation.TransGen.tail' s_le_t t_e

/-! ## Loaded Clusters -/

/-- A cluster, starting at a right-loaded `root` which is not ≡ᶜ to any parent of it.

Note that there is no explicit `parent` field: the root of the whole tableau may itself be
loaded and then has no parent. Instead, `root_not_to_parent` quantifies over all parents of
the root — which is exactly the property `PathIn.isClusterRoot` that `tabToIntAt` maintains
as an invariant. -/
structure LoadedCluster {X} (tab : Tableau .nil X) where
  /-- The root of the cluster. -/
  root : PathIn tab
  /-- There is no ◃ path from the root to any parent of it (so the root is indeed the root). -/
  root_not_to_parent : root.isClusterRoot
  /-- There is ◃ path from the root to itself (so we have a proper cluster). -/
  proper : root ◃⁺ root
  /-- The root is loaded on the right. -/
  root_loaded_right : (nodeAt root).2.2.isRight
  /-- The set of all paths in the cluster. -/
  CL : Finset (PathIn tab)
  /-- The root is in the cluster. -/
  root_mem_CL : root ∈ CL
  /-- All elements of `CL` are ≡ᶜ and thus can reach each other. -/
  CL_equiv : ∀ s ∈ CL, ∀ t ∈ CL, s ≡ᶜ t
  /-- All paths that are ≡ᶜ to something in `CL` are also in `CL`. -/
  CL_complete : ∀ s ∈ CL, ∀ t, (s ≡ᶜ t) → t ∈ CL
  /-- The root can reach all nodes of the cluster. -/
  root_reaches_all : ∀ s ∈ CL, root ◃* s

namespace LoadedCluster

-- The entry point is `clusterInterpolation` in `Pdl.ClusterInterpolation`, which is given
-- a node together with a proof
-- that it is a cluster root, and uses `LoadedCluster.ofClusterRoot` below.

/-- Make the `LoadedCluster` of a right-loaded node that is the first node of its cluster.
This is the way `tabToIntAt` now gets hold of a `LoadedCluster`. -/
def ofClusterRoot (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_proper : s ◃⁺ s)
    (s_loaded_right : (nodeAt s).2.2.isRight) : LoadedCluster tab where
  root := s
  root_not_to_parent := s_cr
  proper := s_proper
  root_loaded_right := s_loaded_right
  CL := clusterListOf s
  root_mem_CL := by
    rw [clusterListOf_spec]
    exact (eProp tab).1.refl s
  CL_equiv := by
    intro u u_in v v_in
    rw [clusterListOf_spec] at u_in v_in
    exact (eProp tab).1.trans ((eProp tab).1.symm u_in) v_in
  CL_complete := by
    intro u u_in v u_v
    rw [clusterListOf_spec] at u_in ⊢
    exact (eProp tab).1.trans u_in u_v
  root_reaches_all := by
    intro u u_in
    rw [clusterListOf_spec] at u_in
    exact u_in.1

/-- The exits of the cluster, i.e. `C⁺ \ C` from Def 8.14. -/
def exits (C : LoadedCluster tab) : Finset (PathIn tab) :=
  (C.CL.biUnion (fun t => t.children.image Subtype.val)).filter (fun e => e ∉ C.CL)

/-- C⁺, the cluster plus its exits. -/
def clPlus (C : LoadedCluster tab) : Finset (PathIn tab) :=
  C.CL ∪ C.exits

/-- The set `C.CL` contains exactly the exits in the sense of `isExitOf`. -/
lemma mem_CL_iff (C : LoadedCluster tab) (p : PathIn tab) :
    p ∈ C.CL ↔ p ≡ᶜ C.root :=
  ⟨ fun p_in => C.CL_equiv p p_in C.root C.root_mem_CL
  , fun p_c_root => C.CL_complete C.root C.root_mem_CL p ((cEquiv.symm p C.root).mp p_c_root) ⟩

/-- The set `C.exits` contains exactly the exits in the sense of `isExitOf`. -/
lemma mem_exits_iff (C : LoadedCluster tab) (e : PathIn tab) :
    e ∈ C.exits ↔ isExitOf C.root e := by
  rw [LoadedCluster.exits, Finset.mem_filter, Finset.mem_biUnion]
  simp only [isExitOf, ← PathIn.children_spec]
  constructor
  · rintro ⟨⟨t, t_in, t_e⟩, e_not_in⟩
    exact ⟨ fun e_c_root => e_not_in ((C.mem_CL_iff e).mpr e_c_root)
          , t, (C.mem_CL_iff t).mp t_in, t_e ⟩
  · rintro ⟨e_not_root, t, t_root, t_e⟩
    exact ⟨ ⟨t, (C.mem_CL_iff t).mpr t_root, t_e⟩
          , fun e_in => e_not_root ((C.mem_CL_iff e).mp e_in) ⟩

/-- All nodes that are `◃`-between the root of a cluster and itself are loaded. -/
lemma isLoaded_of_between (C : LoadedCluster tab) {v : PathIn tab}
    (h1 : C.root ◃* v) (h2 : v ◃* C.root) : (nodeAt v).isLoaded := by
  by_contra v_free
  have root_eq_v : C.root = v := eq_of_cEquiv_of_isFree v_free ⟨h2, h1⟩
  have v_right := C.root_loaded_right
  rw [root_eq_v] at v_right
  apply v_free
  rcases hh : nodeAt v with ⟨L, R, _|(o|o)⟩ <;> rw [hh] at v_right <;>
    simp_all [Sequent.isLoaded]

/-- Lemma 9.4 (a) -/
lemma all_right_loaded (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).2.2.isRight := by
  intro t t_in
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  exact (cReach_inv t_root.2
    (fun v h1 h2 => C.isLoaded_of_between h1 (h2.trans t_root.1)) C.root_loaded_right).1

/-- Lemma 9.4 (b): the left component of a node in the cluster is empty iff the left
component of the root of the cluster is empty. Note that here the left component is the
free side, because a `LoadedCluster` is loaded on the right.
As `Sequent.left ⟨L,R,O⟩ = L ∪ O.L` and `O.L = ∅` for the nodes in the cluster by
`LoadedCluster.all_right_loaded`, this is the same as `Λ₁(t) = ∅ ↔ Λ₁(r) = ∅`. -/
lemma left_empty_iff_root_left_empty (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).1 = ∅ ↔ (nodeAt C.root).1 = ∅ := by
  intro t t_in
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  constructor
  · exact (cReach_inv t_root.1
      (fun v h1 h2 => C.isLoaded_of_between (t_root.2.trans h1) h2)
      (C.all_right_loaded t t_in)).2
  · exact (cReach_inv t_root.2
      (fun v h1 h2 => C.isLoaded_of_between h1 (h2.trans t_root.1)) C.root_loaded_right).2

/-- Part of Lemma 9.4 (c): All children of t belong to C⁺. -/
lemma children_in_plus (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, ∀ c ∈ t.children, c.val ∈ C.clPlus := by
  intro t t_in c _
  rw [LoadedCluster.clPlus, Finset.mem_union]
  by_cases c_in : c.val ∈ C.CL
  · exact Or.inl c_in
  · refine Or.inr ((C.mem_exits_iff c.val).mpr ⟨fun c_root => c_in ?_, t, ?_, c.2⟩)
    · exact (C.mem_CL_iff c.val).mpr c_root
    · exact (C.mem_CL_iff t).mp t_in

/-- Part of Lemma 9.4 (c): If `t` is not an lpr, then at least one child is in C.
This needs that the cluster is proper, i.e. that its root lies on a `◃`-cycle. -/
lemma nonLpr_some_child_in_C (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, ¬ t.isLrep → ∃ c ∈ t.children, c.val ∈ C.CL := by
  intro t t_in t_not_lrep
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  -- Because the cluster is proper, also `t` lies on a `◃`-cycle:
  have t_cycle : t ◃⁺ t := Relation.TransGen.trans_right t_root.1
    (Relation.TransGen.trans_left C.proper t_root.2)
  obtain ⟨u, t_u, u_t⟩ := Relation.TransGen.head'_iff.mp t_cycle
  -- The first step of that cycle cannot be a ♥ step, because `t` is not an lpr:
  rcases t_u with t_edge_u | ⟨lpr, h_lrep, rfl⟩
  · rw [PathIn.children_spec, Finset.mem_image] at t_edge_u
    obtain ⟨c, c_in, rfl⟩ := t_edge_u
    exact ⟨c, c_in, (C.mem_CL_iff c.val).mpr ⟨u_t.trans t_root.1,
      t_root.2.trans (Relation.ReflTransGen.single (Or.inl c.2))⟩⟩
  · exact absurd (by unfold PathIn.isLrep; rw [h_lrep]; trivial) t_not_lrep

/-- Part of Lemma 9.4 (c): If t is an lpr, then its companion is in C. -/
lemma lpr_comp_in_C {comp} (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, t ♥ comp → comp ∈ C.CL := by
  intro t t_in t_comp
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  refine (C.mem_CL_iff comp).mpr ⟨?_, ?_⟩
  · -- comp ◃* root, because comp is above t.
    exact (cReach_of_le (companion_lt t_comp).to_reflTransGen).trans t_root.1
  · -- root ◃* comp, going via t.
    exact t_root.2.tail (Or.inr t_comp)

/-- Def 9.6: All nodes in cluster with a certain set of formulas on the right.
TODO: `.right` might not get or not keep track of the loaded formula!
Better use `Finset WhateverFormula` and `Sequent.wForms` here maybe?
-/
def nodesWith (C : LoadedCluster tab) (Δ : Finset Formula) : Finset (PathIn tab) :=
  C.CL.filter (fun p => (nodeAt p).right = Δ)

/-- The extended cluster nodes whose right component is the specified formula set. -/
def plusNodesWith (C : LoadedCluster tab) (Δ : Finset Formula) : Finset (PathIn tab) :=
  C.clPlus.filter (fun p => (nodeAt p).right = Δ)

/-! ### The cluster at the fine level

The `CL` field of a `LoadedCluster` only contains the nodes in the coarse `PathIn` sense.
For Definition 9.8 we also need the intermediate nodes inside the local tableaux, so we
now determine which fine nodes belong to the cluster.

An intermediate node `v` inside the local tableau at a node `p` of the cluster belongs to
the cluster iff some child of `p` below `v` is again in the cluster: in that case `v` lies
on a `◃` cycle. Note that the children of `p` are exactly the nodes `p.append (loc Y_in nil)`
for the end nodes `Y` of the local tableau at `p`, and they are labelled with `Y`. -/

/-- A fine node belongs to the cluster `C` iff its base node is in `C` and either it *is*
that base node, or one of the children of the base node below it is in `C`. -/
def memFine (C : LoadedCluster tab) (f : FinePathIn tab) : Prop :=
  f.base ∈ C.CL ∧ ( f.atBigRoot ∨ ∃ q ∈ f.coarseChildrenBelow, q ∈ C.CL )

instance instDecidableMemFine (C : LoadedCluster tab) (f : FinePathIn tab) :
    Decidable (C.memFine f) := by
  unfold memFine; infer_instance

/-- Nodes of the cluster in the coarse sense are also fine nodes of the cluster. -/
lemma memFine_toFine (C : LoadedCluster tab) {p : PathIn tab} (p_in : p ∈ C.CL) :
    C.memFine p.toFine := ⟨by simpa using p_in, Or.inl (by simp)⟩

/-- All fine nodes in the cluster `C`. -/
def fineCL (C : LoadedCluster tab) : List (FinePathIn tab) :=
  (allFinePaths tab).filter (fun f => decide (C.memFine f))

lemma mem_fineCL (C : LoadedCluster tab) (f : FinePathIn tab) :
    f ∈ C.fineCL ↔ C.memFine f := by
  simp [fineCL, f.mem_allFinePaths]

lemma root_toFine_mem_fineCL (C : LoadedCluster tab) : C.root.toFine ∈ C.fineCL :=
  (C.mem_fineCL _).mpr (C.memFine_toFine C.root_mem_CL)

/-- If a fine node of the cluster has a coarse child of the cluster below it, then it has
a fine child in the cluster. -/
lemma exists_child_memFine_aux (C : LoadedCluster tab) {f : FinePathIn tab}
    (f_base : f.base ∈ C.CL) {q : PathIn tab} (hq : q ∈ f.coarseChildrenBelow)
    (q_in : q ∈ C.CL) : ∃ g ∈ f.children, C.memFine g := by
  obtain ⟨g, g_in, hg⟩ := f.exists_child_coarseChildrenBelow q hq
  refine ⟨g, g_in, ?_⟩
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ f_base, Or.inr ⟨q, h2, q_in⟩⟩
  · exact ⟨h1 ▸ q_in, Or.inl h2⟩

/-- Lemma 9.7 (c) at the fine level, for nodes that are not coarse nodes: if a fine node
`f` inside a local tableau belongs to the cluster, then so does one of its children. -/
lemma exists_child_memFine (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : C.memFine f) (h_not : ¬ f.atBigRoot) : ∃ g ∈ f.children, C.memFine g := by
  obtain ⟨f_base, hor⟩ := hf
  rcases hor with h | ⟨q, q_below, q_in⟩
  · exact absurd h h_not
  · exact C.exists_child_memFine_aux f_base q_below q_in

/-- Lemma 9.7 (c) at the fine level, in general: any fine node of the cluster that is not
a loaded-path repeat has a child in the cluster. For coarse nodes this uses Lemma 9.4 (c),
i.e. `nonLpr_some_child_in_C`, and hence needs that the cluster is proper. -/
lemma exists_child_memFine_of_not_isLrep (C : LoadedCluster tab)
    {f : FinePathIn tab} (hf : C.memFine f) (h_lrep : ¬ f.base.isLrep) :
    ∃ g ∈ f.children, C.memFine g := by
  by_cases hbr : f.atBigRoot
  · obtain ⟨c, -, c_CL⟩ := C.nonLpr_some_child_in_C f.base hf.1 h_lrep
    have hmem : c.val ∈ f.base.toFine.coarseChildrenBelow :=
      PathIn.mem_coarseChildrenBelow_toFine _ _ c.2
    rw [← f.eq_toFine_base_of_atBigRoot hbr] at hmem
    exact C.exists_child_memFine_aux hf.1 hmem c_CL
  · exact C.exists_child_memFine hf hbr

/-- All fine nodes just outside the cluster `C`, i.e. `C⁺ \ C` at the fine level. -/
def fineExits (C : LoadedCluster tab) : Finset (FinePathIn tab) :=
  (C.fineCL.toFinset.sup FinePathIn.children).filter (fun f => decide (¬ C.memFine f))

/-- The fine version of `C⁺`. -/
def fineCLplus (C : LoadedCluster tab) : Finset (FinePathIn tab) :=
  C.fineCL.toFinset ∪ C.fineExits

/-- `Λ₂[C]`, the right components of the fine nodes of the cluster. -/
def lambdaTwo (C : LoadedCluster tab) : Finset Sequent :=
  (C.fineCL.toFinset.image (fun f => f.label.rightOnly))

/-- `Λ₂[C⁺]`, the right components of the fine nodes of the cluster and of its exits. -/
def lambdaTwoPlus (C : LoadedCluster tab) : Finset Sequent :=
  (C.fineCLplus.image (fun f => f.label.rightOnly))

/-- `C_Δ` from Def 9.6, at the fine level. -/
def nodesWithFine (C : LoadedCluster tab) (Δ : Sequent) : List (FinePathIn tab) :=
  C.fineCL.filter (fun f => decide (f.label.rightOnly = Δ))

/-- `C⁺_Δ` from Def 9.6, at the fine level. -/
def plusNodesWithFine (C : LoadedCluster tab) (Δ : Sequent) :
    Finset (FinePathIn tab) :=
  C.fineCLplus.filter (fun f => decide (f.label.rightOnly = Δ))

/-- `C^R_Δ` from Def 9.6: nodes with right component `Δ` where a right rule is applied. -/
def nodesWithFineRight (C : LoadedCluster tab) (Δ : Sequent) :
    List (FinePathIn tab) :=
  (C.nodesWithFine Δ).filter (fun f => f.usesRightRule)

/-- `C^L_Δ` from Def 9.6: nodes with right component `Δ` where a left rule is applied. -/
def nodesWithFineLeft (C : LoadedCluster tab) (Δ : Sequent) :
    List (FinePathIn tab) :=
  (C.nodesWithFine Δ).filter (fun f => f.usesLeftRule)

/-- Nodes with right component `Δ` where no rule is applied at all. These are the
loaded-path repeats and the closing rules, which Lemma 9.7 (a) in the paper does not
mention. -/
def nodesWithFineNoRule (C : LoadedCluster tab) (Δ : Sequent) :
    List (FinePathIn tab) :=
  (C.nodesWithFine Δ).filter (fun f => !f.usesLeftRule && !f.usesRightRule)

/-- Lemma 9.7 (a), first part: `C_Δ` is the union of `C^L_Δ` and `C^R_Δ` and the nodes
where no rule is applied. -/
lemma mem_nodesWithFine_iff (C : LoadedCluster tab) (Δ : Sequent) (f : FinePathIn tab) :
    f ∈ C.nodesWithFine Δ ↔
      f ∈ C.nodesWithFineLeft Δ ∨ f ∈ C.nodesWithFineRight Δ ∨ f ∈ C.nodesWithFineNoRule Δ := by
  simp only [nodesWithFineLeft, nodesWithFineRight, nodesWithFineNoRule, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro h
    by_cases hl : f.usesLeftRule
    · exact Or.inl ⟨h, hl⟩
    · by_cases hr : f.usesRightRule
      · exact Or.inr (Or.inl ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, by simp_all⟩)
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact h

/-- Lemma 9.7 (a), second part: `C^L_Δ` and `C^R_Δ` are disjoint. -/
lemma nodesWithFineLeft_disjoint_right (C : LoadedCluster tab) (Δ : Sequent) :
    ∀ f ∈ C.nodesWithFineLeft Δ, f ∉ C.nodesWithFineRight Δ := by
  intro f f_in f_in'
  simp only [nodesWithFineLeft, nodesWithFineRight, List.mem_filter] at f_in f_in'
  exact f.not_left_and_right ⟨f_in.2, f_in'.2⟩

/-- `Δ ∈ Λ₂[C]` iff `C_Δ ≠ ∅`, the remark after the invariant in Def 9.8. -/
lemma mem_lambdaTwo_iff (C : LoadedCluster tab) (Δ : Sequent) :
    Δ ∈ C.lambdaTwo ↔ C.nodesWithFine Δ ≠ [] := by
  simp [lambdaTwo, ne_eq, nodesWithFine, List.filter_eq_nil_iff, not_forall, decide_eq_true_eq]

/-- The right components of the children of a node in `C^R_Δ`.

For the quasi-tableau in Def 9.8 we need, given `Δ ∈ Λ₂[C]`, the sequents `Π₁, …, Πₙ`
obtained by applying the right rule to `Δ` — both for local rules (Lemma 9.7 (f)) and for
the modal rule when `Δ` is basic (Lemma 9.7 (e)). Instead of using uniformity to *choose*
such a rule we here simply *look up* the first node of `C^R_Δ` and read off the right
components of its children. By uniformity (which we do not prove here) this does not
depend on the chosen node. When `C^R_Δ` is empty — which by Lemma 9.7 (d) only happens
when `C_Δ` is empty, i.e. when `Δ ∉ Λ₂[C]` — we return the empty list, but note that the
construction of `Q` below never uses `stepOf` in that case. -/
def stepOf (C : LoadedCluster tab) (Δ : Sequent) : Finset Sequent :=
  match (C.nodesWithFineRight Δ).head? with
  | some f => f.children.image (fun g => g.label.rightOnly)
  | none => {}

/-- If some right rule is applied at a node of the cluster with right component `Δ`, then
`stepOf Δ` is non-empty: by Lemma 9.7 (c) that node has a child in the cluster, so the rule
applied there cannot be a closing rule. -/
lemma stepOf_ne_nil (C : LoadedCluster tab) {Δ : Sequent}
    (h : C.nodesWithFineRight Δ ≠ []) : C.stepOf Δ ≠ {} := by
  unfold stepOf
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hh) h
  | some f =>
    have f_in := List.mem_of_mem_head? hh
    simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at f_in
    obtain ⟨⟨f_CL, -⟩, f_right⟩ := f_in
    obtain ⟨g, g_in, -⟩ := C.exists_child_memFine_of_not_isLrep
      ((C.mem_fineCL f).mp f_CL) (f.not_isLrep_base_of_usesRightRule f_right)
    simp only [ne_eq, Finset.image_eq_empty]
    intro hnil
    rw [hnil] at g_in
    simp at g_in

/-- The sorted list of sequents produced by a cluster's step operation. -/
def stepOfL (C : LoadedCluster tab) : (Δ : Sequent) → List Sequent :=
  Finset.pdlSeqSort ∘ C.stepOf

lemma stepOfL_ne_nil (C : LoadedCluster tab) {Δ : Sequent}
    (h : C.nodesWithFineRight Δ ≠ []) : C.stepOfL Δ ≠ [] := by
  have := stepOf_ne_nil C h
  unfold stepOfL
  simp
  grind

/-! ### Uniformity

`stepOf` reads off the children of the *first* node of `C^R_Δ`. Using `head?` is a legitimate
way to implement the "unique local rule `R₂` with principal formula `ξ`" of Lemma 9.7 (f)
without making a choice, and it is harmless *as long as* all nodes of `C^R_Δ` agree on the
right components of their children — which is exactly what *uniformity* of the tableau
(conditions U1 and U2 in the paper) is for. Without uniformity nothing relates `stepOf Δ` to
the nodes of `C^R_Δ` other than the arbitrarily chosen first one, and the correctness proofs
of the pre-interpolants do need the relation for *every* node of the region `R_x = C^R_Δ`.

Two remarks. First, uniformity is only needed when `Δ` is not basic: when `Δ` is basic, the
rule applied at a node of `C^R_Δ` is the modal rule applied to the unique loaded formula of
`Δ` (Lemma 9.7 (e)), so the right components of the children are determined by `Δ` alone.
Second, `stepOf` produces an ordered *list*, so what is needed is agreement of the children
lists including their order; since the right components of the children of a node in
`C^R_Δ` are determined by `Δ` together with the rule and its principal formula, this follows
from uniformity in the form of Lemma 9.7 (f).

Uniformity is not available in this development yet, so for now we state the property that
is needed as an explicit assumption, and `stepOf_spec` shows that it suffices to justify the
use of `head?`. -/

/-- The consequence of uniformity that the quasi-tableau construction needs: any two nodes
of the cluster with the same right component `Δ` at which a right rule is applied have the
same right components below them, in the same order. Compare Lemma 9.7 (f). -/
def HasUniformSteps (C : LoadedCluster tab) : Prop :=
  ∀ Δ : Sequent, ∀ f ∈ C.nodesWithFineRight Δ, ∀ g ∈ C.nodesWithFineRight Δ,
    f.children.image (fun h => h.label.rightOnly) = g.children.image (fun h => h.label.rightOnly)

/-- Given `HasUniformSteps`, the list `stepOf Δ` really describes the right components of
the children of *every* node in `C^R_Δ`, and not just of the first one. -/
lemma stepOf_spec (C : LoadedCluster tab) (hU : C.HasUniformSteps) (Δ : Sequent)
    {f : FinePathIn tab} (hf : f ∈ C.nodesWithFineRight Δ) :
    f.children.image (fun g => g.label.rightOnly) = (C.stepOf Δ) := by
  unfold stepOf
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => rw [List.head?_eq_none_iff.mp hh] at hf; simp at hf
  | some g => exact hU Δ f hf g (List.mem_of_mem_head? hh)

/-- A child of a fine node of the cluster is a fine node of `C⁺`. -/
lemma mem_fineCLplus_of_child (C : LoadedCluster tab) {f g : FinePathIn tab}
    (hf : f ∈ C.fineCL) (hg : g ∈ f.children) : g ∈ C.fineCLplus := by
  by_cases h : C.memFine g
  · simp only [fineCLplus, Finset.mem_union, List.mem_toFinset, C.mem_fineCL g]
    exact Or.inl h
  · unfold fineCLplus
    simp_all [fineExits]
    grind

/-- The right component of a fine node of `C⁺` is in `Λ₂[C⁺]`. -/
lemma mem_lambdaTwoPlus_of_mem_fineCLplus (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : f ∈ C.fineCLplus) : f.label.rightOnly ∈ C.lambdaTwoPlus := by
  simp only [lambdaTwoPlus, Finset.mem_image]
  exact ⟨f, hf, rfl⟩

/-- `Λ₂[C] ⊆ Λ₂[C⁺]`. -/
lemma lambdaTwo_subset_lambdaTwoPlus (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, Δ ∈ C.lambdaTwoPlus := by
  intro Δ hΔ
  simp only [lambdaTwo, Finset.mem_image, List.mem_toFinset] at hΔ
  obtain ⟨f, hf, rfl⟩ := hΔ
  apply C.mem_lambdaTwoPlus_of_mem_fineCLplus
  unfold fineCLplus fineExits
  simp
  grind

/-- The labels given by `stepOf` are in `Λ₂[C⁺]`. This is the invariant needed in Def 9.8:
a node of `Q` is labelled with an element of `Λ₂[C⁺]`, and it is a leaf exactly when it is
a repeat or its label is not in `Λ₂[C]`, i.e. when it is an exit. -/
lemma stepOf_mem_lambdaTwoPlus (C : LoadedCluster tab) (Δ : Sequent) :
    ∀ Pi ∈ C.stepOf Δ, Pi ∈ C.lambdaTwoPlus := by
  intro Pi hPi
  unfold stepOf at hPi
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => rw [hh] at hPi; simp at hPi
  | some f =>
    rw [hh] at hPi
    simp only [Finset.mem_image] at hPi
    obtain ⟨g, hg, rfl⟩ := hPi
    have hf : f ∈ C.fineCL := by
      have := List.mem_of_mem_head? hh
      simp only [nodesWithFineRight, nodesWithFine, List.mem_filter] at this
      exact this.1.1
    exact C.mem_lambdaTwoPlus_of_mem_fineCLplus (C.mem_fineCLplus_of_child hf hg)

end LoadedCluster

/-! ### Interpolants for the exit regions (Def 9.13 and Lemma 9.14)

By the assumption of Lemma 9.3 we have an interpolant `θ_t` for every exit node
`t ∈ C⁺ \ C`. Here these are given by a map `θ` on the fine nodes; the assumption that
they are interpolants is `∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)`. -/

/-- `C⁺_Δ \ C_Δ`, i.e. the exit nodes whose right component is `Δ`. -/
def LoadedCluster.exitsWithFine (C : LoadedCluster tab) (Δ : Sequent) :
    Finset (FinePathIn tab) :=
  C.fineExits.filter (fun f => decide (f.label.rightOnly = Δ))

/-- Def 9.13: `θ_Δ`, the disjunction of the interpolants of all exit nodes whose right
component is `Δ`. Note that `θ_Δ = ⊥` in case there are no such exit nodes. -/
def LoadedCluster.thetaOf (C : LoadedCluster tab) (θ : FinePathIn tab → Formula)
    (Δ : Sequent) : Formula :=
  ((C.exitsWithFine Δ).image θ).pdlDis

/-- Membership in `C⁺_Δ \ C_Δ` means: being an exit node with right component `Δ`. -/
lemma LoadedCluster.mem_exitsWithFine_iff (C : LoadedCluster tab) (Δ : Sequent)
    (f : FinePathIn tab) :
    f ∈ C.exitsWithFine Δ ↔ f ∈ C.fineExits ∧ f.label.rightOnly = Δ := by
  simp [exitsWithFine]

/-- The right component of an exit node with right component `Δ` is the right component
of `Δ`. -/
lemma LoadedCluster.right_of_mem_exitsWithFine (C : LoadedCluster tab) {Δ : Sequent}
    {f : FinePathIn tab} (hf : f ∈ C.exitsWithFine Δ) : f.label.right = Δ.right := by
  rw [← ((C.mem_exitsWithFine_iff Δ f).mp hf).2]
  rfl

open HasSat in
/-- Lemma 9.14 (a): `Λ₁(t) ⊨ θ_Δ` for all `t ∈ C⁺_Δ \ C_Δ`. -/
lemma LoadedCluster.thetaOf_left (C : LoadedCluster tab) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) (Δ : Sequent) :
    ∀ f ∈ C.exitsWithFine Δ, ¬ satisfiable ({~ C.thetaOf θ Δ} ∪ f.label.left) := by
  rintro f hf ⟨W, M, w, hw⟩
  have hfE : f ∈ C.fineExits := ((C.mem_exitsWithFine_iff Δ f).mp hf).1
  refine (hθ f hfE).2.1 ⟨W, M, w, ?_⟩
  intro φ hφ
  rcases Finset.mem_union.mp hφ with hφ' | hmem
  · rw [Finset.mem_singleton] at hφ'
    subst hφ'
    have h1 : evaluate M w (~ C.thetaOf θ Δ) :=
      hw _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    simp only [evaluate, thetaOf, Finset.disEval, Finset.mem_image, exists_exists_and_eq_and,
      not_exists, not_and] at h1 ⊢
    intro hcon
    grind
  · exact hw _ (Finset.mem_union_right _ hmem)

open HasSat in
/-- Lemma 9.14 (b): `Δ ⊨ ¬θ_Δ`. -/
lemma LoadedCluster.thetaOf_right (C : LoadedCluster tab) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) (Δ : Sequent) :
    ¬ satisfiable ({C.thetaOf θ Δ} ∪ Δ.right) := by
  rintro ⟨W, M, w, hw⟩
  have h1 : evaluate M w (C.thetaOf θ Δ) :=
    hw _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
  rw [thetaOf, Finset.disEval] at h1
  obtain ⟨φ, hφ, hev⟩ := h1
  simp only [Finset.mem_image] at hφ
  obtain ⟨f, hf, rfl⟩ := hφ
  have hfE : f ∈ C.fineExits := ((C.mem_exitsWithFine_iff Δ f).mp hf).1
  refine (hθ f hfE).2.2 ⟨W, M, w, ?_⟩
  intro ψ hψ
  rcases Finset.mem_union.mp hψ with hψ' | hmem
  · rw [Finset.mem_singleton] at hψ'
    subst hψ'
    exact hev
  · exact hw _ (Finset.mem_union_right _ (C.right_of_mem_exitsWithFine hf ▸ hmem))

/-- Lemma 9.14 (c): the vocabulary of `θ_Δ` is included in the vocabulary of `Δ` and in the
union of the vocabularies of the left components of the exit nodes with right component
`Δ`. -/
lemma LoadedCluster.thetaOf_voc (C : LoadedCluster tab) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) (Δ : Sequent) :
    (C.thetaOf θ Δ).voc
      ⊆ Vocab.fromFinset ((C.exitsWithFine Δ).image
        (fun f => f.label.left.pdlFvoc)) ∩ Δ.right.pdlFvoc := by
  intro n hn
  rw [thetaOf, Finset.in_voc_dis] at hn
  obtain ⟨φ, hφ, hn⟩ := hn
  simp only [Finset.mem_image] at hφ
  obtain ⟨f, hf, rfl⟩ := hφ
  have hfE : f ∈ C.fineExits := ((C.mem_exitsWithFine_iff Δ f).mp hf).1
  have hsub := (hθ f hfE).1 hn
  simp only [jvoc, Finset.mem_inter] at hsub
  rw [Finset.mem_inter]
  refine ⟨?_, ?_⟩
  · rw [Vocab.fromFinset]
    simp only [Finset.pdlFvoc, Vocab.fromFinset, Finset.sup_image, Function.id_comp, Finset.mem_sup]
    use f
    simp_all
  · rw [← C.right_of_mem_exitsWithFine hf]
    exact hsub.2

end PDL
