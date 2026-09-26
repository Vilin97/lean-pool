/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.Curve
public import LeanPool.Schoenflies.Concatenate
public import LeanPool.Schoenflies.Topology

/-!
# Separating curves, absorption, and the two cells of a crosscut

Definition 2.4 calls a Jordan curve *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with the curve as its boundary. Everything Part I proves
about a polygonal curve and Part II proves about a general one is packaged in that single
predicate, and the two lemmas below are the ones needed on both sides of the divide: they are
proved from the definition alone.

## The interface: `inside` and `outside` are total functions

The blueprint writes `Int(C)` and `Ext(C)` for the two regions and its consumers — the two
crosscut theorems — name them in their *statements*. So the two regions must be functions of
`C`, not sets produced by an existential inside the definition of separation. They are defined
here for an arbitrary set: `inside C` is the union of the bounded components of the complement
and `outside C` the union of the unbounded ones; together they partition `Cᶜ`.
Separation is then the assertion that each of the two halves is *one* region with boundary `C`
(Definition 2.4); that one is bounded and the other unbounded is then automatic, and so is
"exactly two regions", since a connected clopen piece of `Cᶜ` is a component of it.

`IsRegionOf C Ω` says `Ω` is one of the two, and `IsRegionPair C Ω Ω'` that `Ω, Ω'` are the two
in one order or the other. That is what lets Lemma 2.6 be stated once instead of twice: the
blueprint's `Ω` is sometimes `Int(C)` and sometimes `Ext(C)`, and every step of its proof is
symmetric in that choice.

## What the crosscut lemma actually needs

Lemma 2.6 is stated for a crosscut `P` of a separating curve `C` with arcs `A₁, A₂`, but its
proof never uses that `P` and the `Aᵢ` are arcs, nor the endpoints `p, q`, nor even that
`C = A₁ ∪ A₂`. What it uses is: `Aᵢ ⊆ C`, `P ∩ C ⊆ Aᵢ` (the crosscut meets the curve only in
the shared endpoints, which lie on both arcs), `Jᵢ = Aᵢ ∪ P` separating, and `A₁ ≠ A₂`. The
lemmas below are therefore stated at that level of generality, with `arcs_ne` supplying
`A₁ ≠ A₂` from the arc picture and `isJordanCurve_union` supplying the sentence "these are
Jordan curves" from `IsJordanCurve.of_two_arcs`.

One further hypothesis of the blueprint is dropped: `Ω` is described there as the region
containing `P ∖ {p, q}`, but what actually pins the roles of `Ω`, `Ω†`, `Wᵢ` and `Vᵢ` is the
inclusion `Ω† ⊆ Wᵢ`, which is a hypothesis here. A consumer supplies it by
`IsSeparating.exists_isRegionPair_subset`, which is the formal content of the blueprint's
"being connected it lies in one region of `ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".

## Blueprint

* `inside`, `outside`, `IsSeparating` — Definition 2.4 (separating Jordan curve).
* `IsSeparating.absorption` — Lemma 2.5 (absorption).
* `crosscut_cells` — Lemma 2.6 (crosscut cells), all three parts, with the per-part lemmas
  `cell_subset_region_diff`, `cell_isComponent`, `closure_cell_inter_curve` stated separately
  because the bundled form carries the hypotheses of both indices at once.
-/

public section

open Bornology Set

namespace Schoenflies

variable {C J P A A₁ A₂ Ω Ω' W V : Set Plane} {x p q : Plane}

/-! ### The inside and the outside of a set

Both are defined for an arbitrary set, without any separation hypothesis: `inside C` collects
the points whose component in the complement is bounded, `outside C` the rest of the
complement. -/

/-- The union of the bounded components of the complement — the blueprint's `Int(C)` once `C`
is known to be separating. -/
def inside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x)}

/-- The union of the unbounded components of the complement — the blueprint's `Ext(C)` once `C`
is known to be separating. -/
def outside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x)}

theorem mem_inside_iff : x ∈ inside C ↔ x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x) := Iff.rfl

theorem mem_outside_iff : x ∈ outside C ↔ x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x) :=
  Iff.rfl

theorem inside_subset_compl : inside C ⊆ Cᶜ := fun _ hx => hx.1

theorem outside_subset_compl : outside C ⊆ Cᶜ := fun _ hx => hx.1

theorem inside_union_outside (C : Set Plane) : inside C ∪ outside C = Cᶜ := by
  ext z
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    by_cases hb : IsBounded (connectedComponentIn Cᶜ z)
    · exact Or.inl ⟨hz, hb⟩
    · exact Or.inr ⟨hz, hb⟩

theorem disjoint_inside_outside : Disjoint (inside C) (outside C) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hb⟩ ⟨-, hb'⟩
  exact hb' hb

/-- Boundedness of the component is constant along a component, so the inside is a union of
whole components. -/
theorem connectedComponentIn_subset_inside (hx : x ∈ inside C) :
    connectedComponentIn Cᶜ x ⊆ inside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

theorem connectedComponentIn_subset_outside (hx : x ∈ outside C) :
    connectedComponentIn Cᶜ x ⊆ outside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

/-- A union of components of an open set is open. -/
theorem isOpen_inside (hC : IsClosed C) : IsOpen (inside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_inside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

theorem isOpen_outside (hC : IsClosed C) : IsOpen (outside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_outside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

/-! ### Definition 2.4: a separating Jordan curve -/

/-- Definition 2.4. A Jordan curve is *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with boundary `C`.

Since `inside C` and `outside C` always partition the complement into the bounded-component
part and the unbounded-component part, "exactly two regions, one bounded and one unbounded"
says precisely that each part is a single region; and the boundedness of one and unboundedness
of the other are then consequences rather than hypotheses (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`). -/
structure IsSeparating (C : Set Plane) : Prop where
  /-- The set is a Jordan curve. -/
  isJordanCurve : IsJordanCurve C
  /-- The bounded part of the complement is a single region. -/
  isConnected_inside : IsConnected (inside C)
  /-- The unbounded part of the complement is a single region. -/
  isConnected_outside : IsConnected (outside C)
  /-- The inside has the curve as its boundary. -/
  frontier_inside : frontier (inside C) = C
  /-- The outside has the curve as its boundary. -/
  frontier_outside : frontier (outside C) = C

namespace IsSeparating

theorem isClosed (h : IsSeparating C) : IsClosed C := h.isJordanCurve.isClosed

theorem isOpen_inside (h : IsSeparating C) : IsOpen (Schoenflies.inside C) :=
  Schoenflies.isOpen_inside h.isClosed

theorem isOpen_outside (h : IsSeparating C) : IsOpen (Schoenflies.outside C) :=
  Schoenflies.isOpen_outside h.isClosed

/-- The inside is bounded: it is connected and lies inside the complement, hence inside the
component of any of its points, which is bounded by definition of `inside`. -/
theorem isBounded_inside (h : IsSeparating C) : IsBounded (Schoenflies.inside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_inside.nonempty
  exact hz.2.subset
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hz inside_subset_compl)

/-- The outside is unbounded: it contains an unbounded component. -/
theorem not_isBounded_outside (h : IsSeparating C) : ¬ IsBounded (Schoenflies.outside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_outside.nonempty
  exact fun hb => hz.2 (hb.subset (connectedComponentIn_subset_outside hz))

/-- The inside really is one *region* of the complement, that is, a connected component of it:
it is a union of components which is itself connected. Together with its twin below this is
the "exactly two regions" clause of Definition 2.4. -/
theorem connectedComponentIn_eq_inside (h : IsSeparating C) (hx : x ∈ Schoenflies.inside C) :
    connectedComponentIn Cᶜ x = Schoenflies.inside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_inside hx)
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hx inside_subset_compl)

/-- The outside is a connected component of the complement. -/
theorem connectedComponentIn_eq_outside (h : IsSeparating C) (hx : x ∈ Schoenflies.outside C) :
    connectedComponentIn Cᶜ x = Schoenflies.outside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_outside hx)
    (h.isConnected_outside.isPreconnected.subset_connectedComponentIn hx outside_subset_compl)

end IsSeparating

/-! ### The two regions, named

`IsRegionOf C Ω` is "`Ω` is a region of `ℝ² ∖ C`" and `IsRegionPair C Ω Ω'` is "`Ω` and `Ω'`
are *the* two regions". Both are stated without a separation hypothesis; the facts that make
them useful carry one. -/

/-- `Ω` is a region of the complement of `C`. -/
def IsRegionOf (C Ω : Set Plane) : Prop := Ω = inside C ∨ Ω = outside C

/-- `Ω` and `Ω'` are the two regions of the complement of `C`, in one order or the other. -/
def IsRegionPair (C Ω Ω' : Set Plane) : Prop :=
  (Ω = inside C ∧ Ω' = outside C) ∨ (Ω = outside C ∧ Ω' = inside C)

/-- Every component of the complement is one of the two regions: there are no others. This is
the last clause of "exactly two regions". -/
theorem IsSeparating.isRegionOf_connectedComponentIn (h : IsSeparating C) (hx : x ∉ C) :
    IsRegionOf C (connectedComponentIn Cᶜ x) := by
  have hx' : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hx
  rcases hx' with hx' | hx'
  · exact Or.inl (h.connectedComponentIn_eq_inside hx')
  · exact Or.inr (h.connectedComponentIn_eq_outside hx')

namespace IsRegionOf

theorem inside (C : Set Plane) : IsRegionOf C (Schoenflies.inside C) := Or.inl rfl

theorem outside (C : Set Plane) : IsRegionOf C (Schoenflies.outside C) := Or.inr rfl

theorem subset_compl (h : IsRegionOf C Ω) : Ω ⊆ Cᶜ := by
  rcases h with rfl | rfl
  · exact inside_subset_compl
  · exact outside_subset_compl

theorem isOpen (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsOpen Ω := by
  rcases h with rfl | rfl
  · exact hC.isOpen_inside
  · exact hC.isOpen_outside

theorem isConnected (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsConnected Ω := by
  rcases h with rfl | rfl
  · exact hC.isConnected_inside
  · exact hC.isConnected_outside

/-- A region is a connected component of the complement. -/
theorem connectedComponentIn_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) (hx : x ∈ Ω) :
    connectedComponentIn Cᶜ x = Ω := by
  rcases h with rfl | rfl
  · exact hC.connectedComponentIn_eq_inside hx
  · exact hC.connectedComponentIn_eq_outside hx

theorem frontier_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : frontier Ω = C := by
  rcases h with rfl | rfl
  · exact hC.frontier_inside
  · exact hC.frontier_outside

/-- Every point of the curve is a limit of points of the region: this is the half of
`frontier Ω = C` that absorption uses. -/
theorem subset_closure (h : IsRegionOf C Ω) (hC : IsSeparating C) : C ⊆ closure Ω := by
  rw [← h.frontier_eq hC]
  exact frontier_subset_closure

/-- The closure of a region is the region together with the curve. -/
theorem closure_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : closure Ω = Ω ∪ C := by
  have hfr := h.frontier_eq hC
  rw [(h.isOpen hC).frontier_eq] at hfr
  rw [← hfr, Set.union_sdiff_cancel _root_.subset_closure]

end IsRegionOf

namespace IsRegionPair

theorem left (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem right (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem symm (h : IsRegionPair C Ω Ω') : IsRegionPair C Ω' Ω := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem union_eq (h : IsRegionPair C Ω Ω') : Ω ∪ Ω' = Cᶜ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inside_union_outside C
  · rw [Set.union_comm]
    exact inside_union_outside C

theorem disjoint (h : IsRegionPair C Ω Ω') : Disjoint Ω Ω' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact disjoint_inside_outside
  · exact disjoint_inside_outside.symm

/-- A connected set off the curve and off one region lies in the other. This is the only place
where "exactly two regions" is used, and it is used in exactly that form. -/
theorem subset_left_of_isPreconnected (h : IsRegionPair C Ω Ω') (hC : IsSeparating C)
    {S : Set Plane} (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : S ⊆ Cᶜ)
    (hSΩ' : Disjoint S Ω') : S ⊆ Ω := by
  obtain ⟨z, hz⟩ := hne
  have hcover : S ⊆ Ω ∪ Ω' := by rw [h.union_eq]; exact hSC
  have hzΩ : z ∈ Ω := (hcover hz).resolve_right fun hz' => Set.disjoint_left.1 hSΩ' hz hz'
  exact hS.subset_left_of_subset_union (h.left.isOpen hC) (h.right.isOpen hC) h.disjoint hcover
    ⟨z, hz, hzΩ⟩

end IsRegionPair

/-- A nonempty connected set disjoint from the curve lies in one of the two regions. This is
the well-definedness clause of Lemma 2.6: "being connected it lies in one region of
`ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined". -/
theorem IsSeparating.exists_isRegionPair_subset (hC : IsSeparating C) {S : Set Plane}
    (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : Disjoint S C) :
    ∃ W V, IsRegionPair C W V ∧ S ⊆ W := by
  obtain ⟨z, hz⟩ := hne
  have hSc : S ⊆ Cᶜ := fun w hw => Set.disjoint_left.1 hSC hw
  have hcover : S ⊆ inside C ∪ outside C := by rw [inside_union_outside]; exact hSc
  by_cases hzin : z ∈ inside C
  · exact ⟨inside C, outside C, Or.inl ⟨rfl, rfl⟩,
      hS.subset_left_of_subset_union hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
        hcover ⟨z, hz, hzin⟩⟩
  · refine ⟨outside C, inside C, Or.inr ⟨rfl, rfl⟩, ?_⟩
    refine hS.subset_left_of_subset_union hC.isOpen_outside hC.isOpen_inside
      disjoint_inside_outside.symm ?_ ⟨z, hz, (hcover hz).resolve_left hzin⟩
    rw [Set.union_comm]
    exact hcover

/-! ### Lemma 2.5: absorption -/

/-- Lemma 2.5 (absorption), set-theoretic core. If every point of `C` is a limit of points of
`Ω`, and `Ω` sits inside an open `V` whose frontier lies in `J`, then `C` misses `V` only where
`J` does. -/
theorem absorption_of_subset_closure (hCΩ : C ⊆ closure Ω) (hV : IsOpen V)
    (hfr : frontier V ⊆ J) (hsub : Ω ⊆ V) : C \ J ⊆ V := by
  rintro z ⟨hzC, hzJ⟩
  by_contra hzV
  -- `z` lies in the closure of `V` but not in `V`, so it lies on the frontier, hence in `J`.
  exact hzJ (hfr (by rw [hV.frontier_eq]; exact ⟨closure_mono hsub (hCΩ hzC), hzV⟩))

/-- Lemma 2.5 (absorption). If a region `Ω` of the complement of a separating curve `C` is
contained in a region `V` of the complement of a separating curve `J`, then all of `C` off `J`
lies in `V`. -/
theorem IsSeparating.absorption (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionOf C Ω) (hV : IsRegionOf J V) (hsub : Ω ⊆ V) : C \ J ⊆ V :=
  absorption_of_subset_closure (hΩ.subset_closure hC) (hV.isOpen hJ)
    (hV.frontier_eq hJ).subset hsub

/-! ### Lemma 2.6: the two cells of a crosscut

The setting: `C` is a separating curve, `Ω` and `Ω'` its two regions, `J` a separating curve
with `P ⊆ J ⊆ C ∪ P`, and `W, V` the two regions of `ℝ² ∖ J`, with `Ω' ⊆ W`. The blueprint's
`J` is `Aᵢ ∪ P` for one of the two arcs `Aᵢ`; the proof only needs the two inclusions. -/

/-- The far region `Ω'` absorbs all of `C` off `J`, so the near cell `V` misses `C` entirely:
the part of `C` off `J` is in `W`, and the part on `J` is off `V` because `V` misses `J`. -/
theorem disjoint_cell_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : Disjoint V C := by
  have hCW : C \ J ⊆ W := hC.absorption hJ hΩ' hWV.left hΩW
  rw [Set.disjoint_left]
  intro z hzV hzC
  by_cases hzJ : z ∈ J
  · exact hWV.right.subset_compl hzV hzJ
  · exact Set.disjoint_left.1 hWV.symm.disjoint hzV (hCW ⟨hzC, hzJ⟩)

/-- Lemma 2.6, first half of (a): the cell `V` is contained in `Ω ∖ P`. It misses `C`, it is
connected, and it misses `Ω'` because `Ω' ⊆ W`; so it lies in `Ω`. It misses `P` because it
misses `J ⊇ P`. -/
theorem cell_subset_region_diff (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) : V ⊆ Ω \ P := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ.right hWV hΩW
  have hVJ : V ⊆ Jᶜ := hWV.right.subset_compl
  -- `V` and `W` are the two regions of `ℝ² ∖ J`, and `Ω'` sits inside `W`.
  have hVΩ' : Disjoint V Ω' := hWV.symm.disjoint.mono_right hΩW
  have hVΩ : V ⊆ Ω :=
    hΩ.subset_left_of_isPreconnected hC (hWV.right.isConnected hJ).isPreconnected
      (hWV.right.isConnected hJ).nonempty (fun z hz => Set.disjoint_left.1 hVC hz) hVΩ'
  exact fun z hz => ⟨hVΩ hz, fun hzP => hVJ hz (hPJ hzP)⟩

/-- Lemma 2.6 (a): the cell `V` is a connected component of `Ω ∖ P`. Its frontier is `J`, which
lies in `C ∪ P` and so misses the open set `Ω ∖ P`; Lemma 1.7 does the rest. -/
theorem cell_isComponent (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) (hJCP : J ⊆ C ∪ P) :
    ∀ z ∈ V, connectedComponentIn (Ω \ P) z = V := by
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected
    (cell_subset_region_diff hC hJ hΩ hWV hΩW hPJ) ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hwΩ, hwP⟩
  rcases hJCP hwJ with hwC | hwP'
  · exact hΩ.left.subset_compl hwΩ hwC
  · exact hwP hwP'

/-- Lemma 2.6 (c): the closure of the cell meets `C` exactly in `J ∩ C`. The closure is
`V ∪ J`, and `V` misses `C`. -/
theorem closure_cell_inter_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : closure V ∩ C = J ∩ C := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ' hWV hΩW
  rw [hWV.right.closure_eq hJ, Set.union_inter_distrib_right, hVC.inter_eq, Set.empty_union]

/-! ### The arc-level side conditions

Two small facts turn the blueprint's arc picture into the hypotheses the lemmas above take. -/

/-- The two curves of Lemma 2.6 are Jordan curves: an arc from `p` to `q` and a second arc from
`p` to `q` meeting it only at those two points glue to a Jordan curve. -/
theorem isJordanCurve_union (hA : IsArcBetween A p q) (hP : IsArcBetween P p q)
    (hmeet : ∀ z ∈ A, z ∈ P → z = p ∨ z = q) : IsJordanCurve (A ∪ P) :=
  IsJordanCurve.of_two_arcs hA hP.reverse hmeet

/-- Lemma 2.6 (b), arc side: the two arcs of `C` from `p` to `q` are distinct, because they
meet only at `p` and `q` while neither is just `{p, q}`. -/
theorem arcs_ne (hmeet : A₁ ∩ A₂ ⊆ {p, q}) (hA : ¬ A₁ ⊆ {p, q}) : A₁ ≠ A₂ := by
  rintro rfl
  exact hA fun z hz => hmeet ⟨hz, hz⟩

/-! ### Lemma 2.6, bundled -/

/-- **Lemma 2.6 (crosscut cells).** Let `C` be a separating curve with regions `Ω` and `Ω'`,
let `A₁, A₂ ⊆ C` be the two arcs cut out by a crosscut `P` which meets `C` only in points of
both arcs, and suppose the two curves `Jᵢ = Aᵢ ∪ P` are separating. Let `Wᵢ` be the region of
`ℝ² ∖ Jᵢ` containing `Ω'` and `Vᵢ` the other one. Then

* (a) each `Vᵢ` is a connected component of `Ω ∖ P`;
* (b) `V₁ ≠ V₂`;
* (c) `closure Vᵢ ∩ C = Aᵢ`.

The blueprint proves (b) from the boundaries; here it falls straight out of (c), since
`V₁ = V₂` would make `A₁ = A₂`. -/
theorem crosscut_cells (hC : IsSeparating C)
    (hJ₁ : IsSeparating (A₁ ∪ P)) (hJ₂ : IsSeparating (A₂ ∪ P))
    (hA₁ : A₁ ⊆ C) (hA₂ : A₂ ⊆ C) (hP₁ : P ∩ C ⊆ A₁) (hP₂ : P ∩ C ⊆ A₂) (hne : A₁ ≠ A₂)
    (hΩ : IsRegionPair C Ω Ω')
    {W₁ V₁ W₂ V₂ : Set Plane}
    (hWV₁ : IsRegionPair (A₁ ∪ P) W₁ V₁) (hΩW₁ : Ω' ⊆ W₁)
    (hWV₂ : IsRegionPair (A₂ ∪ P) W₂ V₂) (hΩW₂ : Ω' ⊆ W₂) :
    (V₁ ⊆ Ω \ P ∧ ∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (V₂ ⊆ Ω \ P ∧ ∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      V₁ ≠ V₂ ∧ closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  -- The two inclusions that replace the arc hypotheses.
  have hPJ : ∀ A : Set Plane, P ⊆ A ∪ P := fun A => Set.subset_union_right
  have hJCP : ∀ {A : Set Plane}, A ⊆ C → A ∪ P ⊆ C ∪ P := fun hA =>
    Set.union_subset_union_left P hA
  -- (c): `(Aᵢ ∪ P) ∩ C = Aᵢ`, since `Aᵢ ⊆ C` and `P ∩ C ⊆ Aᵢ`.
  have hinter : ∀ {A : Set Plane}, A ⊆ C → P ∩ C ⊆ A → (A ∪ P) ∩ C = A := by
    intro A hAC hPC
    refine Set.Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hAC hz⟩
    rintro z ⟨hz | hz, hzC⟩
    · exact hz
    · exact hPC ⟨hz, hzC⟩
  have hc₁ : closure V₁ ∩ C = A₁ := by
    rw [closure_cell_inter_curve hC hJ₁ hΩ.right hWV₁ hΩW₁]; exact hinter hA₁ hP₁
  have hc₂ : closure V₂ ∩ C = A₂ := by
    rw [closure_cell_inter_curve hC hJ₂ hΩ.right hWV₂ hΩW₂]; exact hinter hA₂ hP₂
  refine ⟨⟨cell_subset_region_diff hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁),
      cell_isComponent hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁) (hJCP hA₁)⟩,
    ⟨cell_subset_region_diff hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂),
      cell_isComponent hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂) (hJCP hA₂)⟩, ?_, hc₁, hc₂⟩
  -- (b): equal cells would have equal closures, hence equal arcs.
  rintro rfl
  exact hne (hc₁.symm.trans hc₂)

end Schoenflies
