/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.CrosscutCells
public import LeanPool.Schoenflies.CrosscutAtMostTwo
public import LeanPool.Schoenflies.TwoArcs

/-!
# The crosscut theorem for a general Jordan curve

`P` is a simple polygonal arc with distinct endpoints `p, q` on a Jordan curve `C` and all its
remaining points in `D = Int(C)`; `A₁, A₂` are the two arcs of `C` from `p` to `q`. Then
`D ∖ P` has exactly two components, namely `Int(A₁ ∪ P)` and `Int(A₂ ∪ P)`, and consequently
`ℝ² ∖ (C ∪ P)` has precisely three regions, with boundaries `C`, `A₁ ∪ P`, `A₂ ∪ P`.

The proof is short because both halves already exist. `Schoenflies.crosscut_cells` exhibits two
distinct components of `D ∖ P`; `Schoenflies.crosscut_components_exhaust` says there are no
others; and the final paragraph is `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`
applied three times. All this module does is fit the pieces together and name the result.

## The two sides are named by their arcs, and they are `inside (Aᵢ ∪ P)`

Everything Part II asks of this theorem is asked of *one labelled side*:
`lem:crosscut-side-correspondence` wants "the component whose closure meets `C` in `Aᵢ`" as a
function of `i`, and `prop:initial-pair`, `lem:cellulation-invariants` and `thm:finite-transfer`
all consume the labelled form. So there is no existential anywhere in the conclusions below: the
side belonging to the arc `A` is literally `Schoenflies.inside (A ∪ P)`, which is already a
function of `A`, carries the whole `inside`/`IsSeparating` API, and is exactly the set the
blueprint writes `Int(A ∪ P)`. The labelling lemma is `IsCrosscut.closure_side_inter`:

    closure (inside (A₁ ∪ P)) ∩ C = A₁.

Each statement is proved for `A₁` only; `IsCutPair.symm` swaps the two arcs, so
`h.foo hjordan hcut.symm` is the `A₂` instance of `h.foo hjordan hcut`. That is why no lemma
below mentions `A₂` in its conclusion.

## What is assumed

Two hypotheses are threaded through, both of which are being discharged elsewhere right now:

* `hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S` — `thm:jordan`. Only the
  separation clause is used; the boundary clause is part of `Schoenflies.IsSeparating`, so no
  second hypothesis is needed.
* `hcollars : HasArcCollars (inside C) P` — blueprint Lemma 1.8 (b) for the arc `P` inside the
  Jordan domain, the standing hypothesis of `Schoenflies/CrosscutAtMostTwo.lean`.

Neither is a restatement of anything proved here.

## Blueprint

* `Schoenflies.IsCrosscut` — the hypotheses of `thm:general-crosscut` on `C, P, p, q`.
* `Schoenflies.IsCutPair` — "`A₁, A₂` the two arcs of `C` from `p` to `q`, as in
  `lem:jordan-circle`"; `Schoenflies.exists_isCutPair` produces one from
  `IsJordanCurve.two_arcs`.
* `Schoenflies.IsCrosscut.side_subset`, `.side_isComponent`, `.closure_side_inter`,
  `.side_ne`, `.disjoint_sides`, `.components_eq`, `.inside_diff_eq` — the first half of
  `thm:general-crosscut`, one labelled side at a time, and then the exhaustion. The side's own
  topology comes with it: `.isOpen_side`, `.isConnected_side`, `.isBounded_side`,
  `.side_nonempty`, `.frontier_side`, `.closure_side`.
* `Schoenflies.general_crosscut` — `thm:general-crosscut`, first sentence, bundled.
* `Schoenflies.IsCrosscut.compl_eq`, `.compl_eq_three`, `.outside_isComponent`,
  `.side_isComponent_compl`, `.three_regions` — the "consequently" sentence.
* `Schoenflies.general_crosscut_three_regions` — `thm:general-crosscut`, second sentence,
  bundled, with the three boundaries.
* `Schoenflies.IsArcBetween.not_subset_pair` — an arc is more than its two endpoints; general,
  and the only new fact about arcs this module needs.
-/

@[expose] public section

open Bornology Set unitInterval

namespace Schoenflies

variable {C P A A₁ A₂ : Set Plane} {p q z : Plane}

/-! ### An arc is more than its two endpoints

This is what `Schoenflies.arcs_ne` needs in order to conclude `A₁ ≠ A₂` from the fact that the
two arcs meet only at `p` and `q`. It is a general fact about arcs and belongs in
`Schoenflies/Curve.lean`; it is here because nothing on `main` states it. -/

/-- An arc between two points is not just those two points: the midpoint parameter carries a
third point of it, because the parametrisation is injective. -/
theorem IsArcBetween.not_subset_pair (h : IsArcBetween A p q) : ¬ A ⊆ ({p, q} : Set Plane) := by
  obtain ⟨f, -, hi, rfl, rfl, rfl⟩ := h
  intro hsub
  have hhalf : (1 / 2 : ℝ) ∈ I := ⟨by norm_num, by norm_num⟩
  have hmem := hsub (mem_image_of_mem f hhalf)
  simp only [mem_insert_iff, mem_singleton_iff] at hmem
  rcases hmem with h' | h'
  · exact absurd (hi hhalf zero_mem_I h') (by norm_num)
  · exact absurd (hi hhalf one_mem_I h') (by norm_num)

/-! ### The configuration

Two bundles of hypotheses. `IsCrosscut C P p q` is the blueprint's "`P` is a simple polygonal
arc with distinct endpoints `p, q ∈ C` and all other points in `D = Int(C)`"; distinctness of
`p` and `q` is *not* a field, since an arc between two points always has them distinct.
`IsCutPair C p q A₁ A₂` is "`A₁, A₂` are the two arcs of `C` from `p` to `q`". The two are kept
apart because the arcs are a *choice* — swapping them is a symmetry of the whole theorem, and
`IsCutPair.symm` is what makes every statement below need proving only once. -/

/-- **The crosscut configuration.** A Jordan curve `C` and a simple polygonal arc `P` from
`p ∈ C` to `q ∈ C` whose remaining points all lie in the Jordan domain `inside C`. -/
structure IsCrosscut (C P : Set Plane) (p q : Plane) : Prop where
  /-- `C` is a Jordan curve. -/
  curve : IsJordanCurve C
  /-- `P` is a simple arc from `p` to `q`. -/
  arc : IsArcBetween P p q
  /-- `P` is polygonal. -/
  polygonal : IsPolygonal P
  /-- The first endpoint is on the curve. -/
  left_mem : p ∈ C
  /-- The second endpoint is on the curve. -/
  right_mem : q ∈ C
  /-- Every other point of the crosscut is inside the curve. -/
  sdiff_subset : P \ {p, q} ⊆ inside C

/-- **The two arcs of `C` from `p` to `q`**, as in `lem:jordan-circle`: two arcs between the
same two points which cover the curve and meet in exactly those two points. -/
structure IsCutPair (C : Set Plane) (p q : Plane) (A₁ A₂ : Set Plane) : Prop where
  /-- The first piece is an arc from `p` to `q`. -/
  fst : IsArcBetween A₁ p q
  /-- The second piece is an arc from `p` to `q`. -/
  snd : IsArcBetween A₂ p q
  /-- The two pieces cover the curve. -/
  union_eq : A₁ ∪ A₂ = C
  /-- The two pieces meet exactly at the two cut points. -/
  inter_eq : A₁ ∩ A₂ = {p, q}

namespace IsCutPair

/-- Swapping the two arcs. Every conclusion of this module is proved for `A₁` and obtained for
`A₂` by composing with this. -/
theorem symm (h : IsCutPair C p q A₁ A₂) : IsCutPair C p q A₂ A₁ :=
  ⟨h.snd, h.fst, by rw [union_comm]; exact h.union_eq, by rw [inter_comm]; exact h.inter_eq⟩

theorem fst_subset (h : IsCutPair C p q A₁ A₂) : A₁ ⊆ C := by
  rw [← h.union_eq]; exact subset_union_left

theorem snd_subset (h : IsCutPair C p q A₁ A₂) : A₂ ⊆ C := h.symm.fst_subset

/-- The two arcs are distinct: they meet only at `p` and `q`, and neither is just `{p, q}`. -/
theorem ne (h : IsCutPair C p q A₁ A₂) : A₁ ≠ A₂ :=
  arcs_ne h.inter_eq.subset h.fst.not_subset_pair

end IsCutPair

/-- Two distinct points of a Jordan curve cut it into a pair of arcs. This is
`IsJordanCurve.two_arcs`, repackaged. -/
theorem exists_isCutPair (hC : IsJordanCurve C) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A₁ A₂, IsCutPair C p q A₁ A₂ := by
  obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hC.two_arcs hp hq hpq
  exact ⟨A, B, hA, hB, hcov, hmeet⟩

/-! ### Elementary consequences of the configuration

Nothing here needs `thm:jordan`: these are the set-theoretic facts that turn "the crosscut runs
inside the curve" into the hypotheses `Schoenflies.crosscut_cells` takes. -/

namespace IsCrosscut

theorem left_notMem_inside (h : IsCrosscut C P p q) : p ∉ inside C := fun hp =>
  inside_subset_compl hp h.left_mem

theorem right_notMem_inside (h : IsCrosscut C P p q) : q ∉ inside C := fun hq =>
  inside_subset_compl hq h.right_mem

/-- **The crosscut meets the curve exactly at its two endpoints.** Everything else on the
crosscut is inside the curve, hence off it. -/
theorem inter_eq (h : IsCrosscut C P p q) : P ∩ C = {p, q} := by
  refine Subset.antisymm (fun z hz => ?_) (pair_subset ⟨h.arc.left_mem, h.left_mem⟩
    ⟨h.arc.right_mem, h.right_mem⟩)
  by_contra hzpq
  exact inside_subset_compl (h.sdiff_subset ⟨hz.1, hzpq⟩) hz.2

/-- **The crosscut misses the outside of the curve entirely**: its endpoints are on the curve
and everything else is inside. This is the sentence the three-region half opens with. -/
theorem disjoint_outside (h : IsCrosscut C P p q) : Disjoint P (outside C) := by
  rw [disjoint_left]
  intro z hzP hzO
  by_cases hz : z ∈ ({p, q} : Set Plane)
  · rcases hz with rfl | rfl
    exacts [hzO.1 h.left_mem, hzO.1 h.right_mem]
  · exact disjoint_left.1 disjoint_inside_outside (h.sdiff_subset ⟨hzP, hz⟩) hzO

/-- `P ∩ C ⊆ A₁`: the crosscut meets the curve only in the two points that lie on *both* arcs.
This is the hypothesis `hP₁` of `Schoenflies.crosscut_cells`. -/
theorem inter_subset_arc (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    P ∩ C ⊆ A₁ := by
  rw [h.inter_eq]
  exact pair_subset hcut.fst.left_mem hcut.fst.right_mem

/-- `(A₁ ∪ P) ∩ C = A₁`: the curve `J₁` of the blueprint meets `C` exactly in the arc it was
built from. This is what turns clause (c) of `Schoenflies.crosscut_cells` into the labelling
lemma. -/
theorem arc_union_inter (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    (A₁ ∪ P) ∩ C = A₁ := by
  refine Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hcut.fst_subset hz⟩
  rintro z ⟨hz | hz, hzC⟩
  · exact hz
  · exact h.inter_subset_arc hcut ⟨hz, hzC⟩

/-- **`J₁ = A₁ ∪ P` is a Jordan curve.** The arc and the crosscut are two arcs from `p` to `q`
meeting only at those two points. -/
theorem isJordanCurve_union (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    IsJordanCurve (A₁ ∪ P) := by
  refine _root_.Schoenflies.isJordanCurve_union hcut.fst h.arc fun z hzA hzP => ?_
  have hz : z ∈ ({p, q} : Set Plane) := h.inter_eq ▸ ⟨hzP, hcut.fst_subset hzA⟩
  simpa using hz

/-! ### The two separating curves, and where the outside of `C` sits

This is the paragraph of the blueprint proof that pins the roles of `Wᵢ` and `Vᵢ`:
`Ω† = Ext(C)` is connected, unbounded and disjoint from `Jᵢ`, hence lies in `Ext(Jᵢ)`. -/

theorem isSeparating_curve (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) : IsSeparating C :=
  hjordan C h.curve

theorem isSeparating_union (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsSeparating (A₁ ∪ P) :=
  hjordan _ (h.isJordanCurve_union hcut)

/-- **`Ext(C) ⊆ Ext(A ∪ P)`.** The outside of `C` is connected and misses `A ∪ P`, so it lies in
one component of the complement of `A ∪ P`; being unbounded, that component is unbounded, which
is what `Schoenflies.outside` records.

Stated for an arbitrary `A ⊆ C`, since that is all the argument uses. -/
theorem outside_subset_outside_union
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hA : A ⊆ C) : outside C ⊆ outside (A ∪ P) := by
  have hsep := h.isSeparating_curve hjordan
  have hsub : outside C ⊆ (A ∪ P)ᶜ := by
    rintro z hz (hzA | hzP)
    · exact hz.1 (hA hzA)
    · exact disjoint_left.1 h.disjoint_outside hzP hz
  intro z hz
  refine ⟨hsub hz, fun hb => hsep.not_isBounded_outside (hb.subset ?_)⟩
  exact hsep.isConnected_outside.isPreconnected.subset_connectedComponentIn hz hsub

/-- The pair `(Ext(C), Int(C))` in the shape `Schoenflies.crosscut_cells` takes for `(Ω, Ω')`,
with `Ω = Int(C)` the region the crosscut runs in. -/
theorem isRegionPair_curve (C : Set Plane) : IsRegionPair C (inside C) (outside C) :=
  Or.inl ⟨rfl, rfl⟩

/-- The pair `(Wᵢ, Vᵢ) = (Ext(Jᵢ), Int(Jᵢ))`. -/
theorem isRegionPair_union (J : Set Plane) : IsRegionPair J (outside J) (inside J) :=
  Or.inr ⟨rfl, rfl⟩

/-! ### The first half: `Int(A₁ ∪ P)` is a component of `Int(C) ∖ P` with closure meeting `C`
in `A₁`

Three applications of `Schoenflies.crosscut_cells`, one clause each. Everything is stated for the
arc `A₁`; `IsCutPair.symm` supplies the `A₂` instance. -/

/-- **`Int(A₁ ∪ P) ⊆ Int(C) ∖ P`.** Clause (a) of `lem:crosscut-cells`, first half. -/
theorem side_subset (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ⊆ inside C \ P :=
  cell_subset_region_diff (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (isRegionPair_curve C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset) subset_union_right

/-- **`Int(A₁ ∪ P)` is a connected component of `Int(C) ∖ P`.** Clause (a) of
`lem:crosscut-cells`. -/
theorem side_isComponent (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    ∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) :=
  cell_isComponent (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (isRegionPair_curve C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset) subset_union_right
    (union_subset_union_left P hcut.fst_subset)

/-- **The labelling lemma: the closure of the side meets `C` exactly in its own arc.** Clause
(c) of `lem:crosscut-cells`. This is what makes `A ↦ inside (A ∪ P)` the correspondence
`lem:crosscut-side-correspondence` asks for, and it is what distinguishes the two sides. -/
theorem closure_side_inter (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    closure (inside (A₁ ∪ P)) ∩ C = A₁ := by
  rw [closure_cell_inter_curve (h.isSeparating_curve hjordan) (h.isSeparating_union hjordan hcut)
    (IsRegionOf.outside C) (isRegionPair_union (A₁ ∪ P))
    (h.outside_subset_outside_union hjordan hcut.fst_subset)]
  exact h.arc_union_inter hcut

/-- **The two sides are distinct.** Equal sides would have equal closures, hence equal arcs. -/
theorem side_ne (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) := by
  intro heq
  have h₁ := h.closure_side_inter hjordan hcut
  have h₂ := h.closure_side_inter hjordan hcut.symm
  rw [heq] at h₁
  exact hcut.ne (h₁.symm.trans h₂)

theorem side_nonempty (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : (inside (A₁ ∪ P)).Nonempty :=
  (h.isSeparating_union hjordan hcut).isConnected_inside.nonempty

theorem isOpen_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsOpen (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isOpen_inside

theorem isConnected_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) : IsConnected (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isConnected_inside

theorem isBounded_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    IsBounded (inside (A₁ ∪ P)) :=
  (h.isSeparating_union hjordan hcut).isBounded_inside

/-- **The boundary of the side is its own Jordan curve `A₁ ∪ P`.** -/
theorem frontier_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    frontier (inside (A₁ ∪ P)) = A₁ ∪ P :=
  (h.isSeparating_union hjordan hcut).frontier_inside

/-- The closure of the side is the side together with its boundary curve. Paired with
`closure_side_inter` this is the form `lem:crosscut-side-correspondence` reads the closure in. -/
theorem closure_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    closure (inside (A₁ ∪ P)) = inside (A₁ ∪ P) ∪ (A₁ ∪ P) :=
  (IsRegionOf.inside (A₁ ∪ P)).closure_eq (h.isSeparating_union hjordan hcut)

/-- The two sides are disjoint: they are distinct components of the same set. -/
theorem disjoint_sides (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) := by
  rw [disjoint_left]
  intro z hz₁ hz₂
  exact h.side_ne hjordan hcut
    ((h.side_isComponent hjordan hcut z hz₁).symm.trans
      (h.side_isComponent hjordan hcut.symm z hz₂))

/-! ### The second half: there are no other components

`Schoenflies.crosscut_components_exhaust` applied to the two sides, which the previous section
has just shown to be distinct components. -/

/-- **Every component of `Int(C) ∖ P` is one of the two sides.** This is the "at most two"
half, `lem:crosscut-at-most-two`, applied to the two components `lem:crosscut-cells` produced. -/
theorem components_eq (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    ∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
      connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P) := by
  have hsep := h.isSeparating_curve hjordan
  obtain ⟨v₁, hv₁⟩ := h.side_nonempty hjordan hcut
  obtain ⟨v₂, hv₂⟩ := h.side_nonempty hjordan hcut.symm
  have hc₁ := h.side_isComponent hjordan hcut v₁ hv₁
  have hc₂ := h.side_isComponent hjordan hcut.symm v₂ hv₂
  have hexh := crosscut_components_exhaust hsep.isOpen_inside
    hsep.isConnected_inside.isPreconnected h.arc h.polygonal
    h.left_notMem_inside h.right_notMem_inside h.sdiff_subset hcollars
    (h.side_subset hjordan hcut hv₁) (h.side_subset hjordan hcut.symm hv₂)
    (by rw [hc₁, hc₂]; exact h.side_ne hjordan hcut)
  intro z hz
  rcases hexh z hz with hzz | hzz
  · rw [hc₁] at hzz
    exact Or.inl (h.side_isComponent hjordan hcut z hzz)
  · rw [hc₂] at hzz
    exact Or.inr (h.side_isComponent hjordan hcut.symm z hzz)

/-- **`Int(C) ∖ P` is the disjoint union of the two sides.** -/
theorem inside_diff_eq (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
  refine Subset.antisymm (fun z hz => ?_)
    (union_subset (h.side_subset hjordan hcut) (h.side_subset hjordan hcut.symm))
  rcases h.components_eq hjordan hcut hcollars z hz with heq | heq
  · exact Or.inl (heq ▸ mem_connectedComponentIn hz)
  · exact Or.inr (heq ▸ mem_connectedComponentIn hz)

end IsCrosscut

/-- **Theorem "Crosscut theorem", first sentence** (`thm:general-crosscut`). `Int(C) ∖ P` has
exactly two components, namely `Int(A₁ ∪ P)` and `Int(A₂ ∪ P)`.

"Exactly two" is spelled out: the two sets are nonempty, disjoint, each is a component, they
cover, they are distinct, and every component is one of them. The last two clauses are the
labelling `closure (inside (Aᵢ ∪ P)) ∩ C = Aᵢ`, which is what tells the two apart. Each clause
is separately available as a lemma in the `Schoenflies.IsCrosscut` namespace; this bundle exists
only so that the blueprint statement appears once, in one place. -/
theorem general_crosscut (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    inside C \ P = inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      (inside (A₁ ∪ P)).Nonempty ∧ (inside (A₂ ∪ P)).Nonempty ∧
      inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ inside C \ P, connectedComponentIn (inside C \ P) z = inside (A₁ ∪ P) ∨
        connectedComponentIn (inside C \ P) z = inside (A₂ ∪ P)) ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧ closure (inside (A₂ ∪ P)) ∩ C = A₂ :=
  ⟨h.inside_diff_eq hjordan hcut hcollars, h.disjoint_sides hjordan hcut,
    h.side_nonempty hjordan hcut, h.side_nonempty hjordan hcut.symm, h.side_ne hjordan hcut,
    h.side_isComponent hjordan hcut, h.side_isComponent hjordan hcut.symm,
    h.components_eq hjordan hcut hcollars, h.closure_side_inter hjordan hcut,
    h.closure_side_inter hjordan hcut.symm⟩

/-! ### The three regions of `ℝ² ∖ (C ∪ P)`

The blueprint's final paragraph. `P` misses `Ext(C)`, so the complement of `C ∪ P` splits as
`Ext(C) ⊔ (Int(C) ∖ P)`; the first half has just split the second summand in two; and each of
the three pieces is a component of the whole because its boundary misses it
(`lem:clopen-component`, here `Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint`). -/

namespace IsCrosscut

/-- `ℝ² ∖ (C ∪ P) = Ext(C) ⊔ (Int(C) ∖ P)`. The crosscut lies wholly in `C ∪ Int(C)`, so
removing it from the complement of `C` costs the outside nothing. -/
theorem compl_eq (h : IsCrosscut C P p q) : (C ∪ P)ᶜ = outside C ∪ (inside C \ P) := by
  refine Subset.antisymm (fun z hz => ?_) ?_
  · have hzC : z ∉ C := fun hzc => hz (Or.inl hzc)
    have hzP : z ∉ P := fun hzp => hz (Or.inr hzp)
    have hz' : z ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hzC
    rcases hz' with hzi | hzo
    · exact Or.inr ⟨hzi, hzP⟩
    · exact Or.inl hzo
  · rintro z (hzo | ⟨hzi, hzP⟩) (hzc | hzp)
    · exact hzo.1 hzc
    · exact disjoint_left.1 h.disjoint_outside hzp hzo
    · exact hzi.1 hzc
    · exact hzP hzp

/-- `ℝ² ∖ (C ∪ P) = Ext(C) ⊔ Int(A₁ ∪ P) ⊔ Int(A₂ ∪ P)`: the three regions, as sets. -/
theorem compl_eq_three (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
  rw [h.compl_eq, h.inside_diff_eq hjordan hcut hcollars, union_assoc]

theorem outside_subset_compl (h : IsCrosscut C P p q) : outside C ⊆ (C ∪ P)ᶜ := by
  rw [h.compl_eq]; exact subset_union_left

theorem side_subset_compl (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    inside (A₁ ∪ P) ⊆ (C ∪ P)ᶜ := by
  intro w hw
  obtain ⟨hwD, hwP⟩ := h.side_subset hjordan hcut hw
  rintro (hwC | hwP')
  · exact inside_subset_compl hwD hwC
  · exact hwP hwP'

/-- **`Ext(C)` is a region of `ℝ² ∖ (C ∪ P)`.** Its boundary is `C`, which misses that open
set; `lem:clopen-component` does the rest. -/
theorem outside_isComponent (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) :
    ∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C := by
  have hsep := h.isSeparating_curve hjordan
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint hsep.isOpen_outside
    hsep.isConnected_outside.isPreconnected h.outside_subset_compl ?_ hz
  rw [hsep.frontier_outside]
  exact eq_empty_iff_forall_notMem.2 fun w hw => hw.2 (Or.inl hw.1)

/-- **`Int(A₁ ∪ P)` is a region of `ℝ² ∖ (C ∪ P)`.** Its boundary is `A₁ ∪ P ⊆ C ∪ P`, which
misses that open set. -/
theorem side_isComponent_compl (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    ∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) := by
  have hJ := h.isSeparating_union hjordan hcut
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint hJ.isOpen_inside
    hJ.isConnected_inside.isPreconnected (h.side_subset_compl hjordan hcut) ?_ hz
  rw [hJ.frontier_inside]
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwA | hwP, hw⟩
  · exact hw (Or.inl (hcut.fst_subset hwA))
  · exact hw (Or.inr hwP)

/-- **Every region of `ℝ² ∖ (C ∪ P)` is one of the three.** -/
theorem three_regions (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    ∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
      connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
      connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P) := by
  intro z hz
  rw [h.compl_eq_three hjordan hcut hcollars] at hz
  rcases hz with (hz | hz) | hz
  · exact Or.inl (h.outside_isComponent hjordan z hz)
  · exact Or.inr (Or.inl (h.side_isComponent_compl hjordan hcut z hz))
  · exact Or.inr (Or.inr (h.side_isComponent_compl hjordan hcut.symm z hz))

/-- The outside of `C` is disjoint from either side, since the sides lie inside `C`. -/
theorem disjoint_outside_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    Disjoint (outside C) (inside (A₁ ∪ P)) := by
  rw [disjoint_left]
  intro w hw hw'
  exact disjoint_left.1 disjoint_inside_outside (h.side_subset hjordan hcut hw').1 hw

/-- The outside of `C` is not a side: it is unbounded and every side is bounded. -/
theorem outside_ne_side (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂) :
    outside C ≠ inside (A₁ ∪ P) := by
  intro heq
  obtain ⟨w, hw⟩ := h.side_nonempty hjordan hcut
  exact disjoint_left.1 (h.disjoint_outside_side hjordan hcut) (heq ▸ hw) hw

end IsCrosscut

/-- **Theorem "Crosscut theorem", second sentence** (`thm:general-crosscut`). `ℝ² ∖ (C ∪ P)` has
precisely three regions, whose boundaries are `C`, `A₁ ∪ P` and `A₂ ∪ P`.

The three are named: `Ext(C)`, `Int(A₁ ∪ P)`, `Int(A₂ ∪ P)`. They cover, they are pairwise
disjoint and pairwise distinct, each is a component, every component is one of them, and the
three boundaries are as stated. "Pairwise distinct" is what makes this *three* regions and not
fewer; it is not a consequence of the covering, so it is a clause here. -/
theorem general_crosscut_three_regions
    (hjordan : ∀ S : Set Plane, IsJordanCurve S → IsSeparating S)
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    (C ∪ P)ᶜ = outside C ∪ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) ∧
      (∀ z ∈ outside C, connectedComponentIn (C ∪ P)ᶜ z = outside C) ∧
      (∀ z ∈ inside (A₁ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P)) ∧
      (∀ z ∈ inside (A₂ ∪ P), connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      (∀ z ∈ (C ∪ P)ᶜ, connectedComponentIn (C ∪ P)ᶜ z = outside C ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₁ ∪ P) ∨
        connectedComponentIn (C ∪ P)ᶜ z = inside (A₂ ∪ P)) ∧
      Disjoint (outside C) (inside (A₁ ∪ P)) ∧ Disjoint (outside C) (inside (A₂ ∪ P)) ∧
        Disjoint (inside (A₁ ∪ P)) (inside (A₂ ∪ P)) ∧
      outside C ≠ inside (A₁ ∪ P) ∧ outside C ≠ inside (A₂ ∪ P) ∧
        inside (A₁ ∪ P) ≠ inside (A₂ ∪ P) ∧
      frontier (outside C) = C ∧ frontier (inside (A₁ ∪ P)) = A₁ ∪ P ∧
        frontier (inside (A₂ ∪ P)) = A₂ ∪ P :=
  ⟨h.compl_eq_three hjordan hcut hcollars, h.outside_isComponent hjordan,
    h.side_isComponent_compl hjordan hcut, h.side_isComponent_compl hjordan hcut.symm,
    h.three_regions hjordan hcut hcollars,
    h.disjoint_outside_side hjordan hcut, h.disjoint_outside_side hjordan hcut.symm,
    h.disjoint_sides hjordan hcut,
    h.outside_ne_side hjordan hcut, h.outside_ne_side hjordan hcut.symm,
    h.side_ne hjordan hcut,
    (h.isSeparating_curve hjordan).frontier_outside,
    h.frontier_side hjordan hcut, h.frontier_side hjordan hcut.symm⟩

end Schoenflies
