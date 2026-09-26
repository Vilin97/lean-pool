/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.GeneratedStructure

/-!
# Carriers, refinement compatibility, and the star lemmas

The interface between the *construction* of the nested cellulations and the *abstraction* the
limit homeomorphism uses. The blueprint says at the head of that section (tex, "The limit
homeomorphism of the interiors") that it "forgets how the decompositions were constructed and
uses only their nesting, matching, and shrinking properties"; everything below is therefore
stated for an abstract refinement relation `Realization.Refines` between two realizations of two
generated structures, and *not* for either elementary constructor. The two constructors enter
only at the very end, as the two theorems that produce a `Refines` from them.

## The carrier is a function

`Realization.carrier` is `car_Γ(x)` of the blueprint, exported as a total function `Plane → γ`
rather than as an existential: `σ_n(x)` is used on every line of the limit argument. Outside the
closed domain it is junk (whence the `[Nonempty γ]`), and every lemma about it carries the
hypothesis `x ∈ D` that makes it meaningful. Its characterising property is
`IsCellDecomposition.carrier_eq`: *any* cell whose open part contains `x` is the carrier.

## What `Refines` is, and why it is the right shape

`R'.Refines R par` says: `par` maps cells of the finer structure to cells of the coarser one and
2-cells to 2-cells, it is compatible with `≼_abs` (assertion (iv) of `lem:cellulation-invariants`),
and each *open* cell of the finer realization sits inside the open cell of its parent. The last
clause is the geometric content of the blueprint's proof of
`lem:refinement-compatibility`(a) — "a point in either new subedge or at the new vertex
had the old open edge as its old carrier" — and it implies the weaker
`closure (R'.cell σ) ⊆ closure (R.cell (par σ))` that part (b) needs.

`Refines` is a relation between two realizations of two *different* abstract structures over the
same name type `γ`, parametrised by the composite parent map. `Refines.trans` composes them, so
"a finite sequence of elementary refinements" needs no separate treatment: a consumer that builds
its stages one operation at a time gets the composite by iterating `trans`.

Part (c) of `lem:refinement-compatibility` — "corresponding cells have corresponding parents" —
is, under the representation of `CombinatorialInvariance.lean`, the statement that *one and the
same* `par : γ → γ` serves both realizations: cells are abstract names, and two `Refines`
instances sharing a `par` is exactly a compatible matched refinement. There is nothing to
transport, and the substance of (c) is its consequence, `Refines.carrier_congr`.

## Blueprint

* `Schoenflies.CellStructure.Realization.carrier` — `car_Γ(x)`, with
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.carrier_eq` its characterisation.
* `Schoenflies.CellStructure.Realization.Refines` — a refinement of one generated matched cell
  structure by another, with `Refines.trans` for a finite sequence of them.
* `lem:refinement-compatibility`:
  * (a) `Schoenflies.CellStructure.Realization.Refines.parent_carrier`;
  * (b) `Schoenflies.CellStructure.Realization.Refines.star_subset` (cells) and
    `Schoenflies.CellStructure.Realization.Refines.star_carrier_subset` (points);
  * (c) `Schoenflies.CellStructure.SkeletonHomeo.carrier_congr` (corresponding *skeleton points*
    have corresponding carriers, via
    `Schoenflies.CellStructure.SkeletonHomeo.image_cell`),
    `Schoenflies.CellStructure.Realization.Refines.carrier_congr` (and then at every earlier
    stage), and the form the limit argument actually cites,
    `Schoenflies.CellStructure.Realization.Refines.target_star_subset` (`T_{n+1}(x) ⊆ T_n(x)`).
* `lem:star-intersection` — `Schoenflies.CellStructure.Realization.star_inter_nonempty_congr`.
* `lem:star-face-mesh` — `Schoenflies.CellStructure.Realization.IsCellDecomposition.star_eq_faces`,
  with (a) `…diam_star_le`, `…diam_star_lt`, `…diam_star_carrier_lt` and (b)
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le`,
  `Schoenflies.CellStructure.Realization.Refines.diam_cell_le_of_forall`.
* `lem:cell-neighborhood` — `Schoenflies.CellStructure.Realization.cellNbhd` and
  `Schoenflies.CellStructure.Realization.IsCellDecomposition.cell_neighborhood`.
* `rem:inductive-invariants` — honoured: nothing here is proved by a case check on the
  constructors. The inductive content lives in `GeneratedStructure.lean`; the two bridge theorems
  `Schoenflies.CellStructure.SubdivData.IsRefinement.refines` and
  `Schoenflies.CellStructure.SplitData.refines` are the only declarations that mention a
  constructor at all.

`Schoenflies.CellStructure.refines_of_elementary` is the shared bridge: both elementary
operations replace a single cell `c` by a set `N` of fresh cells and send `N` to `c`, so one
lemma serves both.
-/

public section

open Set Metric Bornology
open scoped Graph

namespace Schoenflies

namespace CellStructure

variable {γ : Type*} {S : CellStructure γ}

/-- A cell structure has finitely many cells. -/
theorem finite_cells (S : CellStructure γ) : S.cells.Finite :=
  (S.finite_vertexSet.union S.finite_edgeSet).union S.finite_faces

namespace Realization

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-! ### Elementary facts about the closed star

`Realization.star` is the `St` of the blueprint and is defined in `CombinatorialInvariance.lean`;
these are the membership and containment lemmas its consumers need. -/

theorem mem_star_iff : y ∈ R.star σ ↔ ∃ τ, S.sub σ τ ∧ y ∈ closure (R.cell τ) := by
  simp only [star, Set.mem_iUnion, mem_supercells, exists_prop]

/-- A closed supercell sits inside the star. -/
theorem closure_cell_subset_star (h : S.sub σ τ) : closure (R.cell τ) ⊆ R.star σ := fun _ hz =>
  mem_star_iff.2 ⟨τ, h, hz⟩

/-- The index set of a star is finite: it consists of cells. -/
theorem finite_supercells (hS : S.CombInvariants) (σ : γ) : (S.supercells σ).Finite :=
  S.finite_cells.subset fun _ hτ => hS.sub_mem_right hτ

/-- A star is a finite union of closed sets, hence closed. -/
theorem isClosed_star (hS : S.CombInvariants) : IsClosed (R.star σ) :=
  (finite_supercells hS σ).isClosed_biUnion fun _ _ => isClosed_closure

/-! ### The carrier of a point

`car_Γ(x)`, the unique open cell containing `x`. It is a total function; off the closed domain
its value is junk, and every lemma below supplies `x ∈ D`. -/

open scoped Classical in
/-- **The carrier** `car_Γ(x)` of a point: the unique cell whose *open* cell contains `x`.
Uniqueness, and the fact that there is one at all for `x` in the closed domain, are assertion (i)
of `lem:cellulation-invariants` — see `IsCellDecomposition.carrier_eq` and
`IsCellDecomposition.mem_cell_carrier`. -/
noncomputable def carrier [Nonempty γ] (R : S.Realization) (x : Plane) : γ :=
  if h : ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ then h.choose else Classical.arbitrary γ

theorem carrier_spec [Nonempty γ] (R : S.Realization) (x : Plane)
    (h : ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ) :
    R.carrier x ∈ S.cells ∧ x ∈ R.cell (R.carrier x) := by
  rw [carrier, dite_eq_left h]
  exact h.choose_spec

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ τ ρ : γ} {x y z : Plane}

/-- Every open cell lies in the closed domain. -/
theorem cell_subset_domain (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : R.cell σ ⊆ D := by
  rw [← h.iUnion_eq]
  exact Set.subset_biUnion_of_mem hσ

/-- A point of the closed domain lies in some open cell — the covering half of assertion (i). -/
theorem exists_cell (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    ∃ σ, σ ∈ S.cells ∧ x ∈ R.cell σ := by
  rw [← h.iUnion_eq] at hx
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨σ, hσ, hxσ⟩

theorem mem_cells_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    R.carrier x ∈ S.cells := (R.carrier_spec x (h.exists_cell hx)).1

theorem mem_cell_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    x ∈ R.cell (R.carrier x) := (R.carrier_spec x (h.exists_cell hx)).2

/-- **The characterising property of the carrier**: any cell whose open part contains `x` *is*
the carrier of `x`. This is the uniqueness half of assertion (i), and it is the lemma every
computation of a carrier goes through. -/
theorem carrier_eq [Nonempty γ] (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells)
    (hx : x ∈ R.cell σ) : R.carrier x = σ := by
  have hxD : x ∈ D := h.cell_subset_domain hσ hx
  by_contra hne
  exact Set.disjoint_left.1 (h.disjoint (h.mem_cells_carrier hxD) hσ hne)
    (h.mem_cell_carrier hxD) hx

/-- A point lies in the star of its own carrier. -/
theorem mem_star_carrier [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D) :
    x ∈ R.star (R.carrier x) :=
  closure_cell_subset_star (h.sub_refl (h.mem_cells_carrier hx))
    (_root_.subset_closure (h.mem_cell_carrier hx))

theorem star_nonempty (h : R.IsCellDecomposition D) (hσ : σ ∈ S.cells) : (R.star σ).Nonempty := by
  obtain ⟨z, hz⟩ := h.nonempty hσ
  exact ⟨z, closure_cell_subset_star (h.sub_refl hσ) (_root_.subset_closure hz)⟩

/-- A star lies in the closure of the domain, so a bounded domain bounds every star. -/
theorem star_subset_closure_domain (h : R.IsCellDecomposition D) (hS : S.CombInvariants) :
    R.star σ ⊆ closure D := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact closure_mono (h.cell_subset_domain (hS.sub_mem_right hτ)) hyτ

theorem isBounded_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) : IsBounded (R.star σ) :=
  hD.closure.subset (h.star_subset_closure_domain hS)

/-- A star is compact: it is closed, and bounded once the domain is. The limit argument needs
this to intersect a nested sequence of stars. -/
theorem isCompact_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) : IsCompact (R.star σ) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_star hS) (h.isBounded_star hS hD)

/-- Stars are antitone in the subcell relation. The transitivity this needs is not assumed of a
`CellStructure`; it is read off assertion (i) by `IsCellDecomposition.sub_trans`. -/
theorem star_anti_of_sub (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hσ : σ ∈ S.cells) (hρ : ρ ∈ S.cells) (hsub : S.sub σ ρ) : R.star ρ ⊆ R.star σ := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact mem_star_iff.2 ⟨τ, h.sub_trans hσ hρ (hS.sub_mem_right hτ) hsub hτ, hyτ⟩

end IsCellDecomposition

/-! ### Refinement

The abstract relation "`R'` refines `R` with parent map `par`". It is deliberately not tied to
either elementary operation: the limit argument uses only these three clauses. -/

/-- **`R'` refines `R` along the parent map `par`.**

`R'` and `R` realize two different abstract structures over the same name type; `par` is the
composite parent map of `lem:cellulation-invariants`(iv). The three combinatorial
clauses say that `par` takes cells to cells, 2-cells to 2-cells, and respects `≼_abs`; the
geometric clause says that each *open* cell of the finer stage lies inside the open cell of its
parent, which is what makes carriers refine (part (a)). -/
structure Refines {S' S : CellStructure γ} (R' : S'.Realization) (R : S.Realization)
    (par : γ → γ) : Prop where
  /-- The parent of a cell is a cell. -/
  parent_mem_cells : ∀ ⦃σ⦄, σ ∈ S'.cells → par σ ∈ S.cells
  /-- The parent of a 2-cell is a 2-cell. -/
  parent_mem_faces : ∀ ⦃F⦄, F ∈ S'.faces → par F ∈ S.faces
  /-- **Assertion (iv)**: the parent map is compatible with the subcell relation. -/
  sub_parent : ∀ ⦃σ τ⦄, S'.sub σ τ → S.sub (par σ) (par τ)
  /-- Each open cell lies inside the open cell of its parent. -/
  cell_subset : ∀ ⦃σ⦄, σ ∈ S'.cells → R'.cell σ ⊆ R.cell (par σ)

namespace Refines

variable {S' S'' : CellStructure γ} {R : S.Realization} {R' : S'.Realization}
  {R'' : S''.Realization} {par par' : γ → γ}

/-- Every realization refines itself along the identity: the empty sequence of elementary
refinements. -/
theorem refl (R : S.Realization) : R.Refines R id where
  parent_mem_cells := fun _ hσ => hσ
  parent_mem_faces := fun _ hF => hF
  sub_parent := fun _ _ h => h
  cell_subset := fun _ _ => subset_rfl

/-- **Refinements compose.** This is what turns `lem:refinement-compatibility` from a statement
about one elementary refinement into a statement about "a finite sequence of elementary
refinements": a consumer that builds its stages one operation at a time iterates this. -/
theorem trans (h' : R''.Refines R' par') (h : R'.Refines R par) : R''.Refines R (par ∘ par') where
  parent_mem_cells := fun _ hσ => h.parent_mem_cells (h'.parent_mem_cells hσ)
  parent_mem_faces := fun _ hF => h.parent_mem_faces (h'.parent_mem_faces hF)
  sub_parent := fun _ _ hst => h.sub_parent (h'.sub_parent hst)
  cell_subset := fun _ hσ => (h'.cell_subset hσ).trans (h.cell_subset (h'.parent_mem_cells hσ))

/-- The closed cells refine along with the open ones. -/
theorem closure_cell_subset (h : R'.Refines R par) {σ : γ} (hσ : σ ∈ S'.cells) :
    closure (R'.cell σ) ⊆ closure (R.cell (par σ)) :=
  closure_mono (h.cell_subset hσ)

/-- **`lem:refinement-compatibility`(a)**: the parent of the carrier of `x` at the finer stage is
its carrier at the coarser stage. -/
theorem parent_carrier [Nonempty γ] (href : R'.Refines R par) (h : R.IsCellDecomposition D)
    (h' : R'.IsCellDecomposition D') {x : Plane} (hx : x ∈ D') :
    par (R'.carrier x) = R.carrier x :=
  (h.carrier_eq (href.parent_mem_cells (h'.mem_cells_carrier hx))
    (href.cell_subset (h'.mem_cells_carrier hx) (h'.mem_cell_carrier hx))).symm

/-- **`lem:refinement-compatibility`(b)**, the cell-star inclusion: once a star is small it stays
small. -/
theorem star_subset (href : R'.Refines R par) (hS' : S'.CombInvariants) {σ : γ} :
    R'.star σ ⊆ R.star (par σ) := by
  intro y hy
  obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
  exact closure_cell_subset_star (href.sub_parent hτ)
    (href.closure_cell_subset (hS'.sub_mem_right hτ) hyτ)

/-- **`lem:refinement-compatibility`(b)**, pointwise: closed stars of a fixed point are monotone
under refinement. -/
theorem star_carrier_subset [Nonempty γ] (href : R'.Refines R par) (hS' : S'.CombInvariants)
    (h : R.IsCellDecomposition D) (h' : R'.IsCellDecomposition D') {x : Plane} (hx : x ∈ D') :
    R'.star (R'.carrier x) ⊆ R.star (R.carrier x) := by
  rw [← href.parent_carrier h h' hx]
  exact href.star_subset hS'

end Refines

/-! ### Matched refinements: part (c)

Two realizations of one abstract structure are matched; a *compatible matched refinement* is a
pair of `Refines` instances sharing one parent map. That sharing **is** the blueprint's
"corresponding cells have corresponding parents": the parent map is a map of abstract names, so
there is only ever one of it. The substance is the consequence recorded here. -/

namespace Refines

variable {S' : CellStructure γ} {R₁ R₂ : S.Realization} {R₁' R₂' : S'.Realization} {par : γ → γ}
  {D₁ D₂ D₁' D₂' : Set Plane}

/-- **`lem:refinement-compatibility`(c)**: if `x` and `y` have corresponding carriers at the
finer stage — corresponding means *equal as abstract cells* — then they have corresponding
carriers at the coarser stage, and hence at every earlier stage by iteration. -/
theorem carrier_congr [Nonempty γ] (h₁ : R₁'.Refines R₁ par) (h₂ : R₂'.Refines R₂ par)
    (hd₁ : R₁.IsCellDecomposition D₁) (hd₁' : R₁'.IsCellDecomposition D₁')
    (hd₂ : R₂.IsCellDecomposition D₂) (hd₂' : R₂'.IsCellDecomposition D₂')
    {x y : Plane} (hx : x ∈ D₁') (hy : y ∈ D₂')
    (hxy : R₁'.carrier x = R₂'.carrier y) : R₁.carrier x = R₂.carrier y := by
  rw [← h₁.parent_carrier hd₁ hd₁' hx, ← h₂.parent_carrier hd₂ hd₂' hy, hxy]

/-- **The nesting the limit map runs on.** With `R₁` the source realization and `R₂` the target
one, `T_n(x) = R₂.star (R₁.carrier x)` is the closed target star of the cell corresponding to
`σ_n(x)`, and this says `T_{n+1}(x) ⊆ T_n(x)`.

Only the *source* decompositions are needed: the parent map is abstract, so the target stage
inherits the inclusion from the source carrier. -/
theorem target_star_subset [Nonempty γ] (h₁ : R₁'.Refines R₁ par) (h₂ : R₂'.Refines R₂ par)
    (hS' : S'.CombInvariants) (hd₁ : R₁.IsCellDecomposition D₁)
    (hd₁' : R₁'.IsCellDecomposition D₁') {x : Plane} (hx : x ∈ D₁') :
    R₂'.star (R₁'.carrier x) ⊆ R₂.star (R₁.carrier x) := by
  rw [← h₁.parent_carrier hd₁ hd₁' hx]
  exact h₂.star_subset hS'

end Refines

/-! ### Intersection of corresponding stars -/

/-- One direction of `lem:star-intersection`. The two realizations are realizations of the *same*
abstract structure, so "the corresponding cells" are literally `σ` and `τ` again. -/
theorem star_inter_nonempty_of_star_inter_nonempty {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane}
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂) (hS : S.CombInvariants)
    {σ τ : γ} (hne : (R₁.star σ ∩ R₁.star τ).Nonempty) : (R₂.star σ ∩ R₂.star τ).Nonempty := by
  obtain ⟨p, hpσ, hpτ⟩ := hne
  obtain ⟨α, hσα, hpα⟩ := mem_star_iff.1 hpσ
  obtain ⟨β, hτβ, hpβ⟩ := mem_star_iff.1 hpτ
  have hα : α ∈ S.cells := hS.sub_mem_right hσα
  have hβ : β ∈ S.cells := hS.sub_mem_right hτβ
  -- the carrier `ρ` of `p` in the first realization is a subcell of both `α` and `β`
  rw [h₁.closure_eq hα] at hpα
  obtain ⟨ρ, ⟨hρ, hρα⟩, hpρ⟩ := Set.mem_iUnion₂.1 hpα
  have hρβ : S.sub ρ β := h₁.sub_of_mem hρ hβ hpρ hpβ
  -- both relations are relations of the common abstract structure, so they hold on the other side
  obtain ⟨w, hw⟩ := h₂.nonempty hρ
  exact ⟨w, closure_cell_subset_star hσα (h₂.subset_closure hρ hα hρα hw),
    closure_cell_subset_star hτβ (h₂.subset_closure hρ hβ hρβ hw)⟩

/-- **`lem:star-intersection`**: corresponding stars meet on one side exactly when they meet on
the other. This is what makes the limit map injective. -/
theorem star_inter_nonempty_congr {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane}
    (h₁ : R₁.IsCellDecomposition D₁) (h₂ : R₂.IsCellDecomposition D₂) (hS : S.CombInvariants)
    {σ τ : γ} : (R₁.star σ ∩ R₁.star τ).Nonempty ↔ (R₂.star σ ∩ R₂.star τ).Nonempty :=
  ⟨star_inter_nonempty_of_star_inter_nonempty h₁ h₂ hS,
    star_inter_nonempty_of_star_inter_nonempty h₂ h₁ hS⟩

/-! ### Stars and the face mesh -/

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {σ : γ} {x y : Plane} {η : ℝ}

/-- **`lem:star-face-mesh`**, the displayed equality: a closed star is the union of the closed
2-cells incident with the cell. Every supercell is a subcell of some 2-cell by assertion (v), and
its closure is then inside that closed 2-cell. -/
theorem star_eq_faces (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hσ : σ ∈ S.cells) :
    R.star σ = ⋃ F ∈ {F | F ∈ S.faces ∧ S.sub σ F}, closure (R.cell F) := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨τ, hτ, hyτ⟩ := mem_star_iff.1 hy
    have hτc : τ ∈ S.cells := hS.sub_mem_right hτ
    obtain ⟨F, hF, hτF⟩ := hS.mem_face hτc
    have hFc : F ∈ S.cells := S.mem_cells_of_mem_faces hF
    refine Set.mem_iUnion₂.2 ⟨F, ⟨hF, h.sub_trans hσ hτc hFc hτ hτF⟩, ?_⟩
    exact closure_minimal (h.subset_closure hτc hFc hτF) isClosed_closure hyτ
  · exact Set.iUnion₂_subset fun _ hF => closure_cell_subset_star hF.2

/-- Every closed 2-cell incident with `σ` contains every point of the open cell `σ`. -/
theorem mem_closure_face (h : R.IsCellDecomposition D) {F : γ} (hσ : σ ∈ S.cells)
    (hF : F ∈ S.faces) (hsub : S.sub σ F) (hx : x ∈ R.cell σ) : x ∈ closure (R.cell F) :=
  h.subset_closure hσ (S.mem_cells_of_mem_faces hF) hsub hx

/-- Every point of the star of `σ` is within `η` of every point of the open cell `σ`, when the
closed 2-cells incident with `σ` all have diameter at most `η`. -/
theorem dist_le_of_mem_star (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) ≤ η)
    (hx : x ∈ R.cell σ) (hy : y ∈ R.star σ) : dist x y ≤ η := by
  rw [h.star_eq_faces hS hσ] at hy
  obtain ⟨F, ⟨hF, hsub⟩, hyF⟩ := Set.mem_iUnion₂.1 hy
  have hbdd : IsBounded (closure (R.cell F)) :=
    (hD.subset (h.cell_subset_domain (S.mem_cells_of_mem_faces hF))).closure
  exact le_trans (dist_le_diam_of_mem hbdd (h.mem_closure_face hσ hF hsub hx) hyF) (hdiam hF hsub)

/-- **`lem:star-face-mesh`(a)**, in its non-strict form: a mesh bound on the closed 2-cells
incident with a cell doubles to a bound on the diameter of its star. -/
theorem diam_star_le (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hD : IsBounded D)
    (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) ≤ η) :
    diam (R.star σ) ≤ 2 * η := by
  obtain ⟨x, hx⟩ := h.nonempty hσ
  obtain ⟨F, hF, hσF⟩ := hS.mem_face hσ
  have hη : 0 ≤ η := le_trans diam_nonneg (hdiam hF hσF)
  refine diam_le_of_forall_dist_le (by linarith) fun y hy z hz => ?_
  have hxy : dist x y ≤ η := h.dist_le_of_mem_star hS hD hσ hdiam hx hy
  have hxz : dist x z ≤ η := h.dist_le_of_mem_star hS hD hσ hdiam hx hz
  calc dist y z ≤ dist y x + dist x z := dist_triangle y x z
    _ = dist x y + dist x z := by rw [dist_comm y x]
    _ ≤ 2 * η := by linarith

/-- **`lem:star-face-mesh`(a)**: if every closed 2-cell incident with `σ` has diameter *strictly*
less than `η`, the star has diameter strictly less than `2η`.

Strictness costs the finiteness of the set of incident 2-cells: the bound is realised at the
largest of them, and there are finitely many. -/
theorem diam_star_lt (h : R.IsCellDecomposition D) (hS : S.CombInvariants) (hD : IsBounded D)
    (hσ : σ ∈ S.cells)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub σ F → diam (closure (R.cell F)) < η) :
    diam (R.star σ) < 2 * η := by
  classical
  have hfin : {F | F ∈ S.faces ∧ S.sub σ F}.Finite := S.finite_faces.subset fun _ hF => hF.1
  have hne : {F | F ∈ S.faces ∧ S.sub σ F}.Nonempty := by
    obtain ⟨F, hF, hσF⟩ := hS.mem_face hσ
    exact ⟨F, hF, hσF⟩
  obtain ⟨F₀, hF₀, hmax⟩ := Finset.exists_max_image hfin.toFinset
    (fun F => diam (closure (R.cell F))) (hfin.toFinset_nonempty.2 hne)
  rw [Set.Finite.mem_toFinset] at hF₀
  have hle : diam (R.star σ) ≤ 2 * diam (closure (R.cell F₀)) :=
    h.diam_star_le hS hD hσ fun F hF hsub =>
      hmax F (Set.Finite.mem_toFinset hfin |>.2 ⟨hF, hsub⟩)
  exact lt_of_le_of_lt hle (by have := hdiam hF₀.1 hF₀.2; linarith)

/-- **`lem:star-face-mesh`(a)** at a point: the form the shrinking-stars proposition consumes. -/
theorem diam_star_carrier_lt [Nonempty γ] (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hD : IsBounded D) (hx : x ∈ D)
    (hdiam : ∀ ⦃F⦄, F ∈ S.faces → S.sub (R.carrier x) F → diam (closure (R.cell F)) < η) :
    diam (R.star (R.carrier x)) < 2 * η :=
  h.diam_star_lt hS hD (h.mem_cells_carrier hx) hdiam

end IsCellDecomposition

namespace Refines

variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {D : Set Plane} {η : ℝ}

/-- **`lem:star-face-mesh`(b)**: a new 2-cell is contained in its parent 2-cell, so refinement
cannot increase the diameter of a 2-cell. -/
theorem diam_cell_le (href : R'.Refines R par) (h : R.IsCellDecomposition D) (hD : IsBounded D)
    {F : γ} (hF : F ∈ S'.cells) :
    diam (closure (R'.cell F)) ≤ diam (closure (R.cell (par F))) :=
  diam_mono (href.closure_cell_subset hF)
    ((hD.subset (h.cell_subset_domain (href.parent_mem_cells hF))).closure)

/-- **`lem:star-face-mesh`(b)**: refinement cannot increase the maximum diameter of the
2-cells. -/
theorem diam_cell_le_of_forall (href : R'.Refines R par) (h : R.IsCellDecomposition D)
    (hD : IsBounded D) (hdiam : ∀ ⦃F⦄, F ∈ S.faces → diam (closure (R.cell F)) ≤ η)
    {F : γ} (hF : F ∈ S'.faces) : diam (closure (R'.cell F)) ≤ η :=
  le_trans (href.diam_cell_le h hD (S'.mem_cells_of_mem_faces hF))
    (hdiam (href.parent_mem_faces hF))

end Refines

/-! ### Finite cell neighborhoods -/

/-- **The finite cell neighbourhood** of `lem:cell-neighborhood`: the complement of the union of
all closed cells that do not contain `x`. It is open, contains `x`, and its points have carriers
above the carrier of `x`. -/
def cellNbhd (R : S.Realization) (x : Plane) : Set Plane :=
  (⋃ τ ∈ {τ | τ ∈ S.cells ∧ x ∉ closure (R.cell τ)}, closure (R.cell τ))ᶜ

theorem isOpen_cellNbhd (R : S.Realization) (x : Plane) : IsOpen (R.cellNbhd x) :=
  ((S.finite_cells.subset fun _ hτ => hτ.1).isClosed_biUnion
    fun _ _ => isClosed_closure).isOpen_compl

theorem mem_cellNbhd_self (R : S.Realization) (x : Plane) : x ∈ R.cellNbhd x := by
  intro hx
  obtain ⟨τ, hτ, hxτ⟩ := Set.mem_iUnion₂.1 hx
  exact hτ.2 hxτ

theorem cellNbhd_mem_nhds (R : S.Realization) (x : Plane) : R.cellNbhd x ∈ nhds x :=
  (isOpen_cellNbhd R x).mem_nhds (mem_cellNbhd_self R x)

/-- Every closed cell that meets the neighbourhood contains `x`. -/
theorem mem_closure_of_mem_cellNbhd {R : S.Realization} {x z : Plane} {τ : γ} (hτ : τ ∈ S.cells)
    (hz : z ∈ R.cellNbhd x) (hzτ : z ∈ closure (R.cell τ)) : x ∈ closure (R.cell τ) := by
  by_contra hx
  exact hz (Set.mem_iUnion₂.2 ⟨τ, ⟨hτ, hx⟩, hzτ⟩)

namespace IsCellDecomposition

variable {R : S.Realization} {D : Set Plane} {x z : Plane}

/-- **`lem:cell-neighborhood`**, the carrier half: for `z` in the neighbourhood, the carrier of
`x` is a subcell of the carrier of `z`. -/
theorem sub_carrier_of_mem_cellNbhd [Nonempty γ] (h : R.IsCellDecomposition D) (hx : x ∈ D)
    (hz : z ∈ R.cellNbhd x) (hzD : z ∈ D) : S.sub (R.carrier x) (R.carrier z) := by
  have hxclos : x ∈ closure (R.cell (R.carrier z)) :=
    mem_closure_of_mem_cellNbhd (h.mem_cells_carrier hzD) hz
      (_root_.subset_closure (h.mem_cell_carrier hzD))
  exact h.sub_of_mem (h.mem_cells_carrier hx) (h.mem_cells_carrier hzD)
    (h.mem_cell_carrier hx) hxclos

/-- **`lem:cell-neighborhood`**: `R.cellNbhd x ∩ D` is a relative neighbourhood of `x` in the
closed domain on which the carrier of `x` is a subcell of every carrier, so that the stars there
are all contained in the star of `x`.

For the *cross-realization* form the limit map needs — `T_n(z) ⊆ T_n(x)`, the target star of the
source carrier — combine `sub_carrier_of_mem_cellNbhd` in the source realization with
`star_anti_of_sub` in the target one: the subcell relation is a relation of the common abstract
structure, so it moves between realizations without transport. -/
theorem cell_neighborhood [Nonempty γ] (h : R.IsCellDecomposition D) (hS : S.CombInvariants)
    (hx : x ∈ D) (hz : z ∈ R.cellNbhd x) (hzD : z ∈ D) :
    S.sub (R.carrier x) (R.carrier z) ∧ R.star (R.carrier z) ⊆ R.star (R.carrier x) := by
  have hsub := h.sub_carrier_of_mem_cellNbhd hx hz hzD
  exact ⟨hsub, h.star_anti_of_sub hS (h.mem_cells_carrier hx) (h.mem_cells_carrier hzD) hsub⟩

end IsCellDecomposition

/-! ### Corresponding skeleton points

The second sentence of `lem:refinement-compatibility`(c). A point of the realized skeleton lies
in an open 0-cell or an open 1-cell, and the skeleton homeomorphism carries each of those onto
the open cell of the *same abstract name*; so corresponding skeleton points have carriers that
correspond, with nothing to transport. -/

/-- The two ends of a drawn edge lie on its arc. Needed to cut the two endpoints out of the arc
on both sides of the skeleton homeomorphism at once. -/
theorem pos_pair_subset_edgeArc (R : S.Realization) {e a b : γ} (hl : S.skel.IsLink e a b) :
    ({R.pos a, R.pos b} : Set Plane) ⊆ Graph.edgeArc R.drawing e := by
  obtain ⟨-, -, hlink⟩ := R.isDrawing.edge_param (by rw [Graph.edgeSet_map]; exact hl.edge_mem)
  have h0 : R.drawing e 0 ∈ Graph.edgeArc R.drawing e := Set.mem_image_of_mem _ zero_mem_I
  have h1 : R.drawing e 1 ∈ Graph.edgeArc R.drawing e := Set.mem_image_of_mem _ one_mem_I
  have hpair : ({R.pos a, R.pos b} : Set Plane) = {R.drawing e 0, R.drawing e 1} := by
    rcases (hl.map R.pos).eq_and_eq_or_eq_and_eq hlink with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb]; exact Set.pair_comm _ _
  rw [hpair]
  rintro z (rfl | rfl)
  exacts [h0, h1]

end Realization

namespace SkeletonHomeo

variable {R₁ R₂ : S.Realization} {D₁ D₂ : Set Plane} {σ : γ} {x : Plane}

/-- **The skeleton homeomorphism carries open skeleton cells onto open skeleton cells** of the
same abstract name. For a 0-cell this is `pos_apply`; for a 1-cell it is `edgeArc_image` with the
two endpoints removed from both sides, which is legitimate because `g` is injective on the
skeleton. -/
theorem image_cell (g : SkeletonHomeo R₁ R₂) (hσ : σ ∈ V(S.skel) ∪ E(S.skel)) :
    g.toFun '' R₁.cell σ = R₂.cell σ := by
  rcases hσ with hv | he
  · rw [R₁.cell_vertex hv, R₂.cell_vertex hv, Set.image_singleton, g.pos_apply hv]
  · obtain ⟨a, b, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have harc : Graph.edgeArc R₁.drawing σ ⊆ R₁.skeletonSet :=
      Graph.edgeArc_subset_pointSet (by rw [Realization.edgeSet_graph]; exact he)
    rw [R₁.cell_edge hl, R₂.cell_edge hl,
      (g.injOn.mono harc).image_sdiff_subset (R₁.pos_pair_subset_edgeArc hl),
      g.edgeArc_image he, Set.image_pair, g.pos_apply hl.left_mem, g.pos_apply hl.right_mem]

/-- **`lem:refinement-compatibility`(c)**, the skeleton clause: corresponding skeleton points
have corresponding carriers — the same abstract cell on both sides. -/
theorem carrier_congr [Nonempty γ] (g : SkeletonHomeo R₁ R₂) (h₁ : R₁.IsCellDecomposition D₁)
    (h₂ : R₂.IsCellDecomposition D₂) (hσ : σ ∈ V(S.skel) ∪ E(S.skel)) (hx : x ∈ R₁.cell σ) :
    R₂.carrier (g.toFun x) = R₁.carrier x := by
  have hcells : σ ∈ S.cells := by
    rcases hσ with hv | he
    exacts [S.mem_cells_of_mem_vertexSet hv, S.mem_cells_of_mem_edgeSet he]
  have hgx : g.toFun x ∈ R₂.cell σ := by
    rw [← g.image_cell hσ]; exact Set.mem_image_of_mem _ hx
  rw [h₁.carrier_eq hcells hx, h₂.carrier_eq hcells hgx]

end SkeletonHomeo

/-! ### The two elementary operations produce refinements

Both operations have the same shape: a single cell `c` is replaced by a set `N` of fresh cells,
and the parent map sends `N` to `c` and fixes everything else. `refines_of_elementary` proves the
geometric clause of `Refines` from that shape alone — the fresh cells must land inside `c`,
because any other cell of the old stage survives and is unmoved, and open cells of one stage are
disjoint. -/

variable {S' : CellStructure γ} {R : S.Realization} {R' : S'.Realization} {par : γ → γ}
  {c : γ} {N : Set γ} {D : Set Plane}

/-- **The shape shared by the two elementary operations.** Given that the refined cells are the
old ones minus `c` together with the fresh set `N`, that `par` collapses `N` to `c` and fixes old
cells, and that both stages decompose the *same* closed domain with the surviving cells unmoved,
the refined realization refines the old one. -/
theorem refines_of_elementary (hc : c ∈ S.cells) (hcells : S'.cells = (S.cells \ {c}) ∪ N)
    (hfresh : ∀ ⦃σ⦄, σ ∈ N → σ ∉ S.cells) (hpar_new : ∀ ⦃σ⦄, σ ∈ N → par σ = c)
    (hpar_old : ∀ ⦃σ⦄, σ ∈ S.cells → par σ = σ)
    (hfaces : ∀ ⦃F⦄, F ∈ S'.faces → par F ∈ S.faces)
    (hsub : ∀ ⦃σ τ⦄, S'.sub σ τ → S.sub (par σ) (par τ))
    (hcell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ c → R'.cell σ = R.cell σ)
    (h : R.IsCellDecomposition D) (h' : R'.IsCellDecomposition D) : R'.Refines R par where
  parent_mem_cells := by
    intro σ hσ
    rw [hcells] at hσ
    rcases hσ with ⟨hσc, -⟩ | hσN
    · rw [hpar_old hσc]; exact hσc
    · rw [hpar_new hσN]; exact hc
  parent_mem_faces := hfaces
  sub_parent := hsub
  cell_subset := by
    intro σ hσ
    have hσ' := hσ
    rw [hcells] at hσ'
    rcases hσ' with ⟨hσc, hσne⟩ | hσN
    · rw [hpar_old hσc, hcell_eq hσc hσne]
    · rw [hpar_new hσN]
      intro w hw
      -- `w` lies in the old open cell of some old cell `ρ`; every old cell but `c` survives
      -- unmoved, and open cells of the refined stage are disjoint, so `ρ = c`.
      obtain ⟨ρ, hρ, hwρ⟩ := h.exists_cell (h'.cell_subset_domain hσ hw)
      by_cases hρc : ρ = c
      · exact hρc ▸ hwρ
      · have hρ' : ρ ∈ S'.cells := by rw [hcells]; exact Or.inl ⟨hρ, hρc⟩
        have hne : σ ≠ ρ := by rintro rfl; exact hfresh hσN hρ
        have hwρ' : w ∈ R'.cell ρ := by rw [hcell_eq hρ hρc]; exact hwρ
        exact absurd hwρ' (Set.disjoint_left.1 (h'.disjoint hσ hρ' hne) hw)

namespace SubdivData

variable {d : S.SubdivData}

/-- **An edge subdivision is a refinement.** `SubdivData.IsRefinement` already carries everything
the geometric clause needs, so no cell decomposition is required here. -/
theorem IsRefinement.refines (hS : S.CombInvariants) {R : S.Realization}
    {R' : (S.subdivideEdge d).Realization} (href : d.IsRefinement R R') :
    R'.Refines R d.parent where
  parent_mem_cells := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, -⟩ | hσN
    · rw [d.parent_of_mem_cells hσc]; exact hσc
    · rw [d.parent_of_mem_newCells hσN]; exact d.edge_mem_cells
  parent_mem_faces := by
    intro F hF
    rw [subdivideEdge_faces] at hF
    rw [d.parent_of_mem_cells (S.mem_cells_of_mem_faces hF)]
    exact hF
  sub_parent := fun _ _ h => d.sub_parent hS h
  cell_subset := by
    intro σ hσ
    rw [subdivideEdge_cells] at hσ
    rcases hσ with ⟨hσc, hσe⟩ | hσN
    · rw [d.parent_of_mem_cells hσc, href.cell_eq hσc hσe]
    · rw [d.parent_of_mem_newCells hσN]; exact href.cell_subset_edge hσN

end SubdivData

namespace SplitData

variable {d : S.SplitData}

/-- **A 2-cell split is a refinement.** The geometric input is assertion (i) at the refined stage
together with "the split leaves the other cells where they were"; both are supplied by the
consumer, since the split analogue of `SubdivData.IsRefinement` is not yet on `main`. -/
theorem refines (hS : S.CombInvariants) {R : S.Realization}
    {R' : (S.splitFace d).Realization} {D : Set Plane} (h : R.IsCellDecomposition D)
    (h' : R'.IsCellDecomposition D)
    (hcell_eq : ∀ ⦃σ⦄, σ ∈ S.cells → σ ≠ d.face → R'.cell σ = R.cell σ) :
    R'.Refines R d.parent := by
  refine refines_of_elementary d.face_mem_cells (splitFace_cells d)
    (fun _ hσ => notMem_cells_of_mem_newCells hσ) (fun _ hσ => d.parent_of_mem_newCells hσ)
    (fun _ hσ => d.parent_of_mem_cells hσ) ?_ (fun _ _ h => d.sub_parent hS h) hcell_eq h h'
  intro F hF
  rw [splitFace_faces] at hF
  rcases hF with rfl | rfl | ⟨hFc, -⟩
  · rw [d.parent_of_mem_newCells d.face₁_mem_newCells]; exact d.face_mem
  · rw [d.parent_of_mem_newCells d.face₂_mem_newCells]; exact d.face_mem
  · rw [d.parent_of_mem_cells (S.mem_cells_of_mem_faces hFc)]; exact hFc

end SplitData

/-! ### The interface, exercised

The limit homeomorphism opens with: "the sets `T_n(x)` are nonempty and compact … the cell-star
inclusion gives `T_{n+1}(x) ⊆ T_n(x)` … their diameters tend to zero … by
`lem:nested-compact` their intersection is one point". This anonymous example is a machine-checked
statement that the four facts that sentence needs come out of this module for an *abstract*
nested sequence: nothing below mentions how the stages were built, and the mesh hypothesis is
read in the target realization while the carrier is read in the source one. -/
example {γ : Type*} [Nonempty γ] (St : ℕ → CellStructure γ)
    (R : ∀ n, (St n).Realization) (R' : ∀ n, (St n).Realization)
    (par : ℕ → γ → γ) (D D' : Set Plane) (hD' : IsBounded D')
    (hd : ∀ n, (R n).IsCellDecomposition D) (hd' : ∀ n, (R' n).IsCellDecomposition D')
    (hcomb : ∀ n, (St n).CombInvariants)
    (href : ∀ n, (R (n + 1)).Refines (R n) (par n))
    (href' : ∀ n, (R' (n + 1)).Refines (R' n) (par n))
    (η : ℕ → ℝ) (x : Plane) (hx : x ∈ D)
    (hmesh : ∀ n, ∀ ⦃F : γ⦄, F ∈ (St n).faces → (St n).sub ((R n).carrier x) F →
      diam (closure ((R' n).cell F)) < η n) :
    (∀ n, (R' (n + 1)).star ((R (n + 1)).carrier x) ⊆ (R' n).star ((R n).carrier x)) ∧
      (∀ n, ((R' n).star ((R n).carrier x)).Nonempty) ∧
      (∀ n, IsCompact ((R' n).star ((R n).carrier x))) ∧
      (∀ n, diam ((R' n).star ((R n).carrier x)) < 2 * η n) :=
  ⟨fun n => (href n).target_star_subset (href' n) (hcomb (n + 1)) (hd n) (hd (n + 1)) hx,
    fun n => (hd' n).star_nonempty ((hd n).mem_cells_carrier hx),
    fun n => (hd' n).isCompact_star (hcomb n) hD',
    fun n => (hd' n).diam_star_lt (hcomb n) hD' ((hd n).mem_cells_carrier hx) (hmesh n)⟩

end CellStructure

end Schoenflies
