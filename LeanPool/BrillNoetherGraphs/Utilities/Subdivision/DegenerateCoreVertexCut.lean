/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexCutGenusFour
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSeparator
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateRepRigidity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ContractionForestCensusGeneral

/-!
# Core vertex cuts on the CLOSED length orthant

`Certificate/CoreVertexCutGenusFour.lean` proves
`bnExists_one_three_of_genusFourRankOneCheck` against a
`SubdivisionGraph.Spec`, hence only at strictly positive lengths.  The
contraction bridge (the corresponding closed-row proof module,
the corresponding closed-row proof module) consumes the **closed**-orthant shape
`∀ ℓ, IsForest … → ¬ IsLoopy … → BNExists (censusSpec … ℓ …).graph 1 3`.
This module supplies the closed statement for the vertex-cut route.

## Why this port is possible where the mixed-cover port is not

`Certificate/ClosedRowInterface.lean` records that the generated *mixed-cover*
corpus cannot move onto the closed layer: each of its pieces outputs a
`SubdivisionGraph.Spec`, whose `length_pos` is a **structural field**, so a
piece cannot even be constructed at a face.  The vertex-cut certificate is a
different object: `CoreVertexCut.Data core` is proof-free data on the *core*
(`glue : Fin n`, `left : Finset (Fin n)`), with no length information at all,
and `Valid` is a statement about core slots only.  There is no field to
construct at a face, so no structural obstruction.

What *is* genuinely length-dependent is the arithmetic:
`CoreVertexCutGenus.leftGraph_genus` uses `spec.length_pos` to turn
`length e - 1 + 1` back into `length e`.  At a face a vanishing left slot
loses an edge *and* merges two left vertices, so the factor genus is preserved
— but only because the vanishing set is a forest.  That is the mathematical
content of this file, and it is a theorem, not an assumption.

## The route: contract, do not re-derive

We do **not** re-port the 437 lines of `CoreVertexCut.lean` to `DegSpec`
vertex types.  `Certificate/DegenerateSeparator.lean` already builds
`DegSpec.contractedSpec`, a genuinely positive `SubdivisionGraph.Spec` on the
contracted core, together with `DegSpec.canonicalContraction`, whose
`laplacianEquiv` identifies its graph with `d.graph`.  So it suffices to push
the *finite core data* `CoreVertexCut.Data d.core` forward to
`CoreVertexCut.Data d.contractedCore` and check that `Valid`, the factor
genera and the two-regularity conditions survive.  Everything below is finite
combinatorics on cores; no subdivision vertex type is ever touched.

## The one hypothesis a bare `DegSpec` does not supply

`DegSpec.rep` is only required to *identify* the endpoints of vanishing slots
(`rep_zero`); nothing forces its classes to be *generated* by them.  Without
that, a `rep` could merge a left class into a right class across no edge at
all, and no cut could survive.  `DegSpec.RepIsContraction` below is exactly
the missing direction, and it is free for every object a row actually uses:
`censusSpec`'s `rep` is `compFold`, for which `compFold_iff` is precisely this
statement.

## Looplessness

Two different looplessness facts are in play and both are discharged, not
assumed away:

* the *contracted* core is loopless — supplied by `DegSpec.rep_loopless`,
  which on `censusSpec` comes from the census hypothesis `¬ IsLoopy`.  This is
  the `RESULTS.md` §9 hazard: core vertices are not rank-determining on a
  loop-carrying core.  It enters here through `contractedSpec.core_loopless`.
* the *uncontracted* core is loopless — needed to know that no core slot lies
  in both sides at once (`leftSlots_disjoint_rightSlots`).  A `DegSpec` does
  not imply it (a vanishing slot could be a loop), so it is carried as an
  explicit hypothesis `hLoopless`, exactly as `SubdivisionGraph.Spec` carries
  it as the field `core_loopless`; on a concrete row core it is `by decide`.
-/

@[expose] public section

namespace Utilities.Certificate.DegenerateSpec.DegSpec
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential
open Utilities.Certificate.ContractionForestCensusGeneral

variable {n p : ℕ}

/-! `zeroSlotSet`, `forest'`, `RepIsContraction` and `rep_eq_of_reachIn` moved
down to `Utilities/Subdivision/DegenerateRepRigidity.lean` on 2026-08-25, where
the forest-face rigidity statements need them. -/

end Utilities.Certificate.DegenerateSpec.DegSpec

/-! ## Generic reachability monotonicity

This extends the census namespace, which lives in the public `Utilities`
library, so the block is opened absolutely rather than relative to the private
`MarkedGraphs.Certificate` namespace below. -/

namespace Utilities.Certificate.ContractionForestCensusGeneral

open Utilities.Certificate
open Finset ExplicitPotential

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

theorem reachIn_mono {F F' : Finset (Fin p)} (hsub : F ⊆ F') {x y : Fin n}
    (h : ReachIn core F x y) : ReachIn core F' x y := by
  -- v4.33: `ReflTransGen.mono` now concludes with `≤` between whole relations,
  -- so the two points must be supplied before the `ReflTransGen` proof.
  refine Relation.ReflTransGen.mono ?_ x y h
  rintro a b ⟨e, he, hcase⟩
  exact ⟨e, (mem_edgeList _ e).mpr (hsub ((mem_edgeList _ e).mp he)), hcase⟩

end Utilities.Certificate.ContractionForestCensusGeneral

namespace Utilities.Certificate
open MarkedGraphs.Certificate

open Utilities.Certificate
open Utilities
open Finset ExplicitPotential
open Utilities.Certificate.ContractionForestCensusGeneral

/-! ## The cut, transported to a face -/

namespace DegenerateCoreVertexCut

open Utilities.Certificate.DegenerateSpec CoreVertexCut

variable {n p : ℕ} (d : DegSpec n p) (cut : CoreVertexCut.Data d.core)

/-- Vanishing slots lying wholly in the named side. -/
def leftZero : Finset (Fin p) := d.zeroSlotSet ∩ cut.leftSlots

/-- Vanishing slots lying wholly in the complementary side. -/
def rightZero : Finset (Fin p) := d.zeroSlotSet ∩ cut.rightSlots

/-- The vertex identification produced by the vanishing slots of the named
side alone. -/
def repLeft : Fin n → Fin n := compFold d.core (leftZero d cut)

/-- The vertex identification produced by the vanishing slots of the
complementary side alone. -/
def repRight : Fin n → Fin n := compFold d.core (rightZero d cut)

theorem leftZero_subset : leftZero d cut ⊆ d.zeroSlotSet :=
  Finset.inter_subset_left

theorem rightZero_subset : rightZero d cut ⊆ d.zeroSlotSet :=
  Finset.inter_subset_left

theorem leftZero_subset_leftSlots : leftZero d cut ⊆ cut.leftSlots :=
  Finset.inter_subset_right

theorem rightZero_subset_rightSlots : rightZero d cut ⊆ cut.rightSlots :=
  Finset.inter_subset_right

/-! ### Confinement of reachability to one side -/

/-- A left-vanishing-slot walk out of the named side stays in it. -/
theorem mem_left_of_reachLeft {u v : Fin n} (hu : u ∈ cut.left)
    (h : ReachIn d.core (leftZero d cut) u v) : v ∈ cut.left := by
  induction h with
  | refl => exact hu
  | @tail b w _ hbw _ =>
      obtain ⟨e, he, hcase⟩ := hbw
      have hSlot : cut.LeftSlot e :=
        (cut.mem_leftSlots e).mp
          (leftZero_subset_leftSlots d cut ((mem_edgeList _ e).mp he))
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hSlot.2
      · exact hSlot.1

/-- A right-vanishing-slot walk out of the complementary side stays in it. -/
theorem mem_right_of_reachRight {u v : Fin n} (hu : u ∈ cut.right)
    (h : ReachIn d.core (rightZero d cut) u v) : v ∈ cut.right := by
  induction h with
  | refl => exact hu
  | @tail b w _ hbw _ =>
      obtain ⟨e, he, hcase⟩ := hbw
      have hSlot : cut.RightSlot e :=
        (cut.mem_rightSlots e).mp
          (rightZero_subset_rightSlots d cut ((mem_edgeList _ e).mp he))
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hSlot.2
      · exact hSlot.1

/-- **The confinement lemma.**  A vanishing-slot walk starting inside the
named side either never leaves it, or has already reached the articulation
inside it.  This is the whole reason a cut survives contraction: the only way
out of a side is through `glue`. -/
theorem reach_confined_left (hValid : cut.Valid) {u : Fin n} (hu : u ∈ cut.left)
    {v : Fin n} (h : ReachIn d.core d.zeroSlotSet u v) :
    ReachIn d.core (leftZero d cut) u v ∨
      ReachIn d.core (leftZero d cut) u cut.glue := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
      rcases ih with ih | ih
      · have hxleft : x ∈ cut.left := mem_left_of_reachLeft d cut hu ih
        by_cases hxg : x = cut.glue
        · exact Or.inr (hxg ▸ ih)
        · obtain ⟨e, he, hcase⟩ := hxy
          have heZ : e ∈ d.zeroSlotSet := (mem_edgeList _ e).mp he
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · have hy : d.core.head e ∈ cut.left := by
              by_contra hy
              exact hValid.2 e (Or.inl ⟨hxleft, hxg, hy⟩)
            have heL : e ∈ leftZero d cut :=
              Finset.mem_inter.mpr ⟨heZ, (cut.mem_leftSlots e).mpr ⟨hxleft, hy⟩⟩
            exact Or.inl (ih.tail ⟨e, (mem_edgeList _ e).mpr heL, Or.inl ⟨rfl, rfl⟩⟩)
          · have hy : d.core.tail e ∈ cut.left := by
              by_contra hy
              exact hValid.2 e (Or.inr ⟨hxleft, hxg, hy⟩)
            have heL : e ∈ leftZero d cut :=
              Finset.mem_inter.mpr ⟨heZ, (cut.mem_leftSlots e).mpr ⟨hy, hxleft⟩⟩
            exact Or.inl (ih.tail ⟨e, (mem_edgeList _ e).mpr heL, Or.inr ⟨rfl, rfl⟩⟩)
      · exact Or.inr ih

/-- The complementary confinement lemma. -/
theorem reach_confined_right (hValid : cut.Valid) {u : Fin n} (hu : u ∈ cut.right)
    {v : Fin n} (h : ReachIn d.core d.zeroSlotSet u v) :
    ReachIn d.core (rightZero d cut) u v ∨
      ReachIn d.core (rightZero d cut) u cut.glue := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
      rcases ih with ih | ih
      · have hxright : x ∈ cut.right := mem_right_of_reachRight d cut hu ih
        by_cases hxg : x = cut.glue
        · exact Or.inr (hxg ▸ ih)
        · have hxnotleft : x ∉ cut.left := by
            rcases (cut.mem_right_iff x).mp hxright with hg | hnl
            · exact absurd hg hxg
            · exact hnl
          obtain ⟨e, he, hcase⟩ := hxy
          have heZ : e ∈ d.zeroSlotSet := (mem_edgeList _ e).mp he
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · have hy : d.core.head e ∈ cut.right := by
              rcases Finset.decidableMem (d.core.head e) cut.left with hy | hy
              · exact (cut.mem_right_iff _).mpr (Or.inr hy)
              · by_cases hyg : d.core.head e = cut.glue
                · exact (cut.mem_right_iff _).mpr (Or.inl hyg)
                · exact absurd (Or.inr ⟨hy, hyg, hxnotleft⟩) (hValid.2 e)
            have heR : e ∈ rightZero d cut :=
              Finset.mem_inter.mpr ⟨heZ, (cut.mem_rightSlots e).mpr ⟨hxright, hy⟩⟩
            exact Or.inl (ih.tail ⟨e, (mem_edgeList _ e).mpr heR, Or.inl ⟨rfl, rfl⟩⟩)
          · have hy : d.core.tail e ∈ cut.right := by
              rcases Finset.decidableMem (d.core.tail e) cut.left with hy | hy
              · exact (cut.mem_right_iff _).mpr (Or.inr hy)
              · by_cases hyg : d.core.tail e = cut.glue
                · exact (cut.mem_right_iff _).mpr (Or.inl hyg)
                · exact absurd (Or.inl ⟨hy, hyg, hxnotleft⟩) (hValid.2 e)
            have heR : e ∈ rightZero d cut :=
              Finset.mem_inter.mpr ⟨heZ, (cut.mem_rightSlots e).mpr ⟨hy, hxright⟩⟩
            exact Or.inl (ih.tail ⟨e, (mem_edgeList _ e).mpr heR, Or.inr ⟨rfl, rfl⟩⟩)
      · exact Or.inr ih

/-! ### Side-local representatives -/

theorem repLeft_mem_left {u : Fin n} (hu : u ∈ cut.left) :
    repLeft d cut u ∈ cut.left :=
  mem_left_of_reachLeft d cut hu (reachIn_self_compFold d.core (leftZero d cut) u)

theorem repRight_mem_right {u : Fin n} (hu : u ∈ cut.right) :
    repRight d cut u ∈ cut.right :=
  mem_right_of_reachRight d cut hu (reachIn_self_compFold d.core (rightZero d cut) u)

theorem eq_of_reachLeft_of_notMem {u v : Fin n} (hu : u ∉ cut.left)
    (h : ReachIn d.core (leftZero d cut) u v) : v = u := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih =>
      obtain ⟨e, he, hcase⟩ := hxy
      have hSlot : cut.LeftSlot e :=
        (cut.mem_leftSlots e).mp
          (leftZero_subset_leftSlots d cut ((mem_edgeList _ e).mp he))
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (ih ▸ hSlot.1) hu
      · exact absurd (ih ▸ hSlot.2) hu

theorem eq_of_reachRight_of_notMem {u v : Fin n} (hu : u ∉ cut.right)
    (h : ReachIn d.core (rightZero d cut) u v) : v = u := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih =>
      obtain ⟨e, he, hcase⟩ := hxy
      have hSlot : cut.RightSlot e :=
        (cut.mem_rightSlots e).mp
          (rightZero_subset_rightSlots d cut ((mem_edgeList _ e).mp he))
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (ih ▸ hSlot.1) hu
      · exact absurd (ih ▸ hSlot.2) hu

theorem repLeft_eq_self_of_notMem {u : Fin n} (hu : u ∉ cut.left) :
    repLeft d cut u = u :=
  eq_of_reachLeft_of_notMem d cut hu (reachIn_self_compFold d.core (leftZero d cut) u)

theorem repRight_eq_self_of_notMem {u : Fin n} (hu : u ∉ cut.right) :
    repRight d cut u = u :=
  eq_of_reachRight_of_notMem d cut hu (reachIn_self_compFold d.core (rightZero d cut) u)

theorem rep_repLeft {u : Fin n} : d.rep (repLeft d cut u) = d.rep u :=
  (d.rep_eq_of_reachIn (reachIn_mono (leftZero_subset d cut)
    (reachIn_self_compFold d.core (leftZero d cut) u))).symm

theorem rep_repRight {u : Fin n} : d.rep (repRight d cut u) = d.rep u :=
  (d.rep_eq_of_reachIn (reachIn_mono (rightZero_subset d cut)
    (reachIn_self_compFold d.core (rightZero d cut) u))).symm

/-! ### Side stability: a class off the articulation lies wholly on one side -/

/-- **Side stability.**  If a class does not contain the articulation, its
members all lie on the same side of the cut.  This is the fact that makes the
push-forward of a cut along a contraction well defined. -/
theorem mem_left_of_rep_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    {u v : Fin n} (hu : u ∈ cut.left) (huv : d.rep u = d.rep v)
    (hne : d.rep u ≠ d.rep cut.glue) : v ∈ cut.left := by
  rcases reach_confined_left d cut hValid hu (hRep u v huv) with h | h
  · exact mem_left_of_reachLeft d cut hu h
  · exact absurd (d.rep_eq_of_reachIn (reachIn_mono (leftZero_subset d cut) h)) hne

theorem mem_right_of_rep_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    {u v : Fin n} (hu : u ∈ cut.right) (huv : d.rep u = d.rep v)
    (hne : d.rep u ≠ d.rep cut.glue) : v ∈ cut.right := by
  rcases reach_confined_right d cut hValid hu (hRep u v huv) with h | h
  · exact mem_right_of_reachRight d cut hu h
  · exact absurd (d.rep_eq_of_reachIn (reachIn_mono (rightZero_subset d cut) h)) hne

/-- **Fibre equality.**  On the named side the global classes and the
side-local classes agree: a walk between two left vertices can be rerouted
through left slots only. -/
theorem repLeft_eq_of_rep_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    {u v : Fin n} (hu : u ∈ cut.left) (hv : v ∈ cut.left)
    (huv : d.rep u = d.rep v) : repLeft d cut u = repLeft d cut v := by
  have hEquiv := reachIn_equivalence d.core (leftZero d cut)
  rcases reach_confined_left d cut hValid hu (hRep u v huv) with h | h
  · exact (compFold_iff d.core _ u v).mpr h
  · rcases reach_confined_left d cut hValid hv (hRep v u huv.symm) with h' | h'
    · exact ((compFold_iff d.core _ v u).mpr h').symm
    · exact (compFold_iff d.core _ u v).mpr (hEquiv.trans h (hEquiv.symm h'))

theorem repRight_eq_of_rep_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    {u v : Fin n} (hu : u ∈ cut.right) (hv : v ∈ cut.right)
    (huv : d.rep u = d.rep v) : repRight d cut u = repRight d cut v := by
  have hEquiv := reachIn_equivalence d.core (rightZero d cut)
  rcases reach_confined_right d cut hValid hu (hRep u v huv) with h | h
  · exact (compFold_iff d.core _ u v).mpr h
  · rcases reach_confined_right d cut hValid hv (hRep v u huv.symm) with h' | h'
    · exact ((compFold_iff d.core _ v u).mpr h').symm
    · exact (compFold_iff d.core _ u v).mpr (hEquiv.trans h (hEquiv.symm h'))

/-! ### The rank inequality on each side -/

theorem card_image_repLeft_le (hValid : cut.Valid) (hRep : d.RepIsContraction) :
    (cut.left.image (repLeft d cut)).card ≤ (cut.left.image d.rep).card := by
  refine Finset.card_le_card_of_injOn d.rep ?_ ?_
  · intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image_of_mem d.rep (repLeft_mem_left d cut hu)
  · intro r₁ h₁ r₂ h₂ h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₁)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₂)
    refine repLeft_eq_of_rep_eq d cut hValid hRep hu hv ?_
    rw [← rep_repLeft d cut (u := u), ← rep_repLeft d cut (u := v)]
    exact h

theorem card_image_repRight_le (hValid : cut.Valid) (hRep : d.RepIsContraction) :
    (cut.right.image (repRight d cut)).card ≤ (cut.right.image d.rep).card := by
  refine Finset.card_le_card_of_injOn d.rep ?_ ?_
  · intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_image_of_mem d.rep (repRight_mem_right d cut hu)
  · intro r₁ h₁ r₂ h₂ h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₁)
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h₂)
    refine repRight_eq_of_rep_eq d cut hValid hRep hu hv ?_
    rw [← rep_repRight d cut (u := u), ← rep_repRight d cut (u := v)]
    exact h

theorem card_left_le_image_repLeft :
    cut.left.card ≤ (cut.left.image (repLeft d cut)).card + (leftZero d cut).card := by
  classical
  have hmat : n ≤ (Finset.image (repLeft d cut) Finset.univ).card
      + (leftZero d cut).card :=
    card_le_card_image_compFold_add_card d.core (leftZero d cut)
  have hsub : Finset.image (repLeft d cut) Finset.univ
      ⊆ cut.left.image (repLeft d cut) ∪ (Finset.univ \ cut.left) := by
    intro r hr
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
    by_cases hu : u ∈ cut.left
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
    · rw [repLeft_eq_self_of_notMem d cut hu]
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩)
  have hcard : (Finset.image (repLeft d cut) Finset.univ).card
      ≤ (cut.left.image (repLeft d cut)).card + (Finset.univ \ cut.left).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hdiff : (Finset.univ \ cut.left).card = n - cut.left.card := by
    rw [Finset.card_univ_sdiff]
    simp
  have hle : cut.left.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ cut.left)
  rw [hdiff] at hcard
  omega

theorem card_right_le_image_repRight :
    cut.right.card ≤ (cut.right.image (repRight d cut)).card + (rightZero d cut).card := by
  classical
  have hmat : n ≤ (Finset.image (repRight d cut) Finset.univ).card
      + (rightZero d cut).card :=
    card_le_card_image_compFold_add_card d.core (rightZero d cut)
  have hsub : Finset.image (repRight d cut) Finset.univ
      ⊆ cut.right.image (repRight d cut) ∪ (Finset.univ \ cut.right) := by
    intro r hr
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
    by_cases hu : u ∈ cut.right
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
    · rw [repRight_eq_self_of_notMem d cut hu]
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩)
  have hcard : (Finset.image (repRight d cut) Finset.univ).card
      ≤ (cut.right.image (repRight d cut)).card + (Finset.univ \ cut.right).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hdiff : (Finset.univ \ cut.right).card = n - cut.right.card := by
    rw [Finset.card_univ_sdiff]
    simp
  have hle : cut.right.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ cut.right)
  rw [hdiff] at hcard
  omega

/-! ### The two sides exhaust, and the inequalities are tight -/

theorem card_image_left_add_card_image_right (hValid : cut.Valid)
    (hRep : d.RepIsContraction) :
    (cut.left.image d.rep).card + (cut.right.image d.rep).card
      = (Finset.univ.image d.rep).card + 1 := by
  classical
  have hunion : cut.left.image d.rep ∪ cut.right.image d.rep
      = Finset.univ.image d.rep := by
    rw [← Finset.image_union]
    congr 1
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hv : v ∈ cut.left
    · exact Or.inl hv
    · exact Or.inr (cut.mem_right_of_not_mem_left hv)
  have hinter : cut.left.image d.rep ∩ cut.right.image d.rep = {d.rep cut.glue} := by
    ext r
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, hr⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp hr
      by_contra hne
      have hvleft : v ∈ cut.left :=
        mem_left_of_rep_eq d cut hValid hRep hu hv'.symm hne
      rcases (cut.mem_right_iff v).mp hv with hg | hnl
      · exact hne (by rw [← hv', hg])
      · exact hnl hvleft
    · rintro rfl
      exact ⟨Finset.mem_image_of_mem _ hValid.1,
        Finset.mem_image_of_mem _ ((cut.mem_right_iff _).mpr (Or.inl rfl))⟩
  have hsum := Finset.card_union_add_card_inter
    (cut.left.image d.rep) (cut.right.image d.rep)
  rw [hunion, hinter] at hsum
  simp only [Finset.card_singleton] at hsum
  omega

theorem card_leftZero_add_card_rightZero (hValid : cut.Valid)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e) :
    (leftZero d cut).card + (rightZero d cut).card = d.zeroSlotSet.card := by
  classical
  have hdisj : Disjoint (leftZero d cut) (rightZero d cut) :=
    Finset.disjoint_of_subset_left (leftZero_subset_leftSlots d cut)
      (Finset.disjoint_of_subset_right (rightZero_subset_rightSlots d cut)
        (cut.leftSlots_disjoint_rightSlots hLoopless))
  have hunion : leftZero d cut ∪ rightZero d cut = d.zeroSlotSet := by
    ext e
    simp only [leftZero, rightZero, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases cut.leftSlot_or_rightSlot hValid e with hs | hs
      · exact Or.inl ⟨h, (cut.mem_leftSlots e).mpr hs⟩
      · exact Or.inr ⟨h, (cut.mem_rightSlots e).mpr hs⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- **The face-restricted forest count on the named side.**  This is the
identity that replaces `spec.length_pos` in the genus calculation: a vanishing
left slot removes exactly one left vertex class. -/
theorem card_left_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e) :
    cut.left.card = (cut.left.image d.rep).card + (leftZero d cut).card := by
  have h1 := card_left_le_image_repLeft d cut
  have h2 := card_image_repLeft_le d cut hValid hRep
  have h3 := card_right_le_image_repRight d cut
  have h4 := card_image_repRight_le d cut hValid hRep
  have h5 := cut.right_card_add_left_card hValid
  have h6 := card_image_left_add_card_image_right d cut hValid hRep
  have h7 := card_leftZero_add_card_rightZero d cut hValid hLoopless
  have h8 := d.forest'
  omega

theorem card_right_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e) :
    cut.right.card = (cut.right.image d.rep).card + (rightZero d cut).card := by
  have h1 := card_left_le_image_repLeft d cut
  have h2 := card_image_repLeft_le d cut hValid hRep
  have h3 := card_right_le_image_repRight d cut
  have h4 := card_image_repRight_le d cut hValid hRep
  have h5 := cut.right_card_add_left_card hValid
  have h6 := card_image_left_add_card_image_right d cut hValid hRep
  have h7 := card_leftZero_add_card_rightZero d cut hValid hLoopless
  have h8 := d.forest'
  omega

/-! ## The push-forward of the cut to the contracted core -/

/-- The uncontracted core vertex naming a contracted class. -/
noncomputable def classVal (v' : Fin d.classCard) : Fin n := (d.classIndex.symm v').val

/-- The uncontracted slot naming a surviving slot. -/
noncomputable def slotOf (e' : Fin d.slotCard) : Fin p := (d.slotIndex.symm e').val

theorem rep_classVal (v' : Fin d.classCard) : d.rep (classVal d v') = classVal d v' :=
  (d.classIndex.symm v').property

theorem classVal_injective : Function.Injective (classVal d) := by
  intro a b h
  exact d.classIndex.symm.injective (Subtype.ext h)

theorem classVal_classIndex (r : Fin n) (hr : d.rep r = r) :
    classVal d (d.classIndex ⟨r, hr⟩) = r := by
  show (d.classIndex.symm (d.classIndex ⟨r, hr⟩)).val = r
  rw [Equiv.symm_apply_apply]

theorem slotOf_injective : Function.Injective (slotOf d) := by
  intro a b h
  exact d.slotIndex.symm.injective (Subtype.ext h)

theorem slotOf_pos (e' : Fin d.slotCard) : 0 < d.length (slotOf d e') :=
  (d.slotIndex.symm e').property

theorem slotOf_surj {e : Fin p} (he : 0 < d.length e) : ∃ e', slotOf d e' = e := by
  refine ⟨d.slotIndex ⟨e, he⟩, ?_⟩
  show (d.slotIndex.symm (d.slotIndex ⟨e, he⟩)).val = e
  rw [Equiv.symm_apply_apply]

theorem classVal_tail (e' : Fin d.slotCard) :
    classVal d (d.contractedCore.tail e') = d.rep (d.core.tail (slotOf d e')) := by
  show (d.classIndex.symm (d.classIndex ⟨_, _⟩)).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem classVal_head (e' : Fin d.slotCard) :
    classVal d (d.contractedCore.head e') = d.rep (d.core.head (slotOf d e')) := by
  show (d.classIndex.symm (d.classIndex ⟨_, _⟩)).val = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- **The push-forward cut.**  A contracted class is on the named side exactly
when it contains a named-side vertex.  Off the articulation class that is
unambiguous, by side stability. -/
noncomputable def contractedCut : CoreVertexCut.Data d.contractedCore where
  glue := d.classIndex ⟨d.rep cut.glue, d.rep_idem _⟩
  left := Finset.univ.filter (fun v' => classVal d v' ∈ cut.left.image d.rep)

@[simp] theorem mem_contractedCut_left (v' : Fin d.classCard) :
    v' ∈ (contractedCut d cut).left ↔ classVal d v' ∈ cut.left.image d.rep := by
  simp [contractedCut]

theorem classVal_contractedCut_glue :
    classVal d (contractedCut d cut).glue = d.rep cut.glue :=
  classVal_classIndex d _ (d.rep_idem _)

/-- Membership of a class in the named side, read on the uncontracted core. -/
theorem mem_image_rep_iff (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (v : Fin n) :
    d.rep v ∈ cut.left.image d.rep ↔ (v ∈ cut.left ∨ d.rep v = d.rep cut.glue) := by
  constructor
  · intro h
    obtain ⟨u, hu, hu'⟩ := Finset.mem_image.mp h
    by_cases hg : d.rep v = d.rep cut.glue
    · exact Or.inr hg
    · exact Or.inl (mem_left_of_rep_eq d cut hValid hRep hu hu' (by rw [hu']; exact hg))
  · rintro (h | h)
    · exact Finset.mem_image_of_mem _ h
    · rw [h]
      exact Finset.mem_image_of_mem _ hValid.1

theorem mem_contractedCut_left_iff (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (v : Fin n) (v' : Fin d.classCard) (hv : classVal d v' = d.rep v) :
    v' ∈ (contractedCut d cut).left ↔ (v ∈ cut.left ∨ d.rep v = d.rep cut.glue) := by
  rw [mem_contractedCut_left, hv, mem_image_rep_iff d cut hValid hRep]

/-! ### Validity of the push-forward -/

theorem contractedCut_valid (hValid : cut.Valid) (hRep : d.RepIsContraction) :
    (contractedCut d cut).Valid := by
  classical
  refine ⟨?_, ?_⟩
  · rw [mem_contractedCut_left, classVal_contractedCut_glue]
    exact Finset.mem_image_of_mem _ hValid.1
  · intro e' hCross
    set e : Fin p := slotOf d e' with he
    have hTailMem : d.contractedCore.tail e' ∈ (contractedCut d cut).left ↔
        (d.core.tail e ∈ cut.left ∨ d.rep (d.core.tail e) = d.rep cut.glue) :=
      mem_contractedCut_left_iff d cut hValid hRep _ _ (classVal_tail d e')
    have hHeadMem : d.contractedCore.head e' ∈ (contractedCut d cut).left ↔
        (d.core.head e ∈ cut.left ∨ d.rep (d.core.head e) = d.rep cut.glue) :=
      mem_contractedCut_left_iff d cut hValid hRep _ _ (classVal_head d e')
    have hTailNe : d.contractedCore.tail e' ≠ (contractedCut d cut).glue ↔
        d.rep (d.core.tail e) ≠ d.rep cut.glue := by
      constructor
      · intro h hEq
        exact h (classVal_injective d (by
          rw [classVal_tail d e', classVal_contractedCut_glue]; exact hEq))
      · intro h hEq
        exact h (by rw [← classVal_tail d e', ← classVal_contractedCut_glue, hEq])
    have hHeadNe : d.contractedCore.head e' ≠ (contractedCut d cut).glue ↔
        d.rep (d.core.head e) ≠ d.rep cut.glue := by
      constructor
      · intro h hEq
        exact h (classVal_injective d (by
          rw [classVal_head d e', classVal_contractedCut_glue]; exact hEq))
      · intro h hEq
        exact h (by rw [← classVal_head d e', ← classVal_contractedCut_glue, hEq])
    rcases hCross with ⟨hT, hTg, hH⟩ | ⟨hH, hHg, hT⟩
    · have hTg' := hTailNe.mp hTg
      have hTl : d.core.tail e ∈ cut.left := by
        rcases hTailMem.mp hT with h | h
        · exact h
        · exact absurd h hTg'
      have hTne : d.core.tail e ≠ cut.glue := fun hEq => hTg' (by rw [hEq])
      have hHl : d.core.head e ∉ cut.left := fun h => hH (hHeadMem.mpr (Or.inl h))
      exact hValid.2 e (Or.inl ⟨hTl, hTne, hHl⟩)
    · have hHg' := hHeadNe.mp hHg
      have hHl : d.core.head e ∈ cut.left := by
        rcases hHeadMem.mp hH with h | h
        · exact h
        · exact absurd h hHg'
      have hHne : d.core.head e ≠ cut.glue := fun hEq => hHg' (by rw [hEq])
      have hTl : d.core.tail e ∉ cut.left := fun h => hT (hTailMem.mpr (Or.inl h))
      exact hValid.2 e (Or.inr ⟨hHl, hHne, hTl⟩)

/-! ### The two counts -/

theorem contractedCut_left_card :
    (contractedCut d cut).left.card = (cut.left.image d.rep).card := by
  classical
  have himg : (contractedCut d cut).left.image (classVal d) = cut.left.image d.rep := by
    ext r
    constructor
    · intro hr
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hr
      exact (mem_contractedCut_left d cut v').mp hv'
    · intro hr
      have hfix : d.rep r = r := by
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
        exact d.rep_idem u
      refine Finset.mem_image.mpr ⟨d.classIndex ⟨r, hfix⟩, ?_, classVal_classIndex d r hfix⟩
      rw [mem_contractedCut_left, classVal_classIndex d r hfix]
      exact hr
  rw [← himg, Finset.card_image_of_injective _ (classVal_injective d)]

/-- A surviving slot is wholly on the named side after contraction exactly
when it already was before.  The forward direction is where
`DegSpec.rep_loopless` — hence the census hypothesis `¬ IsLoopy` — is used. -/
theorem contractedCut_leftSlot_iff (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (e' : Fin d.slotCard) :
    (contractedCut d cut).LeftSlot e' ↔ cut.LeftSlot (slotOf d e') := by
  classical
  have hTailMem := mem_contractedCut_left_iff d cut hValid hRep
    (d.core.tail (slotOf d e')) (d.contractedCore.tail e') (classVal_tail d e')
  have hHeadMem := mem_contractedCut_left_iff d cut hValid hRep
    (d.core.head (slotOf d e')) (d.contractedCore.head e') (classVal_head d e')
  have hLoop := d.rep_loopless (slotOf d e') (slotOf_pos d e')
  constructor
  · rintro ⟨hT, hH⟩
    have hT' := hTailMem.mp hT
    have hH' := hHeadMem.mp hH
    by_cases hTl : d.core.tail (slotOf d e') ∈ cut.left
    · by_cases hHl : d.core.head (slotOf d e') ∈ cut.left
      · exact ⟨hTl, hHl⟩
      · have hHg : d.rep (d.core.head (slotOf d e')) = d.rep cut.glue := by
          rcases hH' with h | h
          · exact absurd h hHl
          · exact h
        have hTne : d.core.tail (slotOf d e') ≠ cut.glue := by
          intro hEq
          exact hLoop (by rw [hEq]; exact hHg.symm)
        exact absurd (Or.inl ⟨hTl, hTne, hHl⟩) (hValid.2 _)
    · have hTg : d.rep (d.core.tail (slotOf d e')) = d.rep cut.glue := by
        rcases hT' with h | h
        · exact absurd h hTl
        · exact h
      by_cases hHl : d.core.head (slotOf d e') ∈ cut.left
      · have hHne : d.core.head (slotOf d e') ≠ cut.glue := by
          intro hEq
          exact hLoop (by rw [hEq]; exact hTg)
        exact absurd (Or.inr ⟨hHl, hHne, hTl⟩) (hValid.2 _)
      · have hHg : d.rep (d.core.head (slotOf d e')) = d.rep cut.glue := by
          rcases hH' with h | h
          · exact absurd h hHl
          · exact h
        exact absurd (hTg.trans hHg.symm) hLoop
  · rintro ⟨hT, hH⟩
    exact ⟨hTailMem.mpr (Or.inl hT), hHeadMem.mpr (Or.inl hH)⟩

/-- The surviving named slots, read on the uncontracted core, are exactly the
named slots that do not vanish. -/
theorem contractedCut_leftSlots_image (hValid : cut.Valid)
    (hRep : d.RepIsContraction) :
    (contractedCut d cut).leftSlots.image (slotOf d)
      = cut.leftSlots \ leftZero d cut := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    have hL : cut.LeftSlot (slotOf d e') :=
      (contractedCut_leftSlot_iff d cut hValid hRep e').mp
        (((contractedCut d cut).mem_leftSlots e').mp he')
    refine Finset.mem_sdiff.mpr ⟨(cut.mem_leftSlots _).mpr hL, ?_⟩
    intro hz
    have hzero := (d.mem_zeroSlotSet _).mp (leftZero_subset d cut hz)
    have := slotOf_pos d e'
    omega
  · intro he
    obtain ⟨heL, heZ⟩ := Finset.mem_sdiff.mp he
    have hL := (cut.mem_leftSlots e).mp heL
    have hpos : 0 < d.length e := by
      rcases Nat.eq_zero_or_pos (d.length e) with h | h
      · exact absurd (Finset.mem_inter.mpr ⟨(d.mem_zeroSlotSet e).mpr h, heL⟩) heZ
      · exact h
    obtain ⟨e', rfl⟩ := slotOf_surj d hpos
    exact Finset.mem_image.mpr ⟨e', ((contractedCut d cut).mem_leftSlots e').mpr
      ((contractedCut_leftSlot_iff d cut hValid hRep e').mpr hL), rfl⟩

theorem contractedCut_leftSlots_card_add (hValid : cut.Valid)
    (hRep : d.RepIsContraction) :
    (contractedCut d cut).leftSlots.card + (leftZero d cut).card
      = cut.leftSlots.card := by
  classical
  have himg := contractedCut_leftSlots_image d cut hValid hRep
  have hcard : (contractedCut d cut).leftSlots.card
      = (cut.leftSlots \ leftZero d cut).card := by
    rw [← himg, Finset.card_image_of_injective _ (slotOf_injective d)]
  rw [hcard]
  exact Finset.card_sdiff_add_card_eq_card (leftZero_subset_leftSlots d cut)

/-! ### Genus is preserved -/

/-- **The named factor genus is preserved at every forest face.**  This is the
theorem that replaces `SubdivisionGraph.Spec.length_pos` in
`CoreVertexCutGenus.leftGraph_genus`: a vanishing left slot removes one left
slot *and* one left vertex class, so the difference is unchanged. -/
theorem contractedCut_leftGenus (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e) :
    (contractedCut d cut).leftGenus = cut.leftGenus := by
  have h1 := contractedCut_leftSlots_card_add d cut hValid hRep
  have h2 := contractedCut_left_card d cut
  have h3 := card_left_eq d cut hValid hRep hLoopless
  unfold CoreVertexCut.Data.leftGenus CoreVertexCut.Data.leftSlotCount
  omega

theorem classCard_add_zero : d.classCard + d.zeroSlotSet.card = n := by
  show Fintype.card d.Class + _ = n
  rw [d.card_class]
  exact d.forest'

theorem slotCard_add_zero : d.slotCard + d.zeroSlotSet.card = p := by
  have h1 : d.slotCard = (Finset.univ.filter (fun e : Fin p => 0 < d.length e)).card := by
    show Fintype.card d.PositiveSlot = _
    rw [Fintype.card_subtype]
  rw [h1]
  exact d.card_pos_add_card_zero

/-- The complementary factor genus is preserved too — by genus additivity on
both cores, so no second counting argument is needed. -/
theorem contractedCut_rightGenus (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e) :
    (contractedCut d cut).rightGenus = cut.rightGenus := by
  have hA := cut.leftGenus_add_rightGenus hValid hLoopless
  have hB := (contractedCut d cut).leftGenus_add_rightGenus
    (contractedCut_valid d cut hValid hRep) d.contractedSpec.core_loopless
  have hC := contractedCut_leftGenus d cut hValid hRep hLoopless
  have h1 := classCard_add_zero d
  have h2 := slotCard_add_zero d
  omega

/-! ### Two-regularity, the rigidity half of the `(3,1)` branch

`GenusFourRankOneAlternatives` conjoins `RightTwoRegular` with
`rightGenus = 1` for a reason: `PointedGenusOneRigid` is what the `(3,1)` wedge
theorem consumes, and genus one alone does not supply it.  So the push-forward
has to carry two-regularity, not just the genus.

The count is: a contracted class `k` of the complementary side has retained
degree `2 · #(k ∩ right) - 2 · #(vanishing right slots inside k)`, because each
collapsed slot destroys exactly two incidences.  That is `2` exactly when the
class carries one fewer collapsed slot than vertices — the *per-class* form of
`card_right_eq`, which the global identity forces once each class satisfies the
matroid inequality separately. -/

/-- The members of one contracted class on the complementary side. -/
def rightFibre (k : Fin n) : Finset (Fin n) :=
  cut.right.filter (fun v => d.rep v = k)

/-- The vanishing complementary slots inside one contracted class. -/
def rightFibreSlots (k : Fin n) : Finset (Fin p) :=
  (rightZero d cut).filter (fun e => d.rep (d.core.tail e) = k)

/-- The members of one contracted class on the named side. -/
def leftFibre (k : Fin n) : Finset (Fin n) :=
  cut.left.filter (fun v => d.rep v = k)

/-- The vanishing named slots inside one contracted class. -/
def leftFibreSlots (k : Fin n) : Finset (Fin p) :=
  (leftZero d cut).filter (fun e => d.rep (d.core.tail e) = k)

/-- The contracted class is constant along a vanishing-slot walk. -/
theorem rep_eq_of_reachIn_zero {F : Finset (Fin p)} (hF : F ⊆ d.zeroSlotSet)
    {u v : Fin n} (h : ReachIn d.core F u v) : d.rep u = d.rep v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨e, heF, hends⟩ := hstep
      have hz : d.length e = 0 :=
        (Utilities.Certificate.DegenerateSpec.DegSpec.mem_zeroSlotSet d e).mp
          (hF ((mem_edgeList F e).mp heF))
      have hre := d.rep_zero e hz
      rcases hends with ⟨ht, hh⟩ | ⟨hh, ht⟩
      · rw [ih, ← ht, hre, hh]
      · rw [ih, ← hh, ← hre, ht]

/-- A vanishing-slot walk between two vertices of one contracted class uses
only slots of that class, so the walk survives restriction to the fibre. -/
theorem reachIn_rightFibreSlots_of_reachIn {k : Fin n}
    {u v : Fin n} (hku : d.rep u = k)
    (h : ReachIn d.core (rightZero d cut) u v) :
    ReachIn d.core (rightFibreSlots d cut k) u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hwalk hstep ih =>
      obtain ⟨e, heF, hends⟩ := hstep
      have heR : e ∈ rightZero d cut := (mem_edgeList _ e).mp heF
      have hsub : rightZero d cut ⊆ d.zeroSlotSet := Finset.inter_subset_left
      -- `b` is in class `k`, and the slot does not leave it.
      have hb : d.rep b = k := by
        rw [← hku]
        exact (rep_eq_of_reachIn_zero (d := d) hsub hwalk).symm
      have hz : d.length e = 0 :=
        (Utilities.Certificate.DegenerateSpec.DegSpec.mem_zeroSlotSet d e).mp
          (hsub heR)
      have hre := d.rep_zero e hz
      have hmem : e ∈ rightFibreSlots d cut k := by
        refine Finset.mem_filter.mpr ⟨heR, ?_⟩
        rcases hends with ⟨ht, -⟩ | ⟨hh, ht⟩
        · rw [ht]; exact hb
        · rw [hre, hh]; exact hb
      exact Relation.ReflTransGen.tail ih
        ⟨e, (mem_edgeList _ e).mpr hmem, hends⟩

/-- The left twin of `reachIn_rightFibreSlots_of_reachIn`. -/
theorem reachIn_leftFibreSlots_of_reachIn {k : Fin n}
    {u v : Fin n} (hku : d.rep u = k)
    (h : ReachIn d.core (leftZero d cut) u v) :
    ReachIn d.core (leftFibreSlots d cut k) u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hwalk hstep ih =>
      obtain ⟨e, heF, hends⟩ := hstep
      have heL : e ∈ leftZero d cut := (mem_edgeList _ e).mp heF
      have hsub : leftZero d cut ⊆ d.zeroSlotSet := Finset.inter_subset_left
      have hb : d.rep b = k := by
        rw [← hku]
        exact (rep_eq_of_reachIn_zero (d := d) hsub hwalk).symm
      have hz : d.length e = 0 :=
        (Utilities.Certificate.DegenerateSpec.DegSpec.mem_zeroSlotSet d e).mp
          (hsub heL)
      have hre := d.rep_zero e hz
      have hmem : e ∈ leftFibreSlots d cut k := by
        refine Finset.mem_filter.mpr ⟨heL, ?_⟩
        rcases hends with ⟨ht, -⟩ | ⟨hh, ht⟩
        · rw [ht]; exact hb
        · rw [hre, hh]; exact hb
      exact Relation.ReflTransGen.tail ih
        ⟨e, (mem_edgeList _ e).mpr hmem, hends⟩

/-! ### Fibre bookkeeping -/

theorem mem_rightFibre_iff {k v : Fin n} :
    v ∈ rightFibre d cut k ↔ v ∈ cut.right ∧ d.rep v = k := Finset.mem_filter

theorem mem_leftFibre_iff {k v : Fin n} :
    v ∈ leftFibre d cut k ↔ v ∈ cut.left ∧ d.rep v = k := Finset.mem_filter

theorem mem_rightFibreSlots_iff {k : Fin n} {e : Fin p} :
    e ∈ rightFibreSlots d cut k ↔ e ∈ rightZero d cut ∧ d.rep (d.core.tail e) = k :=
  Finset.mem_filter

theorem mem_leftFibreSlots_iff {k : Fin n} {e : Fin p} :
    e ∈ leftFibreSlots d cut k ↔ e ∈ leftZero d cut ∧ d.rep (d.core.tail e) = k :=
  Finset.mem_filter

/-- Both endpoints of a vanishing complementary slot of class `k` lie in the
fibre of `k`: the slot lies wholly on the complementary side, and vanishing
makes its two endpoints share a class. -/
theorem tail_mem_rightFibre {k : Fin n} {e : Fin p}
    (he : e ∈ rightFibreSlots d cut k) : d.core.tail e ∈ rightFibre d cut k := by
  obtain ⟨heZ, hk⟩ := (mem_rightFibreSlots_iff d cut).mp he
  exact (mem_rightFibre_iff d cut).mpr
    ⟨((cut.mem_rightSlots e).mp (rightZero_subset_rightSlots d cut heZ)).1, hk⟩

theorem head_mem_rightFibre {k : Fin n} {e : Fin p}
    (he : e ∈ rightFibreSlots d cut k) : d.core.head e ∈ rightFibre d cut k := by
  obtain ⟨heZ, hk⟩ := (mem_rightFibreSlots_iff d cut).mp he
  have hz : d.length e = 0 :=
    (Utilities.Certificate.DegenerateSpec.DegSpec.mem_zeroSlotSet d e).mp
      (rightZero_subset d cut heZ)
  exact (mem_rightFibre_iff d cut).mpr
    ⟨((cut.mem_rightSlots e).mp (rightZero_subset_rightSlots d cut heZ)).2,
      by rw [← d.rep_zero e hz]; exact hk⟩

theorem tail_mem_leftFibre {k : Fin n} {e : Fin p}
    (he : e ∈ leftFibreSlots d cut k) : d.core.tail e ∈ leftFibre d cut k := by
  obtain ⟨heZ, hk⟩ := (mem_leftFibreSlots_iff d cut).mp he
  exact (mem_leftFibre_iff d cut).mpr
    ⟨((cut.mem_leftSlots e).mp (leftZero_subset_leftSlots d cut heZ)).1, hk⟩

theorem head_mem_leftFibre {k : Fin n} {e : Fin p}
    (he : e ∈ leftFibreSlots d cut k) : d.core.head e ∈ leftFibre d cut k := by
  obtain ⟨heZ, hk⟩ := (mem_leftFibreSlots_iff d cut).mp he
  have hz : d.length e = 0 :=
    (Utilities.Certificate.DegenerateSpec.DegSpec.mem_zeroSlotSet d e).mp
      (leftZero_subset d cut heZ)
  exact (mem_leftFibre_iff d cut).mpr
    ⟨((cut.mem_leftSlots e).mp (leftZero_subset_leftSlots d cut heZ)).2,
      by rw [← d.rep_zero e hz]; exact hk⟩

/-- A walk through the slots of one class cannot start outside that class. -/
theorem eq_of_reachIn_rightFibreSlots_of_notMem {k : Fin n} {u v : Fin n}
    (hu : u ∉ rightFibre d cut k)
    (h : ReachIn d.core (rightFibreSlots d cut k) u v) : v = u := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih =>
      obtain ⟨e, he, hcase⟩ := hxy
      have hmem : e ∈ rightFibreSlots d cut k := (mem_edgeList _ e).mp he
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (ih ▸ tail_mem_rightFibre d cut hmem) hu
      · exact absurd (ih ▸ head_mem_rightFibre d cut hmem) hu

theorem eq_of_reachIn_leftFibreSlots_of_notMem {k : Fin n} {u v : Fin n}
    (hu : u ∉ leftFibre d cut k)
    (h : ReachIn d.core (leftFibreSlots d cut k) u v) : v = u := by
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih =>
      obtain ⟨e, he, hcase⟩ := hxy
      have hmem : e ∈ leftFibreSlots d cut k := (mem_edgeList _ e).mp he
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (ih ▸ tail_mem_leftFibre d cut hmem) hu
      · exact absurd (ih ▸ head_mem_leftFibre d cut hmem) hu

/-- **The whole fibre is one class of its own slot set.**  This is what
`reachIn_rightFibreSlots_of_reachIn` buys: the walk joining two members of a
class can be rerouted through the slots of that class alone. -/
theorem compFold_rightFibreSlots_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    {k : Fin n} {u v : Fin n} (hu : u ∈ rightFibre d cut k)
    (hv : v ∈ rightFibre d cut k) :
    compFold d.core (rightFibreSlots d cut k) u
      = compFold d.core (rightFibreSlots d cut k) v := by
  obtain ⟨hur, huk⟩ := (mem_rightFibre_iff d cut).mp hu
  obtain ⟨hvr, hvk⟩ := (mem_rightFibre_iff d cut).mp hv
  have hEq : compFold d.core (rightZero d cut) u = compFold d.core (rightZero d cut) v :=
    repRight_eq_of_rep_eq d cut hValid hRep hur hvr (by rw [huk, hvk])
  exact (compFold_iff d.core _ u v).mpr
    (reachIn_rightFibreSlots_of_reachIn d cut huk ((compFold_iff d.core _ u v).mp hEq))

theorem compFold_leftFibreSlots_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    {k : Fin n} {u v : Fin n} (hu : u ∈ leftFibre d cut k)
    (hv : v ∈ leftFibre d cut k) :
    compFold d.core (leftFibreSlots d cut k) u
      = compFold d.core (leftFibreSlots d cut k) v := by
  obtain ⟨hul, huk⟩ := (mem_leftFibre_iff d cut).mp hu
  obtain ⟨hvl, hvk⟩ := (mem_leftFibre_iff d cut).mp hv
  have hEq : compFold d.core (leftZero d cut) u = compFold d.core (leftZero d cut) v :=
    repLeft_eq_of_rep_eq d cut hValid hRep hul hvl (by rw [huk, hvk])
  exact (compFold_iff d.core _ u v).mpr
    (reachIn_leftFibreSlots_of_reachIn d cut huk ((compFold_iff d.core _ u v).mp hEq))

/-- **The per-class matroid inequality.**  The whole fibre collapses to a
single class of its own slot set, which off the fibre is the identity, so the
graphic-matroid rank bound applied to `rightFibreSlots k` alone reads
`#(rightFibre k) ≤ #(rightFibreSlots k) + 1`. -/
theorem card_rightFibre_le (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (k : Fin n) :
    (rightFibre d cut k).card ≤ (rightFibreSlots d cut k).card + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty (rightFibre d cut k) with hE | ⟨v₀, hv₀⟩
  · rw [hE]
    simp
  · have hmat : n ≤ (Finset.image (compFold d.core (rightFibreSlots d cut k))
        Finset.univ).card + (rightFibreSlots d cut k).card :=
      card_le_card_image_compFold_add_card d.core (rightFibreSlots d cut k)
    have hsub : Finset.image (compFold d.core (rightFibreSlots d cut k)) Finset.univ
        ⊆ insert (compFold d.core (rightFibreSlots d cut k) v₀)
            (Finset.univ \ rightFibre d cut k) := by
      intro r hr
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
      by_cases hu : u ∈ rightFibre d cut k
      · exact Finset.mem_insert.mpr
          (Or.inl (compFold_rightFibreSlots_eq d cut hValid hRep hu hv₀))
      · rw [eq_of_reachIn_rightFibreSlots_of_notMem d cut hu
          (reachIn_self_compFold d.core (rightFibreSlots d cut k) u)]
        exact Finset.mem_insert_of_mem
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩)
    have hcard : (Finset.image (compFold d.core (rightFibreSlots d cut k))
        Finset.univ).card ≤ (Finset.univ \ rightFibre d cut k).card + 1 :=
      le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
    have hdiff : (Finset.univ \ rightFibre d cut k).card
        = n - (rightFibre d cut k).card := by
      rw [Finset.card_univ_sdiff]
      simp
    have hle : (rightFibre d cut k).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (rightFibre d cut k))
    omega

theorem card_leftFibre_le (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (k : Fin n) :
    (leftFibre d cut k).card ≤ (leftFibreSlots d cut k).card + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty (leftFibre d cut k) with hE | ⟨v₀, hv₀⟩
  · rw [hE]
    simp
  · have hmat : n ≤ (Finset.image (compFold d.core (leftFibreSlots d cut k))
        Finset.univ).card + (leftFibreSlots d cut k).card :=
      card_le_card_image_compFold_add_card d.core (leftFibreSlots d cut k)
    have hsub : Finset.image (compFold d.core (leftFibreSlots d cut k)) Finset.univ
        ⊆ insert (compFold d.core (leftFibreSlots d cut k) v₀)
            (Finset.univ \ leftFibre d cut k) := by
      intro r hr
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hr
      by_cases hu : u ∈ leftFibre d cut k
      · exact Finset.mem_insert.mpr
          (Or.inl (compFold_leftFibreSlots_eq d cut hValid hRep hu hv₀))
      · rw [eq_of_reachIn_leftFibreSlots_of_notMem d cut hu
          (reachIn_self_compFold d.core (leftFibreSlots d cut k) u)]
        exact Finset.mem_insert_of_mem
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩)
    have hcard : (Finset.image (compFold d.core (leftFibreSlots d cut k))
        Finset.univ).card ≤ (Finset.univ \ leftFibre d cut k).card + 1 :=
      le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
    have hdiff : (Finset.univ \ leftFibre d cut k).card
        = n - (leftFibre d cut k).card := by
      rw [Finset.card_univ_sdiff]
      simp
    have hle : (leftFibre d cut k).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (leftFibre d cut k))
    omega

/-- **Per-class tightness on the complementary side.**  Each class satisfies
the matroid inequality `card_rightFibre_le` separately; the fibres partition
`cut.right` and the fibre slot sets partition `rightZero`, so summing those
inequalities over the classes reproduces the already-proved global identity
`card_right_eq`.  A sum of `≤`s that meets its bound is termwise tight. -/
theorem card_rightFibre_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    {k : Fin n} (hk : k ∈ cut.right.image d.rep) :
    (rightFibre d cut k).card = (rightFibreSlots d cut k).card + 1 := by
  classical
  have hle : ∀ j ∈ cut.right.image d.rep,
      (rightFibre d cut j).card ≤ (rightFibreSlots d cut j).card + 1 :=
    fun j _ => card_rightFibre_le d cut hValid hRep j
  have hfib : cut.right.card
      = ∑ j ∈ cut.right.image d.rep, (rightFibre d cut j).card :=
    Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_image_of_mem d.rep hv)
  have hslot : (rightZero d cut).card
      = ∑ j ∈ cut.right.image d.rep, (rightFibreSlots d cut j).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => Finset.mem_image_of_mem d.rep
      ((cut.mem_rightSlots e).mp (rightZero_subset_rightSlots d cut he)).1)
  have hconst : ∑ j ∈ cut.right.image d.rep, ((rightFibreSlots d cut j).card + 1)
      = ∑ j ∈ cut.right.image d.rep, (rightFibreSlots d cut j).card
        + (cut.right.image d.rep).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hglobal := card_right_eq d cut hValid hRep hLoopless
  have hsum : ∑ j ∈ cut.right.image d.rep, (rightFibre d cut j).card
      = ∑ j ∈ cut.right.image d.rep, ((rightFibreSlots d cut j).card + 1) := by
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum k hk

/-- Per-class tightness on the named side; the mirror of
`card_rightFibre_eq`. -/
theorem card_leftFibre_eq (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    {k : Fin n} (hk : k ∈ cut.left.image d.rep) :
    (leftFibre d cut k).card = (leftFibreSlots d cut k).card + 1 := by
  classical
  have hle : ∀ j ∈ cut.left.image d.rep,
      (leftFibre d cut j).card ≤ (leftFibreSlots d cut j).card + 1 :=
    fun j _ => card_leftFibre_le d cut hValid hRep j
  have hfib : cut.left.card
      = ∑ j ∈ cut.left.image d.rep, (leftFibre d cut j).card :=
    Finset.card_eq_sum_card_fiberwise (fun v hv => Finset.mem_image_of_mem d.rep hv)
  have hslot : (leftZero d cut).card
      = ∑ j ∈ cut.left.image d.rep, (leftFibreSlots d cut j).card :=
    Finset.card_eq_sum_card_fiberwise (fun e he => Finset.mem_image_of_mem d.rep
      ((cut.mem_leftSlots e).mp (leftZero_subset_leftSlots d cut he)).1)
  have hconst : ∑ j ∈ cut.left.image d.rep, ((leftFibreSlots d cut j).card + 1)
      = ∑ j ∈ cut.left.image d.rep, (leftFibreSlots d cut j).card
        + (cut.left.image d.rep).card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hglobal := card_left_eq d cut hValid hRep hLoopless
  have hsum : ∑ j ∈ cut.left.image d.rep, (leftFibre d cut j).card
      = ∑ j ∈ cut.left.image d.rep, ((leftFibreSlots d cut j).card + 1) := by
    omega
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum k hk

/-! ### Regrouping incidences by contracted class -/

/-- **Generic incidence regrouping.**  For a slot set `S` all of whose slots
have both endpoints in a vertex set `V`, the incidences of the *surviving*
slots of `S` at one contracted class `k` are the incidences of all of `S` at
the members of that class, less the two incidences that each vanishing slot of
the class contributes to it. -/
theorem sum_incidence_class (V : Finset (Fin n)) (S : Finset (Fin p))
    (hS : ∀ e ∈ S, d.core.tail e ∈ V ∧ d.core.head e ∈ V) (k : Fin n) :
    (∑ e ∈ S \ (d.zeroSlotSet ∩ S),
        ((if d.rep (d.core.tail e) = k then 1 else 0)
          + (if d.rep (d.core.head e) = k then 1 else 0)))
      + 2 * ((d.zeroSlotSet ∩ S).filter
          (fun e => d.rep (d.core.tail e) = k)).card
      = ∑ v ∈ V.filter (fun v => d.rep v = k),
          ∑ e ∈ S, ((if d.core.tail e = v then 1 else 0)
            + (if d.core.head e = v then 1 else 0)) := by
  classical
  have hsub : d.zeroSlotSet ∩ S ⊆ S := Finset.inter_subset_right
  have hRHS : (∑ v ∈ V.filter (fun v => d.rep v = k),
        ∑ e ∈ S, ((if d.core.tail e = v then 1 else 0)
          + (if d.core.head e = v then 1 else 0)))
      = ∑ e ∈ S, ((if d.rep (d.core.tail e) = k then 1 else 0)
          + (if d.rep (d.core.head e) = k then 1 else 0)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨hT, hH⟩ := hS e he
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    congr 1
    · by_cases h : d.rep (d.core.tail e) = k
      · rw [if_pos (Finset.mem_filter.mpr ⟨hT, h⟩), if_pos h]
      · have hm : d.core.tail e ∉ V.filter (fun v => d.rep v = k) :=
          fun hm => h (Finset.mem_filter.mp hm).2
        rw [if_neg hm, if_neg h]
    · by_cases h : d.rep (d.core.head e) = k
      · rw [if_pos (Finset.mem_filter.mpr ⟨hH, h⟩), if_pos h]
      · have hm : d.core.head e ∉ V.filter (fun v => d.rep v = k) :=
          fun hm => h (Finset.mem_filter.mp hm).2
        rw [if_neg hm, if_neg h]
  have hsplit := Finset.sum_sdiff
    (f := fun e => (if d.rep (d.core.tail e) = k then 1 else 0)
      + (if d.rep (d.core.head e) = k then 1 else 0)) hsub
  have hzero : (∑ e ∈ d.zeroSlotSet ∩ S,
        ((if d.rep (d.core.tail e) = k then 1 else 0)
          + (if d.rep (d.core.head e) = k then 1 else 0)))
      = 2 * ((d.zeroSlotSet ∩ S).filter
          (fun e => d.rep (d.core.tail e) = k)).card := by
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hz : d.length e = 0 :=
      (Utilities.Certificate.DegenerateSpec.DegSpec.mem_zeroSlotSet d e).mp
        (Finset.mem_inter.mp he).1
    rw [d.rep_zero e hz]
    by_cases h : d.rep (d.core.head e) = k <;> simp [h]
  omega

/-- The complementary-side instance of `sum_incidence_class`. -/
theorem sum_rightIncidentDegree_fibre (k : Fin n) :
    (∑ e ∈ cut.rightSlots \ rightZero d cut,
        ((if d.rep (d.core.tail e) = k then 1 else 0)
          + (if d.rep (d.core.head e) = k then 1 else 0)))
      + 2 * (rightFibreSlots d cut k).card
      = ∑ v ∈ rightFibre d cut k, cut.rightIncidentDegree v :=
  sum_incidence_class d cut.right cut.rightSlots
    (fun e he => (cut.mem_rightSlots e).mp he) k

/-- The named-side instance of `sum_incidence_class`. -/
theorem sum_leftIncidentDegree_fibre (k : Fin n) :
    (∑ e ∈ cut.leftSlots \ leftZero d cut,
        ((if d.rep (d.core.tail e) = k then 1 else 0)
          + (if d.rep (d.core.head e) = k then 1 else 0)))
      + 2 * (leftFibreSlots d cut k).card
      = ∑ v ∈ leftFibre d cut k, cut.leftIncidentDegree v :=
  sum_incidence_class d cut.left cut.leftSlots
    (fun e he => (cut.mem_leftSlots e).mp he) k

/-! ### The complementary side of the push-forward, read on the core -/

/-- A contracted class on the complementary side of the push-forward is the
class of an uncontracted complementary vertex. -/
theorem classVal_mem_image_rep_right {k' : Fin d.classCard}
    (hk' : k' ∈ (contractedCut d cut).right) :
    classVal d k' ∈ cut.right.image d.rep := by
  rcases ((contractedCut d cut).mem_right_iff k').mp hk' with hg | hnl
  · rw [hg, classVal_contractedCut_glue]
    exact Finset.mem_image_of_mem d.rep ((cut.mem_right_iff _).mpr (Or.inl rfl))
  · have hnot : classVal d k' ∉ cut.left.image d.rep := fun h =>
      hnl ((mem_contractedCut_left d cut k').mpr h)
    have hnl' : classVal d k' ∉ cut.left := fun h =>
      hnot (Finset.mem_image.mpr ⟨classVal d k', h, rep_classVal d k'⟩)
    exact Finset.mem_image.mpr ⟨classVal d k',
      (cut.mem_right_iff _).mpr (Or.inr hnl'), rep_classVal d k'⟩

/-- The mirror of `contractedCut_leftSlot_iff`, obtained from it by the
side dichotomy on both cores. -/
theorem contractedCut_rightSlot_iff (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (e' : Fin d.slotCard) :
    (contractedCut d cut).RightSlot e' ↔ cut.RightSlot (slotOf d e') := by
  have hL := contractedCut_leftSlot_iff d cut hValid hRep e'
  have hor1 := (contractedCut d cut).leftSlot_or_rightSlot
    (contractedCut_valid d cut hValid hRep) e'
  have hnot1 := (contractedCut d cut).not_leftSlot_and_rightSlot
    d.contractedSpec.core_loopless e'
  have hor2 := cut.leftSlot_or_rightSlot hValid (slotOf d e')
  have hnot2 := cut.not_leftSlot_and_rightSlot hLoopless (slotOf d e')
  tauto

theorem contractedCut_rightSlots_image (hValid : cut.Valid)
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e) :
    (contractedCut d cut).rightSlots.image (slotOf d)
      = cut.rightSlots \ rightZero d cut := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    have hR : cut.RightSlot (slotOf d e') :=
      (contractedCut_rightSlot_iff d cut hValid hRep hLoopless e').mp
        (((contractedCut d cut).mem_rightSlots e').mp he')
    refine Finset.mem_sdiff.mpr ⟨(cut.mem_rightSlots _).mpr hR, ?_⟩
    intro hz
    have hzero := (d.mem_zeroSlotSet _).mp (rightZero_subset d cut hz)
    have := slotOf_pos d e'
    omega
  · intro he
    obtain ⟨heR, heZ⟩ := Finset.mem_sdiff.mp he
    have hR := (cut.mem_rightSlots e).mp heR
    have hpos : 0 < d.length e := by
      rcases Nat.eq_zero_or_pos (d.length e) with h | h
      · exact absurd (Finset.mem_inter.mpr ⟨(d.mem_zeroSlotSet e).mpr h, heR⟩) heZ
      · exact h
    obtain ⟨e', rfl⟩ := slotOf_surj d hpos
    exact Finset.mem_image.mpr ⟨e', ((contractedCut d cut).mem_rightSlots e').mpr
      ((contractedCut_rightSlot_iff d cut hValid hRep hLoopless e').mpr hR), rfl⟩

/-- The contracted incident degree, transported back to the uncontracted
core: it counts the surviving complementary slots incident to the class. -/
theorem contractedCut_rightIncidentDegree (hValid : cut.Valid)
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (k' : Fin d.classCard) :
    (contractedCut d cut).rightIncidentDegree k'
      = ∑ e ∈ cut.rightSlots \ rightZero d cut,
          ((if d.rep (d.core.tail e) = classVal d k' then 1 else 0)
            + (if d.rep (d.core.head e) = classVal d k' then 1 else 0)) := by
  classical
  have hdef : (contractedCut d cut).rightIncidentDegree k'
      = ∑ e' ∈ (contractedCut d cut).rightSlots,
          ((if d.contractedCore.tail e' = k' then 1 else 0)
            + (if d.contractedCore.head e' = k' then 1 else 0)) := rfl
  rw [hdef, ← contractedCut_rightSlots_image d cut hValid hRep hLoopless,
    Finset.sum_image (fun x _ y _ h => slotOf_injective d h)]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have h1 : (d.contractedCore.tail e' = k')
      ↔ (d.rep (d.core.tail (slotOf d e')) = classVal d k') := by
    constructor
    · intro h; rw [← classVal_tail d e', h]
    · intro h; exact classVal_injective d ((classVal_tail d e').trans h)
  have h2 : (d.contractedCore.head e' = k')
      ↔ (d.rep (d.core.head (slotOf d e')) = classVal d k') := by
    constructor
    · intro h; rw [← classVal_head d e', h]
    · intro h; exact classVal_injective d ((classVal_head d e').trans h)
  simp only [h1, h2]

theorem contractedCut_leftIncidentDegree (hValid : cut.Valid)
    (hRep : d.RepIsContraction) (k' : Fin d.classCard) :
    (contractedCut d cut).leftIncidentDegree k'
      = ∑ e ∈ cut.leftSlots \ leftZero d cut,
          ((if d.rep (d.core.tail e) = classVal d k' then 1 else 0)
            + (if d.rep (d.core.head e) = classVal d k' then 1 else 0)) := by
  classical
  have hdef : (contractedCut d cut).leftIncidentDegree k'
      = ∑ e' ∈ (contractedCut d cut).leftSlots,
          ((if d.contractedCore.tail e' = k' then 1 else 0)
            + (if d.contractedCore.head e' = k' then 1 else 0)) := rfl
  rw [hdef, ← contractedCut_leftSlots_image d cut hValid hRep,
    Finset.sum_image (fun x _ y _ h => slotOf_injective d h)]
  refine Finset.sum_congr rfl fun e' _ => ?_
  have h1 : (d.contractedCore.tail e' = k')
      ↔ (d.rep (d.core.tail (slotOf d e')) = classVal d k') := by
    constructor
    · intro h; rw [← classVal_tail d e', h]
    · intro h; exact classVal_injective d ((classVal_tail d e').trans h)
  have h2 : (d.contractedCore.head e' = k')
      ↔ (d.rep (d.core.head (slotOf d e')) = classVal d k') := by
    constructor
    · intro h; rw [← classVal_head d e', h]
    · intro h; exact classVal_injective d ((classVal_head d e').trans h)
  simp only [h1, h2]

/-- **Two-regularity of the complementary side survives contraction.**

For a class `k'` of `right'`, the sum defining `rightIncidentDegree'`
transports back along `slotOf`/`classVal` to the surviving complementary slots
incident to the class, and regrouping by the fibre gives

    rightIncidentDegree' k'
      = ∑_{v ∈ rightFibre k} rightIncidentDegree v − 2 · #(rightFibreSlots k)
      = 2 · #(rightFibre k) − 2 · #(rightFibreSlots k)   [by `hReg`]
      = 2                                                [by `card_rightFibre_eq`].
-/
theorem contractedCut_rightTwoRegular (hValid : cut.Valid)
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (hReg : cut.RightTwoRegular) : (contractedCut d cut).RightTwoRegular := by
  classical
  intro k' hk'
  have hdeg := contractedCut_rightIncidentDegree d cut hValid hRep hLoopless k'
  have hsum := sum_rightIncidentDegree_fibre d cut (classVal d k')
  have hcard := card_rightFibre_eq d cut hValid hRep hLoopless
    (classVal_mem_image_rep_right d cut hk')
  have hreg : ∑ v ∈ rightFibre d cut (classVal d k'), cut.rightIncidentDegree v
      = (rightFibre d cut (classVal d k')).card * 2 := by
    rw [Finset.sum_congr rfl (fun v hv => hReg v ((mem_rightFibre_iff d cut).mp hv).1),
      Finset.sum_const, smul_eq_mul]
  omega

/-- **Two-regularity of the named side survives contraction.**  The mirror of
`contractedCut_rightTwoRegular`. -/
theorem contractedCut_leftTwoRegular (hValid : cut.Valid)
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (hReg : cut.LeftTwoRegular) : (contractedCut d cut).LeftTwoRegular := by
  classical
  intro k' hk'
  have hdeg := contractedCut_leftIncidentDegree d cut hValid hRep k'
  have hsum := sum_leftIncidentDegree_fibre d cut (classVal d k')
  have hcard := card_leftFibre_eq d cut hValid hRep hLoopless
    ((mem_contractedCut_left d cut k').mp hk')
  have hreg : ∑ v ∈ leftFibre d cut (classVal d k'), cut.leftIncidentDegree v
      = (leftFibre d cut (classVal d k')).card * 2 := by
    rw [Finset.sum_congr rfl (fun v hv => hReg v ((mem_leftFibre_iff d cut).mp hv).1),
      Finset.sum_const, smul_eq_mul]
  omega

/-! ## The closed-orthant conclusion -/

theorem contractedCut_alternatives (hValid : cut.Valid) (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (h : cut.GenusFourRankOneAlternatives) :
    (contractedCut d cut).GenusFourRankOneAlternatives := by
  have hL := contractedCut_leftGenus d cut hValid hRep hLoopless
  have hR := contractedCut_rightGenus d cut hValid hRep hLoopless
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨by rw [hL, h1], by rw [hR, h2]⟩
  · exact Or.inr (Or.inl ⟨by rw [hL, h1],
      contractedCut_rightTwoRegular d cut hValid hRep hLoopless h2, by rw [hR, h3]⟩)
  · exact Or.inr (Or.inr ⟨contractedCut_leftTwoRegular d cut hValid hRep hLoopless h1,
      by rw [hL, h2], by rw [hR, h3]⟩)

/-- **The closed-orthant genus-four vertex-cut theorem.**

Same hypotheses as `CoreVertexCut.Data.bnExists_one_three_of_genusFourRankOneConditions`
— a valid cut on a connected core with admissible factor genera — but the
conclusion holds on the *whole* closed length orthant: at every face where the
vanishing set is a forest whose contraction leaves no loop, not only at
strictly positive lengths. -/
theorem bnExists_one_three_of_genusFourRankOneConditions
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (hCond : cut.GenusFourRankOneConditions) :
    BNExists d.graph 1 3 := by
  have hConn' : d.contractedSpec.core.Connected :=
    d.canonicalContraction.target_core_connected hCond.2.1
  have hCond' : (contractedCut d cut).GenusFourRankOneConditions :=
    ⟨contractedCut_valid d cut hCond.1 hRep, hConn',
      contractedCut_alternatives d cut hCond.1 hRep hLoopless hCond.2.2⟩
  have h := (contractedCut d cut).bnExists_one_three_of_genusFourRankOneConditions
    d.contractedSpec hCond'
  exact (d.canonicalContraction.laplacianEquiv.bnExists_iff 1 3).mp h

/-- **The `(2,2)` branch, with no two-regularity obligation.**  Stated
separately rather than as a corollary of the theorem above, because the
three-way `rcases` in `contractedCut_alternatives` puts all three branches in
the proof term, so while the two-regularity transfer was still deferred a
`(2,2)` row routed through the general theorem inherited the `(3,1)` branch's
`sorry`.  Both routes are now `sorry`-free; this one is kept because it is
also the cheaper proof term. -/
theorem bnExists_one_three_of_two_two
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (hValid : cut.Valid) (hConn : d.core.Connected)
    (hLeft : cut.leftGenus = 2) (hRight : cut.rightGenus = 2) :
    BNExists d.graph 1 3 := by
  have hConn' : d.contractedSpec.core.Connected :=
    d.canonicalContraction.target_core_connected hConn
  have hAlt : (contractedCut d cut).GenusFourRankOneAlternatives :=
    Or.inl ⟨by rw [contractedCut_leftGenus d cut hValid hRep hLoopless, hLeft],
      by rw [contractedCut_rightGenus d cut hValid hRep hLoopless, hRight]⟩
  have h := (contractedCut d cut).bnExists_one_three_of_genusFourRankOneConditions
    d.contractedSpec ⟨contractedCut_valid d cut hValid hRep, hConn', hAlt⟩
  exact (d.canonicalContraction.laplacianEquiv.bnExists_iff 1 3).mp h

/-- Checker-facing form: the same finite `genusFourRankOneCheck` that the
open-orthant corpus already runs, now concluding on the closed orthant. -/
theorem bnExists_one_three_of_genusFourRankOneCheck
    (tree : SpanningTreeConnectivity.Certificate d.core)
    (hRep : d.RepIsContraction)
    (hLoopless : ∀ e : Fin p, d.core.tail e ≠ d.core.head e)
    (hCheck : cut.genusFourRankOneCheck tree = true) :
    BNExists d.graph 1 3 :=
  bnExists_one_three_of_genusFourRankOneConditions d cut hRep hLoopless
    (cut.genusFourRankOneConditions_of_check tree hCheck)

end DegenerateCoreVertexCut

end Utilities.Certificate
