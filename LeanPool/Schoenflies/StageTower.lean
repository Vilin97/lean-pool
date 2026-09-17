/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.StageTransition
import LeanPool.Schoenflies.LimitMap
import LeanPool.Schoenflies.BoundaryContinuity2

/-!
# From a sequence of transferred stages to a `LimitTower`

Two interfaces in this library were designed from opposite ends and have never met.

* `Schoenflies.GeneratedPair` (`FiniteTransfer.lean`) is what `thm:finite-transfer` consumes and
  produces: one abstract cell structure, its two realizations, the skeleton homeomorphism, the
  two cell decompositions, and weak admissibility on both sides.
* `Schoenflies.CellStructure.LimitTower` (`LimitMap.lean`) is what the limit section consumes:
  the same data indexed by `ℕ`, plus the nesting and the two halves of `prop:shrinking-stars`.

This module joins them. `Schoenflies.StageSequence` is a sequence of `GeneratedPair`s carrying
exactly the extra data the recursion of `quantitative-refinement` produces at each step — the
shared parent map, the growth of the source skeleton, the nesting of the skeleton maps, and the
two shrinking estimates — and `StageSequence.limitTower` turns one into a `LimitTower` for the
concrete source and target of the problem.

Every field is either read off a
`GeneratedPair` or is one of the four recorded facts about the concrete domains. The point of
writing it before the recursion exists is that it pins the interface down: the recursion now has
a single named target, and any mismatch between what `thm:finite-transfer` delivers and what the
limit section demands shows up here rather than at the end. Two such mismatches would otherwise
have been easy to miss, and both check out:

* `LimitTower` wants the *same* parent map on both sides (`srcRefines` and `tgtRefines` along one
  `par n`). `IsPartialTransferOf` delivers exactly that — its `refines_src` and `refines_tgt`
  share `par` — which is `lem:refinement-compatibility`(c).
* `LimitTower` wants the two cell decompositions against *closed* domains `C ∪ D` and `Q`, and
  `GeneratedPair` is parametrized by exactly those two sets.

## The four facts about the concrete domains

`LimitTower` asks for the source domain to be closed and bounded and its interior open, and the
same for the target. On the source side `IsSeparating C` gives all three:
`Schoenflies.isClosed_union_inside`, `Schoenflies.union_inside_sdiff` with
`IsSeparating.isOpen_inside`, and boundedness through `C = frontier (inside C) ⊆ closure (inside C)`
— which is why `isBounded_dom` needs no extra hypothesis, though `LimitMap.lean` warns that it is
not optional (`Metric.diam` is `0` on an unbounded set). On the target side they are the standard
facts about the square.

## Blueprint

* `Schoenflies.StageSequence` — the output of the recursion of the section *Quantitative
  refinement*: the stage-`n` matched cellulations `(Γ_n, Γ'_n)` with their parent maps and the
  two convergence statements of `prop:shrinking-stars`.
* `Schoenflies.StageSequence.limitTower` — the passage to the head of the section *The limit
  homeomorphism of the interiors*, i.e. to `tex 2568`'s "we now forget how the decompositions
  were constructed".
* `Schoenflies.StageSequence.isHomeoOn_F`, `.interior_homeomorphism` —
  **`prop:interior-homeomorphism`** for a stage sequence, which is the third conjunct of
  `Schoenflies.HasLimitHomeomorphism`.
-/

open Bornology Filter Metric Set Topology
open scoped Graph

namespace Schoenflies

variable {γ : Type*} [Nonempty γ] {S₀ : CellStructure γ} {C : Set Plane}

/-! ### The concrete domains

`LimitTower` is stated for arbitrary closed domains; the construction uses two. These are the
facts it asks about them, collected so that `limitTower` below reads as a repackaging. -/

/-- The closed Jordan domain is bounded. `IsSeparating` does not say so directly — it says the
*inside* is bounded — but `C` is the frontier of the inside, hence inside its closure. -/
theorem isBounded_union_inside (hC : IsSeparating C) : IsBounded (C ∪ inside C) := by
  rw [Set.union_comm, ← (IsRegionOf.inside C).closure_eq hC]
  exact hC.isBounded_inside.closure

/-- The interior of the closed Jordan domain is open — after the rewriting `LimitTower` needs,
which asks for `IsOpen (dom \ bdry)` rather than `IsOpen (inside C)`. -/
theorem isOpen_union_inside_sdiff (hC : IsSeparating C) : IsOpen ((C ∪ inside C) \ C) := by
  rw [union_inside_sdiff]; exact hC.isOpen_inside

/-- The interior of the closed square is open, in the same shape. -/
theorem isOpen_closedSquare_sdiff_modelCurve :
    IsOpen (Plane.closedSquare 0 1 \ modelCurve) := by
  rw [closedSquare_sdiff_modelCurve]; exact Plane.isOpen_openSquare 0 1

/-! ### A sequence of transferred stages -/

/-- **The output of the recursion of *Quantitative refinement*.**

A sequence of generated matched cellulations of the closed Jordan domain and the closed square,
each refining its predecessor along one parent map shared by the two sides, with growing source
skeletons, nested skeleton maps, and the two convergence statements of `prop:shrinking-stars`.

Every field beyond `stage` and `base` is something the recursion establishes at the step that
produces it; none is a property of a single stage, which is why they cannot live in
`GeneratedPair`. -/
structure StageSequence (γ : Type*) [Nonempty γ] (S₀ : CellStructure γ) (C : Set Plane) where
  /-- The stage-`n` matched cellulation `(Γ_n, Γ'_n)`, with both realizations. -/
  stage : ℕ → GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)
  /-- The parent map from stage `n + 1` to stage `n`, shared by the two sides. -/
  par : ℕ → γ → γ
  /-- Both compatible refinements, source-skeleton growth, and nesting of the skeleton maps. -/
  transition : ∀ n, StageTransition (stage (n + 1)) (stage n) (par n)
  /-- The uniform target mesh, `2 ε_n` of the blueprint. -/
  eps : ℕ → ℝ
  /-- **`prop:shrinking-stars`, the uniform half.** -/
  diam_tgtStar_le : ∀ n, ∀ ⦃σ⦄, σ ∈ (stage n).str.cells → diam ((stage n).tgt.star σ) ≤ eps n
  /-- …and the mesh tends to zero. -/
  tendsto_eps : Tendsto eps atTop (nhds 0)
  /-- **`prop:shrinking-stars`, the pointwise half.** -/
  tendsto_diam_srcStar : ∀ ⦃x⦄, x ∈ inside C →
    Tendsto (fun n => diam ((stage n).src.star ((stage n).src.carrier x))) atTop (nhds 0)
  /-- The combinatorial invariants hold at the base of `def:generated-structure`; every stage
  inherits them by `GeneratedPair.combInvariants`. -/
  base : S₀.CombInvariants
  /-- `C` separates the plane — `thm:jordan`, which the caller has. -/
  isSeparating : IsSeparating C

namespace StageSequence

variable (T : StageSequence γ S₀ C)

/-- Consecutive source realizations refine along the recorded parent map. -/
theorem refines_src (n : ℕ) :
    (T.stage (n + 1)).src.Refines (T.stage n).src (T.par n) :=
  (T.transition n).refines_src

/-- The target realizations refine along the same parent map. -/
theorem refines_tgt (n : ℕ) :
    (T.stage (n + 1)).tgt.Refines (T.stage n).tgt (T.par n) :=
  (T.transition n).refines_tgt

/-- The realized source skeletons grow from one stage to the next. -/
theorem skeletonSet_mono (n : ℕ) :
    (T.stage n).src.skeletonSet ⊆ (T.stage (n + 1)).src.skeletonSet :=
  (T.transition n).sourceSkeletonSet_subset

/-- Consecutive skeleton homeomorphisms agree on the preceding source skeleton. -/
theorem skelHomeo_succ (n : ℕ) :
    Set.EqOn (T.stage (n + 1)).homeo.toFun (T.stage n).homeo.toFun
      (T.stage n).src.skeletonSet :=
  (T.transition n).homeo_eqOn

/-- **The tower the limit section consumes.** Every field is read off the stages or is one of
the four facts about the two concrete domains; there is no mathematics here beyond the two
recorded above. -/
def limitTower : CellStructure.LimitTower γ where
  str n := (T.stage n).str
  src n := (T.stage n).src
  tgt n := (T.stage n).tgt
  skelHomeo n := (T.stage n).homeo
  par := T.par
  dom := C ∪ inside C
  bdry := C
  dom' := Plane.closedSquare 0 1
  bdry' := modelCurve
  eps := T.eps
  srcDecomp n := (T.stage n).src_isCellDecomposition
  tgtDecomp n := (T.stage n).tgt_isCellDecomposition
  comb n := (T.stage n).combInvariants T.base
  srcRefines := T.refines_src
  tgtRefines := T.refines_tgt
  srcOuterSet n := (T.stage n).src_isWeaklyAdmissible.outerSet_eq
  tgtOuterSet n := (T.stage n).tgt_isWeaklyAdmissible.outerSet_eq
  isClosed_dom := isClosed_union_inside T.isSeparating
  isClosed_dom' := Plane.isClosed_closedSquare 0 1
  isBounded_dom := isBounded_union_inside T.isSeparating
  isBounded_dom' := Plane.isBounded_closedSquare 0 1
  isOpen_int := isOpen_union_inside_sdiff T.isSeparating
  isOpen_int' := isOpen_closedSquare_sdiff_modelCurve
  skeletonSet_mono := T.skeletonSet_mono
  skelHomeo_succ := T.skelHomeo_succ
  diam_tgtStar_le := T.diam_tgtStar_le
  tendsto_eps := T.tendsto_eps
  tendsto_diam_srcStar := by
    intro x hx
    exact T.tendsto_diam_srcStar (by rwa [union_inside_sdiff] at hx)

@[simp] theorem limitTower_region : T.limitTower.region = inside C := union_inside_sdiff C

@[simp] theorem limitTower_region' : T.limitTower.region' = Plane.openSquare 0 1 :=
  closedSquare_sdiff_modelCurve

/-- **`prop:interior-homeomorphism` for a stage sequence**, in the `Schoenflies.IsHomeoOn` shape
`Schoenflies.HasLimitHomeomorphism` asks for: the limit map is a homeomorphism of the open
Jordan domain onto the open square. -/
theorem isHomeoOn_F :
    IsHomeoOn T.limitTower.F T.limitTower.inv (inside C) (Plane.openSquare 0 1) := by
  have h := T.limitTower.isHomeoOn_F
  rwa [limitTower_region, limitTower_region'] at h

/-- **`prop:skeleton-agreement`** for a stage sequence: on the closed domain the limit map agrees
with every stage's skeleton homeomorphism wherever that stage's skeleton reaches.

This is the bridge that will discharge `Schoenflies.HasAnchorCrosscuts`: the crosscut a stage
produces between two anchors lies in that stage's skeleton, so `F` carries it to the target
crosscut by the *finite* map, and `Schoenflies.image_sdiff_eq_of_eqOn` finishes. -/
theorem F_eq_skelHomeo {n : ℕ} {x : Plane} (hx : x ∈ (T.stage n).src.skeletonSet)
    (hxD : x ∈ C ∪ inside C) : T.limitTower.F x = (T.stage n).homeo.toFun x :=
  CellStructure.LimitTower.F_eq_skelHomeo hx hxD

end StageSequence

end Schoenflies
