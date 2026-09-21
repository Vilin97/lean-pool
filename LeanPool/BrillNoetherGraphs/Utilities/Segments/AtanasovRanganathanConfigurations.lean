/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Segments.AtanasovRanganathan
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.MovingPosition
import LeanPool.BrillNoetherGraphs.Utilities.Segments.GenusFourLoopLemma

/-!
# Reusable Atanasov--Ranganathan configuration moves

The seven pictures in Atanasov--Ranganathan, Lemma 4.1, are local Dhar
calculations.  This file records the common proof interface independently of
those pictures: a configuration supplies an integral firing script whose
removed-chip residual is effective, hence a `StrongSeparator.Reaches` fact.

Two geometric patterns are isolated here.

* A segment configuration starts with one chip at each endpoint and uses an
  exact two-endpoint reflection to reach a named point of the segment.  The
  `min(a,b)` and `a-b` positions occurring in configurations six and seven
  are exposed through `MovingPosition`.
* The doubled-path configuration is fully discharged using the interpolated
  truncated-ramp potential already proved in `GenusFourLoopLemma`.

The paper's diagrams do not specify an ordered core-slot encoding, edge
orientations, or which dashed half-edge continues outside each solid
configuration.  Consequently this module does not assert that a numbered
picture, or Core 095, has been encoded.  It gives the reusable checked moves
to which such incidence data must eventually be connected.
-/

namespace AtanasovRanganathan.Configurations

open Utilities

open Certificate
open Certificate.StrongSeparator
open Certificate.GenusFourLoopLemma

variable {G : CFGraph}

/-! ## A uniform interface for one Dhar calculation -/

/-- One local Dhar calculation: after removing the target chip, the displayed
integral firing script leaves an effective residual. -/
structure DharMove (G : CFGraph) (D : CFDiv G) (target : G.V) where
  script : firing_script G
  residual_effective :
    effective (D - one_chip target + prin G script)

namespace DharMove

/-- A checked local Dhar move proves the corresponding reachability fact. -/
theorem reaches {D : CFDiv G} {target : G.V}
    (move : DharMove G D target) :
    Reaches G D target := by
  unfold Reaches winnable
  refine ⟨D - one_chip target + prin G move.script,
    move.residual_effective, ?_⟩
  exact linearEquiv_add_prin (D - one_chip target) move.script

/-- Conversely, an explicit effective representative and its firing script
can be packaged as a local move without mentioning linear equivalence again. -/
def ofScript {D : CFDiv G} {target : G.V} (script : firing_script G)
    (hEffective : effective (D - one_chip target + prin G script)) :
    DharMove G D target :=
  ⟨script, hEffective⟩

/-- A reachability proof already contains a firing script: unfold its effective
representative and extract the principal divisor witnessing linear
equivalence.  This converse is noncomputable only because `Reaches` is stated
existentially; the resulting `DharMove` is checked by the same residual
effectivity field as a hand-authored move. -/
noncomputable def ofReaches {D : CFDiv G} {target : G.V}
    (hReach : Reaches G D target) : DharMove G D target := by
  unfold Reaches winnable at hReach
  let E : CFDiv G := Classical.choose hReach
  have hE := Classical.choose_spec hReach
  have hEffective : effective E := hE.1
  have hEquiv : linear_equiv G (D - one_chip target) E := hE.2
  let script : firing_script G := Classical.choose
    ((principal_iff_eq_prin G (E - (D - one_chip target))).mp hEquiv)
  have hScript : E - (D - one_chip target) = prin G script :=
    Classical.choose_spec
      ((principal_iff_eq_prin G (E - (D - one_chip target))).mp hEquiv)
  refine ⟨script, ?_⟩
  have hResidual : D - one_chip target + prin G script = E := by
    rw [← hScript]
    abel
  rwa [hResidual]

/-- Rank at least one supplies a checked Dhar move at every target.  This is
the useful converse to `DharMove.reaches` when a row is proved by a global
rank argument (for example a strong-separator or transmission theorem) rather
than by retaining its local scripts as primary data. -/
noncomputable def ofRankOne {D : CFDiv G} (hRank : rank G D ≥ 1)
    (target : G.V) : DharMove G D target :=
  ofReaches ((rank_ge_one_iff_winnable_sub_one_chip G D).mp hRank target)

end DharMove

/-- Configuration version of the off-support lemma: it is enough to attach a
local Dhar move to every vertex outside the support of an effective divisor. -/
theorem rank_ge_one_of_dharMoves_off_support
    (D : CFDiv G) (hEffective : effective D)
    (hMoves : ∀ vertex : G.V, D vertex = 0 → DharMove G D vertex) :
    rank G D ≥ 1 := by
  apply rank_ge_one_of_reaches_off_support D hEffective
  intro vertex hZero
  exact (hMoves vertex hZero).reaches

/-- Degree bookkeeping for a configuration proof of any rank-one pencil. -/
theorem bnExists_one_of_dharMoves_off_support
    (D : CFDiv G) (hEffective : effective D) {degree : ℤ}
    (hDegree : deg D = degree)
    (hMoves : ∀ vertex : G.V, D vertex = 0 → DharMove G D vertex) :
    BNExists G 1 degree :=
  ⟨D, hDegree,
    rank_ge_one_of_dharMoves_off_support D hEffective hMoves⟩

/-- Degree-three specialization retained for the genus-four configurations. -/
theorem bnExists_one_three_of_dharMoves_off_support
    (D : CFDiv G) (hEffective : effective D) (hDegree : deg D = 3)
    (hMoves : ∀ vertex : G.V, D vertex = 0 → DharMove G D vertex) :
    BNExists G 1 3 :=
  bnExists_one_of_dharMoves_off_support D hEffective hDegree hMoves

/-! ## Three-chip divisors with a named moving chip -/

/-- The degree-three divisor used throughout the genus-four pictures.  The
three vertices need not be distinct. -/
def threeChipDivisor (first second third : G.V) : CFDiv G :=
  one_chip first + one_chip second + one_chip third

theorem threeChipDivisor_effective (first second third : G.V) :
    effective (threeChipDivisor first second third) := by
  exact (Eff G).add_mem
    ((Eff G).add_mem (eff_one_chip first) (eff_one_chip second))
    (eff_one_chip third)

@[simp] theorem deg_threeChipDivisor (first second third : G.V) :
    deg (threeChipDivisor first second third) = 3 := by
  simp [threeChipDivisor, deg.map_add, deg_one_chip]

theorem threeChipDivisor_has_chip_first (first second third : G.V) :
    1 ≤ threeChipDivisor first second third first := by
  simp only [threeChipDivisor, Pi.add_apply, one_chip, ↓reduceIte]
  omega

theorem threeChipDivisor_has_chip_second (first second third : G.V) :
    1 ≤ threeChipDivisor first second third second := by
  simp only [threeChipDivisor, Pi.add_apply, one_chip, ↓reduceIte]
  omega

theorem threeChipDivisor_has_chip_third (first second third : G.V) :
    1 ≤ threeChipDivisor first second third third := by
  simp only [threeChipDivisor, Pi.add_apply, one_chip, ↓reduceIte, le_add_iff_nonneg_left]
  omega

/-- Every displayed chip position is automatically reached; Dhar moves are
needed only away from these three positions. -/
theorem threeChipDivisor_reaches_of_eq
    (first second third target : G.V)
    (hTarget : target = first ∨ target = second ∨ target = third) :
    Reaches G (threeChipDivisor first second third) target := by
  have hEffective := threeChipDivisor_effective first second third
  apply reaches_of_effective_representative
    (linear_equiv.refl G (threeChipDivisor first second third)) hEffective
  rcases hTarget with hTarget | hTarget | hTarget
  · rw [hTarget]
    exact threeChipDivisor_has_chip_first first second third
  · rw [hTarget]
    exact threeChipDivisor_has_chip_second first second third
  · rw [hTarget]
    exact threeChipDivisor_has_chip_third first second third

namespace MovingDivisor

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- A three-chip divisor whose first chip is at the `min(a,b)` position used
in the sixth and seventh configurations of the paper. -/
def atMinLength (movingEdge leftLength rightLength : Fin p)
    (hBound : min (spec.length leftLength) (spec.length rightLength) ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) : CFDiv spec.graph :=
  threeChipDivisor
    (spec.pathVertex movingEdge
      (spec.minLengthPosition movingEdge leftLength rightLength hBound))
    fixedFirst fixedSecond

@[simp] theorem deg_atMinLength
    (movingEdge leftLength rightLength : Fin p)
    (hBound : min (spec.length leftLength) (spec.length rightLength) ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) :
    deg (atMinLength spec movingEdge leftLength rightLength hBound
      fixedFirst fixedSecond) = 3 := by
  exact deg_threeChipDivisor _ _ _

theorem effective_atMinLength
    (movingEdge leftLength rightLength : Fin p)
    (hBound : min (spec.length leftLength) (spec.length rightLength) ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) :
    effective (atMinLength spec movingEdge leftLength rightLength hBound
      fixedFirst fixedSecond) :=
  threeChipDivisor_effective _ _ _

theorem reaches_minLengthPosition
    (movingEdge leftLength rightLength : Fin p)
    (hBound : min (spec.length leftLength) (spec.length rightLength) ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) :
    Reaches spec.graph
      (atMinLength spec movingEdge leftLength rightLength hBound
        fixedFirst fixedSecond)
      (spec.pathVertex movingEdge
        (spec.minLengthPosition movingEdge leftLength rightLength hBound)) := by
  exact threeChipDivisor_reaches_of_eq _ _ _ _ (Or.inl rfl)

/-- A three-chip divisor whose first chip is at a truncated difference of
edge lengths, as in the three macroscopic cases of the first genus-four
family. -/
def atDifference (movingEdge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) : CFDiv spec.graph :=
  threeChipDivisor
    (spec.pathVertex movingEdge
      (spec.differencePosition movingEdge minuend subtrahend hBound))
    fixedFirst fixedSecond

@[simp] theorem deg_atDifference
    (movingEdge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) :
    deg (atDifference spec movingEdge minuend subtrahend hBound
      fixedFirst fixedSecond) = 3 := by
  exact deg_threeChipDivisor _ _ _

theorem effective_atDifference
    (movingEdge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) :
    effective (atDifference spec movingEdge minuend subtrahend hBound
      fixedFirst fixedSecond) :=
  threeChipDivisor_effective _ _ _

theorem reaches_differencePosition
    (movingEdge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤
      spec.length movingEdge)
    (fixedFirst fixedSecond : spec.Vertex) :
    Reaches spec.graph
      (atDifference spec movingEdge minuend subtrahend hBound
        fixedFirst fixedSecond)
      (spec.pathVertex movingEdge
        (spec.differencePosition movingEdge minuend subtrahend hBound)) := by
  exact threeChipDivisor_reaches_of_eq _ _ _ _ (Or.inl rfl)

end MovingDivisor

/-! ## Configuration 1: two endpoint chips on a segment -/

/-- An exact reflection starting with one chip at each of two endpoints.  The
second output chip is allowed to coincide with the requested target. -/
def TwoEndpointReflection (left right target : G.V) : Prop :=
  ∃ (reflected : G.V) (script : firing_script G),
    prin G script =
      -one_chip left - one_chip right +
        one_chip target + one_chip reflected

theorem effective_sub_two_distinct_chips
    {D : CFDiv G} {left right : G.V}
    (hEffective : effective D) (hLeft : 1 ≤ D left)
    (hRight : 1 ≤ D right) (hDistinct : left ≠ right) :
    effective (D - one_chip left - one_chip right) := by
  intro vertex
  by_cases hVL : vertex = left
  · subst vertex
    simp only [Pi.sub_apply, one_chip, ↓reduceIte, hDistinct, sub_zero, Int.sub_nonneg]
    omega
  · by_cases hVR : vertex = right
    · subst vertex
      simp only [Pi.sub_apply, one_chip, hDistinct.symm, ↓reduceIte, sub_zero, Int.sub_nonneg]
      omega
    · simpa [one_chip, hVL, hVR] using hEffective vertex

/-- The first pictured configuration, abstracted to its exact principal
identity: endpoint chips plus a segment reflection reach the requested point. -/
theorem reaches_of_endpoint_chips_of_twoEndpointReflection
    {D : CFDiv G} {left right target : G.V}
    (hEffective : effective D) (hLeft : 1 ≤ D left)
    (hRight : 1 ≤ D right) (hDistinct : left ≠ right)
    (hReflection : TwoEndpointReflection left right target) :
    Reaches G D target := by
  obtain ⟨reflected, script, hScript⟩ := hReflection
  let residual : CFDiv G :=
    D - one_chip left - one_chip right + one_chip reflected
  have hResidualEffective : effective residual := by
    exact (Eff G).add_mem
      (effective_sub_two_distinct_chips hEffective hLeft hRight hDistinct)
      (eff_one_chip reflected)
  have hRewrite :
      D - one_chip target + prin G script = residual := by
    rw [hScript]
    dsimp [residual]
    abel
  let move : DharMove G D target :=
    ⟨script, by simpa only [hRewrite] using hResidualEffective⟩
  exact move.reaches

namespace SegmentConfiguration

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- Exact geometric obligation for a subdivided segment: its two endpoint
chips reflect to a named path position and one further effective chip. -/
def ReflectsTo (edge : Fin p) (position : spec.PathPosition edge) : Prop :=
  TwoEndpointReflection (G := spec.graph)
    (spec.coreVertex (spec.core.tail edge))
    (spec.coreVertex (spec.core.head edge))
    (spec.pathVertex edge position)

/-- Once the segment potential identity is known, the endpoint-chip
configuration reaches the named subdivision position. -/
theorem reaches_pathPosition
    (D : CFDiv spec.graph) (edge : Fin p)
    (position : spec.PathPosition edge)
    (hEffective : effective D)
    (hTail : 1 ≤ D (spec.coreVertex (spec.core.tail edge)))
    (hHead : 1 ≤ D (spec.coreVertex (spec.core.head edge)))
    (hReflection : ReflectsTo spec edge position) :
    Reaches spec.graph D (spec.pathVertex edge position) := by
  apply reaches_of_endpoint_chips_of_twoEndpointReflection
    hEffective hTail hHead
  · intro hEqual
    exact spec.core_loopless edge (Sum.inl.inj hEqual)
  · exact hReflection

/-- `min(a,b)` specialization of the segment configuration. -/
theorem reaches_minLengthPosition
    (D : CFDiv spec.graph) (edge leftLength rightLength : Fin p)
    (hBound : min (spec.length leftLength) (spec.length rightLength) ≤
      spec.length edge)
    (hEffective : effective D)
    (hTail : 1 ≤ D (spec.coreVertex (spec.core.tail edge)))
    (hHead : 1 ≤ D (spec.coreVertex (spec.core.head edge)))
    (hReflection : ReflectsTo spec edge
      (spec.minLengthPosition edge leftLength rightLength hBound)) :
    Reaches spec.graph D
      (spec.pathVertex edge
        (spec.minLengthPosition edge leftLength rightLength hBound)) :=
  reaches_pathPosition spec D edge _ hEffective hTail hHead hReflection

/-- Difference-position specialization used by the first genus-four family. -/
theorem reaches_differencePosition
    (D : CFDiv spec.graph) (edge minuend subtrahend : Fin p)
    (hBound : spec.length minuend - spec.length subtrahend ≤
      spec.length edge)
    (hEffective : effective D)
    (hTail : 1 ≤ D (spec.coreVertex (spec.core.tail edge)))
    (hHead : 1 ≤ D (spec.coreVertex (spec.core.head edge)))
    (hReflection : ReflectsTo spec edge
      (spec.differencePosition edge minuend subtrahend hBound)) :
    Reaches spec.graph D
      (spec.pathVertex edge
        (spec.differencePosition edge minuend subtrahend hBound)) :=
  reaches_pathPosition spec D edge _ hEffective hTail hHead hReflection

end SegmentConfiguration

/-! ## Doubled-path configuration: a closed potential proof -/

/-- Two chips at the common base of two subdivided paths reach their bivalent
marker.  Unlike `SegmentConfiguration.ReflectsTo`, the geometric potential
identity here is already fully proved by the truncated-ramp interpolation
API. -/
theorem reaches_parallelPathMarker_of_two_chips
    {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (base marker : Fin n) (first second : Fin p)
    (hFirstSecond : first ≠ second)
    (hFirstTail : spec.core.tail first = base)
    (hFirstHead : spec.core.head first = marker)
    (hSecondTail : spec.core.tail second = base)
    (hSecondHead : spec.core.head second = marker)
    (hOnly : ∀ edge : Fin p,
      spec.core.tail edge = marker ∨ spec.core.head edge = marker →
        edge = first ∨ edge = second)
    (D : CFDiv spec.graph) (hEffective : effective D)
    (hTwo : 2 ≤ D (spec.coreVertex base)) :
    Reaches spec.graph D (spec.coreVertex marker) := by
  have hRepresentative :
      HasTwoChipsRepresentative D (spec.coreVertex base) :=
    ⟨D, hEffective, linear_equiv.refl spec.graph D, hTwo⟩
  apply reaches_of_twoChipsRepresentative_of_twoChipReflection hRepresentative
  exact twoChipReflection_of_two_paths spec base marker first second
    hFirstSecond hFirstTail hFirstHead hSecondTail hSecondHead hOnly

/-- Rank-one wrapper for a subdivision in which the doubled-path marker is
the only core reachability test not discharged elsewhere. -/
theorem bnExists_one_three_of_parallelPathMarker
    {n p : ℕ} (spec : SubdivisionGraph.Spec n p)
    (hConnected : graph_connected spec.graph)
    (base marker : Fin n) (first second : Fin p)
    (hFirstSecond : first ≠ second)
    (hFirstTail : spec.core.tail first = base)
    (hFirstHead : spec.core.head first = marker)
    (hSecondTail : spec.core.tail second = base)
    (hSecondHead : spec.core.head second = marker)
    (hOnly : ∀ edge : Fin p,
      spec.core.tail edge = marker ∨ spec.core.head edge = marker →
        edge = first ∨ edge = second)
    (D : CFDiv spec.graph) (hEffective : effective D)
    (hDegree : deg D = 3)
    (hTwo : 2 ≤ D (spec.coreVertex base))
    (hOther : ∀ vertex : Fin n, vertex ≠ marker →
      Reaches spec.graph D (spec.coreVertex vertex)) :
    BNExists spec.graph 1 3 := by
  apply bnExists_of_reaches_coreVertices spec hConnected D 3 hDegree
  intro vertex
  by_cases hVertex : vertex = marker
  · subst vertex
    exact reaches_parallelPathMarker_of_two_chips spec base marker first second
      hFirstSecond hFirstTail hFirstHead hSecondTail hSecondHead hOnly
      D hEffective hTwo
  · exact hOther vertex hVertex

end AtanasovRanganathan.Configurations
