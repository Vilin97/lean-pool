/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaGeometry
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaPrefix

/-!
# Verified local input for theta torsion

The segment-reflection script gives the one-strand canonical-divisor identity
used in the paper's evenly-marked theta argument.  The stronger identity for
multiples of two marks is recorded below as an explicit remaining interface;
it is not assumed here.
-/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec
open Utilities.SegmentReflection

/-! The raw prefix calculation behind the paper's `eq:multDiffMarkedPts`
is available from `ThetaPrefix`.  Its forward-oriented normalized adapter is
verified there; reversed slots still require the corresponding reflected
endpoint calculation. -/

/-- Paper source: reflection ingredient behind `eq:multDiffMarkedPts`.

A path position and its reflection add to the banana canonical divisor. -/
theorem path_reflection_linear_equiv
    (B : Banana 2) (α : Fin 3)
    (p : B.PathPosition α) :
    linear_equiv B.graph (canonical_divisor B.graph)
      (one_chip (strandVertex B α p) +
        one_chip (strandVertex B α (strandMirror B α p))) := by
  rw [canonical_divisor_eq_endpoints B]
  norm_num
  exact endpoint_sum_linearEquiv_strand_reflection B α p

/-! Normalized strand coordinates must be translated before applying any
raw-path firing identity.  In the reversed orientation, normalized position
`i` is stored at raw position `length - i`.  The adapter for this
(`normalizedPathPosition`, `strandVertex_eq_pathVertex_normalized`,
`normalizedPathPosition_isInterior`) lives in `BananaBasics.lean`; nothing
below this point ended up needing it directly. -/

/-- Paper source: `eq:multDiffMarkedPts` and `cor:evenlyMarkedKGT`; this is an
explicit contract for the currently missing graph-specific firing identity.

The exact graph lemma needed to finish the evenly-marked torsion proof.

For `B : Banana 2`, distinct strands `α ≠ β`, and interior positions `i,j`
with common rational ratio, put
`k = B.length α / gcd (B.length α) i.val`.  The paper's equation
`K - n(u-v) ~ reflected(ni) + (nj)` implies the following endpoint case at
`n = k`, hence the desired torsion witness.

This was originally a specification of a then-missing multi-strand
firing-script lemma.  It is now *discharged* by
`ThetaResidue.evenlyMarkedTheta_multiple_principal`, and
`Statements.evenlyMarkedTheta_torsion` is unconditional.  The named `Prop` is
kept only as the interface through which that discharge is routed.
-/
def EvenlyMarkedThetaMultiplePrincipalContract : Prop :=
  ∀ (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β),
    EvenlyMarkedTheta B α β i j →
    let k := B.length α / Nat.gcd (B.length α) i.val;
      linear_equiv B.graph
      ((k : ℤ) •
        (one_chip (strandVertex B α i) -
          one_chip (strandVertex B β j))) 0

/-- The missing multi-strand firing identity immediately yields the positive
torsion witness used by the transmission API.  This adapter deliberately does
not claim minimality of the period. -/
/- TeX label: `cor:evenlyMarkedKGT` (torsion witness adapter). -/
theorem torsionWitness_of_evenlyMarkedTheta_contract
    (hContract : EvenlyMarkedThetaMultiplePrincipalContract)
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    TorsionWitness
      (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) := by
  rcases hEven with ⟨hαβ, hiPos, hiLt, hjPos, hjLt, hRatio⟩
  let k := B.length α / Nat.gcd (B.length α) i.val
  have hk : 0 < k := by
    have hgcd : 0 < Nat.gcd (B.length α) i.val :=
      Nat.gcd_pos_of_pos_left _ (B.length_pos α)
    exact Nat.div_pos
      (Nat.gcd_le_left _ (B.length_pos α)) hgcd
  refine ⟨hk, ?_⟩
  change linear_equiv B.graph
    ((k : ℤ) •
      (one_chip (strandVertex B α i) -
        one_chip (strandVertex B β j))) 0
  exact hContract B α β i j
    ⟨hαβ, hiPos, hiLt, hjPos, hjLt, hRatio⟩

end Bananas
