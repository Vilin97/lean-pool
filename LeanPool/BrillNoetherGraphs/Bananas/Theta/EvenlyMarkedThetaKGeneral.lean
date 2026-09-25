/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaTorsionAPI
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaExactTorsionRelabel
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaArithmetic
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaGenusTwoCornerSum
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInvTauCorrection
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaBoundarySubmodularity
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI

/-!
# Evenly marked theta graphs

The evenly-marked theta family: all-submodularity, exact torsion order,
non-recurrence, and k-general transmission (Lemma 4.15, Theorem 4.8,
Corollary 4.17).
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- TeX labels: `thm:thetaSimple` (Theorem 1.12, part 1), `defn:evenlyMarked`
(Definition 4.14).

The submodularity component of the evenly-marked theta theorem follows
from the distinct-interior-strand classification, independently of the
torsion and inversion-count arguments. -/
theorem evenlyMarkedTheta_allSubmodular
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    AllSubmodular
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) := by
  rcases hEven with ⟨hAlphaBeta, hiPos, hiLt, hjPos, hjLt, _hRatio⟩
  exact theta_allSubmodular_of_distinct_interior_strands B alpha beta i j hAlphaBeta
    ⟨hiPos, hiLt⟩ ⟨hjPos, hjLt⟩

/-- TeX label: Lemma 4.15 (unlabeled in the source), annihilation half; its
proof runs through `eq:multDiffMarkedPts`.

Lemma 4.15 asserts that `[v_{α,i} - v_{β,j}]` has *order* `n_α/gcd(n_α,i)`.
Only the annihilation `k·(u - v) ∼ 0` is proved here; minimality is the
separate torsion-order form below. -/
theorem evenlyMarkedTheta_torsion
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    TorsionWitness
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (B.length alpha / Nat.gcd (B.length alpha) i.val) := by
  have hContract : EvenlyMarkedThetaMultiplePrincipalContract := by
    intro B' α' β' i' j' hEven'
    exact evenlyMarkedTheta_multiple_principal B' α' β' i' j' hEven'
  exact torsionWitness_of_evenlyMarkedTheta_contract hContract B alpha beta i j hEven

/-- TeX label: Lemma 4.15 (unlabeled), exact torsion order for arbitrary
distinct evenly marked theta strands.  This removes the paper's harmless
``without loss of generality'' normalization by a certified slot reindexing. -/
theorem evenlyMarkedTheta_isTorsionOrder
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (B.length alpha / Nat.gcd (B.length alpha) i.val) := by
  exact evenlyMarkedTheta_isTorsionOrder_relabel B alpha beta i j hEven

/-- TeX label: Lemma 4.15 (unlabeled), the equality
`n_α/gcd(n_α,i) = n_β/gcd(n_β,j)`; restated in `cor:evenlyMarkedKGT`
(Corollary 4.17).  This is pure arithmetic, separated from the
graph-theoretic firing and minimality arguments. -/
theorem evenlyMarkedTheta_periods_agree
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    B.length alpha / Nat.gcd (B.length alpha) i.val =
      B.length beta / Nat.gcd (B.length beta) j.val := by
  exact evenlyMarkedTheta_gcd_quotients_eq B alpha beta i j hEven

/-- TeX label: `thm:kgtThetas` (Theorem 4.8), both directions.

A rigidly marked theta graph of exact torsion order `k` has `k`-general
transmission if and only if `[u - v]` is non-recurrent.

Hypothesis note: the paper's "rigidly marked" (Definition 4.4) is
all-divisor submodularity together with `r(u+v) = 0`, and in genus two the
latter is equivalent to `u + v ≁ K_G`, which is the form `hRigid` takes.
The paper states Theorem 4.8 for an arbitrary genus-two graph; this is the
theta case, which is the one its own application (`thm:g2general`, case 3)
uses. -/
theorem thetaRigid_kGeneral_iff_nonRecurrent_class
    {k : ℕ} (B : Banana 2) (u v : B.graph.V)
    (hSub : AllSubmodular (mark B.graph u v))
    (hTO : IsTorsionOrder (mark B.graph u v) k)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph)) :
    KGeneralTransmission (mark B.graph u v) k ↔
      NonRecurrent (mark B.graph u v) k :=
  thetaRigid_kGeneral_iff_nonRecurrent B u v hSub hTO hRigid

/-- TeX label: `thm:kgtThetas` (Theorem 4.8), the "if" direction.

For a rigidly marked genus-two graph with torsion order `k`, non-recurrence of
`[u - v]` gives `k`-general transmission.  This is the direction that the
genus-two corner-sum machinery supplies, and it holds for an *arbitrary*
marking of a theta graph, not only an evenly marked one — the evenly marked
case (`evenlyMarkedTheta_kGeneral` below) is now a corollary.

Two notes on hypotheses.  The paper's "rigidly marked" (Definition 4.4) is
all-divisor submodularity together with `r(u+v) = 0`; the form used here takes
submodularity as `hSub` and the consequence `u + v ≁ K_G` as `hRigid` (in
genus two `r(K_G) = 1`, so `r(u+v) = 0` does imply it).  The converse
direction is `nonRecurrent_of_kGeneralTransmission`; the two are packaged as
`thetaRigid_kGeneral_iff_nonRecurrent_class` above. -/
theorem thetaRigid_kGeneral_of_nonRecurrent
    {k : ℕ} (B : Banana 2) (u v : B.graph.V)
    (hSub : AllSubmodular (mark B.graph u v))
    (hTO : IsTorsionOrder (mark B.graph u v) k)
    (hNonrec : NonRecurrent (mark B.graph u v) k)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph)) :
    KGeneralTransmission (mark B.graph u v) k := by
  refine ⟨hTO.1, hSub, ?_⟩
  intro D
  obtain ⟨τ, hτ, hAffine, hFinite⟩ :=
    exists_affine_transmission_of_allSubmodular
      (graphConnected B) hTO.1 hSub D
  refine ⟨τ, hτ, hAffine, hFinite, ?_⟩
  have hCount := kInversionCount_le_two_of_nonRecurrent_of_rigid
    B u v D k τ hTO hτ hAffine hNonrec hRigid
  simpa [mark, B.genus_graph] using hCount

/-- TeX label: Lemma 4.15 (unlabeled in the source), non-recurrence half.

The other two halves of Lemma 4.15 are `evenlyMarkedTheta_torsion` and
`evenlyMarkedTheta_periods_agree` above; this is the geometric statement that
the marked difference class is non-recurrent, proved in
`ThetaNonrecurrence.lean` via disjointness of the canonical-complement rank
supports. -/
theorem evenlyMarkedTheta_nonRecurrent_class
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β) (hEven : EvenlyMarkedTheta B α β i j) :
    NonRecurrent (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) :=
  evenlyMarkedTheta_nonRecurrent B α β i j hEven

/-- TeX labels: `cor:evenlyMarkedKGT` (Corollary 4.17), `thm:thetaSimple`
(Theorem 1.12, part 2).

Every evenly marked pair on a theta graph has general transmission at its
exact gcd period.  The proof combines the exact-order firing calculation,
the all-submodularity classification, and the finite genus-two inversion
formula of Lemma 4.10. -/
theorem evenlyMarkedTheta_kGeneral
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) :=
  thetaRigid_kGeneral_of_nonRecurrent B _ _
    (evenlyMarkedTheta_allSubmodular B α β i j hEven)
    (evenlyMarkedTheta_isTorsionOrder B α β i j hEven)
    (evenlyMarkedTheta_nonRecurrent B α β i j hEven)
    (evenlyMarkedTheta_mark_pair_not_linearEquiv_canonical B α β i j hEven)

end Bananas
