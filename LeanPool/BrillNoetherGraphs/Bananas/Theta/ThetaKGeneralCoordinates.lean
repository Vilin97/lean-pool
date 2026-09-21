/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaCoordinateRigidity
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInvTauCorrection

/-!
# The theta-coordinate branch of Theorem 4.13

Each non-endpoint coordinate family from the all-submodularity classification
is rigid, so the general genus-two nonrecurrence criterion applies without
any residual graph-theoretic hypothesis.
-/

namespace Bananas

open Utilities

/-- Distinct interior theta strands: exact torsion plus nonrecurrence is
equivalent to general transmission. -/
theorem theta_distinctInterior_kGeneral_iff_nonRecurrent
    {k : ℕ} (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition beta j) (hab : alpha ≠ beta)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k) :
    KGeneralTransmission
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k ↔
      NonRecurrent
        (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k :=
  thetaRigid_kGeneral_iff_nonRecurrent B _ _
    (theta_allSubmodular_of_distinct_interior_strands B alpha beta i j hab hi hj)
    hTO
    (distinctInterior_strand_pair_not_linearEquiv_canonical B alpha beta i j hi hj hab)

/-- The normalized `(0,n-1)` theta boundary family is rigid and hence obeys
the same exact nonrecurrence criterion. -/
theorem theta_zeroPenultimate_kGeneral_iff_nonRecurrent
    {k : ℕ} (B : Banana 2) (alpha : Fin 3)
    (hlen : 2 ≤ B.length alpha)
    (hTO : IsTorsionOrder (mark B.graph
      (strandVertex B alpha ⟨0, by omega⟩)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k) :
    KGeneralTransmission (mark B.graph
      (strandVertex B alpha ⟨0, by omega⟩)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k ↔
      NonRecurrent (mark B.graph
        (strandVertex B alpha ⟨0, by omega⟩)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k := by
  apply thetaRigid_kGeneral_iff_nonRecurrent B _ _
    (theta_allSubmodular_zero_penultimate B alpha hlen) hTO
  have hNe : strandVertex B alpha ⟨B.length alpha - 1, by omega⟩ ≠
      rightEndpoint B :=
    strandVertex_ne_rightEndpoint B alpha _ (by
      change B.length alpha - 1 < B.length alpha
      omega)
  rw [strandVertex_zero]
  exact leftEndpoint_add_not_linearEquiv_canonical B
    (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) hNe

/-- The normalized `(1,n)` theta boundary family is rigid and hence obeys
the same exact nonrecurrence criterion. -/
theorem theta_oneLength_kGeneral_iff_nonRecurrent
    {k : ℕ} (B : Banana 2) (alpha : Fin 3)
    (hlen : 2 ≤ B.length alpha)
    (hTO : IsTorsionOrder (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B alpha ⟨B.length alpha, by omega⟩)) k) :
    KGeneralTransmission (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B alpha ⟨B.length alpha, by omega⟩)) k ↔
      NonRecurrent (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B alpha ⟨B.length alpha, by omega⟩)) k := by
  apply thetaRigid_kGeneral_iff_nonRecurrent B _ _
    (theta_allSubmodular_one_length B alpha hlen) hTO
  have hNe : strandVertex B alpha ⟨1, by omega⟩ ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B alpha _ (by
      change 0 < (1 : ℕ)
      omega)
  rw [strandVertex_length]
  exact rightEndpoint_add_not_linearEquiv_canonical B
    (strandVertex B alpha ⟨1, by omega⟩) hNe

end Bananas
