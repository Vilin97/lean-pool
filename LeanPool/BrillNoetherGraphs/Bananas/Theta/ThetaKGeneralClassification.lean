/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaKGeneralCoordinates
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap

/-!
# Endpoint-safe theta form of Theorem 4.13

The predicate deliberately retains the witness path positions from the
all-submodularity classification.  This avoids choosing incompatible proof
terms for endpoint aliases while stating exactly the three non-endpoint
families.
-/

namespace Bananas

open Utilities

def ThetaKGeneralCoordinates
    {k : ℕ} (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) : Prop :=
  (alpha ≠ beta ∧ B.IsInteriorPosition alpha i ∧
    B.IsInteriorPosition beta j ∧
    NonRecurrent (mark B.graph (strandVertex B alpha i)
      (strandVertex B beta j)) k) ∨
  (∃ (gamma : Fin 3) (p q : B.PathPosition gamma),
    p.val < q.val ∧ p.val = 0 ∧ q.val + 1 = B.length gamma ∧
    ((strandVertex B alpha i = strandVertex B gamma p ∧
        strandVertex B beta j = strandVertex B gamma q) ∨
      (strandVertex B alpha i = strandVertex B gamma q ∧
        strandVertex B beta j = strandVertex B gamma p)) ∧
    NonRecurrent (mark B.graph (strandVertex B alpha i)
      (strandVertex B beta j)) k) ∨
  (∃ (gamma : Fin 3) (p q : B.PathPosition gamma),
    p.val < q.val ∧ p.val = 1 ∧ q.val = B.length gamma ∧
    ((strandVertex B alpha i = strandVertex B gamma p ∧
        strandVertex B beta j = strandVertex B gamma q) ∨
      (strandVertex B alpha i = strandVertex B gamma q ∧
        strandVertex B beta j = strandVertex B gamma p)) ∧
    NonRecurrent (mark B.graph (strandVertex B alpha i)
      (strandVertex B beta j)) k)

private theorem zero_vertex_eq
    (B : Banana 2) (gamma : Fin 3) (p : B.PathPosition gamma)
    (hp : p.val = 0) :
    strandVertex B gamma p = leftEndpoint B := by
  have hp' : p = ⟨0, Nat.succ_pos _⟩ := Fin.ext hp
  rw [hp', strandVertex_zero]

private theorem penultimate_vertex_eq
    (B : Banana 2) (gamma : Fin 3) (q : B.PathPosition gamma)
    (hq : q.val + 1 = B.length gamma) :
    strandVertex B gamma q =
      strandVertex B gamma ⟨B.length gamma - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
  apply congrArg (strandVertex B gamma)
  apply Fin.ext
  change q.val = B.length gamma - 1
  omega

private theorem one_vertex_eq
    (B : Banana 2) (gamma : Fin 3) (p : B.PathPosition gamma)
    (hp : p.val = 1) :
    strandVertex B gamma p =
      strandVertex B gamma ⟨1, Nat.succ_lt_succ (B.length_pos gamma)⟩ := by
  apply congrArg (strandVertex B gamma)
  exact Fin.ext hp

private theorem length_vertex_eq
    (B : Banana 2) (gamma : Fin 3) (q : B.PathPosition gamma)
    (hq : q.val = B.length gamma) :
    strandVertex B gamma q = rightEndpoint B := by
  have hq' : q = ⟨B.length gamma, Nat.lt_succ_self _⟩ := Fin.ext hq
  rw [hq', strandVertex_length]

private theorem theta_zeroPenult_rigid
    (B : Banana 2) (gamma : Fin 3) (p q : B.PathPosition gamma)
    (_hpq : p.val < q.val) (hp : p.val = 0)
    (hq : q.val + 1 = B.length gamma)
    (u v : B.graph.V)
    (hPair : (u = strandVertex B gamma p ∧ v = strandVertex B gamma q) ∨
      (u = strandVertex B gamma q ∧ v = strandVertex B gamma p)) :
    ¬ linearEquiv B.graph (oneChip u + oneChip v)
      (canonicalDivisor B.graph) := by
  have hqLt : q.val < B.length gamma := by omega
  have hNe : strandVertex B gamma q ≠ rightEndpoint B :=
    strandVertex_ne_rightEndpoint B gamma q hqLt
  have hLeft := zero_vertex_eq B gamma p hp
  rcases hPair with hPair | hPair
  · rw [hPair.1, hPair.2, hLeft]
    exact leftEndpoint_add_not_linearEquiv_canonical B _ hNe
  · rw [hPair.1, hPair.2, hLeft]
    simpa [add_comm] using leftEndpoint_add_not_linearEquiv_canonical B _ hNe

private theorem theta_oneLength_rigid
    (B : Banana 2) (gamma : Fin 3) (p q : B.PathPosition gamma)
    (hp : p.val = 1) (hq : q.val = B.length gamma)
    (u v : B.graph.V)
    (hPair : (u = strandVertex B gamma p ∧ v = strandVertex B gamma q) ∨
      (u = strandVertex B gamma q ∧ v = strandVertex B gamma p)) :
    ¬ linearEquiv B.graph (oneChip u + oneChip v)
      (canonicalDivisor B.graph) := by
  have hpPos : 0 < p.val := by omega
  have hNe : strandVertex B gamma p ≠ leftEndpoint B :=
    strandVertex_ne_leftEndpoint B gamma p hpPos
  have hRight := length_vertex_eq B gamma q hq
  rcases hPair with hPair | hPair
  · rw [hPair.1, hPair.2, hRight]
    exact rightEndpoint_add_not_linearEquiv_canonical B _ hNe
  · rw [hPair.1, hPair.2, hRight]
    simpa [add_comm] using rightEndpoint_add_not_linearEquiv_canonical B _ hNe

theorem theta_kGeneral_iff_coordinates_nonRecurrent
    {k : ℕ} (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k) :
    KGeneralTransmission
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k ↔
      ThetaKGeneralCoordinates (k := k) B alpha beta i j := by
  constructor
  · intro hK
    have hSub := hK.2.1
    have hCoords := (theta_allSubmodular_iff_coordinates B alpha beta i j).mp hSub
    rcases hCoords with hCross | hBoundary
    · rcases hCross with ⟨hab, hi, hj⟩
      left
      exact ⟨hab, hi, hj,
        (theta_distinctInterior_kGeneral_iff_nonRecurrent B alpha beta i j
          hi hj hab hTO).mp hK⟩
    rcases hBoundary with ⟨gamma, p, q, hpq, hCase, hPair⟩
    rcases hCase with hZero | hOne
    · rcases hZero with ⟨hp, hqPenult | hqLength⟩
      · right; left
        refine ⟨gamma, p, q, hpq, hp, hqPenult, hPair, ?_⟩
        exact (thetaRigid_kGeneral_iff_nonRecurrent B _ _ hSub hTO
          (theta_zeroPenult_rigid B gamma p q hpq hp hqPenult _ _ hPair)).mp hK
      · have hLeft := zero_vertex_eq B gamma p hp
        have hRight := length_vertex_eq B gamma q hqLength
        rcases hPair with hPair | hPair
        · have hBad : KGeneralTransmission
              (mark B.graph (leftEndpoint B) (rightEndpoint B)) k := by
            rw [← hLeft, ← hRight, ← hPair.1, ← hPair.2]
            exact hK
          exact (endpoint_marking_not_kGeneral (by omega) B hBad).elim
        · have hBadSwap : KGeneralTransmission
              (mark B.graph (rightEndpoint B) (leftEndpoint B)) k := by
            rw [← hRight, ← hLeft, ← hPair.1, ← hPair.2]
            exact hK
          exact (endpoint_marking_not_kGeneral (by omega) B
            (KGeneralTransmission.swap_marks _ _ hBadSwap)).elim
    · rcases hOne with ⟨hp, hq⟩
      right; right
      refine ⟨gamma, p, q, hpq, hp, hq, hPair, ?_⟩
      exact (thetaRigid_kGeneral_iff_nonRecurrent B _ _ hSub hTO
        (theta_oneLength_rigid B gamma p q hp hq _ _ hPair)).mp hK
  · intro hCases
    rcases hCases with hCross | hCases
    · rcases hCross with ⟨hab, hi, hj, hNonrec⟩
      exact (theta_distinctInterior_kGeneral_iff_nonRecurrent B alpha beta i j
        hi hj hab hTO).mpr hNonrec
    rcases hCases with hZero | hOne
    · rcases hZero with ⟨gamma, p, q, hpq, hp, hq, hPair, hNonrec⟩
      have hSub : AllSubmodular
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) := by
        rcases hPair with hPair | hPair
        · rw [hPair.1, hPair.2]
          have hlen : 2 ≤ B.length gamma := by omega
          have hP := zero_vertex_eq B gamma p hp
          have hQ := penultimate_vertex_eq B gamma q hq
          have hPStd : strandVertex B gamma p =
              strandVertex B gamma ⟨0, Nat.succ_pos _⟩ := by
            rw [hP, strandVertex_zero]
          rw [hPStd, hQ]
          exact theta_allSubmodular_zero_penultimate B gamma hlen
        · rw [hPair.1, hPair.2]
          have hlen : 2 ≤ B.length gamma := by omega
          have hP := zero_vertex_eq B gamma p hp
          have hQ := penultimate_vertex_eq B gamma q hq
          have hPStd : strandVertex B gamma p =
              strandVertex B gamma ⟨0, Nat.succ_pos _⟩ := by
            rw [hP, strandVertex_zero]
          rw [hPStd, hQ]
          exact allSubmodular_mark_swap B.graph _ _
            (theta_allSubmodular_zero_penultimate B gamma hlen)
      exact (thetaRigid_kGeneral_iff_nonRecurrent B _ _ hSub hTO
        (theta_zeroPenult_rigid B gamma p q hpq hp hq _ _ hPair)).mpr hNonrec
    · rcases hOne with ⟨gamma, p, q, hpq, hp, hq, hPair, hNonrec⟩
      have hSub : AllSubmodular
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) := by
        rcases hPair with hPair | hPair
        · rw [hPair.1, hPair.2]
          have hP := one_vertex_eq B gamma p hp
          have hQ := length_vertex_eq B gamma q hq
          have hQStd : strandVertex B gamma q =
              strandVertex B gamma ⟨B.length gamma, Nat.lt_succ_self _⟩ := by
            rw [hQ, strandVertex_length]
          rw [hP, hQStd]
          exact theta_allSubmodular_one_length B gamma (by omega)
        · rw [hPair.1, hPair.2]
          have hP := one_vertex_eq B gamma p hp
          have hQ := length_vertex_eq B gamma q hq
          have hQStd : strandVertex B gamma q =
              strandVertex B gamma ⟨B.length gamma, Nat.lt_succ_self _⟩ := by
            rw [hQ, strandVertex_length]
          rw [hP, hQStd]
          exact allSubmodular_mark_swap B.graph _ _
            (theta_allSubmodular_one_length B gamma (by omega))
      exact (thetaRigid_kGeneral_iff_nonRecurrent B _ _ hSub hTO
        (theta_oneLength_rigid B gamma p q hp hq _ _ hPair)).mpr hNonrec

end Bananas
