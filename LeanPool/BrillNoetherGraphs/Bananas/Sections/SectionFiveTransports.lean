/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap
import LeanPool.BrillNoetherGraphs.Bananas.Basics.MarkedIso
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.RankDeltaDuality
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionDuality

/-!
# Section 5: transmission transports

The three exact transport calculations used in Section 5 of
the twice-marked banana paper.  They are kept apart from the statement ledger so
that the latter can expose the paper-facing names without becoming an
implementation dependency for later symmetry arguments.
-/

namespace Bananas

open Utilities

/-- The reflected inverse used after exchanging marks has the expected value
relation.  This is the raw-function form of the first calculation in Lemma
5.2. -/
theorem sectionFive_swap_value_iff_proof
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau) (a b : ℤ) :
    tau b = a ↔ swapTransmissionPermutation tau (-a) = -b := by
  unfold swapTransmissionPermutation rawAffineReflection
  constructor
  · intro h
    have hInv : rawInverse tau a = b := by
      rw [← h]
      exact rawInverse_apply_apply tau hTau.1 b
    simp only [neg_neg]
    change -rawInverse tau a = -b
    rw [hInv]
  · intro h
    simp only [neg_neg] at h
    change -rawInverse tau a = -b at h
    have hInv : rawInverse tau a = b := neg_injective h
    calc
      tau b = tau (rawInverse tau a) := by rw [hInv]
      _ = a := apply_rawInverse_apply tau hTau.1 a
/-- Canonical duality gives the raw inverse transmission permutation at the
exchanged marks.  Riemann--Roch supplies the only non-formal ingredient: it
identifies the marked second differences of a divisor and its normalized
canonical complement. -/
theorem sectionFive_dual_transmission_proof
    {G : CFGraph} (hconn : _root_.graph_connected G) (u v : G.V)
    {D : CFDiv G} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation (mark G v u)
      (transmissionDualDivisor u v D) (rawInverse tau) := by
  refine ⟨rawInverse_bijective hTau.1, ?_⟩
  intro a b
  have hInverse : rawInverse tau b = a ↔ tau a = b := by
    constructor
    · intro h
      calc
        tau a = tau (rawInverse tau b) := by rw [h]
        _ = b := apply_rawInverse_apply tau hTau.1 b
    · intro h
      rw [← h]
      exact rawInverse_apply_apply tau hTau.1 a
  rw [show (if rawInverse tau b = a then (1 : ℤ) else 0) =
      (if tau a = b then 1 else 0) by simp only [hInverse]]
  rw [hTau.2 b a]
  rw [rankDelta_mark_swap G u v]
  have hDual := rankDelta_canonical_dual (mark G u v) hconn
    (D + b • one_chip u - a • one_chip v)
  change rankDelta (mark G u v) (D + b • one_chip u - a • one_chip v) =
    rankDelta (mark G u v)
      (transmissionDualDivisor u v D + a • one_chip v - b • one_chip u)
  calc
    rankDelta (mark G u v) (D + b • one_chip u - a • one_chip v) =
        rankDelta (mark G u v)
          (canonical_divisor G + one_chip u + one_chip v -
            (D + b • one_chip u - a • one_chip v)) := hDual
    _ = rankDelta (mark G u v)
          (transmissionDualDivisor u v D + a • one_chip v - b • one_chip u) := by
      congr 1
      unfold transmissionDualDivisor
      abel

/-- Relabeling a graph transports a raw transmission permutation unchanged.
This is the raw counterpart of `CFGraphIso.satisfiesTransmission_mapDiv`. -/
theorem sectionFive_map_transmission_proof
    {G H : CFGraph} (phi : CFGraphIso G H) (u v : G.V)
    {D : CFDiv G} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation
      (mark H (phi.vertexEquiv u) (phi.vertexEquiv v))
      (phi.mapDiv D) tau := by
  let M : TwiceMarked := mark G u v
  let N : TwiceMarked := mark H (phi.vertexEquiv u) (phi.vertexEquiv v)
  change IsTransmissionPermutation N (phi.mapDiv D) tau
  exact (isTransmissionPermutation_mapDiv_of_marks_iff (M := M) (N := N)
    phi rfl rfl D tau).mpr hTau

end Bananas
