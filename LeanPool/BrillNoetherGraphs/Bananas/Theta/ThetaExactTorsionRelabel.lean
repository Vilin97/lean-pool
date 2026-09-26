/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaExactTorsion
public import LeanPool.BrillNoetherGraphs.Bananas.Basics.MarkedIso
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso

/-!
# Exact torsion order on arbitrary theta strands

This file removes the `(0,1)` normalization from the exact-torsion theorem by
reindexing the three strand occurrences.  The reindexing is orientation
preserving and fixes the two core vertices, so normalized strand coordinates
and the ordered pair of marks are preserved.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- A permutation sending two distinct indices to `0` and `1`. -/
def thetaNormalizeSlots (alpha beta : Fin 3) : Equiv.Perm (Fin 3) :=
  (Equiv.swap alpha 0).trans
    (Equiv.swap ((Equiv.swap alpha 0) beta) 1)

theorem thetaNormalizeSlots_apply_left (alpha beta : Fin 3)
    (h : alpha ≠ beta) :
    thetaNormalizeSlots alpha beta alpha = 0 := by
  fin_cases alpha <;> fin_cases beta <;>
    simp_all [thetaNormalizeSlots, Equiv.swap_apply_def]

theorem thetaNormalizeSlots_apply_right (alpha beta : Fin 3) :
    thetaNormalizeSlots alpha beta beta = 1 := by
  simp [thetaNormalizeSlots]

/-- The same banana presentation with its strand occurrences normalized so
that `alpha` and `beta` become slots `0` and `1`. -/
def thetaNormalizedBanana (B : Banana 2) (alpha beta : Fin 3) : Banana 2 :=
  specReindex B (Equiv.refl (Fin 2)) (thetaNormalizeSlots alpha beta) (by omega)

/-- The relabeling identifying a theta banana with the normalization of its two chosen strands. -/
def thetaNormalizationRelabeling (B : Banana 2) (alpha beta : Fin 3) :
    B.Relabeling (thetaNormalizedBanana B alpha beta) :=
  specReindexRelabeling B (Equiv.refl (Fin 2))
    (thetaNormalizeSlots alpha beta) (by omega)

theorem thetaNormalization_length
    (B : Banana 2) (alpha beta gamma : Fin 3) :
    (thetaNormalizedBanana B alpha beta).length
        (thetaNormalizeSlots alpha beta gamma) = B.length gamma := by
  simp [thetaNormalizedBanana, specReindex]

theorem thetaNormalization_position_val
    (B : Banana 2) (alpha beta gamma : Fin 3)
    (p : B.PathPosition gamma) :
    (positionEquiv B (thetaNormalizedBanana B alpha beta)
      (thetaNormalizationRelabeling B alpha beta) gamma p).val = p.val := by
  rw [positionEquiv_val]
  simp [thetaNormalizationRelabeling, specReindexRelabeling]

theorem thetaNormalization_strandVertex
    (B : Banana 2) (alpha beta gamma : Fin 3)
    (p : B.PathPosition gamma) :
    vertexEquiv B (thetaNormalizedBanana B alpha beta)
        (thetaNormalizationRelabeling B alpha beta) (strandVertex B gamma p) =
      strandVertex (thetaNormalizedBanana B alpha beta)
        (thetaNormalizeSlots alpha beta gamma)
        (positionEquiv B (thetaNormalizedBanana B alpha beta)
          (thetaNormalizationRelabeling B alpha beta) gamma p) := by
  unfold strandVertex
  rw [← pathVertex_positionEquiv]
  apply (thetaNormalizedBanana B alpha beta).pathVertex_eq_of_val_eq _
  have hTail :
      (thetaNormalizedBanana B alpha beta).core.tail
          (thetaNormalizeSlots alpha beta gamma) = B.core.tail gamma := by
    simp [thetaNormalizedBanana, specReindex, coreReindex]
  rw [hTail]
  by_cases h : B.core.tail gamma = 0
  · simp [h, thetaNormalization_position_val]
  · simp [h, thetaNormalization_position_val, thetaNormalization_length]

/-- Transporting a path position along equality of strand slots does not
change its numerical coordinate. -/
theorem pathPosition_slot_cast_val
    (B : Banana 2) {alpha beta : Fin 3} (h : alpha = beta)
    (p : B.PathPosition alpha) :
    (h ▸ p).val = p.val := by
  subst beta
  rfl

/-- `strandVertex` respects dependent transport along equality of strand
slots. -/
theorem strandVertex_slot_cast
    (B : Banana 2) {alpha beta : Fin 3} (h : alpha = beta)
    (p : B.PathPosition alpha) :
    strandVertex B alpha p = strandVertex B beta (h ▸ p) := by
  subst beta
  rfl

/-- Lemma 4.15 without a normalization of the two distinct theta strands. -/
theorem evenlyMarkedTheta_isTorsionOrder_relabel
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (B.length alpha / Nat.gcd (B.length alpha) i.val) := by
  rcases hEven with
    ⟨hDistinct, hiPos, hiLt, hjPos, hjLt, hRatio⟩
  let e := thetaNormalizeSlots alpha beta
  let B' := thetaNormalizedBanana B alpha beta
  let rel := thetaNormalizationRelabeling B alpha beta
  have hRelAlpha : rel.slotEquiv alpha = 0 := by
    dsimp [rel, thetaNormalizationRelabeling, specReindexRelabeling]
    exact thetaNormalizeSlots_apply_left alpha beta hDistinct
  have hRelBeta : rel.slotEquiv beta = 1 := by
    dsimp [rel, thetaNormalizationRelabeling, specReindexRelabeling]
    exact thetaNormalizeSlots_apply_right alpha beta
  let iMapped : B'.PathPosition (rel.slotEquiv alpha) :=
    positionEquiv B B' rel alpha i
  let jMapped : B'.PathPosition (rel.slotEquiv beta) :=
    positionEquiv B B' rel beta j
  let i' : B'.PathPosition 0 := hRelAlpha ▸ iMapped
  let j' : B'.PathPosition 1 := hRelBeta ▸ jMapped
  have hiVal : i'.val = i.val := by
    calc
      i'.val = iMapped.val := pathPosition_slot_cast_val B' hRelAlpha iMapped
      _ = i.val := by
        dsimp [iMapped, B', rel]
        exact thetaNormalization_position_val B alpha beta alpha i
  have hjVal : j'.val = j.val := by
    calc
      j'.val = jMapped.val := pathPosition_slot_cast_val B' hRelBeta jMapped
      _ = j.val := by
        dsimp [jMapped, B', rel]
        exact thetaNormalization_position_val B alpha beta beta j
  have hLength0 : B'.length 0 = B.length alpha := by
    rw [← thetaNormalizeSlots_apply_left alpha beta hDistinct]
    exact thetaNormalization_length B alpha beta alpha
  have hLength1 : B'.length 1 = B.length beta := by
    rw [← thetaNormalizeSlots_apply_right alpha beta]
    exact thetaNormalization_length B alpha beta beta
  have hEven' : EvenlyMarkedTheta B' 0 1 i' j' := by
    refine ⟨by decide, ?_⟩
    simpa [hiVal, hjVal, hLength0, hLength1] using
      ⟨hiPos, hiLt, hjPos, hjLt, hRatio⟩
  have hOrder' := evenlyMarkedTheta_isTorsionOrder_01 B' i' j' hEven'
  let phi : CFGraphIso B.graph B'.graph := graphIso B B' rel
  have hu : phi.vertexEquiv (strandVertex B alpha i) = strandVertex B' 0 i' := by
    calc
      phi.vertexEquiv (strandVertex B alpha i) =
          strandVertex B' (rel.slotEquiv alpha) iMapped := by
        dsimp [phi, iMapped, B', rel]
        exact thetaNormalization_strandVertex B alpha beta alpha i
      _ = strandVertex B' 0 i' := by
        exact strandVertex_slot_cast B' hRelAlpha iMapped
  have hv : phi.vertexEquiv (strandVertex B beta j) = strandVertex B' 1 j' := by
    calc
      phi.vertexEquiv (strandVertex B beta j) =
          strandVertex B' (rel.slotEquiv beta) jMapped := by
        dsimp [phi, jMapped, B', rel]
        exact thetaNormalization_strandVertex B alpha beta beta j
      _ = strandVertex B' 1 j' := by
        exact strandVertex_slot_cast B' hRelBeta jMapped
  have hTransport :=
    (isTorsionOrder_map_of_marks_iff
      (M := mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (N := mark B'.graph (strandVertex B' 0 i') (strandVertex B' 1 j'))
      phi hu hv
      (B.length alpha / Nat.gcd (B.length alpha) i.val)).mp
      (by simpa [hLength0, hiVal] using hOrder')
  exact hTransport

end Bananas
