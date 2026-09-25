/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095CasesTwoThree

/-!
# Endpoint replay for the short Core-095 chamber

`GenusFourCore095CasesTwoThree` defines the two compatible signed-window
profiles in the chamber `0 < C-B < min(X,Delta)`.  This file performs their
sparse endpoint replay and closes the three remaining core reachability
tests.
-/

@[expose] public section

namespace LowGenus.GenusFourRow095.CaseThree
open Utilities.Certificate

open Utilities

open Finset
open SubdivisionGraph
open WindowProfile
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.Configurations

variable (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)
variable (hNorm : length 0 ≤ length 5) (hBC : B length < C length)
variable (hYpos : 0 < Y length)
variable (hYsmall : Y length < min (X length) (Delta length))

/-- Sparse endpoint expansion of the Case-3 profile reaching `d=1`. -/
theorem dProfile_endpointDivisors :
    (dProfile length hLength hBC hYsmall).endpointDivisors =
      (oneChip ((Spec length hLength).pathVertex 4
          ((dProfile length hLength hBC hYsmall).startPosition 4)) -
        oneChip ((Spec length hLength).pathVertex 4
          ((dProfile length hLength hBC hYsmall).stopPosition 4))) +
      (oneChip ((Spec length hLength).pathVertex 5
          ((dProfile length hLength hBC hYsmall).startPosition 5)) -
        oneChip ((Spec length hLength).pathVertex 5
          ((dProfile length hLength hBC hYsmall).stopPosition 5))) +
      (oneChip ((Spec length hLength).pathVertex 8
          ((dProfile length hLength hBC hYsmall).startPosition 8)) -
        oneChip ((Spec length hLength).pathVertex 8
          ((dProfile length hLength hBC hYsmall).stopPosition 8))) := by
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, dProfile]
  abel

private theorem d_start_four_eq_one :
    (Spec length hLength).pathVertex 4
        ((dProfile length hLength hBC hYsmall).startPosition 4) =
      (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 4
        ⟨0, by change 0 < length 4 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 4) := by
          exact (Spec length hLength).pathVertex_zero 4
    _ = _ := rfl

private theorem d_stop_four_eq_s :
    (Spec length hLength).pathVertex 4
        ((dProfile length hLength hBC hYsmall).stopPosition 4) =
      s length hLength hYsmall := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem d_stop_five_eq_q :
    (Spec length hLength).pathVertex 5
        ((dProfile length hLength hBC hYsmall).stopPosition 5) =
      q length hLength hNorm := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem d_stop_eight_eq_four :
    (Spec length hLength).pathVertex 8
        ((dProfile length hLength hBC hYsmall).stopPosition 8) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 8
        ⟨length 8, by change length 8 < length 8 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.head 8) := by
          exact (Spec length hLength).pathVertex_length 8
    _ = _ := rfl

include hBC in
/-- In the short chamber, the first profile reaches `d=1`; after endpoint
cancellation the residual is exactly two positive chips. -/
theorem reaches_one :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm)
        (s length hLength hYsmall))
      ((Spec length hLength).coreVertex 1) := by
  apply (dProfile length hLength hBC hYsmall).reaches_of_effective_endpointDivisors
  rw [dProfile_endpointDivisors length hLength hBC hYsmall,
    d_start_four_eq_one length hLength hBC hYsmall,
    d_stop_four_eq_s length hLength hBC hYsmall,
    d_stop_five_eq_q length hLength hNorm hBC hYsmall,
    d_stop_eight_eq_four length hLength hBC hYsmall]
  convert (Eff (Spec length hLength).graph).add_mem
    (eff_one_chip ((Spec length hLength).pathVertex 5
      ((dProfile length hLength hBC hYsmall).startPosition 5)))
    (eff_one_chip ((Spec length hLength).pathVertex 8
      ((dProfile length hLength hBC hYsmall).startPosition 8))) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

/-- Raw sparse endpoint expansion of the shared Case-3 `e/f` profile. -/
private theorem efProfile_sparse :
    (efProfile length hLength hBC hYsmall).endpointDivisors =
      -(oneChip ((Spec length hLength).pathVertex 3
          ((efProfile length hLength hBC hYsmall).startPosition 3)) -
        oneChip ((Spec length hLength).pathVertex 3
          ((efProfile length hLength hBC hYsmall).stopPosition 3))) +
      (oneChip ((Spec length hLength).pathVertex 4
          ((efProfile length hLength hBC hYsmall).startPosition 4)) -
        oneChip ((Spec length hLength).pathVertex 4
          ((efProfile length hLength hBC hYsmall).stopPosition 4))) +
      (oneChip ((Spec length hLength).pathVertex 5
          ((efProfile length hLength hBC hYsmall).startPosition 5)) -
        oneChip ((Spec length hLength).pathVertex 5
          ((efProfile length hLength hBC hYsmall).stopPosition 5))) +
      (oneChip ((Spec length hLength).pathVertex 8
          ((efProfile length hLength hBC hYsmall).startPosition 8)) -
        oneChip ((Spec length hLength).pathVertex 8
          ((efProfile length hLength hBC hYsmall).stopPosition 8))) := by
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, efProfile]
  abel

private theorem ef_start_three_eq_one :
    (Spec length hLength).pathVertex 3
        ((efProfile length hLength hBC hYsmall).startPosition 3) =
      (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 3
        ⟨0, by change 0 < length 3 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 3) := by
          exact (Spec length hLength).pathVertex_zero 3
    _ = _ := rfl

private theorem ef_stop_three_eq_three :
    (Spec length hLength).pathVertex 3
        ((efProfile length hLength hBC hYsmall).stopPosition 3) =
      (Spec length hLength).coreVertex 3 := by
  calc
    _ = (Spec length hLength).pathVertex 3
        ⟨length 3, by change length 3 < length 3 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.head 3) := by
          exact (Spec length hLength).pathVertex_length 3
    _ = _ := rfl

private theorem ef_start_four_eq_one :
    (Spec length hLength).pathVertex 4
        ((efProfile length hLength hBC hYsmall).startPosition 4) =
      (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 4
        ⟨0, by change 0 < length 4 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 4) := by
          exact (Spec length hLength).pathVertex_zero 4
    _ = _ := rfl

private theorem ef_stop_four_eq_s :
    (Spec length hLength).pathVertex 4
        ((efProfile length hLength hBC hYsmall).stopPosition 4) =
      s length hLength hYsmall := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem ef_stop_five_eq_q :
    (Spec length hLength).pathVertex 5
        ((efProfile length hLength hBC hYsmall).stopPosition 5) =
      q length hLength hNorm := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem ef_start_eight_eq_two :
    (Spec length hLength).pathVertex 8
        ((efProfile length hLength hBC hYsmall).startPosition 8) =
      (Spec length hLength).coreVertex 2 := by
  calc
    _ = (Spec length hLength).pathVertex 8
        ⟨0, by change 0 < length 8 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 8) := by
          exact (Spec length hLength).pathVertex_zero 8
    _ = _ := rfl

private theorem ef_stop_eight_eq_four :
    (Spec length hLength).pathVertex 8
        ((efProfile length hLength hBC hYsmall).stopPosition 8) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 8
        ⟨length 8, by change length 8 < length 8 + 1; omega⟩ := by
          apply (Spec length hLength).pathVertex_eq_of_val_eq
          rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.head 8) := by
          exact (Spec length hLength).pathVertex_length 8
    _ = _ := rfl

/-- Simplified endpoint divisor of the shared Case-3 `e/f` profile. -/
theorem efProfile_endpointDivisors :
    (efProfile length hLength hBC hYsmall).endpointDivisors =
      oneChip ((Spec length hLength).coreVertex 3) -
        oneChip (s length hLength hYsmall) +
      oneChip ((Spec length hLength).pathVertex 5
        ((efProfile length hLength hBC hYsmall).startPosition 5)) -
        oneChip (q length hLength hNorm) +
      oneChip ((Spec length hLength).coreVertex 2) -
        oneChip ((Spec length hLength).coreVertex 4) := by
  rw [efProfile_sparse length hLength hBC hYsmall,
    ef_start_three_eq_one length hLength hBC hYsmall,
    ef_stop_three_eq_three length hLength hBC hYsmall,
    ef_start_four_eq_one length hLength hBC hYsmall,
    ef_stop_four_eq_s length hLength hBC hYsmall,
    ef_stop_five_eq_q length hLength hNorm hBC hYsmall,
    ef_start_eight_eq_two length hLength hBC hYsmall,
    ef_stop_eight_eq_four length hLength hBC hYsmall]
  abel

include hBC in
/-- The shared short-chamber profile reaches `e=2`. -/
theorem reaches_two :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm)
        (s length hLength hYsmall))
      ((Spec length hLength).coreVertex 2) := by
  apply (efProfile length hLength hBC hYsmall).reaches_of_effective_endpointDivisors
  rw [efProfile_endpointDivisors length hLength hNorm hBC hYsmall]
  convert (Eff (Spec length hLength).graph).add_mem
    (eff_one_chip ((Spec length hLength).coreVertex 3))
    (eff_one_chip ((Spec length hLength).pathVertex 5
      ((efProfile length hLength hBC hYsmall).startPosition 5))) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

include hBC in
/-- The same profile reaches `f=3`. -/
theorem reaches_three :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm)
        (s length hLength hYsmall))
      ((Spec length hLength).coreVertex 3) := by
  apply (efProfile length hLength hBC hYsmall).reaches_of_effective_endpointDivisors
  rw [efProfile_endpointDivisors length hLength hNorm hBC hYsmall]
  convert (Eff (Spec length hLength).graph).add_mem
    (eff_one_chip ((Spec length hLength).coreVertex 2))
    (eff_one_chip ((Spec length hLength).pathVertex 5
      ((efProfile length hLength hBC hYsmall).startPosition 5))) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

include hNorm hBC hYsmall in
/-- The short Core-095 chamber proves the genus-four degree-three pencil. -/
theorem bnExists_one_three : BNExists (Spec length hLength).graph 1 3 := by
  refine CoreVertexReachability.bnExists_of_reaches_coreVertices
    (Spec length hLength) (graphConnected length hLength)
    (threeChipDivisor ((Spec length hLength).coreVertex 4)
      (q length hLength hNorm)
      (s length hLength hYsmall)) 3 ?_ ?_
  · exact deg_threeChipDivisor _ _ _
  intro vertex
  fin_cases vertex
  · exact reaches_zero length hLength hNorm
      (s length hLength hYsmall)
  · exact reaches_one length hLength hNorm hBC hYsmall
  · exact reaches_two length hLength hNorm hBC hYsmall
  · exact reaches_three length hLength hNorm hBC hYsmall
  · exact threeChipDivisor_reaches_of_eq _ _ _ _ (Or.inl rfl)
  · exact reaches_five length hLength hNorm
      (s length hLength hYsmall)

end LowGenus.GenusFourRow095.CaseThree
