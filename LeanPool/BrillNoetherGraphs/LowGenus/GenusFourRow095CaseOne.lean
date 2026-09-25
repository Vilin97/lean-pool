/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095

/-!
# Core 095, first Atanasov--Ranganathan chamber

This is the `B ≥ C` chamber of the first-family picture.  The moving chip is
on slot `3`, at distance `P = B - C` from the vertex `1`.  The two window
profiles below are exactly the two Dhar moves recorded in the reassessment
note: the first reaches vertex `1`, and the second simultaneously reaches
vertices `2` and `3`.

The proof deliberately uses only signed-window endpoint identities.  Thus
the rather complicated firing scripts on arbitrary subdivisions are never
expanded vertex-by-vertex.
-/

namespace LowGenus.GenusFourRow095.CaseOne
open Utilities.Certificate

open Utilities

open Finset
open SubdivisionGraph
open WindowProfile
open AtanasovRanganathan.Configurations

variable (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)

/-- The excess of the `d--f` slot over the `e--c` slot. -/
abbrev P : ℕ := B length - C length

/-- The common depth of the three positive windows in the first Dhar move. -/
abbrev m : ℕ := min (P length) (min (X length) (Delta length))

/-- The third chip in the chamber `B ≥ C`. -/
def p (_hBC : C length ≤ B length) : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 3
    ⟨P length, by
      change P length < length 3 + 1
      exact Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/-- The first profile's three positive-window starts. -/
def pStart : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 3
    ⟨P length - m length, by
      change P length - m length < length 3 + 1
      have hP : P length ≤ length 3 := Nat.sub_le _ _
      omega⟩

def deltaStart : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 4
    ⟨Delta length - m length, by
      change Delta length - m length < length 4 + 1
      have hD : Delta length ≤ length 4 := by rfl
      omega⟩

def xStart : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 5
    ⟨X length - m length, by
      change X length - m length < length 5 + 1
      have hX : X length ≤ length 5 := Nat.sub_le _ _
      omega⟩

/-- The signed-window profile reaching the vertex `d=1`. -/
def dProfile (_hBC : C length ≤ B length) :
    WindowProfile.Data (Spec length hLength) where
  coreValue := ![m length, 0, m length, m length, m length, m length]
  start := fun edge =>
    if edge = 3 then P length - m length else
    if edge = 4 then Delta length - m length else
    if edge = 5 then X length - m length else 0
  stop := fun edge =>
    if edge = 3 then P length else
    if edge = 4 then Delta length else
    if edge = 5 then X length else 0
  slope := fun edge => if edge = 3 ∨ edge = 4 ∨ edge = 5 then 1 else 0
  start_le_stop := by
    intro edge
    fin_cases edge <;> simp [m]
  stop_le_length := by
    intro edge
    fin_cases edge <;> simp [P, B, C, Delta, X]
  endpoint_compatible := by
    intro edge
    fin_cases edge <;> simp [core, P, m, B, C, Delta, X]

/-- The profile used for both `e=2` and `f=3`. -/
def efProfile (hBC : C length ≤ B length) :
    WindowProfile.Data (Spec length hLength) where
  coreValue := ![C length, C length, 0, 0, C length, C length]
  start := fun edge => if edge = 3 then P length else 0
  stop := fun edge => if edge = 3 then B length else if edge = 8 then C length else 0
  slope := fun edge => if edge = 3 then -1 else if edge = 8 then 1 else 0
  start_le_stop := by
    intro edge
    fin_cases edge <;> simp [P, B, C]
  stop_le_length := by
    intro edge
    fin_cases edge <;> simp [B, C]
  endpoint_compatible := by
    intro edge
    fin_cases edge
    · simp [core]
    · simp [core]
    · simp [core]
    · simp [core, P]
      omega
    · simp [core]
    · simp [core]
    · simp [core]
    · simp [core]
    · simp [core]

@[simp] theorem dProfile_slope (hBC : C length ≤ B length) (edge : Fin 9) :
    (dProfile length hLength hBC).slope edge =
      if edge = 3 ∨ edge = 4 ∨ edge = 5 then 1 else 0 := rfl

@[simp] theorem efProfile_slope (hBC : C length ≤ B length) (edge : Fin 9) :
    (efProfile length hLength hBC).slope edge =
      if edge = 3 then -1 else if edge = 8 then 1 else 0 := rfl

@[simp] theorem dProfile_start_three (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 3
        ((dProfile length hLength hBC).startPosition 3) = pStart length hLength := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem dProfile_stop_three (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 3
        ((dProfile length hLength hBC).stopPosition 3) = p length hLength hBC := by
  change (Spec length hLength).pathVertex 3 _ =
    (Spec length hLength).pathVertex 3 _
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem dProfile_start_four (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 4
        ((dProfile length hLength hBC).startPosition 4) = deltaStart length hLength := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem dProfile_stop_four (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 4
        ((dProfile length hLength hBC).stopPosition 4) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 4 ⟨length 4, by
      change length 4 < length 4 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.head 4) :=
      (Spec length hLength).pathVertex_length 4
    _ = _ := rfl

@[simp] theorem dProfile_start_five (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 5
        ((dProfile length hLength hBC).startPosition 5) = xStart length hLength := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem dProfile_stop_five (hNorm : length 0 ≤ length 5) (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 5
        ((dProfile length hLength hBC).stopPosition 5) = q length hLength hNorm := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem efProfile_start_three (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 3
        ((efProfile length hLength hBC).startPosition 3) = p length hLength hBC := by
  change (Spec length hLength).pathVertex 3 _ =
    (Spec length hLength).pathVertex 3 _
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem efProfile_stop_three (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 3
        ((efProfile length hLength hBC).stopPosition 3) =
      (Spec length hLength).coreVertex 3 := by
  calc
    _ = (Spec length hLength).pathVertex 3 ⟨length 3, by
      change length 3 < length 3 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.head 3) :=
      (Spec length hLength).pathVertex_length 3
    _ = _ := rfl

@[simp] theorem efProfile_start_eight (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 8
        ((efProfile length hLength hBC).startPosition 8) =
      (Spec length hLength).coreVertex 2 := by
  calc
    _ = (Spec length hLength).pathVertex 8 ⟨0, by
      change 0 < length 8 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.tail 8) :=
      (Spec length hLength).pathVertex_zero 8
    _ = _ := rfl

@[simp] theorem efProfile_stop_eight (hBC : C length ≤ B length) :
    (Spec length hLength).pathVertex 8
        ((efProfile length hLength hBC).stopPosition 8) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 8 ⟨length 8, by
      change length 8 < length 8 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.head 8) :=
      (Spec length hLength).pathVertex_length 8
    _ = _ := rfl

/-- Exact sparse endpoint divisor of the `d` profile. -/
theorem dProfile_endpointDivisors (hNorm : length 0 ≤ length 5) (hBC : C length ≤ B length) :
    (dProfile length hLength hBC).endpointDivisors =
      oneChip (pStart length hLength) - oneChip (p length hLength hBC) +
      oneChip (deltaStart length hLength) - oneChip ((Spec length hLength).coreVertex 4) +
      oneChip (xStart length hLength) - oneChip (q length hLength hNorm) := by
  classical
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, dProfile_start_three, dProfile_stop_three,
    dProfile_start_four, dProfile_stop_four, dProfile_start_five,
    dProfile_slope]
  abel

/-- Exact sparse endpoint divisor of the common `e/f` profile. -/
theorem efProfile_endpointDivisors (hBC : C length ≤ B length) :
    (efProfile length hLength hBC).endpointDivisors =
      - oneChip (p length hLength hBC) + oneChip ((Spec length hLength).coreVertex 3) +
      oneChip ((Spec length hLength).coreVertex 2) - oneChip ((Spec length hLength).coreVertex 4) := by
  classical
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, efProfile_start_three, efProfile_stop_three,
    efProfile_start_eight, efProfile_stop_eight, efProfile_slope]
  abel

private theorem pStart_eq_one_of_m_eq_P (h : m length = P length) :
    pStart length hLength = (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 3 ⟨0, by
      change 0 < length 3 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      simp [h]
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.tail 3) :=
      (Spec length hLength).pathVertex_zero 3
    _ = _ := rfl

private theorem deltaStart_eq_one_of_m_eq_Delta (h : m length = Delta length) :
    deltaStart length hLength = (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 4 ⟨0, by
      change 0 < length 4 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      simp [h]
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.tail 4) :=
      (Spec length hLength).pathVertex_zero 4
    _ = _ := rfl

private theorem xStart_eq_one_of_m_eq_X (h : m length = X length) :
    xStart length hLength = (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 5 ⟨0, by
      change 0 < length 5 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      simp [h]
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.tail 5) :=
      (Spec length hLength).pathVertex_zero 5
    _ = _ := rfl

private theorem some_start_eq_one :
    pStart length hLength = (Spec length hLength).coreVertex 1 ∨
      deltaStart length hLength = (Spec length hLength).coreVertex 1 ∨
      xStart length hLength = (Spec length hLength).coreVertex 1 := by
  by_cases hP : P length ≤ min (X length) (Delta length)
  · left
    apply pStart_eq_one_of_m_eq_P
    simp [Nat.min_eq_left hP]
  · by_cases hX : X length ≤ Delta length
    · right; right
      apply xStart_eq_one_of_m_eq_X
      have hXP : X length ≤ P length := by omega
      change min (P length) (min (X length) (Delta length)) = X length
      rw [Nat.min_eq_left hX, Nat.min_eq_right hXP]
    · right; left
      apply deltaStart_eq_one_of_m_eq_Delta
      have hDX : Delta length ≤ X length := by omega
      have hDP : Delta length ≤ P length := by omega
      change min (P length) (min (X length) (Delta length)) = Delta length
      rw [Nat.min_eq_right hDX, Nat.min_eq_right hDP]

private theorem effective_three_starts_sub_one :
    effective (oneChip (G := (Spec length hLength).graph) (pStart length hLength) +
      oneChip (deltaStart length hLength) + oneChip (xStart length hLength) -
      oneChip ((Spec length hLength).coreVertex 1)) := by
  rcases some_start_eq_one length hLength with h | h | h
  · rw [h]
    intro vertex
    simp [oneChip]
    split_ifs <;> omega
  · rw [h]
    intro vertex
    simp [oneChip]
    split_ifs <;> omega
  · rw [h]
    intro vertex
    simp [oneChip]
    split_ifs <;> omega

/-- The first Dhar profile reaches `d=1`. -/
theorem reaches_one (hNorm : length 0 ≤ length 5) (hBC : C length ≤ B length) :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm) (p length hLength hBC))
      ((Spec length hLength).coreVertex 1) := by
  apply (dProfile length hLength hBC).reaches_of_effective_endpointDivisors
  rw [dProfile_endpointDivisors length hLength hNorm hBC]
  convert effective_three_starts_sub_one length hLength using 1
  funext vertex
  simp [threeChipDivisor, oneChip]
  ring

/-- The second Dhar profile reaches `e=2`. -/
theorem reaches_two (hNorm : length 0 ≤ length 5) (hBC : C length ≤ B length) :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm) (p length hLength hBC))
      ((Spec length hLength).coreVertex 2) := by
  apply (efProfile length hLength hBC).reaches_of_effective_endpointDivisors
  rw [efProfile_endpointDivisors]
  convert (Eff (Spec length hLength).graph).add_mem
    (eff_one_chip (q length hLength hNorm))
      (eff_one_chip ((Spec length hLength).coreVertex 3)) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

/-- The same second profile reaches `f=3`. -/
theorem reaches_three (hNorm : length 0 ≤ length 5) (hBC : C length ≤ B length) :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm) (p length hLength hBC))
      ((Spec length hLength).coreVertex 3) := by
  apply (efProfile length hLength hBC).reaches_of_effective_endpointDivisors
  rw [efProfile_endpointDivisors]
  convert (Eff (Spec length hLength).graph).add_mem
    (eff_one_chip (q length hLength hNorm))
      (eff_one_chip ((Spec length hLength).coreVertex 2)) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

/-- The first Core-095 chamber proves the genus-four degree-three pencil. -/
theorem bnExists_one_three (hNorm : length 0 ≤ length 5) (hBC : C length ≤ B length) :
    BNExists (Spec length hLength).graph 1 3 := by
  refine Utilities.Certificate.GenusFourLoopLemma.bnExists_of_reaches_coreVertices
    (Spec length hLength) (graphConnected length hLength)
    (threeChipDivisor ((Spec length hLength).coreVertex 4)
      (q length hLength hNorm) (p length hLength hBC)) 3 ?_ ?_
  · exact deg_threeChipDivisor _ _ _
  intro vertex
  fin_cases vertex
  · exact reaches_zero length hLength hNorm (p length hLength hBC)
  · exact reaches_one length hLength hNorm hBC
  · exact reaches_two length hLength hNorm hBC
  · exact reaches_three length hLength hNorm hBC
  · exact threeChipDivisor_reaches_of_eq _ _ _ _ (Or.inl rfl)
  · exact reaches_five length hLength hNorm (p length hLength hBC)

end LowGenus.GenusFourRow095.CaseOne
