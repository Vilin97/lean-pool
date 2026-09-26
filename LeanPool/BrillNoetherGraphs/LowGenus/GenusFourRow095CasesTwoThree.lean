/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095

/-!
# The two `B < C` Dhar profiles for Core 095

This is the middle and right chamber of the first Atanasov--Ranganathan
genus-four family.  The common `a/b` profile is in `GenusFourCore095`; this
file records the two remaining pairs of signed windows and packages their
endpoint computations as reachability statements.
-/

@[expose] public section

namespace LowGenus.GenusFourRow095
open Utilities.Certificate

open Utilities

open Finset
open SubdivisionGraph
open WindowProfile
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.Configurations

variable (length : Fin 9 → ℕ) (hLength : ∀ edge, 0 < length edge)

/-! Case 2: the middle comparison range `B < C` and
`min(X, Delta) ≤ C - B`. -/
namespace CaseTwo

/-- Excess of arm length `C` over `B`, used to locate the moving chip in Case 2. -/
abbrev Y : ℕ := C length - B length
/-- The smaller of the two central lengths `X` and `Delta`, compared with the arm excess in Case
2. -/
abbrev m : ℕ := min (X length) (Delta length)

variable (hNorm : length 0 ≤ length 5) (hBC : B length < C length)
variable (hmy : m length ≤ Y length)

private theorem m_le_X : m length ≤ X length := min_le_left _ _
private theorem m_le_Delta : m length ≤ Delta length := min_le_right _ _

private theorem B_add_m_le_C (hBC : B length < C length)
    (hmy : m length ≤ Y length) : B length + m length ≤ C length := by
  have h := (Nat.le_sub_iff_add_le hBC.le).mp hmy
  omega

/-- The moving third chip in Case 2. -/
def r : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 8
    ⟨B length + m length, by
      exact Nat.lt_succ_iff.mpr (B_add_m_le_C length hBC hmy)⟩

/-- Case-2 window profile which reaches core vertex `d=1`. -/
def dProfile : WindowProfile.Data (Spec length hLength) where
  coreValue := ![m length, 0, 0, 0, m length, m length]
  start := fun edge =>
    if edge = 4 then Delta length - m length else
    if edge = 5 then X length - m length else
    if edge = 8 then B length else 0
  stop := fun edge =>
    if edge = 4 then Delta length else
    if edge = 5 then X length else
    if edge = 8 then B length + m length else 0
  slope := fun edge => if edge = 4 ∨ edge = 5 ∨ edge = 8 then 1 else 0
  start_le_stop := by
    intro edge
    fin_cases edge <;> simp [m]
  stop_le_length := by
    have hBadd := B_add_m_le_C length hBC hmy
    intro edge
    fin_cases edge
    all_goals simp [B, Delta, X, m]
    all_goals omega
  endpoint_compatible := by
    intro edge
    fin_cases edge
    all_goals simp [core, B, Delta, X, m]

/-- Case-2 window profile which reaches the two zero-valued core vertices
`e=2` and `f=3`. -/
def efProfile : WindowProfile.Data (Spec length hLength) where
  coreValue := ![B length + m length, B length, 0, 0,
    B length + m length, B length + m length]
  start := fun edge =>
    if edge = 3 then 0 else
    if edge = 4 then Delta length - m length else
    if edge = 5 then X length - m length else 0
  stop := fun edge =>
    if edge = 3 then B length else
    if edge = 4 then Delta length else
    if edge = 5 then X length else
    if edge = 8 then B length + m length else 0
  slope := fun edge =>
    if edge = 3 then -1 else
    if edge = 4 ∨ edge = 5 ∨ edge = 8 then 1 else 0
  start_le_stop := by
    intro edge
    fin_cases edge <;> simp [m]
  stop_le_length := by
    have hBadd := B_add_m_le_C length hBC hmy
    intro edge
    fin_cases edge
    all_goals simp [B, Delta, X, m]
    all_goals omega
  endpoint_compatible := by
    intro edge
    fin_cases edge
    all_goals simp [core, B, Delta, X, m]

/-- The sparse signed-endpoint expansion of the Case-2 `d` profile. -/
theorem dProfile_endpointDivisors :
    (dProfile length hLength hBC hmy).endpointDivisors =
      (oneChip ((Spec length hLength).pathVertex 4
        ((dProfile length hLength hBC hmy).startPosition 4)) -
        oneChip ((Spec length hLength).pathVertex 4
          ((dProfile length hLength hBC hmy).stopPosition 4))) +
      (oneChip ((Spec length hLength).pathVertex 5
        ((dProfile length hLength hBC hmy).startPosition 5)) -
        oneChip ((Spec length hLength).pathVertex 5
          ((dProfile length hLength hBC hmy).stopPosition 5))) +
      (oneChip ((Spec length hLength).pathVertex 8
        ((dProfile length hLength hBC hmy).startPosition 8)) -
        oneChip ((Spec length hLength).pathVertex 8
          ((dProfile length hLength hBC hmy).stopPosition 8))) := by
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, dProfile]
  abel

private theorem dProfile_stop_four :
    (Spec length hLength).pathVertex 4
      ((dProfile length hLength hBC hmy).stopPosition 4) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 4
        ⟨length 4, by change length 4 < length 4 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.head 4) :=
      (Spec length hLength).pathVertex_length 4
    _ = _ := rfl

private theorem dProfile_stop_five :
    (Spec length hLength).pathVertex 5
      ((dProfile length hLength hBC hmy).stopPosition 5) =
      q length hLength hNorm := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem dProfile_stop_eight :
    (Spec length hLength).pathVertex 8
      ((dProfile length hLength hBC hmy).stopPosition 8) =
      r length hLength hBC hmy := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem dProfile_start_four_eq_one (hm : m length = Delta length) :
    (Spec length hLength).pathVertex 4
      ((dProfile length hLength hBC hmy).startPosition 4) =
      (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 4 ⟨0, by omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      simp [dProfile, hm]
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 4) :=
      (Spec length hLength).pathVertex_zero 4
    _ = _ := rfl

private theorem dProfile_start_five_eq_one (hm : m length = X length) :
    (Spec length hLength).pathVertex 5
      ((dProfile length hLength hBC hmy).startPosition 5) =
      (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 5 ⟨0, by omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      simp [dProfile, hm]
    _ = (Spec length hLength).coreVertex
        ((Spec length hLength).core.tail 5) :=
      (Spec length hLength).pathVertex_zero 5
    _ = _ := rfl

/-- In the middle Case-2 chamber the displayed divisor reaches `d=1`. -/
theorem reaches_one :
    StrongSeparator.Reaches (Spec length hLength).graph
      (threeChipDivisor ((Spec length hLength).coreVertex 4)
        (q length hLength hNorm) (r length hLength hBC hmy))
      ((Spec length hLength).coreVertex 1) := by
  apply (dProfile length hLength hBC hmy).reaches_of_effective_endpointDivisors
  rw [dProfile_endpointDivisors]
  rw [dProfile_stop_four length hLength hBC hmy,
    dProfile_stop_five length hLength hNorm hBC hmy,
    dProfile_stop_eight length hLength hBC hmy]
  by_cases hXD : X length ≤ Delta length
  · have hm : m length = X length := min_eq_left hXD
    rw [dProfile_start_five_eq_one length hLength hBC hmy hm]
    have hRewrite :
        threeChipDivisor ((Spec length hLength).coreVertex 4)
            (q length hLength hNorm) (r length hLength hBC hmy) -
          oneChip ((Spec length hLength).coreVertex 1) +
          ((oneChip ((Spec length hLength).pathVertex 4
              ((dProfile length hLength hBC hmy).startPosition 4)) -
              oneChip ((Spec length hLength).coreVertex 4)) +
            (oneChip ((Spec length hLength).coreVertex 1) -
              oneChip (q length hLength hNorm)) +
            (oneChip ((Spec length hLength).pathVertex 8
              ((dProfile length hLength hBC hmy).startPosition 8)) -
              oneChip (r length hLength hBC hmy))) =
          oneChip (G := (Spec length hLength).graph) ((Spec length hLength).pathVertex 4
              ((dProfile length hLength hBC hmy).startPosition 4)) +
            oneChip (G := (Spec length hLength).graph) ((Spec length hLength).pathVertex 8
              ((dProfile length hLength hBC hmy).startPosition 8)) := by
      simp [threeChipDivisor]
      abel
    rw [hRewrite]
    exact (Eff _).add_mem (eff_one_chip _) (eff_one_chip _)
  · have hDX : Delta length ≤ X length := by omega
    have hm : m length = Delta length := min_eq_right hDX
    rw [dProfile_start_four_eq_one length hLength hBC hmy hm]
    have hRewrite :
        threeChipDivisor ((Spec length hLength).coreVertex 4)
            (q length hLength hNorm) (r length hLength hBC hmy) -
          oneChip ((Spec length hLength).coreVertex 1) +
          ((oneChip ((Spec length hLength).coreVertex 1) -
              oneChip ((Spec length hLength).coreVertex 4)) +
            (oneChip ((Spec length hLength).pathVertex 5
              ((dProfile length hLength hBC hmy).startPosition 5)) -
              oneChip (q length hLength hNorm)) +
            (oneChip ((Spec length hLength).pathVertex 8
              ((dProfile length hLength hBC hmy).startPosition 8)) -
              oneChip (r length hLength hBC hmy))) =
          oneChip (G := (Spec length hLength).graph) ((Spec length hLength).pathVertex 5
              ((dProfile length hLength hBC hmy).startPosition 5)) +
            oneChip (G := (Spec length hLength).graph) ((Spec length hLength).pathVertex 8
              ((dProfile length hLength hBC hmy).startPosition 8)) := by
      simp [threeChipDivisor]
      abel
    rw [hRewrite]
    exact (Eff _).add_mem (eff_one_chip _) (eff_one_chip _)

private theorem ef_start_three_eq_one :
    (Spec length hLength).pathVertex 3
      ((efProfile length hLength hBC hmy).startPosition 3) =
      (Spec length hLength).coreVertex 1 := by
  calc
    _ = (Spec length hLength).pathVertex 3 ⟨0, by change 0 < length 3 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.tail 3) :=
      (Spec length hLength).pathVertex_zero 3
    _ = _ := rfl

private theorem ef_stop_three_eq_three :
    (Spec length hLength).pathVertex 3
      ((efProfile length hLength hBC hmy).stopPosition 3) =
      (Spec length hLength).coreVertex 3 := by
  calc
    _ = (Spec length hLength).pathVertex 3 ⟨length 3, by
      change length 3 < length 3 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.head 3) :=
      (Spec length hLength).pathVertex_length 3
    _ = _ := rfl

private theorem ef_start_four_eq_dStart :
    (Spec length hLength).pathVertex 4
      ((efProfile length hLength hBC hmy).startPosition 4) =
      (Spec length hLength).pathVertex 4
        ((dProfile length hLength hBC hmy).startPosition 4) := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem ef_start_five_eq_dStart :
    (Spec length hLength).pathVertex 5
      ((efProfile length hLength hBC hmy).startPosition 5) =
      (Spec length hLength).pathVertex 5
        ((dProfile length hLength hBC hmy).startPosition 5) := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem ef_stop_four_eq_four :
    (Spec length hLength).pathVertex 4
      ((efProfile length hLength hBC hmy).stopPosition 4) =
      (Spec length hLength).coreVertex 4 := by
  calc
    _ = (Spec length hLength).pathVertex 4 ⟨length 4, by
      change length 4 < length 4 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.head 4) :=
      (Spec length hLength).pathVertex_length 4
    _ = _ := rfl

private theorem ef_stop_five_eq_q :
    (Spec length hLength).pathVertex 5
      ((efProfile length hLength hBC hmy).stopPosition 5) = q length hLength hNorm := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

private theorem ef_start_eight_eq_two :
    (Spec length hLength).pathVertex 8
      ((efProfile length hLength hBC hmy).startPosition 8) =
      (Spec length hLength).coreVertex 2 := by
  calc
    _ = (Spec length hLength).pathVertex 8 ⟨0, by change 0 < length 8 + 1; omega⟩ := by
      apply (Spec length hLength).pathVertex_eq_of_val_eq
      rfl
    _ = (Spec length hLength).coreVertex ((Spec length hLength).core.tail 8) :=
      (Spec length hLength).pathVertex_zero 8
    _ = _ := rfl

private theorem ef_stop_eight_eq_r :
    (Spec length hLength).pathVertex 8
      ((efProfile length hLength hBC hmy).stopPosition 8) = r length hLength hBC hmy := by
  apply (Spec length hLength).pathVertex_eq_of_val_eq
  rfl

@[simp] theorem efProfile_slope (edge : Fin 9) :
    (efProfile length hLength hBC hmy).slope edge =
      if edge = 3 then -1 else if edge = 4 ∨ edge = 5 ∨ edge = 8 then 1 else 0 := rfl

theorem efProfile_endpointDivisors :
    (efProfile length hLength hBC hmy).endpointDivisors =
      (- oneChip ((Spec length hLength).coreVertex 1) + oneChip ((Spec length hLength).coreVertex
        3)) +
      (oneChip ((Spec length hLength).pathVertex 4 ((dProfile length hLength hBC hmy).startPosition
        4)) - oneChip ((Spec length hLength).coreVertex 4)) +
      (oneChip ((Spec length hLength).pathVertex 5 ((dProfile length hLength hBC hmy).startPosition
        5)) - oneChip (q length hLength hNorm)) +
      (oneChip ((Spec length hLength).coreVertex 2) - oneChip (r length hLength hBC hmy)) := by
  rw [WindowProfile.Data.endpointDivisors]
  simp [Fin.sum_univ_succ, efProfile_slope, ef_start_three_eq_one, ef_stop_three_eq_three,
    ef_start_four_eq_dStart, ef_stop_four_eq_four, ef_start_five_eq_dStart,
    ef_start_eight_eq_two, ef_stop_eight_eq_r]
  rw [ef_stop_five_eq_q length hLength hNorm hBC hmy]
  abel

private theorem effective_dStarts_sub_one :
    effective (oneChip (G := (Spec length hLength).graph)
      ((Spec length hLength).pathVertex 4 ((dProfile length hLength hBC hmy).startPosition 4)) +
      oneChip ((Spec length hLength).pathVertex 5 ((dProfile length hLength hBC hmy).startPosition
        5)) -
      oneChip ((Spec length hLength).coreVertex 1)) := by
  by_cases hXD : X length ≤ Delta length
  · rw [dProfile_start_five_eq_one length hLength hBC hmy (min_eq_left hXD)]
    intro vertex; simp [oneChip]; split_ifs <;> omega
  · have hDX : Delta length ≤ X length := by omega
    rw [dProfile_start_four_eq_one length hLength hBC hmy (min_eq_right hDX)]
    intro vertex; simp [oneChip]; split_ifs <;> omega

theorem reaches_two : StrongSeparator.Reaches (Spec length hLength).graph
    (threeChipDivisor ((Spec length hLength).coreVertex 4) (q length hLength hNorm) (r length
      hLength hBC hmy))
    ((Spec length hLength).coreVertex 2) := by
  apply (efProfile length hLength hBC hmy).reaches_of_effective_endpointDivisors
  rw [efProfile_endpointDivisors length hLength hNorm hBC hmy]
  convert (Eff _).add_mem (eff_one_chip ((Spec length hLength).coreVertex 3))
    (effective_dStarts_sub_one length hLength hBC hmy) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

theorem reaches_three : StrongSeparator.Reaches (Spec length hLength).graph
    (threeChipDivisor ((Spec length hLength).coreVertex 4) (q length hLength hNorm) (r length
      hLength hBC hmy))
    ((Spec length hLength).coreVertex 3) := by
  apply (efProfile length hLength hBC hmy).reaches_of_effective_endpointDivisors
  rw [efProfile_endpointDivisors length hLength hNorm hBC hmy]
  convert (Eff _).add_mem (eff_one_chip ((Spec length hLength).coreVertex 2))
    (effective_dStarts_sub_one length hLength hBC hmy) using 2
  all_goals simp only [threeChipDivisor, mem_Eff]
  all_goals abel_nf

theorem bnExists_one_three (hNorm : length 0 ≤ length 5) (hBC : B length < C length)
    (hmy : m length ≤ Y length) : BNExists (Spec length hLength).graph 1 3 := by
  refine Utilities.Certificate.GenusFourLoopLemma.bnExists_of_reaches_coreVertices
    (Spec length hLength) (graphConnected length hLength)
    (threeChipDivisor ((Spec length hLength).coreVertex 4)
      (q length hLength hNorm) (r length hLength hBC hmy)) 3 ?_ ?_
  · exact deg_threeChipDivisor _ _ _
  intro vertex
  fin_cases vertex
  · exact reaches_zero length hLength hNorm (r length hLength hBC hmy)
  · exact reaches_one length hLength hNorm hBC hmy
  · exact reaches_two length hLength hNorm hBC hmy
  · exact reaches_three length hLength hNorm hBC hmy
  · exact threeChipDivisor_reaches_of_eq _ _ _ _ (Or.inl rfl)
  · exact reaches_five length hLength hNorm (r length hLength hBC hmy)

end CaseTwo

/-! Case 3: the strict short comparison range `0 < C-B < min(X,Delta)`. -/
namespace CaseThree

/-- Excess of arm length `C` over `B`, used in the Case-3 window construction. -/
abbrev Y : ℕ := C length - B length

variable (hNorm : length 0 ≤ length 5) (hBC : B length < C length)
variable (hYpos : 0 < Y length)
variable (hYsmall : Y length < min (X length) (Delta length))

private theorem Y_lt_X (hYsmall : Y length < min (X length) (Delta length)) :
    Y length < X length :=
  lt_of_lt_of_le hYsmall (min_le_left _ _)

private theorem Y_lt_Delta (hYsmall : Y length < min (X length) (Delta length)) :
    Y length < Delta length :=
  lt_of_lt_of_le hYsmall (min_le_right _ _)

/-- The moving third chip in Case 3. -/
def s : (Spec length hLength).Vertex :=
  (Spec length hLength).pathVertex 4
    ⟨Y length, by
      exact Nat.lt_succ_iff.mpr (Y_lt_Delta length hYsmall).le⟩

/-- Case-3 window profile which reaches `d=1`. -/
def dProfile : WindowProfile.Data (Spec length hLength) where
  coreValue := ![Y length, 0, 0, 0, Y length, Y length]
  start := fun edge =>
    if edge = 4 then 0 else
    if edge = 5 then X length - Y length else
    if edge = 8 then B length else 0
  stop := fun edge =>
    if edge = 4 then Y length else
    if edge = 5 then X length else
    if edge = 8 then C length else 0
  slope := fun edge => if edge = 4 ∨ edge = 5 ∨ edge = 8 then 1 else 0
  start_le_stop := by
    intro edge
    fin_cases edge <;> simp [Y]
    omega
  stop_le_length := by
    have hYX := (Y_lt_X length hYsmall).le
    have hYD := (Y_lt_Delta length hYsmall).le
    intro edge
    fin_cases edge
    · simp
    · simp
    · simp
    · simp
    · exact hYD
    · exact Nat.sub_le (length 5) (length 0)
    · simp
    · simp
    · simp [C]
  endpoint_compatible := by
    have hYX := (Y_lt_X length hYsmall).le
    have hYeq : B length + Y length = C length := by
      dsimp [Y]
      omega
    have hXeq : X length - Y length + Y length = X length :=
      Nat.sub_add_cancel hYX
    have hXdiff : X length - (X length - Y length) = Y length :=
      Nat.sub_sub_self hYX
    dsimp [B, C, X, Y] at hBC hYpos hYsmall hYX hYeq hXeq hXdiff ⊢
    intro edge
    fin_cases edge
    all_goals simp [core]
    all_goals omega

/-- Case-3 window profile which reaches `e=2` and `f=3`. -/
def efProfile : WindowProfile.Data (Spec length hLength) where
  coreValue := ![C length, B length, 0, 0, C length, C length]
  start := fun edge =>
    if edge = 3 then 0 else
    if edge = 4 then 0 else
    if edge = 5 then X length - Y length else 0
  stop := fun edge =>
    if edge = 3 then B length else
    if edge = 4 then Y length else
    if edge = 5 then X length else
    if edge = 8 then C length else 0
  slope := fun edge =>
    if edge = 3 then -1 else
    if edge = 4 ∨ edge = 5 ∨ edge = 8 then 1 else 0
  start_le_stop := by
    intro edge
    fin_cases edge <;> simp [Y]
  stop_le_length := by
    have hYX := (Y_lt_X length hYsmall).le
    have hYD := (Y_lt_Delta length hYsmall).le
    intro edge
    fin_cases edge
    · simp
    · simp
    · simp
    · simp [B]
    · exact hYD
    · exact Nat.sub_le (length 5) (length 0)
    · simp
    · simp
    · simp [C]
  endpoint_compatible := by
    have hYX := (Y_lt_X length hYsmall).le
    have hYeq : B length + Y length = C length := by
      dsimp [Y]
      omega
    have hXeq : X length - Y length + Y length = X length :=
      Nat.sub_add_cancel hYX
    have hXdiff : X length - (X length - Y length) = Y length :=
      Nat.sub_sub_self hYX
    dsimp [B, C, X, Y] at hBC hYpos hYsmall hYX hYeq hXeq hXdiff ⊢
    intro edge
    fin_cases edge
    all_goals simp [core]
    all_goals omega

end CaseThree

end LowGenus.GenusFourRow095
