/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import LeanPool.BKARForestFormula.BKAR.ThresholdComponents

/-!
# Finite layer-cake decomposition for BKAR threshold components

This file proves the scalar combinatorial layer behind component-form
arguments for the BKAR forest interpolation formula (see `BKAR.Formula`).
For a BKAR forest point `lambda = F.standardInterp u`,
the finitely many values of `lambda`, together with `0` and `1`, determine a
finite set of threshold levels.  The jumps between consecutive levels form
nonnegative weights, and the weighted sum of threshold-component indicators
recovers the BKAR interpolation value.
-/

namespace BKAR

open scoped BigOperators

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/--
The finite set of scalar levels needed for the layer-cake decomposition of a
BKAR interpolation point.
-/
def interpolationLevels (F : Forest V) (u : F.EdgeParam → ℝ) : Finset ℝ :=
  insert 0
    (insert 1
      ((Finset.univ : Finset (Edge V)).image fun e => F.standardInterp u e))

@[simp]
theorem zero_mem_interpolationLevels (F : Forest V) (u : F.EdgeParam → ℝ) :
    0 ∈ F.interpolationLevels u := by
  simp [interpolationLevels]

@[simp]
theorem one_mem_interpolationLevels (F : Forest V) (u : F.EdgeParam → ℝ) :
    1 ∈ F.interpolationLevels u := by
  simp [interpolationLevels]

theorem standardInterp_mem_interpolationLevels
    (F : Forest V) (u : F.EdgeParam → ℝ) (e : Edge V) :
    F.standardInterp u e ∈ F.interpolationLevels u := by
  classical
  simp [interpolationLevels]

theorem interpolationLevels_subset_Icc
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {x : ℝ} (hx : x ∈ F.interpolationLevels u) :
    0 ≤ x ∧ x ≤ 1 := by
  classical
  rw [interpolationLevels] at hx
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | rfl | ⟨e, he⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · rw [← he]
    exact F.standardInterp_mem_Icc u hu e

theorem one_lt_interpolationLevels_card
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    1 < (F.interpolationLevels u).card := by
  rw [Finset.one_lt_card]
  exact ⟨0, F.zero_mem_interpolationLevels u, 1,
    F.one_mem_interpolationLevels u, zero_ne_one⟩

theorem interpolationLevels_card_pos
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    0 < (F.interpolationLevels u).card :=
  Nat.lt_trans Nat.zero_lt_one (F.one_lt_interpolationLevels_card u)

theorem interpolationLevels_min_eq_zero
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (F.interpolationLevels u).min'
        ⟨0, F.zero_mem_interpolationLevels u⟩ = 0 := by
  apply le_antisymm
  · exact (F.interpolationLevels u).min'_le 0
      (F.zero_mem_interpolationLevels u)
  · exact (F.interpolationLevels_subset_Icc u hu
      ((F.interpolationLevels u).min'_mem _)).1

theorem interpolationLevels_max_eq_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (F.interpolationLevels u).max'
        ⟨1, F.one_mem_interpolationLevels u⟩ = 1 := by
  apply le_antisymm
  · exact (F.interpolationLevels_subset_Icc u hu
      ((F.interpolationLevels u).max'_mem _)).2
  · exact (F.interpolationLevels u).le_max' 1
      (F.one_mem_interpolationLevels u)

/-- The `i`th level, in increasing order. -/
def interpolationLevel (F : Forest V) (u : F.EdgeParam → ℝ)
    (i : Fin (F.interpolationLevels u).card) : ℝ :=
  (F.interpolationLevels u).orderEmbOfFin rfl i

theorem interpolationLevel_zero
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    F.interpolationLevel u
        ⟨0, F.interpolationLevels_card_pos u⟩ = 0 := by
  rw [interpolationLevel]
  rw [Finset.orderEmbOfFin_zero rfl (F.interpolationLevels_card_pos u)]
  exact F.interpolationLevels_min_eq_zero u hu

theorem interpolationLevel_last
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    F.interpolationLevel u
        ⟨(F.interpolationLevels u).card - 1,
          Nat.sub_lt (F.interpolationLevels_card_pos u) Nat.zero_lt_one⟩ = 1 := by
  rw [interpolationLevel]
  rw [Finset.orderEmbOfFin_last rfl (F.interpolationLevels_card_pos u)]
  exact F.interpolationLevels_max_eq_one u hu

/-- The threshold level attached to the `i`th layer. -/
def interpolationLayerThreshold
    (F : Forest V) (u : F.EdgeParam → ℝ) (i : ℕ) : ℝ :=
  if hi : i < (F.interpolationLevels u).card - 1 then
    F.interpolationLevel u
      ⟨i + 1, by
        omega⟩
  else
    0

/-- The jump between consecutive sorted interpolation levels. -/
def interpolationGap
    (F : Forest V) (u : F.EdgeParam → ℝ) (i : ℕ) : ℝ :=
  if hi : i < (F.interpolationLevels u).card - 1 then
    F.interpolationLayerThreshold u i -
      F.interpolationLevel u
        ⟨i, by
          omega⟩
  else
    0

theorem interpolationLayerThreshold_of_lt
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    F.interpolationLayerThreshold u i =
      F.interpolationLevel u
        ⟨i + 1, by
          omega⟩ := by
  simp [interpolationLayerThreshold, hi]

theorem interpolationGap_of_lt
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    F.interpolationGap u i =
      F.interpolationLevel u
        ⟨i + 1, by
          omega⟩ -
        F.interpolationLevel u
          ⟨i, by
            omega⟩ := by
  simp [interpolationGap, interpolationLayerThreshold_of_lt F u hi, hi]

theorem interpolationGap_nonneg
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card - 1) :
    0 ≤ F.interpolationGap u i := by
  rw [F.interpolationGap_of_lt u hi]
  have hle :
      F.interpolationLevel u ⟨i, by omega⟩ ≤
        F.interpolationLevel u ⟨i + 1, by omega⟩ := by
    exact ((F.interpolationLevels u).orderEmbOfFin rfl).monotone (by
      exact Nat.le_succ i)
  exact sub_nonneg.mpr hle

theorem interpolationLayerThreshold_pos
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {i : ℕ} (hi : i < (F.interpolationLevels u).card - 1) :
    0 < F.interpolationLayerThreshold u i := by
  rw [F.interpolationLayerThreshold_of_lt u hi]
  have hlt :
      F.interpolationLevel u
          ⟨0, F.interpolationLevels_card_pos u⟩ <
        F.interpolationLevel u
          ⟨i + 1, by omega⟩ := by
    exact ((F.interpolationLevels u).orderEmbOfFin rfl).strictMono (by
      exact Nat.succ_pos i)
  simpa [F.interpolationLevel_zero u hu] using hlt

theorem interpolationLayerThreshold_le_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {i : ℕ} (hi : i < (F.interpolationLevels u).card - 1) :
    F.interpolationLayerThreshold u i ≤ 1 := by
  rw [F.interpolationLayerThreshold_of_lt u hi]
  exact (F.interpolationLevels_subset_Icc u hu
    ((F.interpolationLevels u).orderEmbOfFin_mem rfl ⟨i + 1, by omega⟩)).2

private def interpolationLevelAux
    (F : Forest V) (u : F.EdgeParam → ℝ) (i : ℕ) : ℝ :=
  if hi : i < (F.interpolationLevels u).card then
    F.interpolationLevel u ⟨i, hi⟩
  else
    0

private theorem interpolationLevelAux_of_lt
    (F : Forest V) (u : F.EdgeParam → ℝ) {i : ℕ}
    (hi : i < (F.interpolationLevels u).card) :
    interpolationLevelAux F u i = F.interpolationLevel u ⟨i, hi⟩ := by
  simp [interpolationLevelAux, hi]

theorem sum_interpolationGap_range_eq_interpolationLevel
    (F : Forest V) (u : F.EdgeParam → ℝ)
    {n : ℕ} (hn : n < (F.interpolationLevels u).card) :
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
      F.interpolationLevel u ⟨n, hn⟩ -
        F.interpolationLevel u
          ⟨0, F.interpolationLevels_card_pos u⟩ := by
  let f : ℕ → ℝ := interpolationLevelAux F u
  calc
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
        ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          have hik : i < (F.interpolationLevels u).card - 1 := by
            omega
          rw [F.interpolationGap_of_lt u hik]
          change
            F.interpolationLevel u ⟨i + 1, by omega⟩ -
                F.interpolationLevel u ⟨i, by omega⟩ =
              interpolationLevelAux F u (i + 1) -
                interpolationLevelAux F u i
          rw [interpolationLevelAux_of_lt F u (i := i + 1) (by omega)]
          rw [interpolationLevelAux_of_lt F u (i := i) (by omega)]
    _ = f n - f 0 := Finset.sum_range_sub f n
    _ =
        F.interpolationLevel u ⟨n, hn⟩ -
          F.interpolationLevel u
            ⟨0, F.interpolationLevels_card_pos u⟩ := by
          change interpolationLevelAux F u n - interpolationLevelAux F u 0 =
            F.interpolationLevel u ⟨n, hn⟩ -
              F.interpolationLevel u
                ⟨0, F.interpolationLevels_card_pos u⟩
          rw [interpolationLevelAux_of_lt F u hn]
          rw [interpolationLevelAux_of_lt F u
            (F.interpolationLevels_card_pos u)]

theorem sum_interpolationGap_range_eq_interpolationLevel_of_zero
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {n : ℕ} (hn : n < (F.interpolationLevels u).card) :
    (∑ i ∈ Finset.range n, F.interpolationGap u i) =
      F.interpolationLevel u ⟨n, hn⟩ := by
  rw [F.sum_interpolationGap_range_eq_interpolationLevel u hn]
  rw [F.interpolationLevel_zero u hu]
  simp

theorem sum_interpolationGap_le_eq_of_mem_interpolationLevels
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    {x : ℝ} (hx : x ∈ F.interpolationLevels u) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if F.interpolationLayerThreshold u i ≤ x then
          F.interpolationGap u i
        else
          0) = x := by
  classical
  let n : Fin (F.interpolationLevels u).card :=
    ((F.interpolationLevels u).orderIsoOfFin rfl).symm ⟨x, hx⟩
  have hxlevel : F.interpolationLevel u n = x := by
    rw [interpolationLevel]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [n]
  have hfilter :
      (Finset.range ((F.interpolationLevels u).card - 1)).filter
          (fun i => F.interpolationLayerThreshold u i ≤ x) =
        Finset.range n.1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hle⟩
      have hthr :
          F.interpolationLayerThreshold u i =
            F.interpolationLevel u ⟨i + 1, by omega⟩ :=
        F.interpolationLayerThreshold_of_lt u hi
      have hle' :
          F.interpolationLevel u ⟨i + 1, by omega⟩ ≤
            F.interpolationLevel u n := by
        calc
          F.interpolationLevel u ⟨i + 1, by omega⟩ =
              F.interpolationLayerThreshold u i := hthr.symm
          _ ≤ x := hle
          _ = F.interpolationLevel u n := hxlevel.symm
      have hnat : i + 1 ≤ n.1 := by
        have hfin : (⟨i + 1, by omega⟩ :
            Fin (F.interpolationLevels u).card) ≤ n := by
          exact ((F.interpolationLevels u).orderEmbOfFin rfl).le_iff_le.mp
            (by simpa [interpolationLevel] using hle')
        exact hfin
      omega
    · intro hi
      have hik : i < (F.interpolationLevels u).card - 1 := by
        have hn : n.1 < (F.interpolationLevels u).card := n.2
        omega
      refine ⟨hik, ?_⟩
      have hleNat : i + 1 ≤ n.1 := by omega
      have hle' :
          F.interpolationLevel u ⟨i + 1, by omega⟩ ≤
            F.interpolationLevel u n := by
        exact ((F.interpolationLevels u).orderEmbOfFin rfl).monotone
          (by
            exact hleNat)
      calc
        F.interpolationLayerThreshold u i =
            F.interpolationLevel u ⟨i + 1, by omega⟩ :=
          F.interpolationLayerThreshold_of_lt u hik
        _ ≤ F.interpolationLevel u n := hle'
        _ = x := hxlevel
  rw [← Finset.sum_filter]
  rw [hfilter]
  rw [F.sum_interpolationGap_range_eq_interpolationLevel_of_zero u hu n.2]
  exact hxlevel

theorem sum_interpolationGap_range_last_eq_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        F.interpolationGap u i) = 1 := by
  have hlast :
      (F.interpolationLevels u).card - 1 <
        (F.interpolationLevels u).card :=
    Nat.sub_lt (F.interpolationLevels_card_pos u) Nat.zero_lt_one
  rw [F.sum_interpolationGap_range_eq_interpolationLevel_of_zero u hu hlast]
  exact F.interpolationLevel_last u hu

/--
Layer-cake identity for a BKAR edge value, expressed using threshold
components.
-/
theorem sum_interpolationGap_thresholdComponent_edge_eq_standardInterp
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (e : Edge V) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if e.right ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) e.left then
          F.interpolationGap u i
        else
          0) = F.standardInterp u e := by
  classical
  rw [← F.sum_interpolationGap_le_eq_of_mem_interpolationLevels u hu
    (F.standardInterp_mem_interpolationLevels u e)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hik : i < (F.interpolationLevels u).card - 1 :=
    Finset.mem_range.mp hi
  have hs0 : 0 < F.interpolationLayerThreshold u i :=
    F.interpolationLayerThreshold_pos u hu hik
  have hs1 : F.interpolationLayerThreshold u i ≤ 1 :=
    F.interpolationLayerThreshold_le_one u hu hik
  have hiff :
      F.interpolationLayerThreshold u i ≤ F.standardInterp u e ↔
        e.right ∈ F.thresholdComponent u
          (F.interpolationLayerThreshold u i) e.left :=
    F.le_standardInterp_iff_mem_thresholdComponent u hs0 hs1 e
  by_cases hle :
      F.interpolationLayerThreshold u i ≤ F.standardInterp u e
  · have hmem := hiff.mp hle
    simp [hle, hmem]
  · have hmem :
      e.right ∉ F.thresholdComponent u
        (F.interpolationLayerThreshold u i) e.left := by
      intro hmem
      exact hle (hiff.mpr hmem)
    simp [hle, hmem]

/-- Diagonal layer-cake identity: every threshold component contains its base point. -/
theorem sum_interpolationGap_thresholdComponent_diag_eq_one
    (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (z : V) :
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if z ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) z then
          F.interpolationGap u i
        else
          0) = 1 := by
  calc
    (∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
        if z ∈ F.thresholdComponent u
            (F.interpolationLayerThreshold u i) z then
          F.interpolationGap u i
        else
          0) =
          ∑ i ∈ Finset.range ((F.interpolationLevels u).card - 1),
          F.interpolationGap u i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hmem :
              z ∈ F.thresholdComponent u
                (F.interpolationLayerThreshold u i) z :=
            F.self_mem_thresholdComponent u
              (F.interpolationLayerThreshold u i) z
          simp [hmem]
    _ = 1 := F.sum_interpolationGap_range_last_eq_one u hu

end

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
