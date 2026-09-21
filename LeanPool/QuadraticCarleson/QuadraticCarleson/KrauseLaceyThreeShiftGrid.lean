/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundDyadicStopping
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyShiftedLocalization

/-!
# The finite three-shift grids in the Krause--Lacey reduction

For a largest scale, each of the three grids is an ordinary global dyadic
grid translated by zero, one third, or two thirds of the largest length.
At every finer scale the three translations are permuted modulo one, so the
central thirds partition the line.  This file first establishes the exact
laminar geometry within each translated grid.  The finite support and
three-grid reconstruction are developed from this representation below.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid

open CalderonZygmundDyadicStopping


noncomputable section

/-- A half-open real interval in the global dyadic grid of root length `L`,
translated by `origin`. -/
def translatedDyadicRealInterval
    (origin L : ℝ) (hL : 0 < L) (depth : ℕ) (q : ℤ) : RealInterval where
  left := origin + (q : ℝ) * dyadicLength L depth
  right := origin + ((q : ℝ) + 1) * dyadicLength L depth
  left_lt_right := by
    have hd := dyadicLength_pos hL depth
    linarith

theorem translatedDyadicRealInterval_length
    (origin L : ℝ) (hL : 0 < L) (depth : ℕ) (q : ℤ) :
    (translatedDyadicRealInterval origin L hL depth q).length =
      dyadicLength L depth := by
  unfold translatedDyadicRealInterval RealInterval.length
  ring

theorem translatedDyadicRealInterval_carrier
    (origin L : ℝ) (hL : 0 < L) (depth : ℕ) (q : ℤ) :
    (translatedDyadicRealInterval origin L hL depth q).carrier =
      Ioc (origin + (q : ℝ) * dyadicLength L depth)
        (origin + ((q : ℝ) + 1) * dyadicLength L depth) := rfl

/-- A fine translated dyadic cell is contained in a fixed coarse cell or is
disjoint from it.  This is the exact half-open geometry needed by the finite
stopping recursion. -/
theorem translatedDyadicRealInterval_subset_or_disjoint_of_le
    {origin L : ℝ} (hL : 0 < L) {n m : ℕ} (hnm : n ≤ m) (q r : ℤ) :
    (translatedDyadicRealInterval origin L hL m r).carrier ⊆
        (translatedDyadicRealInterval origin L hL n q).carrier ∨
      Disjoint (translatedDyadicRealInterval origin L hL m r).carrier
        (translatedDyadicRealInterval origin L hL n q).carrier := by
  let D : ℤ := (2 : ℕ) ^ (m - n)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) (m - n))
  have hlen := dyadicLength_eq_pow_mul (L := L) hnm
  have hcastD : (D : ℝ) = (2 : ℝ) ^ (m - n) := by
    simp [D]
  have hdm : 0 < dyadicLength L m := dyadicLength_pos hL m
  by_cases hrange : q * D ≤ r ∧ r < (q + 1) * D
  · left
    intro x hx
    simp only [translatedDyadicRealInterval_carrier, mem_Ioc] at hx ⊢
    have hloZ : q * D ≤ r := hrange.1
    have hhiZ : r + 1 ≤ (q + 1) * D := by omega
    have hloR : ((q * D : ℤ) : ℝ) * dyadicLength L m ≤
        (r : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hloZ) hdm.le
    have hhiR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
        (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hhiZ) hdm.le
    rw [hlen, ← hcastD]
    push_cast at hloR hhiR ⊢
    constructor <;> nlinarith
  · right
    rw [not_and_or] at hrange
    rcases hrange with hlo | hhi
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [translatedDyadicRealInterval_carrier, mem_Ioc] at hxf hxc
      have hz : r + 1 ≤ q * D := by omega
      have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
          ((q * D : ℤ) : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [translatedDyadicRealInterval_carrier, mem_Ioc] at hxf hxc
      have hz : (q + 1) * D ≤ r := by omega
      have hzR : (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m ≤
          (r : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith

/-- Any two intervals in one translated dyadic grid are nested or disjoint. -/
theorem translatedDyadicRealInterval_laminar
    {origin L : ℝ} (hL : 0 < L) (n : ℕ) (q : ℤ) (m : ℕ) (r : ℤ) :
    (translatedDyadicRealInterval origin L hL n q).carrier ⊆
        (translatedDyadicRealInterval origin L hL m r).carrier ∨
      (translatedDyadicRealInterval origin L hL m r).carrier ⊆
          (translatedDyadicRealInterval origin L hL n q).carrier ∨
        Disjoint (translatedDyadicRealInterval origin L hL n q).carrier
          (translatedDyadicRealInterval origin L hL m r).carrier := by
  rcases le_total n m with hnm | hmn
  · rcases translatedDyadicRealInterval_subset_or_disjoint_of_le hL hnm q r with
      hsub | hdis
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr hdis.symm)
  · rcases translatedDyadicRealInterval_subset_or_disjoint_of_le hL hmn r q with
      hsub | hdis
    · exact Or.inl hsub
    · exact Or.inr (Or.inr hdis)

/-- The Euclidean-division address gives the unique dyadic parent. -/
theorem translatedDyadicRealInterval_parent_subset
    {origin L : ℝ} (hL : 0 < L) (depth : ℕ) (q : ℤ) :
    (translatedDyadicRealInterval origin L hL (depth + 1) q).carrier ⊆
      (translatedDyadicRealInterval origin L hL depth (q / 2)).carrier := by
  rcases Int.even_or_odd' q with ⟨r, rfl | rfl⟩
  · have hdiv : (2 * r : ℤ) / 2 = r := by omega
    rw [hdiv]
    intro x hx
    simp only [translatedDyadicRealInterval_carrier, mem_Ioc] at hx ⊢
    rw [dyadicLength_succ] at hx
    have hd := dyadicLength_pos hL depth
    push_cast at hx ⊢
    constructor <;> nlinarith
  · have hdiv : (2 * r + 1 : ℤ) / 2 = r := by omega
    rw [hdiv]
    intro x hx
    simp only [translatedDyadicRealInterval_carrier, mem_Ioc] at hx ⊢
    rw [dyadicLength_succ] at hx
    have hd := dyadicLength_pos hL depth
    push_cast at hx ⊢
    constructor <;> nlinarith

/-- The largest interval length used by a finite KL18 grid whose largest
kernel label is `topScale`. -/
def shiftedGridRootLength (topScale : ℤ) : ℝ :=
  (2 : ℝ) ^ (topScale + 2)

theorem shiftedGridRootLength_pos (topScale : ℤ) :
    0 < shiftedGridRootLength topScale := by
  unfold shiftedGridRootLength
  positivity

/-- Grid `shift` (`0`, `1/3`, or `2/3`) at a specified depth below the
largest kernel scale. -/
def finiteShiftGridInterval
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) : RealInterval :=
  translatedDyadicRealInterval
    ((shift : ℝ) * shiftedGridRootLength topScale / 3)
    (shiftedGridRootLength topScale) (shiftedGridRootLength_pos topScale) depth q

theorem finiteShiftGridInterval_length
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    (finiteShiftGridInterval topScale shift depth q).length =
      dyadicLength (shiftedGridRootLength topScale) depth :=
  translatedDyadicRealInterval_length _ _ _ _ _

/-- Each of the three finite shifted grids is laminar across all of its
represented scales. -/
theorem finiteShiftGridInterval_laminar
    (topScale : ℤ) (shift : Fin 3) (n : ℕ) (q : ℤ) (m : ℕ) (r : ℤ) :
    (finiteShiftGridInterval topScale shift n q).carrier ⊆
        (finiteShiftGridInterval topScale shift m r).carrier ∨
      (finiteShiftGridInterval topScale shift m r).carrier ⊆
          (finiteShiftGridInterval topScale shift n q).carrier ∨
        Disjoint (finiteShiftGridInterval topScale shift n q).carrier
          (finiteShiftGridInterval topScale shift m r).carrier :=
  translatedDyadicRealInterval_laminar (shiftedGridRootLength_pos topScale) n q m r

theorem finiteShiftGridInterval_parent_subset
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    (finiteShiftGridInterval topScale shift (depth + 1) q).carrier ⊆
      (finiteShiftGridInterval topScale shift depth (q / 2)).carrier :=
  translatedDyadicRealInterval_parent_subset
    (shiftedGridRootLength_pos topScale) depth q

theorem finiteShiftGridInterval_parent_length
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    (finiteShiftGridInterval topScale shift depth (q / 2)).length =
      2 * (finiteShiftGridInterval topScale shift (depth + 1) q).length := by
  rw [finiteShiftGridInterval_length, finiteShiftGridInterval_length,
    dyadicLength_succ]
  ring

/-- The consecutive central-third tile number represented by a grid address.
Multiplication by `2^depth` records the permutation of the three shifts when
the grid is refined. -/
def finiteShiftGridTileIndex (shift : Fin 3) (depth : ℕ) (q : ℤ) : ℤ :=
  3 * q + (shift : ℤ) * (2 : ℤ) ^ depth + 1

/-- At each depth, a three-shift interval is literally the parent used in the
fixed-scale central-third tiling. -/
theorem finiteShiftGridInterval_eq_centralThirdTileParent
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    finiteShiftGridInterval topScale shift depth q =
      KrauseLaceyShiftedLocalization.centralThirdTileParent
        (dyadicLength (shiftedGridRootLength topScale) depth)
        (dyadicLength_pos (shiftedGridRootLength_pos topScale) depth)
        (finiteShiftGridTileIndex shift depth q) := by
  unfold finiteShiftGridInterval translatedDyadicRealInterval
    finiteShiftGridTileIndex
    KrauseLaceyShiftedLocalization.centralThirdTileParent
  congr 1
  all_goals
    unfold dyadicLength
    push_cast
    field_simp
    ring

private theorem pow_two_even_three_mul_add_one (e : ℕ) :
    ∃ A : ℤ, (2 : ℤ) ^ (2 * e) = 3 * A + 1 := by
  induction e with
  | zero => exact ⟨0, by norm_num⟩
  | succ e ih =>
      rcases ih with ⟨A, hA⟩
      refine ⟨4 * A + 1, ?_⟩
      rw [show 2 * (e + 1) = 2 * e + 2 by omega, pow_add, hA]
      norm_num
      ring

private theorem pow_two_odd_three_mul_add_two (e : ℕ) :
    ∃ A : ℤ, (2 : ℤ) ^ (2 * e + 1) = 3 * A + 2 := by
  rcases pow_two_even_three_mul_add_one e with ⟨A, hA⟩
  refine ⟨2 * A, ?_⟩
  rw [pow_succ, hA]
  ring

/-- At every depth, the three translated grids exhaust all consecutive
central-third tile parents.  This is the integer content of the exact
three-grid identity in KL18. -/
theorem finiteShiftGridTileIndex_surjective (depth : ℕ) (n : ℤ) :
    ∃ shift : Fin 3, ∃ q : ℤ, finiteShiftGridTileIndex shift depth q = n := by
  let z : ℤ := n - 1
  have hz : z % 3 + 3 * (z / 3) = z := Int.emod_add_mul_ediv z 3
  have hznonneg : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
  have hzlt : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
  have hzcase : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases Nat.even_or_odd' depth with ⟨e, rfl | rfl⟩
  · rcases pow_two_even_three_mul_add_one e with ⟨A, hA⟩
    rcases hzcase with hzero | hone | htwo
    · refine ⟨⟨0, by omega⟩, z / 3, ?_⟩
      norm_num [finiteShiftGridTileIndex]
      omega
    · refine ⟨⟨1, by omega⟩, z / 3 - A, ?_⟩
      norm_num [finiteShiftGridTileIndex]
      omega
    · refine ⟨⟨2, by omega⟩, z / 3 - 2 * A, ?_⟩
      norm_num [finiteShiftGridTileIndex]
      omega
  · rcases pow_two_odd_three_mul_add_two e with ⟨A, hA⟩
    rcases hzcase with hzero | hone | htwo
    · refine ⟨⟨0, by omega⟩, z / 3, ?_⟩
      norm_num [finiteShiftGridTileIndex]
      omega
    · refine ⟨⟨2, by omega⟩, z / 3 - (2 * A + 1), ?_⟩
      norm_num [finiteShiftGridTileIndex]
      omega
    · refine ⟨⟨1, by omega⟩, z / 3 - A, ?_⟩
      norm_num [finiteShiftGridTileIndex]
      omega

/-- A tile address has a unique grid label and integer position. -/
theorem finiteShiftGridTileIndex_injective (depth : ℕ)
    {shift shift' : Fin 3} {q q' : ℤ}
    (h : finiteShiftGridTileIndex shift depth q =
      finiteShiftGridTileIndex shift' depth q') :
    shift = shift' ∧ q = q' := by
  rcases Nat.even_or_odd' depth with ⟨e, rfl | rfl⟩
  · rcases pow_two_even_three_mul_add_one e with ⟨A, hA⟩
    fin_cases shift <;> fin_cases shift' <;>
      norm_num [finiteShiftGridTileIndex] at h ⊢ <;> omega
  · rcases pow_two_odd_three_mul_add_two e with ⟨A, hA⟩
    fin_cases shift <;> fin_cases shift' <;>
      norm_num [finiteShiftGridTileIndex] at h ⊢ <;> omega

/-- The central thirds over all three grids at one depth are pairwise
disjoint, not merely disjoint up to null boundaries. -/
theorem finiteShiftGridCentralThird_pairwiseDisjoint
    (topScale : ℤ) (depth : ℕ) :
    Pairwise (Disjoint on fun p : Fin 3 × ℤ ↦
      (finiteShiftGridInterval topScale p.1 depth p.2).centralThird) := by
  rintro ⟨shift, q⟩ ⟨shift', q'⟩ hne
  change Disjoint
    (finiteShiftGridInterval topScale shift depth q).centralThird
    (finiteShiftGridInterval topScale shift' depth q').centralThird
  rw [finiteShiftGridInterval_eq_centralThirdTileParent,
    finiteShiftGridInterval_eq_centralThirdTileParent]
  apply KrauseLaceyShiftedLocalization.centralThirdTileParents_pairwiseDisjoint
  intro hindex
  rcases finiteShiftGridTileIndex_injective depth hindex with ⟨hs, hq⟩
  exact hne (Prod.ext hs hq)

/-- At every represented scale, the central thirds of the three shifted
grids cover every real point exactly once. -/
theorem existsUnique_mem_finiteShiftGridCentralThird
    (topScale : ℤ) (depth : ℕ) (x : ℝ) :
    ∃! p : Fin 3 × ℤ,
      x ∈ (finiteShiftGridInterval topScale p.1 depth p.2).centralThird := by
  let L := dyadicLength (shiftedGridRootLength topScale) depth
  have hL : 0 < L := dyadicLength_pos (shiftedGridRootLength_pos topScale) depth
  obtain ⟨n, hxn, hnunique⟩ :=
    KrauseLaceyShiftedLocalization.existsUnique_mem_centralThirdTileParent L hL x
  obtain ⟨shift, q, hindex⟩ := finiteShiftGridTileIndex_surjective depth n
  refine ⟨⟨shift, q⟩, ?_, ?_⟩
  · change x ∈ (finiteShiftGridInterval topScale shift depth q).centralThird
    rw [finiteShiftGridInterval_eq_centralThirdTileParent, hindex]
    exact hxn
  · rintro ⟨shift', q'⟩ hx'
    have hindex' : finiteShiftGridTileIndex shift' depth q' = n := by
      apply hnunique
      change x ∈ (KrauseLaceyShiftedLocalization.centralThirdTileParent L hL
        (finiteShiftGridTileIndex shift' depth q')).centralThird
      rw [← finiteShiftGridInterval_eq_centralThirdTileParent]
      exact hx'
    rcases finiteShiftGridTileIndex_injective depth (hindex'.trans hindex.symm) with
      ⟨hs, hq⟩
    exact Prod.ext hs hq

/-- Addresses of the complete finite descendant tree below `q₀`, down to
depth `maxDepth`. -/
noncomputable def completeDescendantIndices
    (maxDepth : ℕ) (q₀ : ℤ) : Finset (ℕ × ℤ) := by
  classical
  exact (Finset.range (maxDepth + 1)).biUnion fun depth ↦
    (Finset.Icc (q₀ * (2 : ℤ) ^ depth)
      ((q₀ + 1) * (2 : ℤ) ^ depth - 1)).image fun q ↦ (depth, q)

theorem mem_completeDescendantIndices_iff
    {maxDepth depth : ℕ} {q₀ q : ℤ} :
    (depth, q) ∈ completeDescendantIndices maxDepth q₀ ↔
      depth ≤ maxDepth ∧
        q₀ * (2 : ℤ) ^ depth ≤ q ∧
        q ≤ (q₀ + 1) * (2 : ℤ) ^ depth - 1 := by
  classical
  simp only [completeDescendantIndices, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨d, hd, q', hq', heq⟩
    cases heq
    exact ⟨by omega, hq'⟩
  · rintro ⟨hd, hq⟩
    exact ⟨depth, by omega, q, hq, rfl⟩

theorem root_mem_completeDescendantIndices (maxDepth : ℕ) (q₀ : ℤ) :
    (0, q₀) ∈ completeDescendantIndices maxDepth q₀ := by
  rw [mem_completeDescendantIndices_iff]
  norm_num

/-- Every positive-depth node in the complete finite tree has its Euclidean
dyadic parent in the same tree. -/
theorem parent_mem_completeDescendantIndices
    {maxDepth depth : ℕ} {q₀ q : ℤ}
    (hmem : (depth, q) ∈ completeDescendantIndices maxDepth q₀)
    (hdepth : 0 < depth) :
    (depth - 1, q / 2) ∈ completeDescendantIndices maxDepth q₀ := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdepth)
  rw [mem_completeDescendantIndices_iff] at hmem ⊢
  have hp : (2 : ℤ) ^ (e + 1) = 2 * (2 : ℤ) ^ e := by
    rw [pow_succ]
    ring
  let a : ℤ := q₀ * (2 : ℤ) ^ e
  let b : ℤ := (q₀ + 1) * (2 : ℤ) ^ e
  have hlo : 2 * a ≤ q := by
    dsimp [a]
    convert hmem.2.1 using 1 <;> rw [hp] <;> ring
  have hhi : q ≤ 2 * b - 1 := by
    dsimp [b]
    convert hmem.2.2 using 1 <;> rw [hp] <;> ring
  have hdecomp : q % 2 + 2 * (q / 2) = q := Int.emod_add_mul_ediv q 2
  have hrem0 : 0 ≤ q % 2 := Int.emod_nonneg q (by norm_num)
  have hrem2 : q % 2 < 2 := Int.emod_lt_of_pos q (by norm_num)
  constructor
  · omega
  constructor <;> dsimp [a, b] <;> omega

/-- The complete finite interval tree in one of the three shifted grids. -/
noncomputable def completeFiniteShiftGridTree
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ) :
    Finset RealInterval := by
  classical
  exact (completeDescendantIndices maxDepth q₀).image fun p ↦
    finiteShiftGridInterval topScale shift p.1 p.2

theorem root_mem_completeFiniteShiftGridTree
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ) :
    finiteShiftGridInterval topScale shift 0 q₀ ∈
      completeFiniteShiftGridTree topScale shift maxDepth q₀ := by
  classical
  apply Finset.mem_image.2
  exact ⟨(0, q₀), root_mem_completeDescendantIndices maxDepth q₀, rfl⟩


end
end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
