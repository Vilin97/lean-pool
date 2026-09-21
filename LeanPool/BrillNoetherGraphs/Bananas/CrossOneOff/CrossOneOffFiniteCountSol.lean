/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiniteRows
import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointCardinality
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffForcedCountLengthTwo

/-!
# Explicit coordinates for the corrected cross-one-off inversion count

This module reparametrizes the finite rows by `x = b - b / n`.  The preferred
row over `x` is `x + x / (n - 1)`; at multiples of `n - 1` there is also the
immediately preceding row.  This is the combinatorial skeleton behind the
count `choose (g - 1) 2 + g / (n - 1)`.
-/

namespace Bananas

open Utilities

/-- The preferred row with compressed coordinate `x`. -/
def crossOneOffColumnPosition (n x : ℕ) : ℕ :=
  x + x / (n - 1)

/-- A row strictly before the preferred row over `x`, chosen so that it is
never a multiple of `n`.  At a multiple of `n-1` it is the exceptional
`-1`-residue row; otherwise it is the preferred row itself. -/
def crossOneOffPredecessorPosition (n x : ℕ) : ℕ :=
  if x % (n - 1) = 0 then crossOneOffColumnPosition n x - 1
  else crossOneOffColumnPosition n x

theorem crossOneOffColumnPosition_div
    {n x : ℕ} (hn : 2 ≤ n) :
    crossOneOffColumnPosition n x / n = x / (n - 1) := by
  let q := x / (n - 1)
  let r := x % (n - 1)
  have hd : 0 < n - 1 := by omega
  have hr : r < n - 1 := by
    dsimp [r]
    exact Nat.mod_lt x hd
  have hx : x = q * (n - 1) + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod x (n - 1)).symm
  have hpos : crossOneOffColumnPosition n x = q * n + r := by
    unfold crossOneOffColumnPosition
    change x + q = q * n + r
    rw [hx]
    calc
      q * (n - 1) + r + q = q * ((n - 1) + 1) + r := by ring
      _ = q * n + r := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hpos]
  change (q * n + r) / n = q
  simpa [Nat.add_comm, Nat.mul_comm, Nat.div_eq_of_lt (by omega : r < n)] using
    (Nat.add_mul_div_left r q (by omega : 0 < n))

theorem crossOneOffColumnPosition_mod
    {n x : ℕ} (hn : 2 ≤ n) :
    crossOneOffColumnPosition n x % n = x % (n - 1) := by
  let q := x / (n - 1)
  let r := x % (n - 1)
  have hd : 0 < n - 1 := by omega
  have hr : r < n - 1 := by
    dsimp [r]
    exact Nat.mod_lt x hd
  have hx : x = q * (n - 1) + r := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod x (n - 1)).symm
  have hpos : crossOneOffColumnPosition n x = q * n + r := by
    unfold crossOneOffColumnPosition
    change x + q = q * n + r
    rw [hx]
    calc
      q * (n - 1) + r + q = q * ((n - 1) + 1) + r := by ring
      _ = q * n + r := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hpos]
  change (q * n + r) % n = r
  rw [Nat.mul_comm q n, Nat.add_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by omega : r < n)]

theorem crossOneOffColumnPosition_decode
    {n x : ℕ} (hn : 2 ≤ n) :
    crossOneOffColumnPosition n x - crossOneOffColumnPosition n x / n = x := by
  rw [crossOneOffColumnPosition_div hn]
  simp only [crossOneOffColumnPosition]
  omega

theorem crossOneOffColumnPosition_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (crossOneOffColumnPosition n) := by
  intro x y hxy
  have := congrArg (fun b : ℕ => b - b / n) hxy
  simpa [crossOneOffColumnPosition_decode hn] using this

theorem crossOneOffPredecessorPosition_decode
    {n x : ℕ} (hn : 2 ≤ n) (hx : 2 ≤ x) :
    crossOneOffPredecessorPosition n x -
        crossOneOffPredecessorPosition n x / n = x := by
  by_cases hr : x % (n - 1) = 0
  · let q := x / (n - 1)
    have hd : 0 < n - 1 := by omega
    have hxq : x = q * (n - 1) := by
      dsimp [q]
      simpa [hr, Nat.mul_comm] using (Nat.div_add_mod x (n - 1)).symm
    have hq : 1 ≤ q := by
      by_contra h
      have : q = 0 := Nat.eq_zero_of_not_pos h
      rw [this] at hxq
      omega
    have hcol : crossOneOffColumnPosition n x = q * n := by
      unfold crossOneOffColumnPosition
      change x + q = q * n
      rw [hxq]
      calc
        q * (n - 1) + q = q * ((n - 1) + 1) := by ring
        _ = q * n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have hpre : crossOneOffPredecessorPosition n x = q * n - 1 := by
      simp [crossOneOffPredecessorPosition, hr, hcol]
    have hsplit : q * n = (q - 1) * n + n := by
      calc
        q * n = ((q - 1) + 1) * n := by rw [Nat.sub_add_cancel hq]
        _ = (q - 1) * n + n := by ring
    have hdiv : (q * n - 1) / n = q - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [hsplit]
        omega
      · rw [Nat.sub_add_cancel hq]
        have hqn : 0 < q * n := Nat.mul_pos (by omega) (by omega)
        omega
    rw [hpre, hdiv]
    have hxq' : x = q * n - q := by
      rw [hxq]
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hqle : q ≤ q * n := by
      exact Nat.le_mul_of_pos_right q (by omega)
    omega
  · rw [crossOneOffPredecessorPosition, if_neg hr]
    exact crossOneOffColumnPosition_decode hn

theorem crossOneOffPredecessorPosition_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Set.InjOn (crossOneOffPredecessorPosition n) (Set.Ici 2) := by
  intro x hx y hy hxy
  have h := congrArg (fun b : ℕ => b - b / n) hxy
  simpa [crossOneOffPredecessorPosition_decode hn hx,
    crossOneOffPredecessorPosition_decode hn hy] using h

theorem crossOneOffColumnPosition_strictMono {n : ℕ} (_hn : 2 ≤ n) :
    StrictMono (crossOneOffColumnPosition n) := by
  intro x y hxy
  unfold crossOneOffColumnPosition
  have hdiv : x / (n - 1) ≤ y / (n - 1) :=
    Nat.div_le_div_right hxy.le
  omega

theorem crossOneOffPredecessorPosition_lt_column
    {n x y : ℕ} (hn : 2 ≤ n) (hyx : y < x) :
    crossOneOffPredecessorPosition n y < crossOneOffColumnPosition n x := by
  have hle : crossOneOffPredecessorPosition n y ≤
      crossOneOffColumnPosition n y := by
    unfold crossOneOffPredecessorPosition
    split <;> omega
  exact hle.trans_lt (crossOneOffColumnPosition_strictMono hn hyx)

theorem crossOneOffColumnPosition_le_cutoff
    {g n x : ℕ} (_hn : 2 ≤ n) (hxg : x ≤ g) :
    crossOneOffColumnPosition n x ≤ crossOneOffCutoff g n := by
  unfold crossOneOffColumnPosition crossOneOffCutoff
  have hdiv : x / (n - 1) ≤ g / (n - 1) :=
    Nat.div_le_div_right hxg
  omega

theorem crossOneOffColumnPosition_row
    {g n x : ℕ} (hn : 2 ≤ n) (hxg : x ≤ g) :
    crossOneOffRow g n (crossOneOffColumnPosition n x) =
      if x % (n - 1) = 0 then x / (n - 1) + 1
      else g + x / (n - 1) + 2 - x := by
  have hmod := crossOneOffColumnPosition_mod (n := n) (x := x) hn
  have hdiv := crossOneOffColumnPosition_div (n := n) (x := x) hn
  have hrlt : x % (n - 1) < n - 1 :=
    Nat.mod_lt x (by omega)
  by_cases hr : x % (n - 1) = 0
  · simp [crossOneOffRow, hmod, hdiv, hr]
  · have hlast : x % (n - 1) ≠ n - 1 := by omega
    rw [crossOneOffRow, if_neg (by simpa [hmod] using hr),
      if_neg (by simpa [hmod] using hlast), if_neg hr, hdiv]
    unfold crossOneOffColumnPosition
    omega

theorem crossOneOffPredecessorPosition_row
    {g n x : ℕ} (hn : 3 ≤ n) (hx : 2 ≤ x) (hxg : x ≤ g) :
    crossOneOffRow g n (crossOneOffPredecessorPosition n x) =
      if x % (n - 1) = 0 then g + x / (n - 1)
      else g + x / (n - 1) + 2 - x := by
  by_cases hr : x % (n - 1) = 0
  · let q := x / (n - 1)
    have hxq : x = q * (n - 1) := by
      dsimp [q]
      simpa [hr, Nat.mul_comm] using
        (Nat.div_add_mod x (n - 1)).symm
    have hq : 1 ≤ q := by
      by_contra h
      have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
      rw [hq0] at hxq
      omega
    have hcol : crossOneOffColumnPosition n x = q * n := by
      unfold crossOneOffColumnPosition
      change x + q = q * n
      rw [hxq]
      calc
        q * (n - 1) + q = q * ((n - 1) + 1) := by ring
        _ = q * n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have hpre : crossOneOffPredecessorPosition n x = q * n - 1 := by
      simp [crossOneOffPredecessorPosition, hr, hcol]
    have hpre' : q * n - 1 = (q - 1) * n + (n - 1) := by
      have hsplit : q * n = (q - 1) * n + n := by
        calc
          q * n = ((q - 1) + 1) * n := by rw [Nat.sub_add_cancel hq]
          _ = (q - 1) * n + n := by ring
      omega
    have hrem : (q * n - 1) % n = n - 1 := by
      rw [hpre', Nat.add_mod]
      simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have hquot : (q * n - 1) / n = q - 1 := by
      rw [hpre']
      simpa [Nat.add_comm, Nat.mul_comm,
        Nat.div_eq_of_lt (by omega : n - 1 < n)] using
        (Nat.add_mul_div_left (n - 1) (q - 1) (by omega : 0 < n))
    rw [if_pos hr, hpre, crossOneOffRow,
      if_neg (by rw [hrem]; omega : (q * n - 1) % n ≠ 0),
      if_pos hrem, hquot]
    omega
  · rw [if_neg hr, crossOneOffPredecessorPosition, if_neg hr]
    rw [crossOneOffColumnPosition_row (by omega) hxg, if_neg hr]

private theorem nat_div_le_div_add_sub
    {d x y : ℕ} (_hd : 1 ≤ d) (hyx : y ≤ x) :
    x / d ≤ y / d + (x - y) := by
  induction x, hyx using Nat.le_induction with
  | base => simp
  | succ x hyx ih =>
      rw [Nat.succ_div]
      split <;> omega

private theorem nat_div_lt_div_add_sub_of_mod_ne_zero
    {d x y : ℕ} (hd : 1 ≤ d) (hyx : y < x)
    (hxMod : x % d ≠ 0) :
    x / d < y / d + (x - y) := by
  let z := x - 1
  have hx : x = z + 1 := by dsimp [z]; omega
  have hyz : y ≤ z := by dsimp [z]; omega
  have hDiv := nat_div_le_div_add_sub hd hyz
  have hNotDvd : ¬ d ∣ z + 1 := by
    intro hDvd
    apply hxMod
    rw [hx]
    exact Nat.mod_eq_zero_of_dvd hDvd
  rw [hx, Nat.succ_div, if_neg hNotDvd]
  omega

/-- A predecessor row at compressed coordinate `y` and a column row at a
larger compressed coordinate `x` form one of the forced inversions. -/
theorem crossOneOff_predecessor_column_mem
    {g n y x : ℕ} (hn : 3 ≤ n) (hy : 2 ≤ y)
    (hyx : y < x) (hxg : x ≤ g) :
    (crossOneOffPredecessorPosition n y,
        crossOneOffColumnPosition n x) ∈
      crossOneOffForcedInversionPairs g n := by
  have hyDiv : y % (n - 1) = 0 → n - 1 ≤ y := by
    intro hry
    exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hry)
  have hPreLo : 2 ≤ crossOneOffPredecessorPosition n y := by
    unfold crossOneOffPredecessorPosition
    split
    · have hqPos : 1 ≤ y / (n - 1) := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < n - 1)).2
        simpa using hyDiv (by assumption)
      unfold crossOneOffColumnPosition
      omega
    · unfold crossOneOffColumnPosition
      exact hy.trans (Nat.le_add_right y _)
  have hColLo : 2 ≤ crossOneOffColumnPosition n x := by
    have hx : 2 ≤ x := hy.trans hyx.le
    unfold crossOneOffColumnPosition
    exact hx.trans (Nat.le_add_right x _)
  have hColHi : crossOneOffColumnPosition n x ≤
      crossOneOffCutoff g n :=
    crossOneOffColumnPosition_le_cutoff (by omega) hxg
  have hPreHi : crossOneOffPredecessorPosition n y ≤
      crossOneOffCutoff g n := by
    exact (crossOneOffPredecessorPosition_lt_column (by omega) hyx).le.trans hColHi
  have hOrder : crossOneOffPredecessorPosition n y <
      crossOneOffColumnPosition n x :=
    crossOneOffPredecessorPosition_lt_column (by omega) hyx
  have hPreRow := crossOneOffPredecessorPosition_row
    (g := g) (n := n) (x := y) hn hy (hyx.le.trans hxg)
  have hColRow := crossOneOffColumnPosition_row
    (g := g) (n := n) (x := x) (by omega) hxg
  have hDivGap : x / (n - 1) ≤
      y / (n - 1) + (x - y) :=
    nat_div_le_div_add_sub (by omega) hyx.le
  have hYSub : g + y / (n - 1) + 2 - y + y =
      g + y / (n - 1) + 2 := by
    apply Nat.sub_add_cancel
    have hyG : y ≤ g := hyx.le.trans hxg
    have hg : g ≤ g + (y / (n - 1) + 2) := Nat.le_add_right _ _
    simpa [Nat.add_assoc] using hyG.trans hg
  have hXSub : g + x / (n - 1) + 2 - x + x =
      g + x / (n - 1) + 2 := by
    apply Nat.sub_add_cancel
    have hg : g ≤ g + (x / (n - 1) + 2) := Nat.le_add_right _ _
    simpa [Nat.add_assoc] using hxg.trans hg
  have hRow : crossOneOffRow g n (crossOneOffPredecessorPosition n y) >
      crossOneOffRow g n (crossOneOffColumnPosition n x) := by
    rw [hPreRow, hColRow]
    by_cases hry : y % (n - 1) = 0
    · rw [if_pos hry]
      have hqyPos : 1 ≤ y / (n - 1) := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < n - 1)).2
        simpa using hyDiv hry
      by_cases hrx : x % (n - 1) = 0
      · rw [if_pos hrx]
        have hqxLt : x / (n - 1) < g := by
          have hxPos : 0 < x := by omega
          have := Nat.div_lt_self hxPos (by omega : 1 < n - 1)
          omega
        omega
      · rw [if_neg hrx]
        have hDivGapStrict : x / (n - 1) <
            y / (n - 1) + (x - y) := by
          exact nat_div_lt_div_add_sub_of_mod_ne_zero
            (by omega) hyx hrx
        have hCross : x / (n - 1) + y <
            y / (n - 1) + x := by omega
        omega
    · rw [if_neg hry]
      by_cases hrx : x % (n - 1) = 0
      · rw [if_pos hrx]
        have hqxLt : x / (n - 1) < g := by
          have hxPos : 0 < x := by omega
          have := Nat.div_lt_self hxPos (by omega : 1 < n - 1)
          omega
        have hLower : x / (n - 1) + 2 ≤
            g + y / (n - 1) + 2 - y := by
          apply Nat.le_sub_of_add_le
          omega
        omega
      · rw [if_neg hrx]
        have hDivGapStrict : x / (n - 1) <
            y / (n - 1) + (x - y) := by
          exact nat_div_lt_div_add_sub_of_mod_ne_zero
            (by omega) hyx hrx
        have hCross : x / (n - 1) + y <
            y / (n - 1) + x := by omega
        omega
  rw [crossOneOffForcedInversionPairs, finiteRowInversionPairs,
    Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hPreLo, hPreHi⟩,
      Finset.mem_Icc.mpr ⟨hColLo, hColHi⟩⟩,
    hOrder, hRow⟩

/-- The triangular family of inversions indexed by unordered pairs in
`{2, ..., g-1}`. -/
noncomputable def crossOneOffTriangularPair (n g : ℕ) :
    Sym2 (Fin (g - 2)) → ℕ × ℕ :=
  Sym2.lift ⟨fun a b =>
    (crossOneOffPredecessorPosition n (min a.val b.val + 2),
      crossOneOffColumnPosition n (max a.val b.val + 3)), by
        intro a b
        simp [min_comm, max_comm]⟩

theorem crossOneOffTriangularPair_injective
    {n g : ℕ} (hn : 2 ≤ n) :
    Function.Injective (crossOneOffTriangularPair n g) := by
  intro x y hxy
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [crossOneOffTriangularPair, Sym2.lift_mk,
        Prod.mk.injEq] at hxy
      have hMin : min a.val b.val = min c.val d.val := by
        have h := crossOneOffPredecessorPosition_injective hn
          (by simp : min a.val b.val + 2 ∈ Set.Ici 2)
          (by simp : min c.val d.val + 2 ∈ Set.Ici 2) hxy.1
        omega
      have hMax : max a.val b.val = max c.val d.val := by
        have h := crossOneOffColumnPosition_injective hn hxy.2
        omega
      apply endpointPairEmbedding_injective (g - 2)
      simp only [endpointPairEmbedding, Sym2.lift_mk, Prod.mk.injEq]
      exact ⟨by exact_mod_cast hMin,
        by exact_mod_cast congrArg Nat.succ hMax⟩

private theorem crossOneOffTriangularPair_mem
    {g n : ℕ} (hn : 3 ≤ n) (x : Sym2 (Fin (g - 2))) :
    crossOneOffTriangularPair n g x ∈
      crossOneOffForcedInversionPairs g n := by
  induction x using Sym2.ind with
  | _ a b =>
    let y := min a.val b.val + 2
    let x := max a.val b.val + 3
    change (crossOneOffPredecessorPosition n y,
      crossOneOffColumnPosition n x) ∈
        crossOneOffForcedInversionPairs g n
    have hy : 2 ≤ y := by simp [y]
    have hyx : y < x := by
      dsimp [y, x]
      omega
    have hxg : x ≤ g := by
      dsimp [x]
      have hMax : max a.val b.val < g - 2 := max_lt a.isLt b.isLt
      omega
    exact crossOneOff_predecessor_column_mem hn hy hyx hxg

/-- The additional adjacent high-to-low inversion over the `i`th complete
column. -/
def crossOneOffAdjacentPair (n : ℕ) (i : ℕ) : ℕ × ℕ :=
  ((i + 1) * n - 1, (i + 1) * n)

theorem crossOneOffAdjacentPair_injective
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (crossOneOffAdjacentPair n) := by
  intro i j hij
  have hSecond := congrArg Prod.snd hij
  change (i + 1) * n = (j + 1) * n at hSecond
  have := Nat.mul_right_cancel hn hSecond
  omega

private theorem crossOneOffAdjacentPair_mem
    {g n F : ℕ} (hg : 2 ≤ g) (hn : 3 ≤ n)
    (hF : F = g / (n - 1)) (i : Fin F) :
    crossOneOffAdjacentPair n i.val ∈
      crossOneOffForcedInversionPairs g n := by
  let q := i.val + 1
  have hq : q ≤ F := by dsimp [q]; omega
  have hMul : F * (n - 1) ≤ g := by
    rw [hF]
    exact Nat.div_mul_le_self g (n - 1)
  have hnEq : n = (n - 1) + 1 := by omega
  have hFn : F * n ≤ g + F := by
    rw [hnEq, Nat.mul_add, Nat.mul_one]
    omega
  have hqn : q * n ≤ g + F :=
    (Nat.mul_le_mul_right n hq).trans hFn
  have hRem : (q * n - 1) % n = n - 1 := by
    have hqPos : 1 ≤ q := by simp [q]
    have hSplit : q * n - 1 = (q - 1) * n + (n - 1) := by
      have hBase : q * n = (q - 1) * n + n := by
        calc
          q * n = ((q - 1) + 1) * n := by rw [Nat.sub_add_cancel hqPos]
          _ = (q - 1) * n + n := by ring
      omega
    rw [hSplit, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  have hQuot : (q * n - 1) / n = q - 1 := by
    have hqPos : 1 ≤ q := by simp [q]
    have hSplit : q * n - 1 = (q - 1) * n + (n - 1) := by
      have hBase : q * n = (q - 1) * n + n := by
        calc
          q * n = ((q - 1) + 1) * n := by rw [Nat.sub_add_cancel hqPos]
          _ = (q - 1) * n + n := by ring
      omega
    rw [hSplit]
    simpa [Nat.add_comm, Nat.mul_comm,
      Nat.div_eq_of_lt (by omega : n - 1 < n)] using
      (Nat.add_mul_div_left (n - 1) (q - 1) (by omega : 0 < n))
  have hHighRow : crossOneOffRow g n (q * n - 1) = g + q := by
    rw [crossOneOffRow, if_neg (by rw [hRem]; omega), if_pos hRem, hQuot]
    omega
  have hLowRow : crossOneOffRow g n (q * n) = q + 1 := by
    simp [crossOneOffRow, Nat.mul_div_left q (by omega : 0 < n)]
  have hnLe : n ≤ q * n :=
    Nat.le_mul_of_pos_left n (by simp [q] : 0 < q)
  have hPreLo : 2 ≤ q * n - 1 := by omega
  have hLowLo : 2 ≤ q * n := by omega
  change (q * n - 1, q * n) ∈ crossOneOffForcedInversionPairs g n
  rw [crossOneOffForcedInversionPairs,
    finiteRowInversionPairs, Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
    Finset.mem_Icc.mpr ?_⟩, ?_⟩
  · exact ⟨hPreLo,
      by simpa [crossOneOffCutoff, hF] using (Nat.sub_le (q * n) 1).trans hqn⟩
  · exact ⟨hLowLo,
      by simpa [crossOneOffCutoff, hF] using hqn⟩
  · refine ⟨by omega, ?_⟩
    rw [hHighRow, hLowRow]
    omega

/-- The two disjoint families used in the corrected count. -/
abbrev CrossOneOffCountDomain (g F : ℕ) :=
  Sum (Sym2 (Fin (g - 2))) (Fin F)

noncomputable def crossOneOffCountPair (n g F : ℕ) :
    CrossOneOffCountDomain g F → ℕ × ℕ
  | Sum.inl x => crossOneOffTriangularPair n g x
  | Sum.inr i => crossOneOffAdjacentPair n i.val

private theorem crossOneOffTriangularPair_ne_adjacentPair
    {n g F : ℕ} (hn : 3 ≤ n) (s : Sym2 (Fin (g - 2))) (j : Fin F) :
    crossOneOffTriangularPair n g s ≠ crossOneOffAdjacentPair n j.val := by
  intro hEq
  induction s using Sym2.ind with
  | _ a b =>
    let y := min a.val b.val + 2
    let x := max a.val b.val + 3
    let z := (j.val + 1) * (n - 1)
    have hz : 2 ≤ z := by
      have hOne : 1 ≤ j.val + 1 := by omega
      have hTwo : 2 ≤ n - 1 := by omega
      simpa [z] using Nat.mul_le_mul hOne hTwo
    have hzMod : z % (n - 1) = 0 := by
      dsimp [z]
      simp
    have hColZ : crossOneOffColumnPosition n z = (j.val + 1) * n := by
      have hDiv : z / (n - 1) = j.val + 1 := by
        dsimp [z]
        exact Nat.mul_div_left (j.val + 1) (by omega)
      unfold crossOneOffColumnPosition
      rw [hDiv]
      dsimp [z]
      have hProduct : (j.val + 1) * n =
          (j.val + 1) * (n - 1) + (j.val + 1) := by
        calc
          (j.val + 1) * n = (j.val + 1) * ((n - 1) + 1) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
          _ = (j.val + 1) * (n - 1) + (j.val + 1) := by ring
      exact hProduct.symm
    have hPreZ : crossOneOffPredecessorPosition n z =
        (j.val + 1) * n - 1 := by
      simp [crossOneOffPredecessorPosition, hzMod, hColZ]
    simp only [crossOneOffTriangularPair, Sym2.lift_mk,
      crossOneOffAdjacentPair, Prod.mk.injEq] at hEq
    have hXEq : x = z := by
      apply crossOneOffColumnPosition_injective (n := n) (by omega)
      simpa [x, hColZ] using hEq.2
    have hYEq : y = z := by
      apply crossOneOffPredecessorPosition_injective (n := n) (by omega)
      · simp [y]
      · exact hz
      · simpa [y, hPreZ] using hEq.1
    have hyx : y < x := by dsimp [y, x]; omega
    omega

theorem crossOneOffCountPair_injective
    {n g F : ℕ} (hn : 3 ≤ n) :
    Function.Injective (crossOneOffCountPair n g F) := by
  intro x y hxy
  rcases x with x | i <;> rcases y with y | j
  · exact congrArg Sum.inl (crossOneOffTriangularPair_injective
      (by omega) hxy)
  · exact (crossOneOffTriangularPair_ne_adjacentPair hn x j hxy).elim
  · exact (crossOneOffTriangularPair_ne_adjacentPair hn y i hxy.symm).elim
  · apply congrArg Sum.inr
    apply Fin.ext
    exact crossOneOffAdjacentPair_injective (by omega) hxy

/-- Corrected finite forced-row count for strand lengths at least three. -/
theorem correctedCrossOneOffForcedCount_le_card_of_three_le
    {g n : ℕ} (hg : 2 ≤ g) (hn : 3 ≤ n) :
    correctedCrossOneOffForcedCount g n ≤
      (crossOneOffForcedInversionPairs g n).card := by
  let F := g / (n - 1)
  have hmap : ∀ x : CrossOneOffCountDomain g F, x ∈ Set.univ →
      crossOneOffCountPair n g F x ∈
        (crossOneOffForcedInversionPairs g n : Set (ℕ × ℕ)) := by
    intro x _
    rcases x with x | i
    · exact crossOneOffTriangularPair_mem hn x
    · exact crossOneOffAdjacentPair_mem hg hn rfl i
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (Set.univ : Set (CrossOneOffCountDomain g F)))
    (t := (crossOneOffForcedInversionPairs g n : Set (ℕ × ℕ)))
    (crossOneOffCountPair n g F) hmap
    (crossOneOffCountPair_injective hn).injOn
    (crossOneOffForcedInversionPairs g n).finite_toSet
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  change Fintype.card (CrossOneOffCountDomain g F) ≤ _ at hle
  have hDomainCard : Fintype.card (CrossOneOffCountDomain g F) =
      Nat.choose (g - 1) 2 + F := by
    simp only [CrossOneOffCountDomain, Fintype.card_sum, Fintype.card_fin]
    rw [show Fintype.card (Sym2 (Fin (g - 2))) =
      Nat.choose (g - 2 + 1) 2 by
        change (Finset.univ : Finset (Sym2 (Fin (g - 2)))).card = _
        rw [← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ]
        simp only [Fintype.card_fin]]
    congr 2
    omega
  rw [hDomainCard] at hle
  simpa [correctedCrossOneOffForcedCount, F, show n ≠ 2 by omega] using hle

/-- Pure arithmetic certificate requested by the corrected Corollary 4.31,
valid for every strand length at least two. -/
theorem correctedCrossOneOffForcedCount_le_card
    {g n : ℕ} (hg : 2 ≤ g) (hn : 2 ≤ n) :
    correctedCrossOneOffForcedCount g n ≤
      (crossOneOffForcedInversionPairs g n).card := by
  by_cases hnTwo : n = 2
  · subst n
    exact correctedCrossOneOffForcedCount_le_card_length_two hg
  · exact correctedCrossOneOffForcedCount_le_card_of_three_le hg (by omega)

end Bananas
