/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.OneOffPeriodBound
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiniteRows
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffFiniteCountSol
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI

/-!
# The refined same-strand one-off inversion count

This proves paper Proposition 4.25.  If `n` is the length of the marked
strand and `f = floor(g/(n-1))`, the paper's auxiliary quantity `h` is
actually `g-f`.  Consequently its displayed lower bound simplifies to

`choose g 2 + f`.

The proof uses the paper's compressed coordinate `x = b - floor(b/n)`.
There is one preferred row over every `1 <= x <= g`, and an additional row
immediately before it whenever `(n-1) | x`.  Every ordered pair of compressed
coordinates gives an inversion, as does each additional adjacent pair.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- The three rows in Lemma 4.23, written as one finite row function. -/
def oneOffRow (g n b : ℕ) : ℕ :=
  if b % n = 0 then b / n
  else if b % n = n - 1 then g + b / n + 1
  else g + 2 * (b / n) + 1 - b

/-- Lemma 4.23, uniformly over its full integral cutoff interval. -/
theorem transmission_oneOff_block
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b : ℕ) (tau : ℤ → ℤ) (hg : 2 ≤ g)
    (hLength : 1 < B.length alpha)
    (_hbLo : 1 ≤ b) (hbHi : b ≤ crossOneOffCutoff g (B.length alpha))
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (oneOffRow g (B.length alpha) b : ℕ) := by
  let n := B.length alpha
  let m := b / n
  let r := b % n
  have hn : 1 < n := by simpa [n] using hLength
  have hnPos : 0 < n := by omega
  have hrLt : r < n := by
    dsimp [r]
    exact Nat.mod_lt b hnPos
  have hDecompose : b = m * n + r := by
    dsimp [m, n, r]
    simpa [Nat.mul_comm] using (Nat.div_add_mod b (B.length alpha)).symm
  have hGap : b - m ≤ g := by
    simpa [m, n] using crossOneOff_sub_div_le_genus hn hbHi
  have hmLeB : m ≤ b := Nat.div_le_self b n
  have hbm : b ≤ g + m := by omega
  by_cases hrZero : r = 0
  · have hbMultiple : b = m * B.length alpha := by
      simpa [n, hrZero] using hDecompose
    have hRow := transmission_oneOff_multiple B alpha b m tau hLength
      hbMultiple hbm hTau
    simpa [oneOffRow, r, n, m, hrZero] using hRow
  · by_cases hrLast : r = n - 1
    · let mp := m + 1
      have hbComplement : b + 1 = mp * B.length alpha := by
        rw [show B.length alpha = n by rfl]
        calc
          b + 1 = (m * n + (n - 1)) + 1 := by rw [hDecompose, hrLast]
          _ = m * n + n := by omega
          _ = (m + 1) * n := by rw [Nat.add_mul, one_mul]
          _ = mp * n := by rfl
      have hRow := transmission_oneOff_complement B alpha b mp tau
        (by omega) hLength (by simp [mp]) hbComplement (by
          dsimp [mp]
          omega) hTau
      have hnPredNe : n - 1 ≠ 0 := by omega
      have hTarget : oneOffRow g n b = g + m + 1 := by
        simp [oneOffRow, r, hrLast, hnPredNe, m, n]
      change tau (b : ℤ) = (oneOffRow g n b : ℕ)
      rw [hTarget, hRow]
      dsimp [mp]
      ring
    · have hrLo : 1 ≤ r := Nat.pos_of_ne_zero hrZero
      have hrHi : r + 1 < n := by omega
      have hRow := transmission_oneOff_positive_residue B alpha b m r tau
        hg hLength (by simpa [n] using hDecompose) hrLo hrHi hbm hTau
      simpa [oneOffRow, r, n, m, hrZero, hrLast] using hRow

/-- The finite set of ordinary inversions visible in Lemma 4.23's block. -/
def oneOffForcedInversionPairs (g n : ℕ) : Finset (ℕ × ℕ) :=
  finiteRowInversionPairs 1 (crossOneOffCutoff g n) (oneOffRow g n)

/-- Every forced finite-row inversion is a normalized affine inversion.
Lemma 4.23's period conclusion supplies the required separation. -/
theorem oneOff_forcedInversionPairs_card_le
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (tau : ℤ → ℤ) (hg : 2 ≤ g) (hk : 0 < k)
    (hLength : 1 < B.length alpha)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hAffine : IsKAffine k tau)
    (hfinite : (kInversions k tau).Finite) :
    (oneOffForcedInversionPairs g (B.length alpha)).card ≤
      kInversionCount k tau := by
  apply finiteRowInversionPairs_card_le_kInversionCount
    (lo := 1) (hi := crossOneOffCutoff g (B.length alpha))
    (row := oneOffRow g (B.length alpha)) (tau := tau)
  · intro b hbLo hbHi
    exact transmission_oneOff_block B alpha b tau hg hLength hbLo hbHi hTau
  · exact (oneOff_affine_period_gt_cutoff B alpha tau hg hk hLength
      hTau hAffine).le
  · exact hfinite

/-! ## Compressed-row arithmetic -/

theorem oneOffColumnPosition_row
    {g n x : ℕ} (hn : 2 ≤ n) (hxg : x ≤ g) :
    oneOffRow g n (crossOneOffColumnPosition n x) =
      if x % (n - 1) = 0 then x / (n - 1)
      else g + x / (n - 1) + 1 - x := by
  have hmod := crossOneOffColumnPosition_mod (n := n) (x := x) hn
  have hdiv := crossOneOffColumnPosition_div (n := n) (x := x) hn
  have hrLt := Nat.mod_lt x (by omega : 0 < n - 1)
  by_cases hr : x % (n - 1) = 0
  · simp [oneOffRow, hmod, hdiv, hr]
  · have hlast : x % (n - 1) ≠ n - 1 := by omega
    rw [oneOffRow, if_neg (by simpa [hmod] using hr),
      if_neg (by simpa [hmod] using hlast), if_neg hr, hdiv]
    unfold crossOneOffColumnPosition
    omega

theorem oneOffPredecessorPosition_row
    {g n x : ℕ} (hn : 2 ≤ n) (hx : 1 ≤ x) (hxg : x ≤ g) :
    oneOffRow g n (crossOneOffPredecessorPosition n x) =
      if x % (n - 1) = 0 then g + x / (n - 1)
      else g + x / (n - 1) + 1 - x := by
  by_cases hr : x % (n - 1) = 0
  · let q := x / (n - 1)
    have hxq : x = q * (n - 1) := by
      dsimp [q]
      simpa [hr, Nat.mul_comm] using (Nat.div_add_mod x (n - 1)).symm
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
    have hsplit : q * n - 1 = (q - 1) * n + (n - 1) := by
      have hbase : q * n = (q - 1) * n + n := by
        calc
          q * n = ((q - 1) + 1) * n := by rw [Nat.sub_add_cancel hq]
          _ = (q - 1) * n + n := by ring
      omega
    have hrem : (q * n - 1) % n = n - 1 := by
      rw [hsplit, Nat.add_mod]
      simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have hquot : (q * n - 1) / n = q - 1 := by
      rw [hsplit]
      simpa [Nat.add_comm, Nat.mul_comm,
        Nat.div_eq_of_lt (by omega : n - 1 < n)] using
        (Nat.add_mul_div_left (n - 1) (q - 1) (by omega : 0 < n))
    rw [if_pos hr, hpre, oneOffRow,
      if_neg (by rw [hrem]; omega : (q * n - 1) % n ≠ 0),
      if_pos hrem, hquot]
    omega
  · rw [if_neg hr, crossOneOffPredecessorPosition, if_neg hr]
    simpa [hr] using oneOffColumnPosition_row hn hxg

/-- The predecessor coordinate has the same compressed coordinate, including
the boundary value `x=1` needed by Proposition 4.25. -/
theorem oneOffPredecessorPosition_decode
    {n x : ℕ} (hn : 2 ≤ n) (hx : 1 ≤ x) :
    crossOneOffPredecessorPosition n x -
        crossOneOffPredecessorPosition n x / n = x := by
  by_cases hr : x % (n - 1) = 0
  · let q := x / (n - 1)
    have hxq : x = q * (n - 1) := by
      dsimp [q]
      simpa [hr, Nat.mul_comm] using (Nat.div_add_mod x (n - 1)).symm
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
    have hqle : q ≤ q * n := Nat.le_mul_of_pos_right q (by omega)
    omega
  · rw [crossOneOffPredecessorPosition, if_neg hr]
    exact crossOneOffColumnPosition_decode hn

theorem oneOffPredecessorPosition_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Set.InjOn (crossOneOffPredecessorPosition n) (Set.Ici 1) := by
  intro x hx y hy hxy
  have h := congrArg (fun b : ℕ => b - b / n) hxy
  simpa [oneOffPredecessorPosition_decode hn hx,
    oneOffPredecessorPosition_decode hn hy] using h

private theorem nat_div_le_div_add_sub_oneOff
    {d x y : ℕ} (_hd : 1 ≤ d) (hyx : y ≤ x) :
    x / d ≤ y / d + (x - y) := by
  induction x, hyx using Nat.le_induction with
  | base => simp
  | succ x hyx ih =>
      rw [Nat.succ_div]
      split <;> omega

private theorem nat_div_lt_div_add_sub_oneOff
    {d x y : ℕ} (hd : 1 ≤ d) (hyx : y < x)
    (hxMod : x % d ≠ 0) :
    x / d < y / d + (x - y) := by
  let z := x - 1
  have hx : x = z + 1 := by dsimp [z]; omega
  have hyz : y ≤ z := by dsimp [z]; omega
  have hDiv := nat_div_le_div_add_sub_oneOff hd hyz
  have hNotDvd : ¬ d ∣ z + 1 := by
    intro hDvd
    apply hxMod
    rw [hx]
    exact Nat.mod_eq_zero_of_dvd hDvd
  rw [hx, Nat.succ_div, if_neg hNotDvd]
  omega

/-- A predecessor row over `y` and the preferred row over `x > y` form an
inversion in the one-off block. -/
theorem oneOff_predecessor_column_mem
    {g n y x : ℕ} (hg : 2 ≤ g) (hn : 2 ≤ n) (hy : 1 ≤ y)
    (hyx : y < x) (hxg : x ≤ g) :
    (crossOneOffPredecessorPosition n y,
        crossOneOffColumnPosition n x) ∈ oneOffForcedInversionPairs g n := by
  have hx : 1 ≤ x := hy.trans hyx.le
  have hPreLo : 1 ≤ crossOneOffPredecessorPosition n y := by
    unfold crossOneOffPredecessorPosition
    split
    · have hColLo : 2 ≤ crossOneOffColumnPosition n y := by
        unfold crossOneOffColumnPosition
        have hDivPos : 1 ≤ y / (n - 1) := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < n - 1)).2
          have hDvd := Nat.dvd_of_mod_eq_zero (by assumption : y % (n - 1) = 0)
          have hLe := Nat.le_of_dvd (by omega : 0 < y) hDvd
          simpa using hLe
        omega
      omega
    · unfold crossOneOffColumnPosition
      exact hy.trans (Nat.le_add_right y _)
  have hColLo : 1 ≤ crossOneOffColumnPosition n x := by
    unfold crossOneOffColumnPosition
    exact hx.trans (Nat.le_add_right x _)
  have hColHi : crossOneOffColumnPosition n x ≤ crossOneOffCutoff g n :=
    crossOneOffColumnPosition_le_cutoff hn hxg
  have hOrder := crossOneOffPredecessorPosition_lt_column hn hyx
  have hPreHi : crossOneOffPredecessorPosition n y ≤
      crossOneOffCutoff g n := hOrder.le.trans hColHi
  have hPreRow := oneOffPredecessorPosition_row hn hy (hyx.le.trans hxg)
  have hColRow := oneOffColumnPosition_row hn hxg
  have hDivLe := nat_div_le_div_add_sub_oneOff
    (by omega : 1 ≤ n - 1) hyx.le
  have hRow : oneOffRow g n (crossOneOffPredecessorPosition n y) >
      oneOffRow g n (crossOneOffColumnPosition n x) := by
    rw [hPreRow, hColRow]
    by_cases hry : y % (n - 1) = 0
    · rw [if_pos hry]
      have hqyPos : 1 ≤ y / (n - 1) := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < n - 1)).2
        have hLe := Nat.le_of_dvd (by omega : 0 < y)
          (Nat.dvd_of_mod_eq_zero hry)
        simpa using hLe
      by_cases hrx : x % (n - 1) = 0
      · rw [if_pos hrx]
        have hqxLe : x / (n - 1) ≤ g :=
          (Nat.div_le_self x (n - 1)).trans hxg
        omega
      · rw [if_neg hrx]
        have hqxSucc : x / (n - 1) + 1 ≤ x := by
          have hxPos : 0 < x := by omega
          have hlt : x / (n - 1) < x := by
            by_cases hdOne : n - 1 = 1
            · have hxMod : x % (n - 1) = 0 := by
                rw [hdOne]
                exact Nat.mod_one x
              exact (hrx hxMod).elim
            · exact Nat.div_lt_self hxPos (by omega)
          omega
        have hNoUnderflow : g + x / (n - 1) + 1 - x ≤ g := by omega
        omega
    · rw [if_neg hry]
      by_cases hrx : x % (n - 1) = 0
      · rw [if_pos hrx]
        have hqxBound : x / (n - 1) ≤ y / (n - 1) + (x - y) := hDivLe
        have hgAdd : g ≤ g + y / (n - 1) + 1 := by
          simp only [Nat.add_assoc]
          exact Nat.le_add_right g (y / (n - 1) + 1)
        have hLeftAdd :
            (g + y / (n - 1) + 1 - y) + y = g + y / (n - 1) + 1 :=
          Nat.sub_add_cancel ((hyx.le.trans hxg).trans hgAdd)
        omega
      · rw [if_neg hrx]
        have hStrict := nat_div_lt_div_add_sub_oneOff
          (by omega : 1 ≤ n - 1) hyx hrx
        have hgAddY : g ≤ g + y / (n - 1) + 1 := by
          simp only [Nat.add_assoc]
          exact Nat.le_add_right g (y / (n - 1) + 1)
        have hgAddX : g ≤ g + x / (n - 1) + 1 := by
          simp only [Nat.add_assoc]
          exact Nat.le_add_right g (x / (n - 1) + 1)
        have hLeftAdd :
            (g + y / (n - 1) + 1 - y) + y = g + y / (n - 1) + 1 :=
          Nat.sub_add_cancel ((hyx.le.trans hxg).trans hgAddY)
        have hRightAdd :
            (g + x / (n - 1) + 1 - x) + x = g + x / (n - 1) + 1 :=
          Nat.sub_add_cancel (hxg.trans hgAddX)
        omega
  rw [oneOffForcedInversionPairs, finiteRowInversionPairs,
    Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hPreLo, hPreHi⟩,
      Finset.mem_Icc.mpr ⟨hColLo, hColHi⟩⟩,
    hOrder, hRow⟩

/-! ## The finite count -/

/-- The inversion indexed by an unordered pair of distinct compressed
coordinates in `{1, ..., g}`. -/
noncomputable def oneOffTriangularPair (n g : ℕ) :
    Sym2 (Fin (g - 1)) → ℕ × ℕ :=
  Sym2.lift ⟨fun a b =>
    (crossOneOffPredecessorPosition n (min a.val b.val + 1),
      crossOneOffColumnPosition n (max a.val b.val + 2)), by
        intro a b
        simp [min_comm, max_comm]⟩

theorem oneOffTriangularPair_injective
    {n g : ℕ} (hn : 2 ≤ n) :
    Function.Injective (oneOffTriangularPair n g) := by
  intro x y hxy
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [oneOffTriangularPair, Sym2.lift_mk, Prod.mk.injEq] at hxy
      have hMin : min a.val b.val = min c.val d.val := by
        have h := oneOffPredecessorPosition_injective hn
          (by simp : min a.val b.val + 1 ∈ Set.Ici 1)
          (by simp : min c.val d.val + 1 ∈ Set.Ici 1) hxy.1
        omega
      have hMax : max a.val b.val = max c.val d.val := by
        have h := crossOneOffColumnPosition_injective hn hxy.2
        omega
      apply endpointPairEmbedding_injective (g - 1)
      simp only [endpointPairEmbedding, Sym2.lift_mk, Prod.mk.injEq]
      exact ⟨by exact_mod_cast hMin,
        by exact_mod_cast congrArg Nat.succ hMax⟩

private theorem oneOffTriangularPair_mem
    {g n : ℕ} (hg : 2 ≤ g) (hn : 2 ≤ n)
    (s : Sym2 (Fin (g - 1))) :
    oneOffTriangularPair n g s ∈ oneOffForcedInversionPairs g n := by
  induction s using Sym2.ind with
  | _ a b =>
    let y := min a.val b.val + 1
    let x := max a.val b.val + 2
    change (crossOneOffPredecessorPosition n y,
      crossOneOffColumnPosition n x) ∈ oneOffForcedInversionPairs g n
    have hy : 1 ≤ y := by simp [y]
    have hyx : y < x := by dsimp [y, x]; omega
    have hxg : x ≤ g := by
      dsimp [x]
      have hMax : max a.val b.val < g - 1 := max_lt a.isLt b.isLt
      omega
    exact oneOff_predecessor_column_mem hg hn hy hyx hxg

private theorem oneOffAdjacentPair_mem
    {g n F : ℕ} (hg : 2 ≤ g) (hn : 2 ≤ n)
    (hF : F = g / (n - 1)) (i : Fin F) :
    crossOneOffAdjacentPair n i.val ∈ oneOffForcedInversionPairs g n := by
  let q := i.val + 1
  let x := q * (n - 1)
  have hq : q ≤ F := by dsimp [q]; omega
  have hx : 1 ≤ x := by
    dsimp [x, q]
    have hpos : 0 < (i.val + 1) * (n - 1) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  have hxg : x ≤ g := by
    dsimp [x]
    have hMul : F * (n - 1) ≤ g := by
      rw [hF]
      exact Nat.div_mul_le_self g (n - 1)
    exact (Nat.mul_le_mul_right (n - 1) hq).trans hMul
  have hxMod : x % (n - 1) = 0 := by simp [x]
  have hxDiv : x / (n - 1) = q := by
    dsimp [x]
    exact Nat.mul_div_left q (by omega)
  have hCol : crossOneOffColumnPosition n x = q * n := by
    unfold crossOneOffColumnPosition
    rw [hxDiv]
    dsimp [x]
    calc
      q * (n - 1) + q = q * ((n - 1) + 1) := by ring
      _ = q * n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hPre : crossOneOffPredecessorPosition n x = q * n - 1 := by
    simp [crossOneOffPredecessorPosition, hxMod, hCol]
  have hPreRow := oneOffPredecessorPosition_row hn hx hxg
  have hColRow := oneOffColumnPosition_row hn hxg
  rw [if_pos hxMod, hxDiv] at hPreRow hColRow
  have hColHi := crossOneOffColumnPosition_le_cutoff hn hxg
  have hPreHi : crossOneOffPredecessorPosition n x ≤
      crossOneOffCutoff g n := by
    rw [hPre]
    exact (Nat.sub_le (q * n) 1).trans (by simpa [hCol] using hColHi)
  have hPreLo : 1 ≤ crossOneOffPredecessorPosition n x := by
    rw [hPre]
    have hqOne : 1 ≤ q := by dsimp [q]; omega
    have : 2 ≤ q * n := by nlinarith
    omega
  have hColLo : 1 ≤ crossOneOffColumnPosition n x := by
    rw [hCol]
    have hpos : 0 < q * n := Nat.mul_pos (by omega) (by omega)
    omega
  change (q * n - 1, q * n) ∈ oneOffForcedInversionPairs g n
  rw [oneOffForcedInversionPairs, finiteRowInversionPairs,
    Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
    Finset.mem_Icc.mpr ?_⟩, ?_⟩
  · simpa [hPre] using And.intro hPreLo hPreHi
  · simpa [hCol] using And.intro hColLo hColHi
  · rw [← hPre, ← hCol, hPreRow, hColRow]
    omega

/-- Counting indices consisting of unordered pairs on the first part and individual
adjacent-pair indices on the second. -/
abbrev OneOffRefinedCountDomain (g F : ℕ) :=
  Sum (Sym2 (Fin (g - 1))) (Fin F)

/-- Realize the triangular and adjacent-pair parts of the refined counting domain as pairs of
natural numbers. -/
noncomputable def oneOffRefinedCountPair (n g F : ℕ) :
    OneOffRefinedCountDomain g F → ℕ × ℕ
  | Sum.inl x => oneOffTriangularPair n g x
  | Sum.inr i => crossOneOffAdjacentPair n i.val

private theorem oneOffTriangularPair_ne_adjacentPair
    {n g F : ℕ} (hn : 2 ≤ n) (s : Sym2 (Fin (g - 1))) (j : Fin F) :
    oneOffTriangularPair n g s ≠ crossOneOffAdjacentPair n j.val := by
  intro hEq
  induction s using Sym2.ind with
  | _ a b =>
    let y := min a.val b.val + 1
    let x := max a.val b.val + 2
    let z := (j.val + 1) * (n - 1)
    have hz : 1 ≤ z := by
      dsimp [z]
      have hpos : 0 < (j.val + 1) * (n - 1) :=
        Nat.mul_pos (by omega) (by omega)
      omega
    have hzMod : z % (n - 1) = 0 := by simp [z]
    have hzDiv : z / (n - 1) = j.val + 1 := by
      dsimp [z]
      exact Nat.mul_div_left (j.val + 1) (by omega)
    have hColZ : crossOneOffColumnPosition n z = (j.val + 1) * n := by
      unfold crossOneOffColumnPosition
      rw [hzDiv]
      dsimp [z]
      calc
        (j.val + 1) * (n - 1) + (j.val + 1) =
            (j.val + 1) * ((n - 1) + 1) := by ring
        _ = (j.val + 1) * n := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    have hPreZ : crossOneOffPredecessorPosition n z =
        (j.val + 1) * n - 1 := by
      simp [crossOneOffPredecessorPosition, hzMod, hColZ]
    simp only [oneOffTriangularPair, Sym2.lift_mk,
      crossOneOffAdjacentPair, Prod.mk.injEq] at hEq
    have hXEq : x = z := by
      apply crossOneOffColumnPosition_injective hn
      simpa [x, hColZ] using hEq.2
    have hYEq : y = z := by
      apply oneOffPredecessorPosition_injective hn
      · simp [y]
      · exact hz
      · simpa [y, hPreZ] using hEq.1
    have hyx : y < x := by dsimp [y, x]; omega
    omega

theorem oneOffRefinedCountPair_injective
    {n g F : ℕ} (hn : 2 ≤ n) :
    Function.Injective (oneOffRefinedCountPair n g F) := by
  intro x y hxy
  rcases x with x | i <;> rcases y with y | j
  · exact congrArg Sum.inl (oneOffTriangularPair_injective hn hxy)
  · exact (oneOffTriangularPair_ne_adjacentPair hn x j hxy).elim
  · exact (oneOffTriangularPair_ne_adjacentPair hn y i hxy.symm).elim
  · apply congrArg Sum.inr
    apply Fin.ext
    exact crossOneOffAdjacentPair_injective (by omega) hxy

/-- The pure finite-row count in Proposition 4.25. -/
theorem oneOff_refinedCount_le_card
    {g n : ℕ} (hg : 2 ≤ g) (hn : 2 ≤ n) :
    Nat.choose g 2 + g / (n - 1) ≤
      (oneOffForcedInversionPairs g n).card := by
  let F := g / (n - 1)
  have hmap : ∀ x : OneOffRefinedCountDomain g F, x ∈ Set.univ →
      oneOffRefinedCountPair n g F x ∈
        (oneOffForcedInversionPairs g n : Set (ℕ × ℕ)) := by
    intro x _
    rcases x with x | i
    · exact oneOffTriangularPair_mem hg hn x
    · exact oneOffAdjacentPair_mem hg hn rfl i
  have hle := Set.ncard_le_ncard_of_injOn
    (s := (Set.univ : Set (OneOffRefinedCountDomain g F)))
    (t := (oneOffForcedInversionPairs g n : Set (ℕ × ℕ)))
    (oneOffRefinedCountPair n g F) hmap
    (oneOffRefinedCountPair_injective hn).injOn
    (oneOffForcedInversionPairs g n).finite_toSet
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
  change Fintype.card (OneOffRefinedCountDomain g F) ≤ _ at hle
  have hDomainCard : Fintype.card (OneOffRefinedCountDomain g F) =
      Nat.choose g 2 + F := by
    simp only [OneOffRefinedCountDomain, Fintype.card_sum, Fintype.card_fin]
    rw [show Fintype.card (Sym2 (Fin (g - 1))) =
      Nat.choose (g - 1 + 1) 2 by
        change (Finset.univ : Finset (Sym2 (Fin (g - 1)))).card = _
        rw [← Finset.sym2_univ, Finset.card_sym2, Finset.card_univ]
        simp only [Fintype.card_fin]]
    congr 2
    omega
  rw [hDomainCard] at hle
  simpa [F] using hle

/-- Proposition 4.25 in its simplified numerical form. -/
theorem oneOff_refined_inversion_lower_bound
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (tau : ℤ → ℤ) (hg : 2 ≤ g) (hk : 0 < k)
    (hLength : 1 < B.length alpha)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hAffine : IsKAffine k tau)
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose g 2 + g / (B.length alpha - 1) ≤
      kInversionCount k tau := by
  exact (oneOff_refinedCount_le_card hg (by omega)).trans
    (oneOff_forcedInversionPairs_card_le B alpha tau hg hk hLength
      hTau hAffine hfinite)

/-- The refined one-off count is already larger than the genus from genus
four onward, so this entire same-strand one-off family is never
`k`-general in that range. -/
theorem oneOff_not_kGeneral_of_four_le_genus
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (hg : 4 ≤ g) (hLength : 1 < B.length alpha) :
    ¬ KGeneralTransmission
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k := by
  intro hK
  obtain ⟨tau, hTau, hAffine, hFinite, hUpper⟩ :=
    hK.2.2 (g • oneChip (rightEndpoint B))
  have hLower := oneOff_refined_inversion_lower_bound
    B alpha tau (by omega) hK.1.1 hLength hTau hAffine hFinite
  have hGenus : Int.toNat (genus
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)).graph) = g := by
    change Int.toNat (genus B.graph) = g
    rw [B.genus_graph]
    omega
  rw [hGenus] at hUpper
  have hChoose : g < Nat.choose g 2 := by
    rw [Nat.choose_two_right]
    have hSub : g - 1 + 1 = g := Nat.sub_add_cancel (by omega)
    have hProduct : 2 * g + 2 ≤ g * (g - 1) := by
      nlinarith
    omega
  have : g < Nat.choose g 2 + g / (B.length alpha - 1) :=
    hChoose.trans_le (Nat.le_add_right _ _)
  exact (not_lt_of_ge (hLower.trans hUpper)) this

/-- TeX label: `prop-oneOffNotGeneral` (Proposition 4.25), simplified equivalent
form.

For the same-strand one-off marking `(leftEndpoint, v_{α,nα-1})`, write
`f = floor(g / (nα - 1))`.  The paper's auxiliary quantity is
`h = g - f`, so its displayed four-family count is exactly
`choose(g,2) + f`.  This statement gives the paper's maximum-inversion
conclusion as a concrete divisor/transmission witness. -/
theorem oneOff_refined_inversion_lower_bound_ledger
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (hg : 2 ≤ g) (hLength : 1 < B.length alpha)
    (hSub : AllSubmodular
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)))
    (hTO : IsTorsionOrder
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k) :
    ∃ tau : ℤ → ℤ,
      IsTransmissionPermutation
        (mark B.graph (leftEndpoint B)
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
        (g • oneChip (rightEndpoint B)) tau ∧
      IsKAffine k tau ∧
      Nat.choose g 2 + g / (B.length alpha - 1) ≤ kInversionCount k tau := by
  obtain ⟨tau, hTau, hAffine, hFinite⟩ :=
    exists_affine_transmission_of_allSubmodular
      (graphConnected B) hTO.1 hSub (g • oneChip (rightEndpoint B))
  exact ⟨tau, hTau, hAffine,
    oneOff_refined_inversion_lower_bound
      B alpha tau hg hTO.1.1 hLength hTau hAffine hFinite⟩

end Bananas
