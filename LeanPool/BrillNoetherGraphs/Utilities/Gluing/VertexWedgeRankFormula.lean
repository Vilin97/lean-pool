/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Gluing.VertexWedge
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankChipStep
import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RiemannRoch

/-!
# Rank profiles under vertex gluing

For divisors `D` and `E` on two graphs glued at `x` and `y`, the expected
tropical-dot-product formula is

`rank (D ⊕ E) = min ell,
  rank (D - (ell+1)x) + rank (E + ell*y) + 1`.

This file proves the threshold form of that formula for every `k ≥ 0`.  The
forward implication follows from the universal effective-subtraction
definition of rank and the exact winnability convolution in
`VertexWedge.lean`.  For the converse, the scalar inequalities force a
staggered crossing of the two marked rank profiles; its one-step offset is
exactly the offset required by the common chip shift on the wedge.
-/

namespace Utilities

universe u v

/-! ## One-dimensional marked rank profiles -/

/-- Adding one marked chip changes rank by either zero or one.  This is the
basic discrete Lipschitz property of a marked rank profile. -/
theorem rank_add_zsmul_one_chip_step
    (G : CFGraph.{u}) (D : CFDiv G) (q : G.V) (n : ℤ) :
    rank G (D + n • one_chip q) ≤
        rank G (D + (n + 1) • one_chip q) ∧
      rank G (D + (n + 1) • one_chip q) ≤
        rank G (D + n • one_chip q) + 1 := by
  have hForward :
      rank G ((D + n • one_chip q) + one_chip q) ≥
        rank G (D + n • one_chip q) :=
    rank_add_one_chip_ge (D + n • one_chip q) q _ le_rfl
  have hBackward :
      rank G ((D + (n + 1) • one_chip q) - one_chip q) ≥
        rank G (D + (n + 1) • one_chip q) - 1 :=
    rank_sub_one_chip_ge_rank_sub_one (D + (n + 1) • one_chip q) q
  constructor
  · have hRewrite :
        (D + n • one_chip q) + one_chip q =
          D + (n + 1) • one_chip q := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hRewrite] at hForward
    exact hForward
  · have hRewrite :
        (D + (n + 1) • one_chip q) - one_chip q =
          D + n • one_chip q := by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hRewrite] at hBackward
    omega

/-- The degree along a marked rank profile is affine with slope one. -/
theorem deg_add_zsmul_one_chip
    (G : CFGraph.{u}) (D : CFDiv G) (q : G.V) (n : ℤ) :
    deg (D + n • one_chip q) = deg D + n := by
  rw [deg.map_add, map_zsmul, deg_one_chip]
  simp

/-- The negative-degree tail of a marked rank profile is constantly `-1`. -/
theorem rank_add_zsmul_one_chip_eq_neg_one_of_degree_neg
    (G : CFGraph.{u}) (D : CFDiv G) (q : G.V) (n : ℤ)
    (hDegree : deg D + n < 0) :
    rank G (D + n • one_chip q) = -1 := by
  apply rank_neg_one_of_deg_neg
  rw [deg_add_zsmul_one_chip]
  exact hDegree

/-- On a connected graph, the sufficiently high-degree tail of a marked rank
profile is the affine Riemann--Roch line `degree - genus`. -/
theorem rank_add_zsmul_one_chip_eq_degree_sub_genus_of_large
    (G : CFGraph.{u}) (hG : graph_connected G)
    (D : CFDiv G) (q : G.V) (n : ℤ)
    (hLarge : 2 * (genus G : ℤ) - 2 < deg D + n) :
    rank G (D + n • one_chip q) = deg D + n - (genus G : ℤ) := by
  let A : CFDiv G := D + n • one_chip q
  change rank G A = deg D + n - (genus G : ℤ)
  have hADegree : deg A = deg D + n := by
    dsimp [A]
    exact deg_add_zsmul_one_chip G D q n
  have hDualDegree : deg (canonical_divisor G - A) < 0 := by
    rw [deg.map_sub, degree_of_canonical_divisor, hADegree]
    omega
  have hDualRank : rank G (canonical_divisor G - A) = -1 :=
    rank_neg_one_of_deg_neg G _ hDualDegree
  have hRR := riemann_roch_for_graphs hG A
  rw [hDualRank, hADegree] at hRR
  omega

/-- A finite sequence which starts below a threshold and ends above it has an
adjacent crossing.  No monotonicity is needed: choose the last failed step. -/
theorem exists_adjacent_crossing_nat
    (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (hStart : ¬ p 0) (hEnd : p n) :
    ∃ i : ℕ, i < n ∧ ¬ p i ∧ p (i + 1) := by
  induction n with
  | zero => exact (hStart hEnd).elim
  | succ n ih =>
      by_cases hn : p n
      · obtain ⟨i, hi, hpi, hpi1⟩ := ih hn
        exact ⟨i, Nat.lt_succ_of_lt hi, hpi, hpi1⟩
      · exact ⟨n, Nat.lt_succ_self n, hn, hEnd⟩

/-- Integer-indexed form of `exists_adjacent_crossing_nat`. -/
theorem exists_adjacent_crossing_int
    (p : ℤ → Prop) [DecidablePred p] (lo hi : ℤ)
    (hlohi : lo ≤ hi) (hStart : ¬ p lo) (hEnd : p hi) :
    ∃ ell : ℤ, ¬ p ell ∧ p (ell + 1) := by
  let n : ℕ := (hi - lo).toNat
  let pNat : ℕ → Prop := fun i => p (lo + (i : ℤ))
  have hnCast : (n : ℤ) = hi - lo := by
    dsimp [n]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hlohi)
  have hNatStart : ¬ pNat 0 := by
    simpa [pNat] using hStart
  have hNatEnd : pNat n := by
    dsimp [pNat]
    convert hEnd using 1
    rw [hnCast]
    ring
  obtain ⟨i, _hi, hpi, hpi1⟩ :=
    exists_adjacent_crossing_nat pNat n hNatStart hNatEnd
  refine ⟨lo + (i : ℤ), hpi, ?_⟩
  convert hpi1 using 1
  dsimp [pNat]
  ring
/-- Wedge addition commutes with subtracting divisors on the two factors. -/
theorem wedgeAddDivisor_sub
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D A : CFDiv G) (E B : CFDiv H) :
    wedgeAddDivisor G H x y D E - wedgeAddDivisor G H x y A B =
      wedgeAddDivisor G H x y (D - A) (E - B) := by
  funext z
  cases z with
  | inl a =>
      simp only [Pi.sub_apply, wedgeAddDivisor_left]
      by_cases ha : a = x
      · simp only [ha, ↓reduceIte]
        ring
      · simp [ha]
  | inr b =>
      simp only [Pi.sub_apply, wedgeAddDivisor_right]

/-- A nonnegative integral multiple of one chip is effective. -/
theorem effective_zsmul_one_chip_of_nonneg
    (G : CFGraph.{u}) (q : G.V) (a : ℤ) (ha : 0 ≤ a) :
    effective (a • one_chip q) := by
  intro z
  by_cases hz : z = q
  · subst z
    simp [one_chip, ha]
  · simp [one_chip, hz]

/-- Winnability is monotone as the coefficient of a marked chip increases. -/
theorem winnable_add_zsmul_one_chip_mono
    (G : CFGraph.{u}) (D : CFDiv G) (q : G.V) (a b : ℤ)
    (hab : a ≤ b) (ha : winnable G (D + a • one_chip q)) :
    winnable G (D + b • one_chip q) := by
  have hEffective : effective ((b - a) • one_chip q) :=
    effective_zsmul_one_chip_of_nonneg G q (b - a) (sub_nonneg.mpr hab)
  have hAdd := winnable_add_effective_divisor G
    (D + a • one_chip q) ((b - a) • one_chip q) ha hEffective
  convert hAdd using 1
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Effective test divisors on the wedge -/

/-- Restrict a wedge divisor to the left factor, assigning the entire common
coefficient to the left. -/
def wedgeRestrictLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) : CFDiv G :=
  fun a => Q (Sum.inl a)

/-- Restrict a wedge divisor to the right factor, assigning zero chips to its
marked vertex (the common coefficient was assigned to the left). -/
def wedgeRestrictRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) : CFDiv H :=
  fun b => if hb : b = y then 0 else Q (Sum.inr ⟨b, hb⟩)

/-- The two canonical restrictions reconstruct the original wedge divisor. -/
theorem wedgeAddDivisor_restrict
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) :
    wedgeAddDivisor G H x y
      (wedgeRestrictLeftDivisor G H x y Q)
      (wedgeRestrictRightDivisor G H x y Q) = Q := by
  funext z
  cases z with
  | inl a =>
      rw [wedgeAddDivisor_left]
      simp [wedgeRestrictLeftDivisor, wedgeRestrictRightDivisor]
  | inr b =>
      rw [wedgeAddDivisor_right]
      simp [wedgeRestrictRightDivisor, b.2]

/-- Effectivity descends to the canonical left restriction. -/
theorem effective_wedgeRestrictLeftDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) (hQ : effective Q) :
    effective (wedgeRestrictLeftDivisor G H x y Q) :=
  fun a => hQ (Sum.inl a)

/-- Effectivity descends to the canonical right restriction. -/
theorem effective_wedgeRestrictRightDivisor
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) (hQ : effective Q) :
    effective (wedgeRestrictRightDivisor G H x y Q) := by
  intro b
  by_cases hb : b = y
  · simp [wedgeRestrictRightDivisor, hb]
  · simpa [wedgeRestrictRightDivisor, hb] using hQ (Sum.inr ⟨b, hb⟩)

/-- The degrees of the two canonical restrictions add to the wedge degree. -/
theorem deg_wedgeRestrictions
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (Q : CFDiv (vertexWedge G H x y)) :
    deg (wedgeRestrictLeftDivisor G H x y Q) +
      deg (wedgeRestrictRightDivisor G H x y Q) = deg Q := by
  rw [← deg_wedgeAddDivisor]
  rw [wedgeAddDivisor_restrict]

/-- A factorwise chip-shift cover for every effective split of degree `k`
implies rank at least `k` on the wedge.  This is the exact converse interface
provided by `winnable_vertexWedge_iff_exists_chipShift`. -/
theorem vertexWedge_rank_ge_of_factor_shift_cover
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ)
    (hCover : ∀ (A : CFDiv G) (B : CFDiv H),
      effective A → effective B → deg A + deg B = k →
      ∃ t : ℤ, winnable G (chipShift G (D - A) x t) ∧
        winnable H (chipShift H (E - B) y (-t))) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k := by
  apply (rank_geq_iff _ _ k).mp
  intro Q hQ
  let A := wedgeRestrictLeftDivisor G H x y Q
  let B := wedgeRestrictRightDivisor G H x y Q
  have hA : effective A := effective_wedgeRestrictLeftDivisor G H x y Q hQ.1
  have hB : effective B := effective_wedgeRestrictRightDivisor G H x y Q hQ.1
  have hDegrees : deg A + deg B = k := by
    rw [deg_wedgeRestrictions G H x y Q, hQ.2]
  obtain ⟨t, hLeft, hRight⟩ := hCover A B hA hB hDegrees
  have hWin := (winnable_vertexWedge_iff_exists_chipShift
    G H x y (D - A) (E - B)).mpr ⟨t, hLeft, hRight⟩
  have hQSplit : Q = wedgeAddDivisor G H x y A B :=
    (wedgeAddDivisor_restrict G H x y Q).symm
  rw [hQSplit, wedgeAddDivisor_sub]
  exact hWin

/-- The profile cover naturally produced by the scalar rank formula is
staggered by one step.  This is also the exact staggering of the two factors
under a common chip shift: the left phase uses `-(ell+1)` and the right phase
uses `ell+1`. -/
theorem vertexWedge_rank_ge_of_staggered_profile_split_cover
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ)
    (hProfile : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → a + b = k →
      ∃ ell : ℤ,
        rank G (D - (ell + 1) • one_chip x) ≥ a ∧
        rank H (E + (ell + 1) • one_chip y) ≥ b) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k := by
  apply vertexWedge_rank_ge_of_factor_shift_cover G H x y D E k
  intro A B hA hB hDegrees
  obtain ⟨ell, hRankA, hRankB⟩ := hProfile (deg A) (deg B)
    (deg_of_eff_nonneg A hA) (deg_of_eff_nonneg B hB) hDegrees
  have hLeftPhase : winnable G
      ((D - (ell + 1) • one_chip x) - A) :=
    ((rank_geq_iff G (D - (ell + 1) • one_chip x) (deg A)).mpr hRankA)
      A ⟨hA, rfl⟩
  have hRightPhase : winnable H
      ((E + (ell + 1) • one_chip y) - B) :=
    ((rank_geq_iff H (E + (ell + 1) • one_chip y) (deg B)).mpr hRankB)
      B ⟨hB, rfl⟩
  refine ⟨-(ell + 1), ?_, ?_⟩
  · convert hLeftPhase using 1
    funext z
    simp only [chipShift, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · convert hRightPhase using 1
    funext z
    simp only [chipShift, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- A convenient finite-rank-profile sufficient condition for the converse.
For every degree split `a+b=k`, it asks for one profile index at which the two
factor ranks simultaneously dominate `a` and `b`. -/
theorem vertexWedge_rank_ge_of_profile_split_cover
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ)
    (hProfile : ∀ a b : ℤ, 0 ≤ a → 0 ≤ b → a + b = k →
      ∃ ell : ℤ,
        rank G (D - (ell + 1) • one_chip x) ≥ a ∧
        rank H (E + ell • one_chip y) ≥ b) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k := by
  apply vertexWedge_rank_ge_of_factor_shift_cover G H x y D E k
  intro A B hA hB hDegrees
  obtain ⟨ell, hRankA, hRankB⟩ := hProfile (deg A) (deg B)
    (deg_of_eff_nonneg A hA) (deg_of_eff_nonneg B hB) hDegrees
  have hLeftPhase : winnable G
      ((D - (ell + 1) • one_chip x) - A) :=
    ((rank_geq_iff G (D - (ell + 1) • one_chip x) (deg A)).mpr hRankA)
      A ⟨hA, rfl⟩
  have hRightPhase : winnable H ((E + ell • one_chip y) - B) :=
    ((rank_geq_iff H (E + ell • one_chip y) (deg B)).mpr hRankB)
      B ⟨hB, rfl⟩
  have hRightShift : winnable H (E - B + (ell + 1) • one_chip y) := by
    apply winnable_add_zsmul_one_chip_mono H (E - B) y ell (ell + 1) (by omega)
    convert hRightPhase using 1
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨-(ell + 1), ?_, ?_⟩
  · convert hLeftPhase using 1
    funext z
    simp only [chipShift, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · convert hRightShift using 1
    funext z
    simp only [chipShift, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-! ## Crossing the two rank profiles -/

/-- The scalar tropical-dot-product inequalities force every nonnegative
degree split to occur across one adjacent pair of phases.  The proof only uses
the two negative-degree tails.  Far to the left the right rank is `-1`, while
far to the right the left rank is `-1`; the assumed scalar inequality forces
the opposite profile above the desired threshold at each endpoint. -/
theorem exists_staggered_rank_profile_split_of_inequalities
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = k)
    (hProfile : ∀ ell : ℤ,
      rank G (D - (ell + 1) • one_chip x) +
          rank H (E + ell • one_chip y) + 1 ≥ k) :
    ∃ ell : ℤ,
      rank G (D - (ell + 1) • one_chip x) ≥ a ∧
      rank H (E + (ell + 1) • one_chip y) ≥ b := by
  classical
  let lo : ℤ := min (-deg E - 1) (deg D)
  let hi : ℤ := deg D
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact min_le_right _ _
  have hRightLoDegree : deg E + lo < 0 := by
    have hlo : lo ≤ -deg E - 1 := by
      dsimp [lo]
      exact min_le_left _ _
    omega
  have hRightLoRank : rank H (E + lo • one_chip y) = -1 :=
    rank_add_zsmul_one_chip_eq_neg_one_of_degree_neg
      H E y lo hRightLoDegree
  have hLeftHiDegree : deg (D - (hi + 1) • one_chip x) < 0 := by
    rw [deg.map_sub, map_zsmul, deg_one_chip]
    dsimp [hi]
    ring_nf
    norm_num
  have hLeftHiRank : rank G (D - (hi + 1) • one_chip x) = -1 :=
    rank_neg_one_of_deg_neg G _ hLeftHiDegree
  have hRightHi : rank H (E + hi • one_chip y) ≥ b := by
    have h := hProfile hi
    rw [hLeftHiRank] at h
    omega
  let p : ℤ → Prop := fun ell =>
    rank H (E + ell • one_chip y) ≥ b
  have hStart : ¬ p lo := by
    dsimp [p]
    rw [hRightLoRank]
    omega
  have hEnd : p hi := hRightHi
  obtain ⟨ell, hEllBelow, hEllNext⟩ :=
    exists_adjacent_crossing_int p lo hi hlohi hStart hEnd
  have hLeft : rank G (D - (ell + 1) • one_chip x) ≥ a := by
    have h := hProfile ell
    dsimp [p] at hEllBelow
    omega
  exact ⟨ell, hLeft, hEllNext⟩

/-- Converse to `vertexWedge_rank_profile_inequality`: the full family of
scalar profile inequalities supplies the staggered profile cover and hence a
rank lower bound on the wedge. -/
theorem vertexWedge_rank_ge_of_profile_inequalities
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ) (_hk : 0 ≤ k)
    (hProfile : ∀ ell : ℤ,
      rank G (D - (ell + 1) • one_chip x) +
          rank H (E + ell • one_chip y) + 1 ≥ k) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k := by
  apply vertexWedge_rank_ge_of_staggered_profile_split_cover G H x y D E k
  intro a b ha hb hab
  exact exists_staggered_rank_profile_split_of_inequalities
    G H x y D E k a b ha hb hab hProfile

/-- One direction of the vertex-gluing rank formula: a rank lower bound on
the wedge forces every tropical-dot-product inequality. -/
theorem vertexWedge_rank_profile_inequality
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ) (_hk : 0 ≤ k)
    (hRank : rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) ≥ k) :
    ∀ ell : ℤ,
      rank G (D - (ell + 1) • one_chip x) +
          rank H (E + ell • one_chip y) + 1 ≥ k := by
  intro ell
  by_contra hProfile
  have hStrict :
      rank G (D - (ell + 1) • one_chip x) +
          rank H (E + ell • one_chip y) + 1 < k := by
    omega
  let r : ℤ := rank G (D - (ell + 1) • one_chip x)
  let s : ℤ := rank H (E + ell • one_chip y)
  obtain ⟨A, hAEffective, hADegree, hAUnwinnable⟩ :=
    rank_get_effective G (D - (ell + 1) • one_chip x)
  obtain ⟨B, hBEffective, hBDegree, hBUnwinnable⟩ :=
    rank_get_effective H (E + ell • one_chip y)
  let c : ℤ := k - (r + s + 2)
  have hc : 0 ≤ c := by
    dsimp [c, r, s]
    omega
  let A' : CFDiv G := A + c • one_chip x
  have hA'Effective : effective A' :=
    fun z => add_nonneg (hAEffective z)
      (effective_zsmul_one_chip_of_nonneg G x c hc z)
  have hA'Degree : deg A' = r + 1 + c := by
    dsimp [A']
    rw [deg.map_add, map_zsmul, deg_one_chip, hADegree]
    dsimp [r]
    ring
  let Q : CFDiv (vertexWedge G H x y) :=
    wedgeAddDivisor G H x y A' B
  have hQEffective : effective Q :=
    effective_wedgeAddDivisor G H x y A' B hA'Effective hBEffective
  have hQDegree : deg Q = k := by
    dsimp [Q]
    rw [deg_wedgeAddDivisor, hA'Degree, hBDegree]
    dsimp [c, s]
    ring
  have hRankGeq : rank_geq (vertexWedge G H x y)
      (wedgeAddDivisor G H x y D E) k :=
    (rank_geq_iff _ _ k).mpr hRank
  have hSubWinnable := hRankGeq Q ⟨hQEffective, hQDegree⟩
  rw [wedgeAddDivisor_sub G H x y D A' E B] at hSubWinnable
  obtain ⟨t, hLeft, hRight⟩ :=
    (winnable_vertexWedge_iff_exists_chipShift
      G H x y (D - A') (E - B)).mp hSubWinnable
  by_cases ht : t ≤ -(ell + 1)
  · have hLeft' : winnable G (D - A + (t - c) • one_chip x) := by
      convert hLeft using 1
      funext z
      simp only [chipShift, A', Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    have hWitness : winnable G
        (D - A + (-(ell + 1)) • one_chip x) :=
      winnable_add_zsmul_one_chip_mono G (D - A) x
        (t - c) (-(ell + 1)) (by omega) hLeft'
    apply hAUnwinnable
    convert hWitness using 1
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have ht' : -t ≤ ell := by omega
    have hRight' : winnable H (E - B + (-t) • one_chip y) := by
      convert hRight using 1
      funext z
      simp only [chipShift, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    have hWitness : winnable H (E - B + ell • one_chip y) :=
      winnable_add_zsmul_one_chip_mono H (E - B) y (-t) ell ht' hRight'
    apply hBUnwinnable
    convert hWitness using 1
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Tropical-dot-product rank criterion for a vertex wedge.  For every
nonnegative threshold `k`, the wedge has rank at least `k` exactly when every
integer phase satisfies the corresponding sum-of-factor-ranks inequality. -/
theorem vertexWedge_rank_ge_iff_profile_inequalities
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (k : ℤ) (hk : 0 ≤ k) :
    rank (vertexWedge G H x y) (wedgeAddDivisor G H x y D E) ≥ k ↔
      ∀ ell : ℤ,
        rank G (D - (ell + 1) • one_chip x) +
            rank H (E + ell • one_chip y) + 1 ≥ k := by
  constructor
  · exact vertexWedge_rank_profile_inequality G H x y D E k hk
  · exact vertexWedge_rank_ge_of_profile_inequalities G H x y D E k hk

end Utilities
