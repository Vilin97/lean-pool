/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.ElementaryExistence
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RankChipStep
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionBN

/-!
# Certifying transmission from finitely many rank corners

The transmission condition for an ASP permutation `τ` is indexed by the whole
lattice `ℤ × ℤ`.  Two general facts collapse it to a finite check.

* **Riemann.**  Every divisor satisfies `rank G E ≥ deg E - genus G`, so a
  transmission row whose threshold is at most `τ.χ + a - b` costs nothing.
* **Chip transport.**  A single rank bound at one lattice point `(a₀, b₀)`
  propagates to every other point, losing one unit for each chip that has to be
  removed:
  `rank (D + a•u - b•v) ≥ r₀ - max 0 (a₀ - a) - max 0 (b - b₀)`.

Consequently a divisor satisfies the full transmission condition as soon as it
achieves finitely many *corner* bounds that, together with the Riemann line,
dominate the slipface of `τ`.  This is the mechanism behind the classical
dictionary: for a Grassmannian `τ` whose diagram is a rectangle the corner list
has a single entry, and transmission becomes an ordinary Brill--Noether
condition `BNExists G r d`; the length of `τ` is exactly `(r+1) * (g - d + r)`,
so `ℓ(τ) ≤ g` is the Brill--Noether inequality `ρ ≥ 0`.
-/

namespace Utilities

/-! ## Riemann and chip transport -/

/-- The Riemann inequality: rank is at least degree minus genus. -/
theorem rank_ge_deg_sub_genus
    {G : CFGraph} (hG : graphConnected G) (D : CFDiv G) :
    rank G D ≥ deg D - (genus G : ℤ) := by
  have hRR := riemann_roch_for_graphs hG D
  have hDual := rank_geq_neg_one G (canonicalDivisor G - D)
  omega

/-- Removing `k` chips at one vertex lowers rank by at most `k`. -/
theorem rank_sub_nsmul_one_chip_ge
    {G : CFGraph} (D : CFDiv G) (w : G.V) (k : ℕ) :
    rank G (D - (k : ℤ) • oneChip w) ≥ rank G D - (k : ℤ) := by
  induction k with
  | zero => simp
  | succ m ih =>
      have hstep :
          rank G ((D - (m : ℤ) • oneChip w) - oneChip w)
            ≥ rank G (D - (m : ℤ) • oneChip w) - 1 :=
        rank_sub_one_chip_ge_rank_sub_one _ w
      have hrw : D - ((m + 1 : ℕ) : ℤ) • oneChip w
          = (D - (m : ℤ) • oneChip w) - oneChip w := by
        funext x
        push_cast
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hrw]
      push_cast
      omega

/-- Adding chips at one vertex never lowers rank. -/
theorem rank_add_nsmul_one_chip_ge
    {G : CFGraph} (D : CFDiv G) (w : G.V) (k : ℕ) :
    rank G (D + (k : ℤ) • oneChip w) ≥ rank G D := by
  induction k with
  | zero => simp
  | succ m ih =>
      have hstep :
          rank G ((D + (m : ℤ) • oneChip w) + oneChip w)
            ≥ rank G (D + (m : ℤ) • oneChip w) :=
        rank_add_one_chip_ge _ w _ le_rfl
      have hrw : D + ((m + 1 : ℕ) : ℤ) • oneChip w
          = (D + (m : ℤ) • oneChip w) + oneChip w := by
        funext x
        push_cast
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hrw]
      omega

/-- Shifting by an integer multiple of one chip costs at most the number of
chips actually removed. -/
theorem rank_add_zsmul_one_chip_ge
    {G : CFGraph} (E : CFDiv G) (w : G.V) (p : ℤ) :
    rank G (E + p • oneChip w) ≥ rank G E - max 0 (-p) := by
  rcases lt_or_ge p 0 with hp | hp
  swap
  · have hk : p = ((p.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hp).symm
    have := rank_add_nsmul_one_chip_ge E w p.toNat
    rw [← hk] at this
    have hmax : max 0 (-p) = 0 := by omega
    omega
  · have hk : -p = (((-p).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
    have hsub := rank_sub_nsmul_one_chip_ge E w (-p).toNat
    rw [← hk] at hsub
    have hrw : E - (-p) • oneChip w = E + p • oneChip w := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hrw] at hsub
    have hmax : max 0 (-p) = -p := by omega
    omega

/-- **Chip transport.**  One rank bound at the lattice point `(a₀, b₀)`
propagates to every lattice point. -/
theorem rank_transmissionTwist_ge_of_corner
    {G : CFGraph} (u v : G.V) (D : CFDiv G) {a₀ b₀ r₀ : ℤ}
    (h : rank G (D + a₀ • oneChip u - b₀ • oneChip v) ≥ r₀)
    (a b : ℤ) :
    rank G (D + a • oneChip u - b • oneChip v)
      ≥ r₀ - max 0 (a₀ - a) - max 0 (b - b₀) := by
  set E : CFDiv G := D + a₀ • oneChip u - b₀ • oneChip v with hE
  have hStep1 := rank_add_zsmul_one_chip_ge E u (a - a₀)
  have hStep2 := rank_add_zsmul_one_chip_ge (E + (a - a₀) • oneChip u) v (b₀ - b)
  have hrw : E + (a - a₀) • oneChip u + (b₀ - b) • oneChip v
      = D + a • oneChip u - b • oneChip v := by
    funext x
    simp only [hE, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hrw] at hStep2
  have h1 : max 0 (-(a - a₀)) = max 0 (a₀ - a) := by
    congr 1
    omega
  have h2 : max 0 (-(b₀ - b)) = max 0 (b - b₀) := by
    congr 1
    omega
  rw [h1] at hStep1
  rw [h2] at hStep2
  omega

/-! ## Corner certificates -/

/-- A corner is a lattice point together with a rank threshold. -/
abbrev Corner := ℤ × ℤ × ℤ

/-- The rank bound that a corner transports to the lattice point `(a, b)`. -/
def cornerBound (c : Corner) (a b : ℤ) : ℤ :=
  c.2.2 - max 0 (c.1 - a) - max 0 (b - c.2.1)

/-- A corner list dominates `τ` when every transmission threshold is met by one
of three things: the trivial bound `rank ≥ -1`, the Riemann line, or transport
from one of the corners. -/
def CornersDominate (τ : AspPerm) (C : List Corner) : Prop :=
  ∀ a b : ℤ,
    τ.s (a + 1) b - 1 < 0 ∨
    τ.s (a + 1) b - 1 ≤ τ.χ + a - b ∨
      ∃ c ∈ C, τ.s (a + 1) b - 1 ≤ cornerBound c a b

/-- **Corner certificate.**  A divisor of the right degree that achieves every
corner bound satisfies the full transmission condition. -/
theorem satisfiesTransmission_of_corners
    {G : CFGraph} (hG : graphConnected G) (u v : G.V)
    (τ : AspPerm) (D : CFDiv G) (C : List Corner)
    (hDegree : deg D = (genus G : ℤ) + τ.χ)
    (hDom : CornersDominate τ C)
    (hCorners : ∀ c ∈ C,
      rank G (D + c.1 • oneChip u - c.2.1 • oneChip v) ≥ c.2.2) :
    SatisfiesTransmission G u v τ D := by
  refine ⟨hDegree, ?_⟩
  intro a b
  unfold TransmissionInequality
  rcases hDom a b with hTrivial | hRiemann | ⟨c, hc, hBound⟩
  · have hNeg := rank_geq_neg_one G (D + a • oneChip u - b • oneChip v)
    omega
  · have hDeg :=
      deg_add_marked_twist_of_degree D u v a b _ hDegree
    have hR := rank_ge_deg_sub_genus hG (D + a • oneChip u - b • oneChip v)
    rw [hDeg] at hR
    omega
  · have hT := rank_transmissionTwist_ge_of_corner u v D (hCorners c hc) a b
    unfold cornerBound at hBound
    omega

/-! ## Existence: the Brill--Noether dictionary -/

/-- A slipface dominated by the Riemann line alone is realized by every divisor
of the correct degree.  This covers exactly the ASP permutations of length
zero. -/
theorem transmissionExists_of_riemann
    {G : CFGraph} (hG : graphConnected G) (u v : G.V) (τ : AspPerm)
    (hDom : ∀ a b : ℤ, τ.s (a + 1) b - 1 ≤ τ.χ + a - b) :
    TransmissionExists G u v τ := by
  classical
  let w : G.V := Classical.arbitrary G.V
  refine ⟨((genus G : ℤ) + τ.χ) • oneChip w, ?_⟩
  refine satisfiesTransmission_of_corners hG u v τ _ [] ?_ ?_ ?_
  · rw [map_zsmul, deg_one_chip]
    simp
  · intro a b
    exact Or.inr (Or.inl (hDom a b))
  · intro c hc
    simp at hc

/-- **One corner is an ordinary Brill--Noether condition.**  If a single corner
`(a₀, b₀, r₀)` dominates the slipface of `τ`, then transmission for `τ` follows
from `BNExists` at rank `r₀` and the corresponding affine degree. -/
theorem transmissionExists_of_corner_of_BNExists
    {G : CFGraph} (hG : graphConnected G) (u v : G.V) (τ : AspPerm)
    (a₀ b₀ r₀ : ℤ)
    (hDom : CornersDominate τ [(a₀, b₀, r₀)])
    (hBN : BNExists G r₀ ((genus G : ℤ) + τ.χ + a₀ - b₀)) :
    TransmissionExists G u v τ := by
  obtain ⟨E, hDegE, hRankE⟩ := hBN
  refine ⟨E - a₀ • oneChip u + b₀ • oneChip v, ?_⟩
  have hTwist :
      E - a₀ • oneChip u + b₀ • oneChip v
        + a₀ • oneChip u - b₀ • oneChip v = E := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine satisfiesTransmission_of_corners hG u v τ _ [(a₀, b₀, r₀)] ?_ hDom ?_
  · rw [deg.map_add, deg.map_sub, map_zsmul, map_zsmul, deg_one_chip,
      deg_one_chip, hDegE]
    simp only [Int.zsmul_eq_mul, mul_one]
    ring
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    dsimp only
    rw [hTwist]
    exact hRankE

/-- The converse for a corner that records the true slipface value: transmission
returns the Brill--Noether witness.  Together with
`transmissionExists_of_corner_of_BNExists` this is an equivalence. -/
theorem BNExists_of_transmissionExists_corner
    {G : CFGraph} (u v : G.V) (τ : AspPerm) (a₀ b₀ r₀ : ℤ)
    (hThreshold : r₀ ≤ τ.s (a₀ + 1) b₀ - 1)
    (h : TransmissionExists G u v τ) :
    BNExists G r₀ ((genus G : ℤ) + τ.χ + a₀ - b₀) :=
  BNExists_of_transmissionExists_row h a₀ b₀ r₀ hThreshold

/-- **Dictionary.**  For a permutation whose slipface has a single dominating
corner recording its true value, transmission on a twice-marked graph is
*equivalent* to ordinary Brill--Noether existence, and in particular does not
depend on the two marks. -/
theorem transmissionExists_iff_BNExists_of_corner
    {G : CFGraph} (hG : graphConnected G) (u v : G.V) (τ : AspPerm)
    (a₀ b₀ r₀ : ℤ)
    (hDom : CornersDominate τ [(a₀, b₀, r₀)])
    (hThreshold : r₀ ≤ τ.s (a₀ + 1) b₀ - 1) :
    TransmissionExists G u v τ ↔
      BNExists G r₀ ((genus G : ℤ) + τ.χ + a₀ - b₀) :=
  ⟨BNExists_of_transmissionExists_corner u v τ a₀ b₀ r₀ hThreshold,
    transmissionExists_of_corner_of_BNExists hG u v τ a₀ b₀ r₀ hDom⟩

/-! ## The elementary range

The Brill--Noether input of a single-corner permutation is elementary exactly in
the two ranges already available unconditionally: rank zero, and rectangle width
at most one.  For a single-corner `τ` the corner rank `r₀` and rectangle width
`w₀ = g - d₀ + r₀ = b₀ - a₀ - τ.χ + r₀` satisfy `ℓ(τ) = (r₀ + 1) * w₀`, so
`ℓ(τ) ≤ 3` forces `r₀ = 0` or `w₀ ≤ 1`.  The first genuinely new input appears at
`ℓ(τ) = 4` with `r₀ = 1` and `w₀ = 2`, which is the critical rank-one width-two
column `W^1_{g-1}`. -/

/-- Transmission in the elementary Brill--Noether range. -/
theorem transmissionExists_of_corner_elementary
    {G : CFGraph} (hG : graphConnected G) (u v : G.V) (τ : AspPerm)
    (a₀ b₀ r₀ : ℤ)
    (hDom : CornersDominate τ [(a₀, b₀, r₀)])
    (hR : 0 ≤ r₀)
    (hRho : 0 ≤ bnNumber G r₀ ((genus G : ℤ) + τ.χ + a₀ - b₀))
    (hEasy : r₀ = 0 ∨
      rectangleWidth G r₀ ((genus G : ℤ) + τ.χ + a₀ - b₀) ≤ 1) :
    TransmissionExists G u v τ :=
  transmissionExists_of_corner_of_BNExists hG u v τ a₀ b₀ r₀ hDom
    (BNExists_elementary hG hR hRho hEasy)

/-- Rank-zero corner: the transmission witness is an effective divisor. -/
theorem transmissionExists_of_corner_rank_zero
    {G : CFGraph} (hG : graphConnected G) (u v : G.V) (τ : AspPerm)
    (a₀ b₀ : ℤ)
    (hDom : CornersDominate τ [(a₀, b₀, 0)])
    (hDeg : 0 ≤ (genus G : ℤ) + τ.χ + a₀ - b₀) :
    TransmissionExists G u v τ := by
  refine transmissionExists_of_corner_elementary hG u v τ a₀ b₀ 0 hDom le_rfl ?_
    (Or.inl rfl)
  unfold bnNumber rectangleWidth
  omega

end Utilities
