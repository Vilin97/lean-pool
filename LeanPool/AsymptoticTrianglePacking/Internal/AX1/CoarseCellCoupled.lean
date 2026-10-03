/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the coarse-cell reduction of the coupled residual to the box allocation

This file carries out the reduction announced in `Nibble.BoxAllocationSpec`:

  `Nibble.AX1.BoxAllocationResidual → Nibble.AX1.BlockCoverResidualCoupled`.

The construction, at a regularity scale `ε₁` and a relative block size `α` chosen by the residual:

* cut every cluster into coarse cells of length `l = ⌈2α·mmax⌉`, `P = ⌊mmin/l⌋` of them per cluster,
  and set the block scale to `τ = l·K/δ` with `K = ⌈64/ε⌉ + 1`;
* take a **sparse feasible point** `y` of the cluster-triple LP whose value dominates `ν₃*`
  (`Nibble.AX1.exists_sparse_clusterTripleLP_nu3star`) and discard the triples using a cluster pair
  of density below `δ` — that costs at most `δ|V|²/2 ≤ ε|V|²/2`
  (`Nibble.AX1.sum_sparse_triples_le`);
* make `⌊(1-ε/8)·y_th /(τ²·d₁d₂d₃)⌋` **copies** of every surviving cluster triple, each demanding
  `⌈K·d/δ⌉ ≤ ⌈K/δ⌉` coarse cells in each of its three clusters, the opposite density `d` deciding
  the size.  The pair capacities of the LP say exactly that the demand of every cluster pair is
  below `(1-ε/64)P²`, so `Nibble.AX1.BoxAllocationResidual` places all copies but a set of total
  area `≤ (ε/64)·(#clusters)²·P²`;
* `Nibble.AX1.exists_gridSubTriple_family_of_placement` turns the placement into the family of block
  sub-triples, and `Nibble.AX1.nu3star_le_cover_of_family_lp_value` compares its covering sum with
  the LP value.

* `Nibble.AX1.blockCoverResidualCoupled_of_boxAllocation` — the reduction;
* `Nibble.AX1.ax1_of_boxAllocation` — AX1 from the box allocation, through
  `Nibble.AX1.ax1_of_blockCoverCoupled`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxAllocationSpec
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterFracUpper
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRectPack
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridLineDesign
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.LinearCombination
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterHost
public import Mathlib.Data.List.GetD
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BlockSplit
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterLP
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterCapacity
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapGridLocalResidual
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.TripleEdgesThree
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockCover


/-! # CoreGapBlockCoverCoupled -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### The arithmetic of the construction

The block scale `τ` is large (`8 ≤ τ·δ`), the blocks have size between `¾τδ` and `⁵⁄₄τ`, and the
regularity scale `ε₁` is small compared with `δ`, `μ₂` and `η`.  The four lemmas below are the only
computations the reduction needs; they are stated in isolation to keep the context small. -/

/-- The blocks have size between `¾·τδ` and `⁵⁄₄·τ`. -/
private theorem block_size_bounds {τ δ s dens : ℝ} (hτ : 0 < τ) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hτδ : 8 ≤ τ * δ) (h1 : δ ≤ dens) (h2 : dens ≤ 1) (habs : |s - τ * dens| ≤ 1) :
    3 / 4 * (τ * δ) ≤ s ∧ s ≤ 5 / 4 * τ := by
  rw [abs_le] at habs
  have h3 : τ * δ ≤ τ * dens := mul_le_mul_of_nonneg_left h1 hτ.le
  have h4 : τ * dens ≤ τ := by nlinarith
  have h6 : τ * δ ≤ τ := by nlinarith
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

/-- The area and the support of a sub-triple, in terms of the scale. -/
private theorem area_bounds {τ δ a b c : ℝ} (hτ : 0 < τ) (_hδ : 0 < δ) (hτδ : 8 ≤ τ * δ)
    (ha : 3 / 4 * (τ * δ) ≤ a) (ha' : a ≤ 5 / 4 * τ)
    (hb : 3 / 4 * (τ * δ) ≤ b) (hb' : b ≤ 5 / 4 * τ)
    (hc : 3 / 4 * (τ * δ) ≤ c) (hc' : c ≤ 5 / 4 * τ) :
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + a * c + b * c ≤ 5 * τ ^ 2 ∧
      0 ≤ a * b + a * c + b * c ∧ a + b + c ≤ 4 * τ ∧ 0 ≤ a + b + c := by
  have ha0 : 0 ≤ a := by nlinarith
  have hb0 : 0 ≤ b := by nlinarith
  have hc0 : 0 ≤ c := by nlinarith
  refine ⟨ha0, hb0, hc0, by nlinarith, by positivity, by linarith, by linarith⟩

/-- The `Elo` of a sub-triple is at least a quarter of `τ²δ³`. -/
private theorem elo_lower {τ δ ε₁ a b c dAB dAC dBC : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hε₁0 : 0 < ε₁) (hε₁b : ε₁ ≤ δ / 2) (hx : δ - ε₁ / 8 ≤ dAB)
    (hAC0 : 0 ≤ dAC) (hBC0 : 0 ≤ dBC)
    (ha : 3 / 4 * (τ * δ) ≤ a) (hb : 3 / 4 * (τ * δ) ≤ b) (hc0 : 0 ≤ c) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) :
    1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b + dAC * a * c + dBC * b * c := by
  have hAB : 15 / 16 * δ ≤ dAB := by linarith
  have hnn : (0:ℝ) ≤ 3 / 4 * (τ * δ) := by positivity
  have hab : 9 / 16 * (τ ^ 2 * δ ^ 2) ≤ a * b := by
    linarith only [mul_le_mul ha hb hnn ha0]
  have hmain : 1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b := by
    have h1 : (15 / 16 * δ) * (9 / 16 * (τ ^ 2 * δ ^ 2)) ≤ dAB * (a * b) :=
      mul_le_mul hAB hab (by positivity) (le_trans (by positivity) hAB)
    have h2 : dAB * a * b = dAB * (a * b) := by ring
    have h3 : (15 / 16 * δ) * (9 / 16 * (τ ^ 2 * δ ^ 2)) = 135 / 256 * (τ ^ 2 * δ ^ 3) := by ring
    have h4 : (0:ℝ) ≤ τ ^ 2 * δ ^ 3 := by positivity
    rw [h2]
    rw [h3] at h1
    linarith
  have h2 : 0 ≤ dAC * a * c := by positivity
  have h3 : 0 ≤ dBC * b * c := by positivity
  linarith

/-- The product of three densities at least `δ` is at least `δ³`. -/
private theorem dens_prod_lower {δ x y z : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y) (hz : δ ≤ z) :
    δ ^ 3 ≤ x * y * z := by
  have h1 : δ * δ ≤ x * y := mul_le_mul hx hy hδ.le (by linarith)
  have h2 : (δ * δ) * δ ≤ (x * y) * z :=
    mul_le_mul h1 hz hδ.le (le_trans (by positivity : (0:ℝ) ≤ δ * δ) h1)
  linarith only [h2]

/-- The triangle-degree scale of a sub-triple is above the floor `d₀`. -/
private theorem d_lower {τ δ d₀ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) (hd₀ : d₀ ≤ τ * δ ^ 3) : d₀ ≤ τ * (x * y * z) :=
  le_trans hd₀ (mul_le_mul_of_nonneg_left (dens_prod_lower hδ hx hy hz) hτ.le)

/-- The triangle-degree scale of a sub-triple is nonnegative. -/
private theorem d_nonneg {τ δ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hx : δ ≤ x) (hy : δ ≤ y)
    (hz : δ ≤ z) : 0 ≤ τ * (x * y * z) := by
  have h := dens_prod_lower hδ hx hy hz
  have h0 : (0:ℝ) < δ ^ 3 := by positivity
  exact mul_nonneg hτ.le (by linarith)

/-- The pruning slack `t` is at most half of `(μ - μ₂)` times the triangle-degree scale. -/
private theorem slack_bound {μ μ₂ τ δ x y z : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hx : δ ≤ x) (hy : δ ≤ y) (hz : δ ≤ z) (hμ₂ : 2 * μ₂ ≤ μ) (hμ₂'₀ : 0 < μ₂) :
    2 * ((μ - μ₂) * τ * δ ^ 3 / 2) ≤ (μ - μ₂) * (τ * (x * y * z)) := by
  have h : τ * δ ^ 3 ≤ τ * (x * y * z) :=
    mul_le_mul_of_nonneg_left (dens_prod_lower hδ hx hy hz) hτ.le
  have hd : (0:ℝ) ≤ μ - μ₂ := by linarith
  linarith only [mul_le_mul_of_nonneg_left h hd]

/-- The pruning slack `t = (μ - μ₂)τδ³/2` is positive. -/
private theorem t_pos {μ μ₂ τ δ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂ : 0 < μ₂)
    (h : 2 * μ₂ ≤ μ) : 0 < (μ - μ₂) * τ * δ ^ 3 / 2 := by
  nlinarith [mul_pos hτ hδ3]

/-- The pruning slack `t = (μ - μ₂)τδ³/2` is at least `μ₂τδ³/2`. -/
private theorem t_lower {μ μ₂ τ δ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (h : 2 * μ₂ ≤ μ) :
    μ₂ * τ * δ ^ 3 / 2 ≤ (μ - μ₂) * τ * δ ^ 3 / 2 := by
  nlinarith [mul_pos hτ hδ3]

/-- One term of the covering estimate: replacing the cluster densities by the block densities and
subtracting the exceptional budget costs at most `17ε₁/24` times the area. -/
private theorem cover_step {ε₁ ε₂ dAB dAC dBC eAB eAC eBC a b c : ℝ}
    (h1 : |eAB - dAB| ≤ ε₁ / 8) (h2 : |eAC - dAC| ≤ ε₁ / 8) (h3 : |eBC - dBC| ≤ ε₁ / 8)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    (dAB * a * b + dAC * a * c + dBC * b * c) / 3
        - (ε₁ / 8 + 4 * ε₂) / 3 * (a * b + a * c + b * c)
      ≤ (eAB * a * b + eAC * a * c + eBC * b * c
          - 4 * ε₂ * (a * b + a * c + b * c)) / 3 := by
  have k1 : -(ε₁ / 8) ≤ eAB - dAB := by linarith only [(abs_le.mp h1).1]
  have k2 : -(ε₁ / 8) ≤ eAC - dAC := by linarith only [(abs_le.mp h2).1]
  have k3 : -(ε₁ / 8) ≤ eBC - dBC := by linarith only [(abs_le.mp h3).1]
  have hab : (0:ℝ) ≤ a * b := mul_nonneg ha0 hb0
  have hac : (0:ℝ) ≤ a * c := mul_nonneg ha0 hc0
  have hbc : (0:ℝ) ≤ b * c := mul_nonneg hb0 hc0
  have m1 : -(ε₁ / 8) * (a * b) ≤ (eAB - dAB) * (a * b) :=
    mul_le_mul_of_nonneg_right k1 hab
  have m2 : -(ε₁ / 8) * (a * c) ≤ (eAC - dAC) * (a * c) :=
    mul_le_mul_of_nonneg_right k2 hac
  have m3 : -(ε₁ / 8) * (b * c) ≤ (eBC - dBC) * (b * c) :=
    mul_le_mul_of_nonneg_right k3 hbc
  linarith only [m1, m2, m3]

/-- The accumulated covering loss is absorbed by half of the accuracy. -/
private theorem cover_tail {ε K N : ℝ} (h : K ≤ ε) (hN : 0 ≤ N) :
    K * (N / 2) ≤ ε / 2 * N := by
  have := mul_le_mul_of_nonneg_right h hN
  linarith only [this]

/-- The block uniformity scale `ε₂ = (ε₁/8)/α` at `α = δ/2`, bounded from a bound on `ε₁`. -/
private theorem eps2_bound {x δ B : ℝ} (hδ : 0 < δ) (h : x ≤ B * δ) : x / (4 * δ) ≤ B / 4 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Multiplying a nonnegative quantity by `δ ≤ 1` only decreases it. -/
private theorem mul_delta_le {B δ : ℝ} (hB : 0 ≤ B) (hδ1 : δ ≤ 1) (_hδ0 : 0 ≤ δ) : B * δ ≤ B := by
  nlinarith

/-- The block scale is large: `2 ≤ τ·μ₂δ³` and `μ₂ ≤ 1` give `2 ≤ τδ³`. -/
private theorem tau_delta3_lower {τ δ μ₂ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂1 : μ₂ ≤ 1)
    (h : 2 ≤ τ * (μ₂ * δ ^ 3)) : 2 ≤ τ * δ ^ 3 := by
  nlinarith [mul_le_mul_of_nonneg_left hμ₂1 (le_of_lt (mul_pos hτ hδ3))]

/-- The block scale is large: `2 ≤ τδ³` and `δ ≤ 1/2` give `8 ≤ τδ`. -/
private theorem tau_delta_lower {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (h : 2 ≤ τ * δ ^ 3) : 8 ≤ τ * δ := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by nlinarith
  have hnn : 0 ≤ τ * δ := mul_nonneg hτ.le hδ.le
  nlinarith only [h, hsq, hnn]

/-- The exceptional-edge clause of the design, as an inequality between real numbers. -/
private theorem exc_bound {ε₂ δ μ₂ η τ t S sup Elo : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) (hμ₂0 : 0 < μ₂) (hη : 0 < η)
    (hε₂0 : 0 < ε₂) (hε₂c : ε₂ ≤ η * μ₂ * δ ^ 6 / 2560) (hε₂d : ε₂ ≤ δ ^ 3 / 160)
    (hS : S ≤ 5 * τ ^ 2) (hsup : sup ≤ 4 * τ) (hsup0 : 0 ≤ sup)
    (hElo : 1 / 4 * (τ ^ 2 * δ ^ 3) ≤ Elo) (ht : μ₂ * τ * δ ^ 3 / 2 ≤ t) (ht0 : 0 < t) :
    2 * (4 * ε₂ * S) / t * sup ≤ η * (Elo - 4 * ε₂ * S) := by
  rw [div_mul_eq_mul_div, div_le_iff₀ ht0]
  have hτ3 : (0:ℝ) < τ ^ 3 := by positivity
  have h1 : 2 * (4 * ε₂ * S) * sup ≤ 160 * ε₂ * τ ^ 3 := by
    have hSs : S * sup ≤ (5 * τ ^ 2) * (4 * τ) := mul_le_mul hS hsup hsup0 (by positivity)
    nlinarith [hSs]
  have hbr : 1 / 8 * (τ ^ 2 * δ ^ 3) ≤ Elo - 4 * ε₂ * S := by
    have hεS : 4 * ε₂ * S ≤ 4 * (δ ^ 3 / 160) * (5 * τ ^ 2) := by nlinarith
    nlinarith [hεS]
  have h2 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2)
      ≤ η * (Elo - 4 * ε₂ * S) * t := by
    have hle1 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) ≤ η * (Elo - 4 * ε₂ * S) :=
      mul_le_mul_of_nonneg_left hbr hη.le
    have hnn : (0:ℝ) ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) := by positivity
    have hnn2 : (0:ℝ) ≤ μ₂ * τ * δ ^ 3 / 2 := by positivity
    exact mul_le_mul hle1 ht hnn2 (le_trans hnn hle1)
  have h3 : 160 * ε₂ * τ ^ 3 ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2) := by
    have hkey : 160 * ε₂ ≤ η * μ₂ * δ ^ 6 / 16 := by linarith
    linarith only [mul_le_mul_of_nonneg_right hkey hτ3.le]
  linarith
/-- **The coupled block-allocation residual.**  Given the accuracy `ε`, a density threshold
`δ ≤ ε`, the block uniformity scale `ε₂` that the caller needs and a scale floor `T₀`, the residual
names a regularity window `ε₁₀ > 0`; for every regularity scale `ε₁ ≤ ε₁₀` it then names a relative
block size `α` with `ε₁/8 ≤ α`, `2α ≤ 1` and `(ε₁/8)/α ≤ ε₂` — the three inequalities the transfer
of regularity from the clusters to the blocks needs — and, for all large enough
`(ε₁/8)`-regular equipartitions, a family of block sub-triples at that `α` with pairwise disjoint
vertex-pair rectangles carrying the fractional optimum up to `ε|V|²`.

Compared with `Nibble.AX1.BlockCoverResidualFine` the two scales `ε₁` and `α` are no longer
universally quantified independently: the residual may demand that the regularity scale be fine
(hence the number of clusters large) and may pick the relative block size itself (hence the number
of blocks per cluster large).  Both are exactly what the reduction to AX1 leaves free, which is why
`Nibble.AX1.ax1_of_blockCoverCoupled` still goes through. -/
def BlockCoverResidualCoupled : Prop :=
  ∀ ε δ ε₂ T₀ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 → δ ≤ ε → 0 < ε₂ → 0 < T₀ →
  ∃ ε₁₀ : ℝ, 0 < ε₁₀ ∧
    ∀ ε₁ : ℝ, 0 < ε₁ → ε₁ ≤ ε₁₀ → ε₁ ≤ 1 →
    ∃ α : ℝ, ε₁ / 8 ≤ α ∧ 2 * α ≤ 1 ∧ ε₁ / 8 / α ≤ ε₂ ∧
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (P : Finpartition (univ : Finset V)),
      n₀ ≤ Fintype.card V →
      P.IsEquipartition →
      4 / ε₁ ≤ (P.parts.card : ℝ) →
      (P.parts.card : ℝ) ≤ ((SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ : ℕ) : ℝ) →
      P.IsUniform G (ε₁ / 8) →
      ∃ (τ : ℝ) (k : ℕ) (U W X A B C : ℕ → Finset V),
        T₀ ≤ τ ∧
        (∀ i < k, IsGridSubTriple G P (ε₁ / 8) δ α τ (U i) (W i) (X i) (A i) (B i) (C i)) ∧
        (∀ i < k, ∀ j < k, i ≠ j →
          Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) ∧
        nu3star (G.regularityReduced P (ε₁ / 8) (ε₁ / 4))
          ≤ (∑ i ∈ Finset.range k,
              ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
                + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
                + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
            + ε * (Fintype.card V : ℝ) ^ 2

theorem subTripleDesignLocalResidual_of_blockCoverCoupled (h : BlockCoverResidualCoupled) :
    SubTripleDesignLocalResidual := by
  classical
  intro ε hε μ hμ η hη d₀ hd₀
  -- ### the parameters of the construction
  obtain ⟨μ₂, hμ₂0, hμ₂1, hμ₂μ, hμ₂half⟩ :
      ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ μ ∧ 2 * m ≤ μ := by
    refine ⟨min μ 1 / 2, ?_, ?_, ?_, ?_⟩
    · have : 0 < min μ 1 := lt_min hμ one_pos; linarith
    · have : min μ 1 ≤ 1 := min_le_right _ _; linarith
    · have : min μ 1 ≤ μ := min_le_left _ _; linarith
    · have : min μ 1 ≤ μ := min_le_left _ _; linarith
  obtain ⟨δ, hδ0, hδhalf, hδε, hδsq⟩ :
      ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ d ≤ ε / 2 ∧ d / 2 ≤ (ε / 2) ^ 2 := by
    have h0 : 0 < min 1 ε := lt_min one_pos hε
    have h1 : min 1 ε ≤ 1 := min_le_left _ _
    have h2 : min 1 ε ≤ ε := min_le_right _ _
    refine ⟨min 1 ε * min 1 ε / 8, by positivity, by nlinarith, by nlinarith, by nlinarith⟩
  have hδ1 : δ ≤ 1 := by linarith
  have hδ3 : (0:ℝ) < δ ^ 3 := by positivity
  obtain ⟨T₀, hT₀0, hT₀1, hT₀2⟩ :
      ∃ T : ℝ, 0 < T ∧ 2 / (μ₂ * δ ^ 3) ≤ T ∧ d₀ / δ ^ 3 ≤ T := by
    refine ⟨2 / (μ₂ * δ ^ 3) + d₀ / δ ^ 3, by positivity, ?_, ?_⟩
    · have : (0:ℝ) ≤ d₀ / δ ^ 3 := by positivity
      linarith
    · have : (0:ℝ) < 2 / (μ₂ * δ ^ 3) := by positivity
      linarith
  -- ### the block uniformity scale the reduction needs
  obtain ⟨ε₂, hε₂0', hε₂1', hε₂A', hε₂C', hε₂D', hε₂E'⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ μ₂ * δ ^ 3 / 96 ∧ e ≤ η * μ₂ * δ ^ 6 / 2560 ∧
        e ≤ δ ^ 3 / 160 ∧ e ≤ ε / 8 := by
    refine ⟨min 1 (min (μ₂ * δ ^ 3 / 96) (min (η * μ₂ * δ ^ 6 / 2560)
      (min (δ ^ 3 / 160) (ε / 8)))), ?_, min_le_left _ _, ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min (by positivity)
        (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- ### the coupling: the residual names the regularity window it can serve
  obtain ⟨ε₁₀, hε₁₀0, hcoup⟩ := h (ε / 2) δ ε₂ T₀ (by linarith) hδ0 hδ1 hδε hε₂0' hT₀0
  obtain ⟨ε₁, hε₁0, hε₁1, hε₁b, hε₁ε, hε₁A, hε₁10⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ δ / 2 ∧ e ≤ ε ∧ e ≤ μ₂ * δ ^ 3 / 12 ∧ e ≤ ε₁₀ := by
    refine ⟨min 1 (min (δ / 2) (min ε (min (μ₂ * δ ^ 3 / 12) ε₁₀))), ?_, min_le_left _ _,
      ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min (by positivity)
        (lt_min hε (lt_min (by positivity) hε₁₀0)))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨ε₁, hε₁0, hε₁ε, hε₁1, ?_⟩
  -- ### the residual supplies the relative block size and the blocks
  obtain ⟨α, hαε, hα2, hε₂, n₀, hres⟩ := hcoup ε₁ hε₁0 hε₁10 hε₁1
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu _hrich
  obtain ⟨τ, k, U, W, X, A, B, C, hτT, hgrid, hdisj, hcov⟩ := hres V G P hV hP hPl hPb hPu
  -- ### the scale `τ` is large
  have hτpos : 0 < τ := lt_of_lt_of_le hT₀0 hτT
  have hτ2 : 2 / (μ₂ * δ ^ 3) ≤ τ := le_trans hT₀1 hτT
  have hτ2' : 2 ≤ τ * (μ₂ * δ ^ 3) := by
    rw [div_le_iff₀ (by positivity)] at hτ2; linarith
  have hτδ3 : 2 ≤ τ * δ ^ 3 := tau_delta3_lower hτpos hδ3 hμ₂1 hτ2'
  have hτδ8 : 8 ≤ τ * δ := tau_delta_lower hτpos hδ0 hδhalf hτδ3
  have hτd₀ : d₀ ≤ τ * δ ^ 3 := by
    have hle : d₀ / δ ^ 3 ≤ τ := le_trans hT₀2 hτT
    rw [div_le_iff₀ hδ3] at hle; linarith
  -- ### the local clauses of the design
  have hα0 : 0 < α := lt_of_lt_of_le (by positivity) hαε
  -- the derived windows for the block uniformity scale `ε₂ = (ε₁/8)/α`
  have hε₂0 : (0:ℝ) < ε₁ / 8 / α := by positivity
  have hε₂1 : ε₁ / 8 / α ≤ 1 := le_trans hε₂ hε₂1'
  have hε₂A : ε₁ / 8 / α ≤ μ₂ * δ ^ 3 / 96 := le_trans hε₂ hε₂A'
  have hε₂C : ε₁ / 8 / α ≤ η * μ₂ * δ ^ 6 / 2560 := le_trans hε₂ hε₂C'
  have hε₂D : ε₁ / 8 / α ≤ δ ^ 3 / 160 := le_trans hε₂ hε₂D'
  have hε₂E : ε₁ / 8 / α ≤ ε / 8 := le_trans hε₂ hε₂E'
  have hδ3le : δ ^ 3 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 1 ≤ 3)
  have hμδpos : (0:ℝ) ≤ μ₂ * δ ^ 3 := by positivity
  have hErr : ε₁ / 8 + 2 * (ε₁ / 8 / α) ≤ μ₂ * δ ^ 3 / 12 := by
    have h1 : ε₁ / 8 ≤ μ₂ * δ ^ 3 / 96 := by linarith
    linarith
  have hdense : 2 * (ε₁ / 8 / α) + ε₁ / 8 ≤ δ := by
    have h1 : ε₁ / 8 ≤ δ / 16 := by linarith
    have h2 : δ ^ 3 / 80 ≤ δ / 80 := by linarith
    linarith
  have hde : ε₁ / 4 ≤ δ := by linarith
  have hshape := subTripleShape_of_gridSubTriples G P U W X A B C hε₁0 hαε (by linarith)
    hδ0 hδ1 hμ₂0 hμ₂1 hde hErr hdense hτ2 hgrid hdisj
  -- ### the numerical data of each sub-triple
  have hdata : ∀ i < k,
      (Disjoint (A i) (B i) ∧ Disjoint (A i) (C i) ∧ Disjoint (B i) (C i)) ∧
      (|((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
          - (G.edgeDensity (U i) (W i) : ℝ)| ≤ ε₁ / 8 ∧
        |((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
          - (G.edgeDensity (U i) (X i) : ℝ)| ≤ ε₁ / 8 ∧
        |((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
          - (G.edgeDensity (W i) (X i) : ℝ)| ≤ ε₁ / 8) := by
    intro i hi
    obtain ⟨h1, -, h3⟩ := gridSubTriple_data G P hε₁0 hαε (by linarith) hde (hgrid i hi)
    exact ⟨h1, h3⟩
  have hsize : ∀ (s dens : ℝ), δ ≤ dens → dens ≤ 1 → |s - τ * dens| ≤ 1 →
      3 / 4 * (τ * δ) ≤ s ∧ s ≤ 5 / 4 * τ :=
    fun s dens h1 h2 habs => block_size_bounds hτpos hδ0 hδ1 hτδ8 h1 h2 habs
  have hblocks : ∀ i < k,
      (3 / 4 * (τ * δ) ≤ (#(A i) : ℝ) ∧ (#(A i) : ℝ) ≤ 5 / 4 * τ) ∧
      (3 / 4 * (τ * δ) ≤ (#(B i) : ℝ) ∧ (#(B i) : ℝ) ≤ 5 / 4 * τ) ∧
      (3 / 4 * (τ * δ) ≤ (#(C i) : ℝ) ∧ (#(C i) : ℝ) ≤ 5 / 4 * τ) := by
    intro i hi
    obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := hgrid i hi
    obtain ⟨⟨hx, hx1⟩, ⟨hy, hy1⟩, ⟨hz, hz1⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact ⟨hsize _ _ hz hz1 hsA, hsize _ _ hy hy1 hsB, hsize _ _ hx hx1 hsC⟩
  have hHdens : ∀ S T : Finset V,
      (0:ℝ) ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity S T : ℚ) : ℝ) := by
    intro S T
    exact_mod_cast (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity_nonneg S T
  -- ### the objects of the design
  refine ⟨ε₁ / 8 / α, μ₂, (μ - μ₂) * τ * δ ^ 3 / 2, k, A, B, C,
    fun i => τ * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
      * (G.edgeDensity (W i) (X i) : ℝ)),
    fun i => ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
      * (#(A i) : ℝ) * (#(B i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
      * (#(A i) : ℝ) * (#(C i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
      * (#(B i) : ℝ) * (#(C i) : ℝ),
    hshape, by positivity, by linarith, ?_, hη.le, hμ₂μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 < t`
    exact t_pos hτpos hδ3 hμ₂0 hμ₂half
  · -- `d₀ ≤ d i`
    intro i hi
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact d_lower hτpos hδ0 hx hy hz hτd₀
  · -- `0 ≤ d i`
    intro i hi
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact d_nonneg hτpos hδ0 hx hy hz
  · -- the slack `2t ≤ (μ - μ₂) d i`
    intro i hi
    obtain ⟨⟨hx, -⟩, ⟨hy, -⟩, ⟨hz, -⟩⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    exact slack_bound hτpos hδ0 hx hy hz hμ₂half hμ₂0
  · -- `Elo i` really is a lower bound for the number of edges
    intro i hi
    obtain ⟨⟨hd1, hd2, hd3⟩, -⟩ := hdata i hi
    exact three_edgeDensity_mul_le_tripleGraph_edges
      (G.regularityReduced P (ε₁ / 8) (ε₁ / 4)) (A i) (B i) (C i) hd1 hd2 hd3
  · -- the exceptional-edge clause
    intro i hi
    obtain ⟨-, habs1, -, -⟩ := hdata i hi
    obtain ⟨⟨-, -⟩, -, -⟩ := gridSubTriple_density_mem G P (hgrid i hi)
    obtain ⟨⟨haL, haU⟩, ⟨hbL, hbU⟩, ⟨hcL, hcU⟩⟩ := hblocks i hi
    obtain ⟨ha0, hb0, hc0, hSle, hS0, hsuple, hsup0⟩ :=
      area_bounds hτpos hδ0 hτδ8 haL haU hbL hbU hcL hcU
    have hdAB : δ - ε₁ / 8
        ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)) := by
      have hlow := (abs_le.mp habs1).1
      have hUW := (gridSubTriple_density_mem G P (hgrid i hi)).1.1
      linarith
    have hElo := elo_lower (ε₁ := ε₁) hτpos hδ0 hδ1 hε₁0 hε₁b hdAB
      (hHdens (A i) (C i)) (hHdens (B i) (C i)) haL hbL hc0 ha0 hb0
    simp only [designBad, designSupport]
    exact exc_bound hτpos hδ0 hμ₂0 hη hε₂0 hε₂C hε₂D hSle hsuple hsup0 hElo
      (t_lower hτpos hδ3 hμ₂half) (t_pos hτpos hδ3 hμ₂0 hμ₂half)
  · -- the covering clause
    have hSsum : ∑ i ∈ Finset.range k,
        ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
          + (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ (Fintype.card V : ℝ) ^ 2 / 2 :=
      sum_area_le_of_rect_disjoint A B C (fun i hi => (hdata i hi).1.1)
        (fun i hi => (hdata i hi).1.2.1) (fun i hi => (hdata i hi).1.2.2) hdisj
    have hper : ∀ i ∈ Finset.range k,
        ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
          - (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 * ((#(A i) : ℝ) * (#(B i) : ℝ)
              + (#(A i) : ℝ) * (#(C i) : ℝ) + (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
              * (#(A i) : ℝ) * (#(B i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
              * (#(A i) : ℝ) * (#(C i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
              * (#(B i) : ℝ) * (#(C i) : ℝ)
            - 4 * (ε₁ / 8 / α) * ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
                + (#(B i) : ℝ) * (#(C i) : ℝ))) / 3 := by
      intro i hmem
      have hi : i < k := Finset.mem_range.mp hmem
      obtain ⟨-, habs1, habs2, habs3⟩ := hdata i hi
      obtain ⟨⟨haL, haU⟩, ⟨hbL, hbU⟩, ⟨hcL, hcU⟩⟩ := hblocks i hi
      obtain ⟨ha0, hb0, hc0, -, -, -, -⟩ :=
        area_bounds hτpos hδ0 hτδ8 haL haU hbL hbU hcL hcU
      exact cover_step habs1 habs2 habs3 ha0 hb0 hc0
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum] at hsum
    have hcoef : (0:ℝ) ≤ (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hSsum hcoef
    have hV2 : (0:ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
    have hK : (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 ≤ ε := by linarith
    have h3 : (ε₁ / 8 + 4 * (ε₁ / 8 / α)) / 3 * ((Fintype.card V : ℝ) ^ 2 / 2)
        ≤ ε / 2 * (Fintype.card V : ℝ) ^ 2 := cover_tail hK hV2
    simp only [designBad]
    linarith only [hcov, hsum, h2, h3]

/-- **AX1 from the coupled block-allocation residual.** -/
theorem ax1_of_blockCoverCoupled (h : BlockCoverResidualCoupled) : AX1Statement :=
  ax1_of_subTripleDesignLocal (subTripleDesignLocalResidual_of_blockCoverCoupled h)

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1

end





/-! # CoreGapBlockAlloc -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The covering sum of one member -/

/-- A product of two prescribed sizes is the product of the two scaled densities, up to `2τ + 1`. -/
theorem prod_approx_of_sizes {τ y z a b : ℝ} (hτ : 0 ≤ τ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : |a - τ * z| ≤ 1) (hb : |b - τ * y| ≤ 1) :
    |a * b - τ ^ 2 * (y * z)| ≤ 2 * τ + 1 := by
  have key : a * b - τ ^ 2 * (y * z)
      = (a - τ * z) * (b - τ * y) + (τ * z) * (b - τ * y) + (τ * y) * (a - τ * z) := by ring
  have h1 : |(a - τ * z) * (b - τ * y)| ≤ 1 := by
    rw [abs_mul]
    calc |a - τ * z| * |b - τ * y| ≤ 1 * 1 :=
          mul_le_mul ha hb (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  have h2 : |(τ * z) * (b - τ * y)| ≤ τ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ τ * z)]
    calc τ * z * |b - τ * y| ≤ τ * 1 * 1 := by
          apply mul_le_mul _ hb (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hz1 hτ
      _ = τ := by ring
  have h3 : |(τ * y) * (a - τ * z)| ≤ τ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ τ * y)]
    calc τ * y * |a - τ * z| ≤ τ * 1 * 1 := by
          apply mul_le_mul _ ha (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hy1 hτ
      _ = τ := by ring
  calc |a * b - τ ^ 2 * (y * z)|
      = |(a - τ * z) * (b - τ * y) + (τ * z) * (b - τ * y) + (τ * y) * (a - τ * z)| := by
        rw [key]
    _ ≤ |(a - τ * z) * (b - τ * y) + (τ * z) * (b - τ * y)| + |(τ * y) * (a - τ * z)| :=
        abs_add_le _ _
    _ ≤ (|(a - τ * z) * (b - τ * y)| + |(τ * z) * (b - τ * y)|) + |(τ * y) * (a - τ * z)| := by
        have := abs_add_le ((a - τ * z) * (b - τ * y)) ((τ * z) * (b - τ * y))
        linarith
    _ ≤ (1 + τ) + τ := by linarith
    _ = 2 * τ + 1 := by ring

/-- **The covering sum of one block sub-triple is balanced.**  With the prescribed sizes of
`Nibble.AX1.IsGridSubTriple`, the covering sum of a member is three times `τ²` times the product of
its three cluster densities, up to an additive `6τ + 3`. -/
theorem cover_approx_of_gridSubTriple (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de α τ : ℝ} {U W X A B C : Finset V}
    (hτ : 0 ≤ τ) (h : IsGridSubTriple G P ep de α τ U W X A B C) :
    |((G.edgeDensity U W : ℝ) * (#A : ℝ) * (#B : ℝ)
        + (G.edgeDensity U X : ℝ) * (#A : ℝ) * (#C : ℝ)
        + (G.edgeDensity W X : ℝ) * (#B : ℝ) * (#C : ℝ))
      - 3 * τ ^ 2 * ((G.edgeDensity U W : ℝ) * (G.edgeDensity U X : ℝ)
          * (G.edgeDensity W X : ℝ))| ≤ 6 * τ + 3 := by
  obtain ⟨-, -, -, -, -, -, -, hsA, hsB, hsC⟩ := h
  set x : ℝ := (G.edgeDensity U W : ℝ) with hx
  set y : ℝ := (G.edgeDensity U X : ℝ) with hy
  set z : ℝ := (G.edgeDensity W X : ℝ) with hz
  have hx0 : 0 ≤ x := by rw [hx]; exact_mod_cast G.edgeDensity_nonneg U W
  have hx1 : x ≤ 1 := by rw [hx]; exact_mod_cast G.edgeDensity_le_one U W
  have hy0 : 0 ≤ y := by rw [hy]; exact_mod_cast G.edgeDensity_nonneg U X
  have hy1 : y ≤ 1 := by rw [hy]; exact_mod_cast G.edgeDensity_le_one U X
  have hz0 : 0 ≤ z := by rw [hz]; exact_mod_cast G.edgeDensity_nonneg W X
  have hz1 : z ≤ 1 := by rw [hz]; exact_mod_cast G.edgeDensity_le_one W X
  -- the three balanced products
  have hAB : |(#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z)| ≤ 2 * τ + 1 :=
    prod_approx_of_sizes hτ hy0 hy1 hz0 hz1 hsA hsB
  have hAC : |(#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z)| ≤ 2 * τ + 1 :=
    prod_approx_of_sizes hτ hx0 hx1 hz0 hz1 hsA hsC
  have hBC : |(#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y)| ≤ 2 * τ + 1 :=
    prod_approx_of_sizes hτ hx0 hx1 hy0 hy1 hsB hsC
  -- multiply the `i`-th of them by the density of the `i`-th pair
  have step : ∀ {d u : ℝ}, 0 ≤ d → d ≤ 1 → |u| ≤ 2 * τ + 1 → |d * u| ≤ 2 * τ + 1 := by
    intro d u hd0 hd1 hu
    rw [abs_mul, abs_of_nonneg hd0]
    calc d * |u| ≤ 1 * (2 * τ + 1) :=
          mul_le_mul hd1 hu (abs_nonneg _) zero_le_one
      _ = 2 * τ + 1 := by ring
  have h1 : |x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))| ≤ 2 * τ + 1 := step hx0 hx1 hAB
  have h2 : |y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))| ≤ 2 * τ + 1 := step hy0 hy1 hAC
  have h3 : |z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))| ≤ 2 * τ + 1 := step hz0 hz1 hBC
  have hsum : (x * (#A : ℝ) * (#B : ℝ) + y * (#A : ℝ) * (#C : ℝ) + z * (#B : ℝ) * (#C : ℝ))
      - 3 * τ ^ 2 * (x * y * z)
      = x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))
        + y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))
        + z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y)) := by ring
  have habs : |(x * (#A : ℝ) * (#B : ℝ) + y * (#A : ℝ) * (#C : ℝ) + z * (#B : ℝ) * (#C : ℝ))
      - 3 * τ ^ 2 * (x * y * z)| ≤ 6 * τ + 3 := by
    rw [hsum]
    calc |x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))
            + y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))
            + z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))|
        ≤ |x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))
            + y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))|
          + |z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))| := abs_add_le _ _
      _ ≤ (|x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z))|
            + |y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z))|)
          + |z * ((#B : ℝ) * (#C : ℝ) - τ ^ 2 * (x * y))| := by
            have := abs_add_le (x * ((#A : ℝ) * (#B : ℝ) - τ ^ 2 * (y * z)))
              (y * ((#A : ℝ) * (#C : ℝ) - τ ^ 2 * (x * z)))
            linarith
      _ ≤ 6 * τ + 3 := by linarith
  exact habs

/-! ### Members on nearly disjoint cluster triples never clash -/

omit [Fintype V] in
/-- The two coordinates of a point of a rectangle lie in **two different** clusters of the
triple. -/
theorem exists_clusters_of_mem_tripleRect {U W X A B C : Finset V}
    (hUW : U ≠ W) (hUX : U ≠ X) (hWX : W ≠ X)
    (hA : A ⊆ U) (hB : B ⊆ W) (hC : C ⊆ X) {u v : V} (h : (u, v) ∈ tripleRect A B C) :
    ∃ S ∈ ({U, W, X} : Finset (Finset V)), ∃ T ∈ ({U, W, X} : Finset (Finset V)),
      S ≠ T ∧ u ∈ S ∧ v ∈ T := by
  classical
  rw [mem_tripleRect_iff, crossAdj] at h
  rcases h with h | h | h | h | h | h
  · exact ⟨U, by simp, W, by simp, hUW, hA h.1, hB h.2⟩
  · exact ⟨W, by simp, U, by simp, hUW.symm, hB h.1, hA h.2⟩
  · exact ⟨U, by simp, X, by simp, hUX, hA h.1, hC h.2⟩
  · exact ⟨X, by simp, U, by simp, hUX.symm, hC h.1, hA h.2⟩
  · exact ⟨W, by simp, X, by simp, hWX, hB h.1, hC h.2⟩
  · exact ⟨X, by simp, W, by simp, hWX.symm, hC h.1, hB h.2⟩

/-- **Automatic disjointness.**  If the cluster triples of two members share at most one cluster,
their vertex-pair rectangles are disjoint.  Hence the disjointness clause of the residual only ever
has to be verified for two members sharing a whole cluster *pair*. -/
theorem tripleRect_disjoint_of_clusters (P : Finpartition (univ : Finset V))
    {U W X U' W' X' A B C A' B' C' : Finset V}
    (hU : U ∈ P.parts) (hW : W ∈ P.parts) (hX : X ∈ P.parts)
    (hU' : U' ∈ P.parts) (hW' : W' ∈ P.parts) (hX' : X' ∈ P.parts)
    (hUW : U ≠ W) (hUX : U ≠ X) (hWX : W ≠ X)
    (hUW' : U' ≠ W') (hUX' : U' ≠ X') (hWX' : W' ≠ X')
    (hA : A ⊆ U) (hB : B ⊆ W) (hC : C ⊆ X)
    (hA' : A' ⊆ U') (hB' : B' ⊆ W') (hC' : C' ⊆ X')
    (hshare : #(({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V))) ≤ 1) :
    Disjoint (tripleRect A B C) (tripleRect A' B' C') := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨u, v⟩ hmem hmem'
  obtain ⟨S, hS, T, hT, hST, huS, hvT⟩ :=
    exists_clusters_of_mem_tripleRect hUW hUX hWX hA hB hC hmem
  obtain ⟨S', hS', T', hT', -, huS', hvT'⟩ :=
    exists_clusters_of_mem_tripleRect hUW' hUX' hWX' hA' hB' hC' hmem'
  have hmemP : ∀ {Y : Finset V}, Y ∈ ({U, W, X} : Finset (Finset V)) → Y ∈ P.parts := by
    intro Y hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl <;> assumption
  have hmemP' : ∀ {Y : Finset V}, Y ∈ ({U', W', X'} : Finset (Finset V)) → Y ∈ P.parts := by
    intro Y hY
    simp only [Finset.mem_insert, Finset.mem_singleton] at hY
    rcases hY with rfl | rfl | rfl <;> assumption
  have hSS' : S = S' := P.eq_of_mem_parts (hmemP hS) (hmemP' hS') huS huS'
  have hTT' : T = T' := P.eq_of_mem_parts (hmemP hT) (hmemP' hT') hvT hvT'
  have hSin : S ∈ ({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V)) :=
    Finset.mem_inter.mpr ⟨hS, hSS' ▸ hS'⟩
  have hTin : T ∈ ({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V)) :=
    Finset.mem_inter.mpr ⟨hT, hTT' ▸ hT'⟩
  have h2 : 1 < #(({U, W, X} : Finset (Finset V)) ∩ ({U', W', X'} : Finset (Finset V))) :=
    Finset.one_lt_card.mpr ⟨S, hSin, T, hTin, hST⟩
  omega

/-! ### The bookkeeping bridge: value of the family ⟹ the covering clause -/

/-- **The covering clause of the residual follows from a lower bound on the *value* of the
family.**  Write `x, y, z` for the three cluster densities of a member; its *value* is `τ²·xyz`,
one third of its balanced covering sum (`Nibble.AX1.cover_approx_of_gridSubTriple`).  If the total
value of the family recovers the cluster capacity LP of the cluster pairs of density at least `θ`,
up to `E`, then the covering clause of `Nibble.AX1.BlockCoverResidualFine` holds with total error
`θ·|V|²/6 + E + k·(2τ + 1)`.

This is the *tight bookkeeping* of the block-allocation route: by
`Nibble.AX1.cover_sum_le_cluster_capacity` the covering sum of a disjoint family can never exceed
the same capacity LP, so the hypothesis `hval` is not only sufficient but essentially necessary. -/
theorem nu3star_le_cover_of_family_value
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    {ep de ep₀ de₀ α τ θ E : ℝ} {k : ℕ} (U W X A B C : ℕ → Finset V)
    (hτ : 0 ≤ τ) (hθ : 0 ≤ θ)
    (hgrid : ∀ i < k, IsGridSubTriple G P ep₀ de₀ α τ (U i) (W i) (X i) (A i) (B i) (C i))
    (hval : (∑ p ∈ P.parts.offDiag.filter (fun p => θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
              (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)) / 6
            ≤ (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
                * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ))) + E) :
    nu3star (G.regularityReduced P ep de)
      ≤ (∑ i ∈ Finset.range k,
          ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
        + (θ * (Fintype.card V : ℝ) ^ 2 / 6 + E + (k : ℝ) * (2 * τ + 1)) := by
  classical
  -- each member's value is at most a third of its covering sum, up to `2τ + 1`
  have hterm : ∀ i ∈ Finset.range k,
      τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
          * (G.edgeDensity (W i) (X i) : ℝ))
        ≤ ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
          + (2 * τ + 1) := by
    intro i hi
    have h := cover_approx_of_gridSubTriple G P hτ (hgrid i (Finset.mem_range.mp hi))
    have := (abs_le.mp h).1
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
    ← Finset.sum_div] at hsum
  have hcap := nu3star_regularityReduced_le_dense_cluster_capacity G P ep de (θ := θ) hθ
  linarith

/-! ### Axiom check -/

section AxCheck





end AxCheck

end Nibble.AX1

end


/-! # ClusterTripleLP -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The program -/

/-- **The density capacity of a cluster pair**: `d(S,T)·|S|·|T|`, the number of edges of `G`
between `S` and `T`. -/
def clusterPairCap (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) : ℝ :=
  (G.edgeDensity S T : ℝ) * (#S : ℝ) * (#T : ℝ)

/-- The cluster triples through a given pair of clusters. -/
def triplesThrough (P : Finpartition (univ : Finset V))
    (S T : {S : Finset V // S ∈ P.parts}) : Finset (Finset {S : Finset V // S ∈ P.parts}) :=
  univ.filter (fun th => S ∈ th ∧ T ∈ th)

/-- **Feasibility for the cluster-triple LP**: nonnegative weights on the cluster triples, supported
on the triangles of the cluster graph, whose total through any cluster pair is at most the density
capacity of that pair. -/
def IsClusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) : Prop :=
  (∀ th, 0 ≤ x th) ∧
  (∀ th, x th ≠ 0 → th ∈ (hostGraph G P ep de).cliqueFinset 3) ∧
  (∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
    ∑ th ∈ triplesThrough P S T, x th ≤ clusterPairCap G (S : Finset V) (T : Finset V))

/-- The value of a point of the cluster-triple LP. -/
def clusterLPValue {P : Finpartition (univ : Finset V)}
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) : ℝ := ∑ th, x th

/-- The support of a point of the cluster-triple LP. -/
noncomputable def clusterLPSupport {P : Finpartition (univ : Finset V)}
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) :
    Finset (Finset {S : Finset V // S ∈ P.parts}) := univ.filter (fun th => x th ≠ 0)

/-! ### The bridge: `ν₃*` of the reduced graph is below the LP -/

/-- The fibre decomposition of a sum over the triangles of the reduced graph along cluster
triples. -/
private theorem sum_fiber_hostTri (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    (f : Finset V → ℝ) (A : Finset (Finset {S : Finset V // S ∈ P.parts})) :
    ∑ th ∈ A, (∑ t ∈ ((G.regularityReduced P ep de).cliqueFinset 3).filter
        (fun t => hostTri P t = th), f t)
      = ∑ t ∈ ((G.regularityReduced P ep de).cliqueFinset 3).filter
          (fun t => hostTri P t ∈ A), f t := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := hostTri P)
    (s := ((G.regularityReduced P ep de).cliqueFinset 3).filter (fun t => hostTri P t ∈ A))
    (t := A) (fun t ht => (Finset.mem_filter.mp ht).2) f]
  refine Finset.sum_congr rfl fun th hth => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext t
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hth⟩, rfl⟩
  · rintro ⟨⟨ht, -⟩, hEq⟩; exact ⟨ht, hEq⟩

/-- **The bridge.**  For every slack `η > 0` there is a feasible point of the cluster-triple LP
whose value is within `η` of `ν₃*` of the regularity-reduced graph. -/
theorem exists_clusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ x : Finset {S : Finset V // S ∈ P.parts} → ℝ, IsClusterTripleLP G P ep de x ∧
      nu3star (G.regularityReduced P ep de) ≤ clusterLPValue x + η := by
  classical
  set R : SimpleGraph V := G.regularityReduced P ep de with hR
  have hne : Set.Nonempty
      {x : ℝ | ∃ w, IsFracPacking R w ∧ x = ∑ T ∈ triangleHypergraphE R, w T} :=
    ⟨0, ⟨fun _ => 0, isFracPacking_zero R, by simp⟩⟩
  obtain ⟨v, ⟨w, hw, rfl⟩, hv⟩ :=
    exists_lt_of_lt_csSup hne (show nu3star R - η < nu3star R by linarith)
  refine ⟨fun th => ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th),
    w (t.powersetCard 2), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun th => Finset.sum_nonneg fun t _ => hw.1 _
  · -- the support consists of cluster triples of triangles
    intro th hth
    by_contra hnot
    refine hth (Finset.sum_eq_zero fun t ht => ?_)
    rw [Finset.mem_filter] at ht
    exact absurd (ht.2 ▸ hostTri_mem_cliqueFinset G P ep de ht.1) hnot
  · -- the capacity constraint
    intro S T hST
    have hEq : ∑ th ∈ triplesThrough P S T,
          (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th), w (t.powersetCard 2))
        = ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ triplesThrough P S T),
            w (t.powersetCard 2) :=
      sum_fiber_hostTri G P ep de (fun t => w (t.powersetCard 2)) _
    rw [hEq]
    -- the triangles counted are injectively charged to hyperedges through the pair
    set C := (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ triplesThrough P S T) with hC
    have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2) (C : Set (Finset V)) :=
      (triangle_powersetCard_two_injOn R).mono (by
        intro t ht
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
    have himg : ∑ t ∈ C, w (t.powersetCard 2)
        = ∑ T' ∈ C.image (fun t => t.powersetCard 2), w T' := (Finset.sum_image hinj).symm
    have hsub : C.image (fun t => t.powersetCard 2)
        ⊆ (triangleHypergraphE R).filter
          (fun T' => ∃ a ∈ (S : Finset V), ∃ b ∈ (T : Finset V), ({a, b} : Finset V) ∈ T') := by
      intro T' hT'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT'
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image_of_mem _ ht.1, ?_⟩
      have h2 := Finset.mem_filter.mp ht.2
      exact exists_edge_of_mem_hostTri P hST h2.2.1 h2.2.2
    have hmono : ∑ T' ∈ C.image (fun t => t.powersetCard 2), w T'
        ≤ ∑ T' ∈ (triangleHypergraphE R).filter
            (fun T' => ∃ a ∈ (S : Finset V), ∃ b ∈ (T : Finset V), ({a, b} : Finset V) ∈ T'),
            w T' :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun T' _ _ => hw.1 T'
    have hcapR := sum_fracPacking_cluster_pair_le R hw (S : Finset V) (T : Finset V)
    have hmono2 : (#(R.interedges (S : Finset V) (T : Finset V)) : ℝ)
        ≤ (#(G.interedges (S : Finset V) (T : Finset V)) : ℝ) := by
      exact_mod_cast card_interedges_mono (G := G) (H := R)
        (hR ▸ SimpleGraph.regularityReduced_le) (S : Finset V) (T : Finset V)
    have hcapG : (#(G.interedges (S : Finset V) (T : Finset V)) : ℝ)
        = clusterPairCap G (S : Finset V) (T : Finset V) :=
      (edgeDensity_mul_card_mul_card G (S : Finset V) (T : Finset V)).symm
    rw [himg]
    rw [hcapG] at hmono2
    linarith
  · -- the value
    have hval : clusterLPValue (P := P)
        (fun th => ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th),
          w (t.powersetCard 2))
        = ∑ T ∈ triangleHypergraphE R, w T := by
      rw [clusterLPValue, sum_triangleHypergraphE R w]
      exact sum_fiber_hostTri G P ep de (fun t => w (t.powersetCard 2)) univ |>.trans
        (Finset.sum_congr (Finset.filter_true_of_mem fun t _ => Finset.mem_univ _) fun _ _ => rfl)
    rw [hval]
    linarith

/-! ### Sparsification -/

/-- The column of a cluster triple: its indicator on ordered pairs of distinct clusters. -/
private def lpCol (P : Finpartition (univ : Finset V))
    (th : Finset {S : Finset V // S ∈ P.parts}) :
    ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts}) → ℝ :=
  fun p => if p.1 ≠ p.2 ∧ p.1 ∈ th ∧ p.2 ∈ th then 1 else 0

/-- The pair sums of a weighting, read off the columns. -/
private theorem sum_triplesThrough_eq (P : Finpartition (univ : Finset V))
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ)
    {S T : {S : Finset V // S ∈ P.parts}} (hST : S ≠ T) :
    ∑ th ∈ triplesThrough P S T, x th = ∑ th, x th * lpCol P th (S, T) := by
  classical
  rw [triplesThrough, Finset.sum_filter]
  refine Finset.sum_congr rfl fun th _ => ?_
  by_cases h : S ∈ th ∧ T ∈ th
  · simp [lpCol, h, hST]
  · simp [lpCol, h, hST]

/-- A triple in the support of a feasible point contains two distinct clusters. -/
private theorem exists_pair_of_support (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {y : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hy : IsClusterTripleLP G P ep de y)
    {th : Finset {S : Finset V // S ∈ P.parts}} (hth : th ∈ clusterLPSupport y) :
    ∃ S T : {S : Finset V // S ∈ P.parts}, S ≠ T ∧ th ∈ triplesThrough P S T := by
  classical
  have hne : y th ≠ 0 := (Finset.mem_filter.mp hth).2
  have htri := hy.2.1 th hne
  have hcard : #th = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htri).card_eq
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  exact ⟨a, b, hab, by simp [triplesThrough]⟩

/-- **Sparsification of the cluster-triple LP.**  A feasible point can be replaced by a feasible
point of at least the same value whose support has at most `#P.parts ^ 2` triples. -/
theorem exists_sparse_clusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {x : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hx : IsClusterTripleLP G P ep de x) :
    ∃ y : Finset {S : Finset V // S ∈ P.parts} → ℝ, IsClusterTripleLP G P ep de y ∧
      clusterLPValue x ≤ clusterLPValue y ∧ #(clusterLPSupport y) ≤ #P.parts ^ 2 := by
  classical
  set Good : ℕ → Prop := fun n => ∃ y, IsClusterTripleLP G P ep de y ∧
    clusterLPValue x ≤ clusterLPValue y ∧ #(clusterLPSupport y) = n with hGoodDef
  have hGne : ∃ n, Good n := ⟨_, x, hx, le_rfl, rfl⟩
  obtain ⟨y, hy, hxy, hysupp⟩ := Nat.find_spec hGne
  have hmin : ∀ m, m < Nat.find hGne → ¬ Good m := fun m hm => Nat.find_min hGne hm
  refine ⟨y, hy, hxy, ?_⟩
  by_contra hbig
  push Not at hbig
  -- more support than the dimension of the pair space: a linear dependency among the columns
  have hdim : Module.finrank ℝ
      (({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts}) → ℝ) = #P.parts ^ 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, card_hostGraph_vertices, sq]
  have hnli : ¬ LinearIndependent ℝ
      (fun th : {th // th ∈ clusterLPSupport y} => lpCol P (th : Finset _)) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, hdim] at this
    omega
  obtain ⟨g, hg0, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hnli
  -- extend the relation by zero off the support
  set z : Finset {S : Finset V // S ∈ P.parts} → ℝ :=
    fun th => if h : th ∈ clusterLPSupport y then g ⟨th, h⟩ else 0 with hzdef
  have hzsupp : ∀ th, z th ≠ 0 → th ∈ clusterLPSupport y := by
    intro th hth
    by_contra h
    rw [hzdef] at hth
    simp only [dite_eq_right h, ne_eq, not_true_eq_false] at hth
  have hzcoe : ∀ i : {th // th ∈ clusterLPSupport y}, z (i : Finset _) = g i := by
    intro i
    rw [hzdef]
    simp [i.2]
  have hzne : z (i₀ : Finset _) ≠ 0 := by rw [hzcoe i₀]; exact hi₀
  have hzrel : ∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
      ∑ th ∈ triplesThrough P S T, z th = 0 := by
    intro S T hST
    have hcol : ∑ i : {th // th ∈ clusterLPSupport y},
        g i * lpCol P (i : Finset _) (S, T) = 0 := by
      have h := congrFun hg0 (S, T)
      simpa [Finset.sum_apply] using h
    rw [sum_triplesThrough_eq P z hST]
    have hsplit : ∑ th, z th * lpCol P th (S, T)
        = ∑ th ∈ clusterLPSupport y, z th * lpCol P th (S, T) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun th _ hth => ?_).symm
      have hz : z th = 0 := by
        by_contra hzz
        exact hth (hzsupp th hzz)
      rw [hz, zero_mul]
    rw [hsplit, ← Finset.sum_coe_sort (clusterLPSupport y)
      (fun th => z th * lpCol P th (S, T))]
    rw [← hcol]
    exact Finset.sum_congr rfl fun i _ => by rw [hzcoe i]
  -- choose the sign so that the value does not decrease
  obtain ⟨u, husupp, hurel, huval, th₀, hth₀⟩ :
      ∃ u : Finset {S : Finset V // S ∈ P.parts} → ℝ,
        (∀ th, u th ≠ 0 → th ∈ clusterLPSupport y) ∧
        (∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T → ∑ th ∈ triplesThrough P S T, u th = 0) ∧
        0 ≤ ∑ th, u th ∧ ∃ th₀, u th₀ ≠ 0 := by
    by_cases hsum : 0 ≤ ∑ th, z th
    · exact ⟨z, hzsupp, hzrel, hsum, (i₀ : Finset _), hzne⟩
    · refine ⟨fun th => -z th, fun th hth => hzsupp th (by simpa using hth), ?_, ?_,
        (i₀ : Finset _), by simpa using hzne⟩
      · intro S T hST
        simp only [Finset.sum_neg_distrib, hzrel S T hST, neg_zero]
      · simp only [Finset.sum_neg_distrib]
        linarith only [not_le.mp hsum]
  by_cases hallpos : ∀ th, 0 ≤ u th
  · -- a nonnegative relation must vanish: its pair sum is zero
    exfalso
    have hpos : 0 < u th₀ := lt_of_le_of_ne (hallpos th₀) (Ne.symm hth₀)
    obtain ⟨S, T, hST, hmem⟩ := exists_pair_of_support G P ep de hy (husupp th₀ hth₀)
    have hle : u th₀ ≤ ∑ th ∈ triplesThrough P S T, u th :=
      Finset.single_le_sum (fun th _ => hallpos th) hmem
    rw [hurel S T hST] at hle
    linarith
  · -- push along the relation until a coordinate vanishes
    push Not at hallpos
    obtain ⟨θ, hθ⟩ := hallpos
    set Neg : Finset (Finset {S : Finset V // S ∈ P.parts}) := univ.filter (fun th => u th < 0)
      with hNegDef
    have hNegne : Neg.Nonempty := ⟨θ, by simp [hNegDef, hθ]⟩
    obtain ⟨θ₁, hθ₁mem, hθ₁min⟩ := Finset.exists_min_image Neg (fun th => y th / (-u th)) hNegne
    set t : ℝ := y θ₁ / (-u θ₁) with htdef
    have hθ₁neg : u θ₁ < 0 := (Finset.mem_filter.mp hθ₁mem).2
    have hθ₁supp : θ₁ ∈ clusterLPSupport y := husupp θ₁ (ne_of_lt hθ₁neg)
    have hyθ₁ : 0 < y θ₁ :=
      lt_of_le_of_ne (hy.1 θ₁) (Ne.symm (Finset.mem_filter.mp hθ₁supp).2)
    have ht0 : 0 < t := div_pos hyθ₁ (by linarith)
    set y' : Finset {S : Finset V // S ∈ P.parts} → ℝ := fun th => y th + t * u th with hy'def
    have hy'nonneg : ∀ th, 0 ≤ y' th := by
      intro th
      rcases lt_or_ge (u th) 0 with hneg | hpos
      · have hmemN : th ∈ Neg := by simp [hNegDef, hneg]
        have hle := hθ₁min th hmemN
        have hposth : (0:ℝ) < -u th := by linarith
        have h1 : t * (-u th) ≤ y th := by
          have h2 := mul_le_mul_of_nonneg_right hle hposth.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hposth)] at h2
        simp only [hy'def]
        nlinarith only [h1]
      · have : 0 ≤ t * u th := mul_nonneg ht0.le hpos
        simp only [hy'def]
        linarith [hy.1 th]
    have hy'supp : ∀ th, y' th ≠ 0 → th ∈ clusterLPSupport y := by
      intro th hth
      by_contra hnot
      have h1 : y th = 0 := by
        by_contra h
        exact hnot (by simp [clusterLPSupport, h])
      have h2 : u th = 0 := by
        by_contra h
        exact hnot (husupp th h)
      simp [hy'def, h1, h2] at hth
    have hy'sum : ∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
        ∑ th ∈ triplesThrough P S T, y' th = ∑ th ∈ triplesThrough P S T, y th := by
      intro S T hST
      simp only [hy'def, Finset.sum_add_distrib, ← Finset.mul_sum, hurel S T hST, mul_zero,
        add_zero]
    have hy'val : ∑ th, y' th = (∑ th, y th) + t * ∑ th, u th := by
      simp only [hy'def, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hy'feas : IsClusterTripleLP G P ep de y' := by
      refine ⟨hy'nonneg, fun th hth => hy.2.1 th ?_, fun S T hST => ?_⟩
      · exact (Finset.mem_filter.mp (hy'supp th hth)).2
      · rw [hy'sum S T hST]; exact hy.2.2 S T hST
    have hy'value : clusterLPValue x ≤ clusterLPValue y' := by
      have : 0 ≤ t * ∑ th, u th := mul_nonneg ht0.le huval
      simp only [clusterLPValue] at hxy ⊢
      rw [hy'val]
      linarith
    -- the support has strictly shrunk
    have hsubset : clusterLPSupport y' ⊆ clusterLPSupport y := by
      intro th hth
      exact hy'supp th (Finset.mem_filter.mp hth).2
    have hcancel : y θ₁ / (-u θ₁) * (-u θ₁) = y θ₁ :=
      div_mul_cancel₀ _ (by linarith : (-u θ₁) ≠ 0)
    have hθ₁zero : y' θ₁ = 0 := by
      simp only [hy'def, htdef]
      linear_combination -hcancel
    have hstrict : clusterLPSupport y' ⊂ clusterLPSupport y := by
      refine ⟨hsubset, fun hsup => ?_⟩
      have : θ₁ ∈ clusterLPSupport y' := hsup hθ₁supp
      exact (Finset.mem_filter.mp this).2 hθ₁zero
    have hlt : #(clusterLPSupport y') < Nat.find hGne := by
      rw [← hysupp]
      exact Finset.card_lt_card hstrict
    exact hmin _ hlt ⟨y', hy'feas, hy'value, rfl⟩

/-- **The bridge and the sparsification, combined.**  For every slack `η > 0` there is a feasible
point of the cluster-triple LP with at most `#P.parts ^ 2` triples in its support whose value is
within `η` of `ν₃*` of the regularity-reduced graph. -/
theorem exists_sparse_clusterTripleLP_nu3star (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ y : Finset {S : Finset V // S ∈ P.parts} → ℝ, IsClusterTripleLP G P ep de y ∧
      #(clusterLPSupport y) ≤ #P.parts ^ 2 ∧
      nu3star (G.regularityReduced P ep de) ≤ clusterLPValue y + η := by
  obtain ⟨x, hx, hxnu⟩ := exists_clusterTripleLP G P ep de hη
  obtain ⟨y, hy, hxy, hcard⟩ := exists_sparse_clusterTripleLP G P ep de hx
  exact ⟨y, hy, hcard, by linarith⟩

/-! ### The covering clause, in LP form -/

/-- **The covering clause of the residual, in LP form.**  If the total *value* `τ²·xyz` of a family
of block sub-triples recovers the value of a point of the cluster-triple LP that itself dominates
`ν₃*` (up to `η`), then the covering clause of `Nibble.AX1.BlockCoverResidualCoupled` holds with
total error `E + η + k·(2τ + 1)`.

This is the LP-form replacement of `Nibble.AX1.nu3star_le_cover_of_family_value`, whose right-hand
side is the *full* cluster capacity: the full capacity is not reachable by a coherent family of
block sub-triples — a cluster triple with `d(S,T) = 1` and `d(S,Y) = d(T,Y) = θ` cannot tile
`S × T` — whereas the LP optimum is exactly what the coarse-cell construction realises. -/
theorem nu3star_le_cover_of_family_lp_value
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    {ep de ep₀ de₀ α τ E η : ℝ} {k : ℕ} (U W X A B C : ℕ → Finset V) (hτ : 0 ≤ τ)
    (hgrid : ∀ i < k, IsGridSubTriple G P ep₀ de₀ α τ (U i) (W i) (X i) (A i) (B i) (C i))
    {x : Finset {S : Finset V // S ∈ P.parts} → ℝ}
    (hnu : nu3star (G.regularityReduced P ep de) ≤ clusterLPValue x + η)
    (hval : clusterLPValue x
        ≤ (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
            * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ))) + E) :
    nu3star (G.regularityReduced P ep de)
      ≤ (∑ i ∈ Finset.range k,
          ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
        + (E + η + (k : ℝ) * (2 * τ + 1)) := by
  classical
  have hterm : ∀ i ∈ Finset.range k,
      τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
          * (G.edgeDensity (W i) (X i) : ℝ))
        ≤ ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ)) / 3
          + (2 * τ + 1) := by
    intro i hi
    have h := cover_approx_of_gridSubTriple G P hτ (hgrid i (Finset.mem_range.mp hi))
    have := (abs_le.mp h).1
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range,
    ← Finset.sum_div] at hsum
  linarith

/-! ### Axiom check -/

section AxCheck






end AxCheck

end Nibble.AX1

end


/-! # ClusterTripleLPCount -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The fibre identity.**  Summing the LP mass through the pairs of a set `F` of ordered cluster
pairs charges every triple with the number of pairs of `F` it contains. -/
theorem sum_pair_fibers (P : Finpartition (univ : Finset V))
    (y : Finset {S : Finset V // S ∈ P.parts} → ℝ)
    (F : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})) :
    ∑ p ∈ F, ∑ th ∈ triplesThrough P p.1 p.2, y th
      = ∑ th, y th * (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
  classical
  have h1 : ∀ p ∈ F, ∑ th ∈ triplesThrough P p.1 p.2, y th
      = ∑ th, (if p.1 ∈ th ∧ p.2 ∈ th then y th else 0) := by
    intro p _
    rw [triplesThrough, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun th _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The sizes of two clusters multiply out to at most `|V|²` over all ordered pairs. -/
theorem sum_card_mul_card_le (P : Finpartition (univ : Finset V)) :
    ∑ p ∈ (univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})),
        (#(p.1 : Finset V) : ℝ) * (#(p.2 : Finset V) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hsum : ∑ S : {S : Finset V // S ∈ P.parts}, (#(S : Finset V) : ℝ)
      = (Fintype.card V : ℝ) := by
    have h : ∑ S ∈ P.parts, #S = Fintype.card V := by
      rw [P.sum_card_parts, Finset.card_univ]
    have h2 : ∑ S : {S : Finset V // S ∈ P.parts}, (#(S : Finset V) : ℝ)
        = ∑ S ∈ P.parts, (#S : ℝ) := by
      rw [← Finset.sum_attach P.parts (fun S => (#S : ℝ))]
      rfl
    rw [h2]
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
  have hprod : ∑ p ∈ (univ : Finset ({S : Finset V // S ∈ P.parts} ×
        {S : Finset V // S ∈ P.parts})), (#(p.1 : Finset V) : ℝ) * (#(p.2 : Finset V) : ℝ)
      = (∑ S : {S : Finset V // S ∈ P.parts}, (#(S : Finset V) : ℝ)) *
          (∑ T : {S : Finset V // S ∈ P.parts}, (#(T : Finset V) : ℝ)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [hprod, hsum]
  exact le_of_eq (by ring)

/-- The pair capacities of a subset of ordered pairs, bounded by a density bound. -/
private theorem sum_cap_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V))
    (F : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})) {d : ℝ}
    (hd : ∀ p ∈ F, (G.edgeDensity (p.1 : Finset V) (p.2 : Finset V) : ℝ) ≤ d) (hd0 : 0 ≤ d) :
    ∑ p ∈ F, clusterPairCap G (p.1 : Finset V) (p.2 : Finset V)
      ≤ d * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hstep : ∀ p ∈ F, clusterPairCap G (p.1 : Finset V) (p.2 : Finset V)
      ≤ d * ((#(p.1 : Finset V) : ℝ) * (#(p.2 : Finset V) : ℝ)) := by
    intro p hp
    rw [clusterPairCap, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hd p hp) (by positivity)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hd0
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun p _ _ => by positivity)) ?_
  exact sum_card_mul_card_le P

/-- The ordered pairs of distinct clusters inside a triple: the off-diagonal of the triple. -/
private theorem filter_pairs_eq_offDiag (P : Finpartition (univ : Finset V))
    (th : Finset {S : Finset V // S ∈ P.parts}) :
    ((univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})).filter
        (fun p => p.1 ≠ p.2)).filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) = th.offDiag := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
  tauto

/-- **The value of a feasible point of the cluster-triple LP is at most `|V|²/6`.** -/
theorem clusterLPValue_le_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {y : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hy : IsClusterTripleLP G P ep de y) :
    6 * clusterLPValue y ≤ (Fintype.card V : ℝ) ^ 2 := by
  classical
  set F := (univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})).filter
    (fun p => p.1 ≠ p.2) with hFdef
  -- every triple in the support has exactly six ordered pairs
  have hcount : ∀ th, y th * 6 ≤ y th * (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
    intro th
    by_cases hz : y th = 0
    · simp [hz]
    · have htri := hy.2.1 th hz
      have hcard : #th = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htri).card_eq
      have heq : #(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) = 6 := by
        rw [hFdef, filter_pairs_eq_offDiag, Finset.offDiag_card, hcard]
      rw [heq]
      norm_num
  have hsum : 6 * clusterLPValue y ≤ ∑ p ∈ F, ∑ th ∈ triplesThrough P p.1 p.2, y th := by
    rw [sum_pair_fibers P y F, clusterLPValue, Finset.mul_sum]
    refine Finset.sum_le_sum fun th _ => ?_
    have := hcount th
    linarith only [this]
  refine le_trans hsum ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hy.2.2 p.1 p.2 ?_)) ?_
  · exact (Finset.mem_filter.mp hp).2
  · refine sum_cap_le G P F (d := 1) (fun p _ => ?_) zero_le_one |>.trans_eq (by ring)
    exact_mod_cast G.edgeDensity_le_one (p.1 : Finset V) (p.2 : Finset V)

/-- The triples of the LP that use a cluster pair of density below `δ`. -/
noncomputable def sparseTriples (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (δ : ℝ) :
    Finset (Finset {S : Finset V // S ∈ P.parts}) :=
  univ.filter (fun th => ∃ S ∈ th, ∃ T ∈ th, S ≠ T ∧
    (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) < δ)

/-- **The mass of the triples using a sparse cluster pair is at most `δ|V|²/2`.**  Every such triple
contains at least two ordered pairs of density below `δ`, and the capacities of those pairs add up
to at most `δ|V|²`. -/
theorem sum_sparse_triples_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {y : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hy : IsClusterTripleLP G P ep de y) :
    2 * ∑ th ∈ sparseTriples G P δ, y th ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set F := (univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})).filter
    (fun p => p.1 ≠ p.2 ∧ (G.edgeDensity (p.1 : Finset V) (p.2 : Finset V) : ℝ) < δ) with hFdef
  -- a sparse triple contains at least two ordered sparse pairs
  have hcount : ∀ th ∈ sparseTriples G P δ,
      2 ≤ (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
    intro th hth
    obtain ⟨S, hS, T, hT, hST, hd⟩ := (Finset.mem_filter.mp hth).2
    have hd' : (G.edgeDensity (T : Finset V) (S : Finset V) : ℝ) < δ := by
      rwa [SimpleGraph.edgeDensity_comm]
    have hmem1 : (S, T) ∈ F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) := by
      simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hST, hd⟩, hS, hT⟩
    have hmem2 : (T, S) ∈ F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) := by
      simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hST.symm, hd'⟩, hT, hS⟩
    have hsub : ({(S, T), (T, S)} : Finset _) ⊆ F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hmem1
      · rw [Finset.mem_singleton.mp hp']
        exact hmem2
    have hcard2 : #({(S, T), (T, S)} : Finset _) = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff]; tauto), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [hcard2] at this
    exact_mod_cast this
  have hynn : ∀ th, 0 ≤ y th := hy.1
  have hstep : 2 * ∑ th ∈ sparseTriples G P δ, y th
      ≤ ∑ th, y th * (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun th hth => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (sparseTriples G P δ))
        (fun th _ _ => mul_nonneg (hynn th) (by positivity)))
    have h := hcount th hth
    have := mul_le_mul_of_nonneg_left h (hynn th)
    linarith only [this]
  rw [← sum_pair_fibers P y F] at hstep
  refine le_trans hstep ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hy.2.2 p.1 p.2 ?_)) ?_
  · exact (Finset.mem_filter.mp hp).2.1
  · exact sum_cap_le G P F (fun p hp => le_of_lt (Finset.mem_filter.mp hp).2.2) hδ0

end Nibble.AX1

end




/-! # CoarseCellBlocks -/

public section

open Finset

namespace Nibble.AX1

/-! ### A subset of a prescribed size -/

variable {V : Type} [DecidableEq V]

/-- A chosen subset of `A` with `n` elements (all of `A` if `n` is too large). -/
noncomputable def takeSub (A : Finset V) (n : ℕ) : Finset V :=
  if h : n ≤ #A then (Finset.exists_subset_card_eq h).choose else A

omit [DecidableEq V] in
theorem takeSub_subset (A : Finset V) (n : ℕ) : takeSub A n ⊆ A := by
  unfold takeSub
  split
  · exact (Finset.exists_subset_card_eq ‹_›).choose_spec.1
  · exact Finset.Subset.refl _

omit [DecidableEq V] in
theorem card_takeSub {A : Finset V} {n : ℕ} (h : n ≤ #A) : #(takeSub A n) = n := by
  unfold takeSub
  rw [dite_eq_left h]
  exact (Finset.exists_subset_card_eq h).choose_spec.2

/-! ### The union of a set of coarse cells -/

/-- **The union of the coarse cells of `S` indexed by `I`**, at cell length `l`. -/
noncomputable def cellUnion (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) : Finset V :=
  I.biUnion (fun i => blockOf S l (i : ℕ))

theorem cellUnion_subset (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) :
    cellUnion S l I ⊆ S := by
  intro v hv
  rw [cellUnion, Finset.mem_biUnion] at hv
  obtain ⟨i, -, hi⟩ := hv
  exact blockOf_subset S l (i : ℕ) hi

theorem card_cellUnion (S : Finset V) {l P : ℕ} (hl : 0 < l) (I : Finset (Fin P))
    (hfit : P * l ≤ #S) : #(cellUnion S l I) = #I * l := by
  classical
  have hcell : ∀ i : Fin P, #(blockOf S l (i : ℕ)) = l := by
    intro i
    refine card_blockOf S hl (le_trans (Nat.mul_le_mul_right l ?_) hfit)
    exact i.isLt
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (blockOf S l (i : ℕ)) (blockOf S l (j : ℕ)) := by
    intro i _ j _ hij
    exact blockOf_disjoint S l (fun h => hij (Fin.ext h))
  rw [cellUnion, Finset.card_biUnion hdisj,
    Finset.sum_congr rfl (fun i _ => hcell i), Finset.sum_const, smul_eq_mul]

theorem cellUnion_disjoint (S : Finset V) (l : ℕ) {P : ℕ} {I J : Finset (Fin P)}
    (h : Disjoint I J) : Disjoint (cellUnion S l I) (cellUnion S l J) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [cellUnion, Finset.mem_biUnion] at hv hv'
  obtain ⟨i, hi, hvi⟩ := hv
  obtain ⟨j, hj, hvj⟩ := hv'
  have hij : (i : ℕ) ≠ (j : ℕ) := by
    intro hcon
    have : i = j := Fin.ext hcon
    exact (Finset.disjoint_left.mp h hi) (this ▸ hj)
  exact (Finset.disjoint_left.mp (blockOf_disjoint S l hij)) hvi hvj

/-- **The vertex block of a member**: `n` vertices inside the union of its coarse cells. -/
noncomputable def cellBlock (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) (n : ℕ) :
    Finset V := takeSub (cellUnion S l I) n

theorem cellBlock_subset_cellUnion (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) (n : ℕ) :
    cellBlock S l I n ⊆ cellUnion S l I := takeSub_subset _ _

theorem cellBlock_subset (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) (n : ℕ) :
    cellBlock S l I n ⊆ S :=
  Finset.Subset.trans (cellBlock_subset_cellUnion S l I n) (cellUnion_subset S l I)

theorem card_cellBlock (S : Finset V) {l P : ℕ} (hl : 0 < l) (I : Finset (Fin P)) {n : ℕ}
    (hfit : P * l ≤ #S) (hn : n ≤ #I * l) : #(cellBlock S l I n) = n := by
  refine card_takeSub ?_
  rw [card_cellUnion S hl I hfit]
  exact hn

/-! ### The disjointness engine -/

variable [Fintype V]

omit [Fintype V] in
/-- The two positions of a vertex pair inside the rectangle of a member. -/
theorem exists_positions_of_mem_tripleRect {f : ZMod 3 → Finset V} {x y : V}
    (h : (x, y) ∈ tripleRect (f 0) (f 1) (f 2)) :
    ∃ a b : ZMod 3, a ≠ b ∧ x ∈ f a ∧ y ∈ f b := by
  rw [mem_tripleRect_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 1, by decide +kernel, h1, h2⟩
  · exact ⟨1, 0, by decide +kernel, h1, h2⟩
  · exact ⟨0, 2, by decide +kernel, h1, h2⟩
  · exact ⟨2, 0, by decide +kernel, h1, h2⟩
  · exact ⟨1, 2, by decide +kernel, h1, h2⟩
  · exact ⟨2, 1, by decide +kernel, h1, h2⟩

omit [Fintype V] in
/-- **The disjointness engine.**  Two members whose blocks sit inside clusters of a partition have
disjoint vertex-pair rectangles as soon as, whenever they share a cluster pair, one of the two
blocks carrying it is disjoint from the corresponding block of the other member. -/
theorem tripleRect_disjoint_of_shared_pairs
    {clA clB blkA blkB : ZMod 3 → Finset V}
    (hA : ∀ a, blkA a ⊆ clA a) (hB : ∀ a, blkB a ⊆ clB a)
    (hpart : ∀ a b : ZMod 3, ∀ v : V, v ∈ clA a → v ∈ clB b → clA a = clB b)
    (hdisj : ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' → clA a = clB a' → clA b = clB b' →
      Disjoint (blkA a) (blkB a') ∨ Disjoint (blkA b) (blkB b')) :
    Disjoint (tripleRect (blkA 0) (blkA 1) (blkA 2)) (tripleRect (blkB 0) (blkB 1) (blkB 2)) := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ hp hq
  obtain ⟨a, b, hab, hxa, hyb⟩ := exists_positions_of_mem_tripleRect hp
  obtain ⟨a', b', hab', hxa', hyb'⟩ := exists_positions_of_mem_tripleRect hq
  have hca : clA a = clB a' := hpart a a' x (hA a hxa) (hB a' hxa')
  have hcb : clA b = clB b' := hpart b b' y (hA b hyb) (hB b' hyb')
  rcases hdisj a b a' b' hab hab' hca hcb with h | h
  · exact (Finset.disjoint_left.mp h hxa) hxa'
  · exact (Finset.disjoint_left.mp h hyb) hyb'

end Nibble.AX1

end


/-! # CoarseCellAssembly -/

public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The block family of a coarse-cell placement.**  Every copy of `Good` becomes a member of the
family: its block at the position `a` is the prescribed number `bs c a` of vertices inside the union
of the coarse cells `I c a` of its cluster `cl c a`. -/
theorem exists_gridSubTriple_family_of_placement
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    {ep de α τ : ℝ} {l Pn : ℕ} (hl : 0 < l)
    {κ : Type}
    (cl : κ → ZMod 3 → {S : Finset V // S ∈ Pp.parts})
    (sz bs : κ → ZMod 3 → ℕ) (I : κ → ZMod 3 → Finset (Fin Pn)) (Good : Finset κ)
    (hcard : ∀ c a, #(I c a) = sz c a)
    (hfitS : ∀ S ∈ Pp.parts, Pn * l ≤ #S)
    (hbs : ∀ c a, bs c a ≤ sz c a * l)
    (hdisjI : ∀ c ∈ Good, ∀ c' ∈ Good, c ≠ c' → ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' →
      cl c a = cl c' a' → cl c b = cl c' b' →
      Disjoint (I c a) (I c' a') ∨ Disjoint (I c b) (I c' b'))
    (hgood : ∀ c ∈ Good,
      GoodTriple G Pp ep de (cl c 0 : Finset V) (cl c 1 : Finset V) (cl c 2 : Finset V))
    (hrel : ∀ c ∈ Good, ∀ a : ZMod 3, α * (#(cl c a : Finset V) : ℝ) ≤ (bs c a : ℝ))
    (hshape : ∀ c ∈ Good, ∀ a : ZMod 3,
      |(bs c a : ℝ)
        - τ * (G.edgeDensity (cl c (a + 1) : Finset V) (cl c (a + 2) : Finset V) : ℝ)| ≤ 1) :
    ∃ (k : ℕ) (U W X A B C : ℕ → Finset V),
      k ≤ #Good ∧
      (∀ i < k, IsGridSubTriple G Pp ep de α τ (U i) (W i) (X i) (A i) (B i) (C i)) ∧
      (∀ i < k, ∀ j < k, i ≠ j →
        Disjoint (tripleRect (A i) (B i) (C i)) (tripleRect (A j) (B j) (C j))) ∧
      (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
          * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ)))
        = ∑ c ∈ Good, τ ^ 2 * ((G.edgeDensity (cl c 0 : Finset V) (cl c 1 : Finset V) : ℝ)
            * (G.edgeDensity (cl c 0 : Finset V) (cl c 2 : Finset V) : ℝ)
            * (G.edgeDensity (cl c 1 : Finset V) (cl c 2 : Finset V) : ℝ)) := by
  classical
  -- the block of the copy `c` at the position `a`
  set blk : κ → ZMod 3 → Finset V :=
    fun c a => cellBlock (cl c a : Finset V) l (I c a) (bs c a) with hblkdef
  have hblksub : ∀ c a, blk c a ⊆ (cl c a : Finset V) := fun c a => cellBlock_subset _ _ _ _
  have hblkcard : ∀ c a, #(blk c a) = bs c a := by
    intro c a
    refine card_cellBlock _ hl _ (hfitS _ (cl c a).2) ?_
    rw [hcard]
    exact hbs c a
  -- two placed copies have disjoint vertex-pair rectangles
  have hrect : ∀ c ∈ Good, ∀ c' ∈ Good, c ≠ c' →
      Disjoint (tripleRect (blk c 0) (blk c 1) (blk c 2))
        (tripleRect (blk c' 0) (blk c' 1) (blk c' 2)) := by
    intro c hc c' hc' hne
    refine tripleRect_disjoint_of_shared_pairs
      (clA := fun a => (cl c a : Finset V)) (clB := fun a => (cl c' a : Finset V))
      (fun a => hblksub c a) (fun a => hblksub c' a) ?_ ?_
    · intro a b v hv hv'
      by_contra hcon
      exact (Finset.disjoint_left.mp (Pp.disjoint (cl c a).2 (cl c' b).2 hcon) hv) hv'
    · intro a b a' b' hab hab' hca hcb
      have hca' : cl c a = cl c' a' := Subtype.ext hca
      have hcb' : cl c b = cl c' b' := Subtype.ext hcb
      rcases hdisjI c hc c' hc' hne a b a' b' hab hab' hca' hcb' with h | h
      · refine Or.inl (Finset.disjoint_of_subset_left (cellBlock_subset_cellUnion _ _ _ _)
          (Finset.disjoint_of_subset_right (cellBlock_subset_cellUnion _ _ _ _) ?_))
        have hEq : (cl c' a' : Finset V) = (cl c a : Finset V) := by rw [hca']
        rw [hEq]
        exact cellUnion_disjoint _ _ h
      · refine Or.inr (Finset.disjoint_of_subset_left (cellBlock_subset_cellUnion _ _ _ _)
          (Finset.disjoint_of_subset_right (cellBlock_subset_cellUnion _ _ _ _) ?_))
        have hEq : (cl c' b' : Finset V) = (cl c b : Finset V) := by rw [hcb']
        rw [hEq]
        exact cellUnion_disjoint _ _ h
  -- the shape of one member
  have hmem : ∀ c ∈ Good, IsGridSubTriple G Pp ep de α τ
      (cl c 0 : Finset V) (cl c 1 : Finset V) (cl c 2 : Finset V)
      (blk c 0) (blk c 1) (blk c 2) := by
    intro c hc
    have h0 := hshape c hc 0
    have h1 := hshape c hc 1
    have h2 := hshape c hc 2
    have e0 : ((0 : ZMod 3) + 1) = 1 := by decide +kernel
    have e0' : ((0 : ZMod 3) + 2) = 2 := by decide +kernel
    have e1 : ((1 : ZMod 3) + 1) = 2 := by decide +kernel
    have e1' : ((1 : ZMod 3) + 2) = 0 := by decide +kernel
    have e2 : ((2 : ZMod 3) + 1) = 0 := by decide +kernel
    have e2' : ((2 : ZMod 3) + 2) = 1 := by decide +kernel
    rw [e0, e0'] at h0
    rw [e1, e1'] at h1
    rw [e2, e2'] at h2
    have hd10 : (G.edgeDensity (cl c 2 : Finset V) (cl c 0 : Finset V) : ℝ)
        = (G.edgeDensity (cl c 0 : Finset V) (cl c 2 : Finset V) : ℝ) := by
      rw [SimpleGraph.edgeDensity_comm]
    have hd20 : (G.edgeDensity (cl c 0 : Finset V) (cl c 1 : Finset V) : ℝ)
        = (G.edgeDensity (cl c 0 : Finset V) (cl c 1 : Finset V) : ℝ) := rfl
    rw [hd10] at h1
    refine ⟨hgood c hc, hblksub c 0, hblksub c 1, hblksub c 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hblkcard]; exact hrel c hc 0
    · rw [hblkcard]; exact hrel c hc 1
    · rw [hblkcard]; exact hrel c hc 2
    · rw [hblkcard]; exact h0
    · rw [hblkcard]; exact h1
    · rw [hblkcard]; rw [hd20] at h2; exact h2
  -- enumerate the placed copies
  rcases Finset.eq_empty_or_nonempty Good with hempty | ⟨c₀, hc₀⟩
  · refine ⟨0, (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅), (fun _ => ∅),
      (fun _ => ∅), Nat.zero_le _, ?_, ?_, ?_⟩
    · intro i hi; omega
    · intro i hi; omega
    · simp [hempty]
  · set L : List κ := Good.toList with hLdef
    set k : ℕ := #Good with hkdef
    have hlen : L.length = k := Finset.length_toList _
    set mem : ℕ → κ := fun i => L.getD i c₀ with hmemdef
    have hmemGood : ∀ i < k, mem i ∈ Good := by
      intro i hi
      rw [hmemdef]
      simp only
      rw [List.getD_eq_getElem L c₀ (by omega : i < L.length)]
      exact Finset.mem_toList.mp (List.getElem_mem _)
    have hmemInj : ∀ i < k, ∀ j < k, i ≠ j → mem i ≠ mem j := by
      intro i hi j hj hij
      rw [hmemdef]
      simp only
      rw [List.getD_eq_getElem L c₀ (by omega : i < L.length),
        List.getD_eq_getElem L c₀ (by omega : j < L.length)]
      intro h
      exact hij ((Finset.nodup_toList Good).getElem_inj_iff.mp h)
    refine ⟨k, fun i => (cl (mem i) 0 : Finset V), fun i => (cl (mem i) 1 : Finset V),
      fun i => (cl (mem i) 2 : Finset V), fun i => blk (mem i) 0, fun i => blk (mem i) 1,
      fun i => blk (mem i) 2, le_of_eq hkdef, ?_, ?_, ?_⟩
    · intro i hi
      exact hmem (mem i) (hmemGood i hi)
    · intro i hi j hj hij
      exact hrect (mem i) (hmemGood i hi) (mem j) (hmemGood j hj) (hmemInj i hi j hj hij)
    · refine Finset.sum_bij (fun i _ => mem i) ?_ ?_ ?_ ?_
      · intro i hi
        exact hmemGood i (Finset.mem_range.mp hi)
      · intro i hi j hj h
        by_contra hij
        exact hmemInj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij h
      · intro c hc
        have hmemL : c ∈ L := Finset.mem_toList.mpr hc
        obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmemL
        refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
        rw [hmemdef]
        simp only
        rw [List.getD_eq_getElem L c₀ hi, hget]
      · intro i hi
        rfl

end Nibble.AX1

end





/-! # GridTripleDesign -/

public section

namespace Nibble.AX1

open Finset

variable {q : ℕ}

/-- **The quadratic shift** of the cluster `v` in the cluster triple of vertex sum `s`. -/
def triShift (s v : ZMod q) : ZMod q := v ^ 2 - v * s

/-- **The block used in cluster `v` by the `j`-th sub-triple** of the cluster triple of vertex
sum `s`. -/
def triBlock (s v j : ZMod q) : ZMod q := j + triShift s v

/-- **The diagonal offset**: in the cluster pair `{a, b}`, the triple of vertex sum `s` occupies
the diagonal `{(k, k + (b - a) * (a + b - s))}`.  For `a ≠ b` this offset is an injective function
of `s`, which is the whole point of the design. -/
theorem triShift_diff (s a b : ZMod q) :
    triShift s b - triShift s a = (b - a) * (a + b - s) := by
  simp only [triShift]; ring

/-- For the triple `{u, w, x}` the offset of the pair `{u, w}` is `-(w - u) * x`: it depends on the
pair and on the *third* vertex only. -/
theorem triShift_diff_third (u w x : ZMod q) :
    triShift (u + w + x) w - triShift (u + w + x) u = -((w - u) * x) := by
  simp only [triShift]; ring

@[simp] theorem triBlock_zero_shift (s v : ZMod q) : triBlock s v 0 = triShift s v := by
  simp [triBlock]

/-- Inside one cluster triple, the `q` sub-triples cover every block of every one of the three
clusters exactly once. -/
theorem triBlock_bijective (s v : ZMod q) : Function.Bijective (triBlock s v) :=
  ⟨fun j j' h => by simpa [triBlock] using h,
   fun k => ⟨k - triShift s v, by simp [triBlock]⟩⟩

/-- The sub-triples of a fixed cluster triple form a *line* in the sense of
`Nibble.AX1.lineTriple`, re-based at the first cluster: all single-triple facts proved for the
line design apply. -/
theorem triBlock_eq_lineTriple (s u w x j : ZMod q) :
    (triBlock s u j, triBlock s w j, triBlock s x j)
      = lineTriple (triShift s w - triShift s u) (triShift s x - triShift s u)
          (triBlock s u j) := by
  simp only [lineTriple, triBlock, Prod.mk.injEq, true_and]
  exact ⟨by ring, by ring⟩

variable [NeZero q]

/-- **The block pairs a cluster triple uses in one of its cluster pairs**: the diagonal of offset
`(b - a) * (a + b - s)`. -/
def triPairSet (s a b : ZMod q) : Finset (ZMod q × ZMod q) :=
  (univ : Finset (ZMod q)).image fun j => (triBlock s a j, triBlock s b j)

theorem mem_triPairSet {s a b : ZMod q} {p : ZMod q × ZMod q} :
    p ∈ triPairSet s a b ↔ ∃ j, (triBlock s a j, triBlock s b j) = p := by
  simp [triPairSet]

/-- A block pair of the diagonal is determined by its first coordinate. -/
theorem triPairSet_snd_eq {s a b : ZMod q} {p : ZMod q × ZMod q} (hp : p ∈ triPairSet s a b) :
    p.2 = p.1 + (triShift s b - triShift s a) := by
  obtain ⟨j, rfl⟩ := mem_triPairSet.1 hp
  simp only [triBlock]; ring

/-- Each cluster triple uses exactly `q` block pairs in each of its three cluster pairs. -/
theorem card_triPairSet (s a b : ZMod q) : #(triPairSet s a b) = q := by
  rw [triPairSet, card_image_of_injective _ (fun j j' h => by
    simpa [triBlock, Prod.ext_iff] using h), card_univ, ZMod.card]

variable [Fact (Nat.Prime q)]

/-- **The allocation is consistent**: two cluster triples with different vertex sums use *disjoint*
sets of block pairs in every cluster pair `{a, b}` they share.  Since the vertex sum is symmetric,
this holds simultaneously for all three pairs of each triple. -/
theorem triPairSet_disjoint {s s' a b : ZMod q} (hab : a ≠ b) (hs : s ≠ s') :
    Disjoint (triPairSet s a b) (triPairSet s' a b) := by
  rw [Finset.disjoint_left]
  rintro p hp hp'
  have h := (triPairSet_snd_eq hp).symm.trans (triPairSet_snd_eq hp')
  rw [add_right_inj, triShift_diff, triShift_diff] at h
  have hz : (b - a) * (s' - s) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hz with h' | h'
  · exact hab (sub_eq_zero.1 h').symm
  · exact hs (sub_eq_zero.1 h').symm

/-- The form used in the assembly: two cluster triples through the same cluster pair `{a, b}`,
with different third clusters, never share a block pair. -/
theorem triPairSet_disjoint_of_third {a b x x' : ZMod q} (hab : a ≠ b) (hx : x ≠ x') :
    Disjoint (triPairSet (a + b + x) a b) (triPairSet (a + b + x') a b) :=
  triPairSet_disjoint hab fun h => hx (by
    have := add_left_cancel h; exact this)

/-- **Feasibility of the allocation**: if `S` is a set of third clusters, the triples
`{a, b, x}`, `x ∈ S`, together use `q * #S` distinct block pairs of the cluster pair `{a, b}`, out
of the `q ^ 2` block pairs available.  So the design fits as long as the number of cluster triples
through a pair is at most the number `q` of blocks per cluster. -/
theorem card_triPairSet_biUnion {a b : ZMod q} (hab : a ≠ b) (S : Finset (ZMod q)) :
    #(S.biUnion fun x => triPairSet (a + b + x) a b) = q * #S := by
  rw [card_biUnion, Finset.sum_congr rfl fun x _ => card_triPairSet _ _ _, sum_const,
    smul_eq_mul, mul_comm]
  intro x _ y _ hxy
  exact triPairSet_disjoint_of_third hab hxy

/-- The block pairs used in a cluster pair are of course among all `q ^ 2` of them, so the count
above is a genuine packing bound: the design never overflows a cluster pair. -/
theorem card_triPairSet_biUnion_le {a b : ZMod q} (hab : a ≠ b) (S : Finset (ZMod q)) :
    #(S.biUnion fun x => triPairSet (a + b + x) a b) ≤ q ^ 2 := by
  have hS : #S ≤ q := by
    have : #S ≤ Fintype.card (ZMod q) := card_le_univ S
    simpa [ZMod.card] using this
  rw [card_triPairSet_biUnion hab, sq]
  exact Nat.mul_le_mul_left _ hS

end Nibble.AX1

end


/-! # GridTripleDesignRect -/

public section

open Finset

namespace Nibble.AX1

/-- A `3`-element set containing two distinct elements `a`, `b` is `{a, b, x}` for a unique third
element `x`. -/
theorem exists_third_of_card_three {α : Type} [DecidableEq α] {T : Finset α} (hT : #T = 3)
    {a b : α} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ x, T = {a, b, x} ∧ x ≠ a ∧ x ≠ b := by
  have hsub : ({a, b} : Finset α) ⊆ T := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  have hcard : #(T \ ({a, b} : Finset α)) = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hT,
      card_insert_of_notMem (by simpa using hab), card_singleton]
  obtain ⟨x, hx⟩ := card_eq_one.1 hcard
  have hxT : x ∈ T \ ({a, b} : Finset α) := by rw [hx]; exact mem_singleton_self x
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hxT
  refine ⟨x, (Finset.eq_of_subset_of_card_le ?_ ?_).symm, hxT.2.1, hxT.2.2⟩
  · intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> [exact ha; exact hb; exact hxT.1]
  · rw [hT, card_insert_of_notMem (by simp [hab, Ne.symm hxT.2.1]),
      card_insert_of_notMem (by simp [Ne.symm hxT.2.2]), card_singleton]

variable {q : ℕ}

/-- **The cells used by one sub-triple of the design**: the cluster triple `T` (a set of cluster
indices) with offset `j` occupies, in the cluster `v ∈ T`, the block `triBlock (∑ T) v j`. -/
def triCells (T : Finset (ZMod q)) (j : ZMod q) : Finset (ZMod q × ZMod q) :=
  T.image fun c => (c, triBlock (∑ v ∈ T, v) c j)

theorem mem_triCells {T : Finset (ZMod q)} {j v : ZMod q} (hv : v ∈ T) :
    (v, triBlock (∑ u ∈ T, u) v j) ∈ triCells T j :=
  mem_image_of_mem _ hv

theorem sum_triple {a b x : ZMod q} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    ∑ v ∈ ({a, b, x} : Finset (ZMod q)), v = a + b + x := by
  rw [sum_insert (by simp [hab, Ne.symm hxa]), sum_insert (by simp [Ne.symm hxb]),
    sum_singleton, add_assoc]

variable [Fact (Nat.Prime q)]

/-- **Two distinct sub-triples of the design share at most one cell.**

If the cluster triples differ, or if they agree but the offsets differ, then no two cells can be
common: two common cells lie in two distinct clusters `a ≠ b`, and the identity
`triShift s b - triShift s a = (b - a) * (a + b - s)` then forces the two vertex sums to be equal,
hence the offsets to be equal and (both triples being `{a, b, ·}` with the same sum) the triples to
be equal. -/
theorem triCells_inter_subsingleton {T T' : Finset (ZMod q)} {j j' : ZMod q}
    (hT : #T = 3) (hT' : #T' = 3) (hne : ¬ (T = T' ∧ j = j'))
    {c d : ZMod q × ZMod q} (hc : c ∈ triCells T j) (hc' : c ∈ triCells T' j')
    (hd : d ∈ triCells T j) (hd' : d ∈ triCells T' j') : c = d := by
  by_contra hcd
  simp only [triCells, mem_image, Prod.ext_iff] at hc hc' hd hd'
  obtain ⟨a, haT, ha1, ha2⟩ := hc
  obtain ⟨a', ha'T, ha1', ha2'⟩ := hc'
  obtain ⟨b, hbT, hb1, hb2⟩ := hd
  obtain ⟨b', hb'T, hb1', hb2'⟩ := hd'
  subst ha1; subst hb1; subst ha1'; subst hb1'
  have hab : c.1 ≠ d.1 := by
    intro h
    exact hcd (Prod.ext h (by rw [← ha2, ← hb2, h]))
  have hs : (∑ v ∈ T, v) = ∑ v ∈ T', v := by
    have e1 : j + triShift (∑ v ∈ T, v) c.1 = j' + triShift (∑ v ∈ T', v) c.1 := by
      have := ha2.trans ha2'.symm; simpa [triBlock] using this
    have e2 : j + triShift (∑ v ∈ T, v) d.1 = j' + triShift (∑ v ∈ T', v) d.1 := by
      have := hb2.trans hb2'.symm; simpa [triBlock] using this
    have e3 : triShift (∑ v ∈ T, v) d.1 - triShift (∑ v ∈ T, v) c.1
        = triShift (∑ v ∈ T', v) d.1 - triShift (∑ v ∈ T', v) c.1 := by
      linear_combination e2 - e1
    rw [triShift_diff, triShift_diff] at e3
    have hz : (d.1 - c.1) * ((∑ v ∈ T', v) - ∑ v ∈ T, v) = 0 := by linear_combination e3
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd (sub_eq_zero.1 h').symm hab
    · exact (sub_eq_zero.1 h').symm
  have hj : j = j' := by
    have h := ha2.trans ha2'.symm
    simp only [triBlock, hs, add_right_cancel_iff] at h
    exact h
  obtain ⟨x, hTx, hxa, hxb⟩ := exists_third_of_card_three hT haT hbT hab
  obtain ⟨x', hTx', hxa', hxb'⟩ := exists_third_of_card_three hT' ha'T hb'T hab
  rw [hTx, hTx', sum_triple hab hxa hxb, sum_triple hab hxa' hxb'] at hs
  have hxx : x = x' := by linear_combination hs
  exact hne ⟨by rw [hTx, hTx', hxx], hj⟩

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A vertex pair of the rectangle of a sub-triple whose three parts sit in the blocks of three
distinct cells joins the blocks of two distinct cells. -/
theorem tripleRect_cells {ι : Type} (blk : ι → Finset V) (S : Finset ι)
    {A B C : Finset V} {cA cB cC : ι} (hA : A ⊆ blk cA) (hB : B ⊆ blk cB) (hC : C ⊆ blk cC)
    (hcA : cA ∈ S) (hcB : cB ∈ S) (hcC : cC ∈ S)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    {p : V × V} (hp : p ∈ tripleRect A B C) :
    ∃ c d, c ∈ S ∧ d ∈ S ∧ c ≠ d ∧ p.1 ∈ blk c ∧ p.2 ∈ blk d := by
  obtain ⟨y, z⟩ := p
  rw [mem_tripleRect_iff] at hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨cA, cB, hcA, hcB, hAB, hA h1, hB h2⟩
  · exact ⟨cB, cA, hcB, hcA, hAB.symm, hB h1, hA h2⟩
  · exact ⟨cA, cC, hcA, hcC, hAC, hA h1, hC h2⟩
  · exact ⟨cC, cA, hcC, hcA, hAC.symm, hC h1, hA h2⟩
  · exact ⟨cB, cC, hcB, hcC, hBC, hB h1, hC h2⟩
  · exact ⟨cC, cB, hcC, hcB, hBC.symm, hC h1, hB h2⟩

omit [Fintype V] in
/-- **The rectangles of the design are pairwise disjoint.**

`blk` assigns to each cell — a pair (cluster index, block index) — a block of vertices, distinct
cells getting disjoint blocks.  Two distinct sub-triples of the design (different cluster triples,
or the same cluster triple with different offsets) have disjoint vertex-pair rectangles, whatever
subsets of the three blocks are used as the parts `A`, `B`, `C`.

Combined with `Nibble.AX1.tripleGraph_edgeDisjoint_of_rect_disjoint` and
`Nibble.AX1.sum_area_le_of_rect_disjoint` this is the edge-disjointness requirement of
`Nibble.AX1.BlockCoverResidual` for the whole family of cluster triples at once. -/
theorem tripleRect_disjoint_of_design (blk : ZMod q × ZMod q → Finset V)
    (hblk : ∀ c d, c ≠ d → Disjoint (blk c) (blk d))
    {T T' : Finset (ZMod q)} {j j' : ZMod q} (hT : #T = 3) (hT' : #T' = 3)
    (hne : ¬ (T = T' ∧ j = j'))
    {u w x u' w' x' : ZMod q}
    (huT : u ∈ T) (hwT : w ∈ T) (hxT : x ∈ T) (huw : u ≠ w) (hux : u ≠ x) (hwx : w ≠ x)
    (huT' : u' ∈ T') (hwT' : w' ∈ T') (hxT' : x' ∈ T')
    (huw' : u' ≠ w') (hux' : u' ≠ x') (hwx' : w' ≠ x')
    {A B C A' B' C' : Finset V}
    (hA : A ⊆ blk (u, triBlock (∑ v ∈ T, v) u j))
    (hB : B ⊆ blk (w, triBlock (∑ v ∈ T, v) w j))
    (hC : C ⊆ blk (x, triBlock (∑ v ∈ T, v) x j))
    (hA' : A' ⊆ blk (u', triBlock (∑ v ∈ T', v) u' j'))
    (hB' : B' ⊆ blk (w', triBlock (∑ v ∈ T', v) w' j'))
    (hC' : C' ⊆ blk (x', triBlock (∑ v ∈ T', v) x' j')) :
    Disjoint (tripleRect A B C) (tripleRect A' B' C') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨c, d, hc, hd, hcd, hp1, hp2⟩ :=
    tripleRect_cells blk (triCells T j) hA hB hC (mem_triCells huT) (mem_triCells hwT)
      (mem_triCells hxT) (by simp [Prod.ext_iff, huw]) (by simp [Prod.ext_iff, hux])
      (by simp [Prod.ext_iff, hwx]) hp
  obtain ⟨c', d', hc', hd', _, hp1', hp2'⟩ :=
    tripleRect_cells blk (triCells T' j') hA' hB' hC' (mem_triCells huT') (mem_triCells hwT')
      (mem_triCells hxT') (by simp [Prod.ext_iff, huw']) (by simp [Prod.ext_iff, hux'])
      (by simp [Prod.ext_iff, hwx']) hp'
  have hcc : c = c' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk c c' h) hp1 hp1'
  have hdd : d = d' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk d d' h) hp2 hp2'
  exact hcd (triCells_inter_subsingleton hT hT' hne hc (hcc ▸ hc') hd (hdd ▸ hd'))

end Nibble.AX1

end


/-! # BlockCoverUniformAux -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### Naming the three elements of a triangle -/

/-- An ordered triple listing the three elements of `t`, when `t` has exactly three of them. -/
noncomputable def pick3 {ι : Type} [Nonempty ι] [DecidableEq ι] (t : Finset ι) : ι × ι × ι :=
  open Classical in
  if h : ∃ x y z : ι, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} then
    (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (Classical.arbitrary ι, Classical.arbitrary ι, Classical.arbitrary ι)

theorem pick3_spec {ι : Type} [Nonempty ι] [DecidableEq ι] {t : Finset ι} (h3 : #t = 3) :
    (pick3 t).1 ≠ (pick3 t).2.1 ∧ (pick3 t).1 ≠ (pick3 t).2.2 ∧
      (pick3 t).2.1 ≠ (pick3 t).2.2 ∧ t = {(pick3 t).1, (pick3 t).2.1, (pick3 t).2.2} := by
  have h : ∃ x y z : ι, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} := Finset.card_eq_three.mp h3
  rw [pick3, dite_eq_left h]
  exact h.choose_spec.choose_spec.choose_spec

theorem pick3_mem {ι : Type} [Nonempty ι] [DecidableEq ι] {t : Finset ι} (h3 : #t = 3) :
    (pick3 t).1 ∈ t ∧ (pick3 t).2.1 ∈ t ∧ (pick3 t).2.2 ∈ t := by
  obtain ⟨-, -, -, ht⟩ := pick3_spec h3
  have hsub : ({(pick3 t).1, (pick3 t).2.1, (pick3 t).2.2} : Finset ι) ⊆ t := ht.ge
  exact ⟨hsub (by simp), hsub (by simp), hsub (by simp)⟩

/-! ### Cell disjointness gives rectangle disjointness -/

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- **The rectangles of two members that share at most one cell are disjoint.**  `blk` assigns a
block of vertices to each cell, distinct cells getting disjoint blocks; a member is given by three
distinct cells, and its three parts are subsets of the corresponding blocks. -/
theorem tripleRect_disjoint_of_cells_inter {ι : Type} [DecidableEq ι] (blk : ι → Finset V)
    (hblk : ∀ c d, c ≠ d → Disjoint (blk c) (blk d))
    {t t' : Finset ι} (hint : #(t ∩ t') ≤ 1)
    {cA cB cC cA' cB' cC' : ι}
    (hcA : cA ∈ t) (hcB : cB ∈ t) (hcC : cC ∈ t)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    (hcA' : cA' ∈ t') (hcB' : cB' ∈ t') (hcC' : cC' ∈ t')
    (hAB' : cA' ≠ cB') (hAC' : cA' ≠ cC') (hBC' : cB' ≠ cC')
    {A B C A' B' C' : Finset V}
    (hA : A ⊆ blk cA) (hB : B ⊆ blk cB) (hC : C ⊆ blk cC)
    (hA' : A' ⊆ blk cA') (hB' : B' ⊆ blk cB') (hC' : C' ⊆ blk cC') :
    Disjoint (tripleRect A B C) (tripleRect A' B' C') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨c, d, hc, hd, hcd, hp1, hp2⟩ :=
    tripleRect_cells blk t hA hB hC hcA hcB hcC hAB hAC hBC hp
  obtain ⟨c', d', hc', hd', -, hp1', hp2'⟩ :=
    tripleRect_cells blk t' hA' hB' hC' hcA' hcB' hcC' hAB' hAC' hBC' hp'
  have hcc : c = c' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk c c' h) hp1 hp1'
  have hdd : d = d' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk d d' h) hp2 hp2'
  have hcmem : c ∈ t ∩ t' := Finset.mem_inter.mpr ⟨hc, hcc ▸ hc'⟩
  have hdmem : d ∈ t ∩ t' := Finset.mem_inter.mpr ⟨hd, hdd ▸ hd'⟩
  have : ({c, d} : Finset ι) ⊆ t ∩ t' := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : 2 ≤ #(t ∩ t') := by
    have := Finset.card_le_card this
    rwa [Finset.card_insert_of_notMem (by simpa using hcd), Finset.card_singleton] at this
  omega

/-! ### A crude bound for the fractional triangle packing number -/

theorem nu3star_le_card_sq {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] : nu3star H ≤ (Fintype.card W : ℝ) ^ 2 := by
  classical
  have hsub : H.cliqueFinset 2 ⊆ (Finset.univ : Finset W).powersetCard 2 := by
    intro t ht
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq⟩
  have hcard : (#(H.cliqueFinset 2) : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by
    have h1 : #(H.cliqueFinset 2) ≤ (Fintype.card W).choose 2 := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_powersetCard, Finset.card_univ] at this
    have h2 : (Fintype.card W).choose 2 ≤ (Fintype.card W) ^ 2 := by
      rw [Nat.choose_two_right]
      calc Fintype.card W * (Fintype.card W - 1) / 2
          ≤ Fintype.card W * (Fintype.card W - 1) := Nat.div_le_self _ _
        _ ≤ Fintype.card W * Fintype.card W := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = (Fintype.card W) ^ 2 := by ring
    exact_mod_cast le_trans h1 h2
  have h3 : (0:ℝ) ≤ (#(H.cliqueFinset 2) : ℝ) := by positivity
  have := Nibble.YusterE.nu3star_le (G := H)
  linarith

end Nibble.AX1

end


/-! # CoarseCellCoupled -/

public section

open Finset SimpleGraph Hypergraph Nibble.YusterE


namespace Nibble.AX1

/-! ### The three positions of a cluster triple -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every element of `ZMod 3` is `0`, `1` or `2`. -/
theorem zmod3_cases (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by revert a; decide

/-! ### Copies -/

/-- **The copies of the elements of `Gd`**: `n th` copies of `th`. -/
def copySet {ι : Type} [DecidableEq ι] (Gd : Finset ι) (n : ι → ℕ) : Finset (ι × ℕ) :=
  Gd.biUnion (fun th => (Finset.range (n th)).image (fun j => (th, j)))

theorem mem_copySet {ι : Type} [DecidableEq ι] {Gd : Finset ι} {n : ι → ℕ} {p : ι × ℕ} :
    p ∈ copySet Gd n ↔ p.1 ∈ Gd ∧ p.2 < n p.1 := by
  classical
  constructor
  · intro hp
    obtain ⟨th, hth, hp'⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hp'
    rw [← hEq]
    exact ⟨hth, Finset.mem_range.mp hj⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_biUnion.mpr ⟨p.1, h1, Finset.mem_image.mpr ⟨p.2, Finset.mem_range.mpr h2, ?_⟩⟩
    rfl

theorem sum_copySet {ι : Type} [DecidableEq ι] {M : Type} [AddCommMonoid M] (Gd : Finset ι)
    (n : ι → ℕ) (f : ι → M) :
    ∑ p ∈ copySet Gd n, f p.1 = ∑ th ∈ Gd, (n th) • f th := by
  classical
  rw [copySet, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun th _ => ?_
    rw [Finset.sum_image (by intro i _ j _ h; exact (Prod.mk.injEq _ _ _ _ ▸ h).2)]
    simp
  · intro th _ th' _ hne
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro p ⟨j, -, rfl⟩ ⟨j', -, hEq⟩
    exact hne (congrArg Prod.fst hEq).symm

theorem card_copySet {ι : Type} [DecidableEq ι] (Gd : Finset ι) (n : ι → ℕ) :
    #(copySet Gd n) = ∑ th ∈ Gd, n th := by
  have h := sum_copySet (M := ℕ) Gd n (fun _ => 1)
  simpa using h

variable (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
  [Nonempty {S : Finset V // S ∈ Pp.parts}]

/-- **The three positions of a cluster triple**, indexed by `ZMod 3`. -/
noncomputable def triPos (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) :
    {S : Finset V // S ∈ Pp.parts} :=
  if a = 0 then (pick3 th).1 else if a = 1 then (pick3 th).2.1 else (pick3 th).2.2

theorem triPos_mem {th : Finset {S : Finset V // S ∈ Pp.parts}} (h3 : #th = 3) (a : ZMod 3) :
    triPos Pp th a ∈ th := by
  obtain ⟨h0, h1, h2⟩ := pick3_mem h3
  rcases zmod3_cases a with rfl | rfl | rfl
  · simpa [triPos] using h0
  · simpa [triPos] using h1
  · have h20 : (2 : ZMod 3) ≠ 0 := by decide
    have h21 : (2 : ZMod 3) ≠ 1 := by decide
    simpa [triPos, h20, h21] using h2

theorem triPos_injective {th : Finset {S : Finset V // S ∈ Pp.parts}} (h3 : #th = 3) :
    Function.Injective (triPos Pp th) := by
  obtain ⟨hab, hac, hbc, -⟩ := pick3_spec h3
  intro a b hEq
  rcases zmod3_cases a with rfl | rfl | rfl <;> rcases zmod3_cases b with rfl | rfl | rfl <;>
    simp only [triPos, ite_eq_left] at hEq ⊢ <;> first
      | rfl
      | (exfalso; first
          | exact hab hEq | exact hab hEq.symm | exact hac hEq | exact hac hEq.symm
          | exact hbc hEq | exact hbc hEq.symm)

/-- **The density of the cluster pair opposite to the position `a`.** -/
noncomputable def dOpp (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) : ℝ :=
  (G.edgeDensity (triPos Pp th (a + 1) : Finset V) (triPos Pp th (a + 2) : Finset V) : ℝ)

/-- **The density product of a cluster triple.** -/
noncomputable def dProd (th : Finset {S : Finset V // S ∈ Pp.parts}) : ℝ :=
  dOpp G Pp th 0 * dOpp G Pp th 1 * dOpp G Pp th 2

theorem dOpp_nonneg (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) :
    0 ≤ dOpp G Pp th a := by
  rw [dOpp]
  exact_mod_cast G.edgeDensity_nonneg _ _

theorem dOpp_le_one (th : Finset {S : Finset V // S ∈ Pp.parts}) (a : ZMod 3) :
    dOpp G Pp th a ≤ 1 := by
  rw [dOpp]
  exact_mod_cast G.edgeDensity_le_one _ _

theorem dOpp_zero (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dOpp G Pp th 0
      = (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
  rw [dOpp, show ((0 : ZMod 3) + 1) = 1 from by decide +kernel,
    show ((0 : ZMod 3) + 2) = 2 from by decide +kernel]

theorem dOpp_one (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dOpp G Pp th 1
      = (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 0 : Finset V) : ℝ) := by
  rw [dOpp, show ((1 : ZMod 3) + 1) = 2 from by decide +kernel,
    show ((1 : ZMod 3) + 2) = 0 from by decide +kernel]

theorem dOpp_two (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dOpp G Pp th 2
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 1 : Finset V) : ℝ) := by
  rw [dOpp, show ((2 : ZMod 3) + 1) = 0 from by decide +kernel,
    show ((2 : ZMod 3) + 2) = 1 from by decide +kernel]

/-- The density product read off the three positions in their natural order. -/
theorem dProd_eq (th : Finset {S : Finset V // S ∈ Pp.parts}) :
    dProd G Pp th
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 1 : Finset V) : ℝ)
        * (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 2 : Finset V) : ℝ)
        * (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
  have h20 : (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 0 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  rw [dProd, dOpp_zero, dOpp_one, dOpp_two, h20]
  ring

/-- **The three opposite densities of a triple, seen from two of its positions.**  For two distinct
positions `a`, `b` the density of the pair `(a, b)` is the density opposite to the third position,
so the three factors multiply out to the density product. -/
theorem dOpp_mul_dOpp_mul_dens (th : Finset {S : Finset V // S ∈ Pp.parts}) {a b : ZMod 3}
    (hab : a ≠ b) :
    dOpp G Pp th a * dOpp G Pp th b
        * (G.edgeDensity (triPos Pp th a : Finset V) (triPos Pp th b : Finset V) : ℝ)
      = dProd G Pp th := by
  have h10 : (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 0 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 1 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have h20 : (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 0 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 0 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  have h21 : (G.edgeDensity (triPos Pp th 2 : Finset V) (triPos Pp th 1 : Finset V) : ℝ)
      = (G.edgeDensity (triPos Pp th 1 : Finset V) (triPos Pp th 2 : Finset V) : ℝ) := by
    rw [SimpleGraph.edgeDensity_comm]
  rcases zmod3_cases a with rfl | rfl | rfl <;> rcases zmod3_cases b with rfl | rfl | rfl <;>
      first
        | (exact absurd rfl hab)
        | (simp only [dProd, dOpp_zero, dOpp_one, dOpp_two, h10, h20, h21]; try ring)


/-! ### Arithmetic of the parameters -/

/-- The small-box restriction `s₀ ≤ θ·P`, from `α ≤ θδ/(16K)`. -/
private theorem small_box_bound {θ δ α Kr Pn s₀ : ℝ} (hθ0 : 0 < θ) (hδ0 : 0 < δ)
    (hα0 : 0 < α) (hK1 : 1 ≤ Kr) (hαθ : 16 * Kr * α ≤ θ * δ) (hPn : 1 / (4 * α) ≤ Pn)
    (hs₀ : s₀ ≤ 2 * (Kr / δ)) : s₀ ≤ θ * Pn := by
  have hPnα : (1 : ℝ) ≤ 4 * α * Pn := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * α)] at hPn
    linarith only [hPn]
  have h5 : 4 * α * (4 * Kr) ≤ 4 * α * (θ * δ * Pn) := by
    nlinarith [mul_le_mul_of_nonneg_left hPnα (mul_nonneg hθ0.le hδ0.le)]
  have h6 : 4 * Kr ≤ θ * δ * Pn := le_of_mul_le_mul_left h5 (by positivity)
  have h7 : 2 * (Kr / δ) ≤ θ * Pn := by
    have e : 2 * (Kr / δ) = 2 * Kr / δ := by ring
    rw [e, div_le_iff₀ hδ0]
    linarith only [hK1, h6]
  linarith only [hs₀, h7]

/-- The density product of three densities above `δ`. -/
private theorem prod_ge_cube {d a b c : ℝ} (hd : 0 < d) (ha : d ≤ a) (hb : d ≤ b) (hc : d ≤ c) :
    d ^ 3 ≤ a * b * c := by
  have hab : d * d ≤ a * b := mul_le_mul ha hb hd.le (hd.le.trans ha)
  have : d * d * d ≤ a * b * c :=
    mul_le_mul hab hc hd.le (mul_nonneg (hd.le.trans ha) (hd.le.trans hb))
  linarith only [this]

/-- The density product of three densities below `1`. -/
private theorem prod_le_one {a b c : ℝ} (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) : a * b * c ≤ 1 := by
  have hab : a * b ≤ 1 := by
    simpa using mul_le_mul ha hb hb0 zero_le_one
  simpa using mul_le_mul hab hc hc0 zero_le_one

/-- The block of a copy is at least `α` times the size of its cluster. -/
private theorem bs_ge_alpha {lr Kr al mmaxr t : ℝ} (hl : 2 * al * mmaxr ≤ lr) (hK : 1 ≤ Kr)
    (hlK : lr * Kr ≤ t) (hmmax : 0 ≤ mmaxr) (hal : 0 ≤ al) : al * mmaxr ≤ t := by
  have h0 : 0 ≤ al * mmaxr := mul_nonneg hal hmmax
  have hlr0 : 0 ≤ lr := by linarith only [hl, h0]
  have h1 : lr ≤ lr * Kr := le_mul_of_one_le_right hlr0 hK
  linarith only [hl, hlK, hlr0, h1]

/-- **The demand of one copy in one ordered cluster pair.**  A copy occupies the pair through at
most one pair of positions, so the double sum of the demand collapses to a single product. -/
private theorem sum_pair_indicator {ι : Type} [DecidableEq ι] {f : ZMod 3 → ι}
    (hf : Function.Injective f) {S T : ι} {w : ZMod 3 → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a b : ZMod 3, f a = S → f b = T → w a * w b ≤ M) :
    ∑ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0) ≤ M := by
  classical
  by_cases hS : ∃ a, f a = S
  · obtain ⟨a₀, ha₀⟩ := hS
    by_cases hT : ∃ b, f b = T
    · obtain ⟨b₀, hb₀⟩ := hT
      have hEq : ∑ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0)
          = w a₀ * w b₀ := by
        rw [Finset.sum_eq_single a₀]
        · rw [Finset.sum_eq_single b₀]
          · rw [ite_eq_left ⟨ha₀, hb₀⟩]
          · intro b _ hb
            refine ite_eq_right ?_
            rintro ⟨-, h2⟩
            exact hb (hf (h2.trans hb₀.symm))
          · intro h; exact absurd (Finset.mem_univ b₀) h
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ite_eq_right ?_
          rintro ⟨h1, -⟩
          exact ha (hf (h1.trans ha₀.symm))
        · intro h; exact absurd (Finset.mem_univ a₀) h
      rw [hEq]
      exact hM a₀ b₀ ha₀ hb₀
    · push Not at hT
      have h0 : ∀ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0) = 0 :=
        fun a => Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => hT b h.2)
      rw [Finset.sum_congr rfl (fun a _ => h0 a)]
      simpa using hM0
  · push Not at hS
    have h0 : ∀ a : ZMod 3, ∑ b : ZMod 3, (if f a = S ∧ f b = T then w a * w b else 0) = 0 :=
      fun a => Finset.sum_eq_zero fun b _ => ite_eq_right (fun h => hS a h.1)
    rw [Finset.sum_congr rfl (fun a _ => h0 a)]
    simpa using hM0

/-- The demand of all the copies of one cluster triple in one ordered cluster pair, against the LP
weight of the triple. -/
private theorem copy_pair_bound {en Kr lr del dP cST ncr yv : ℝ}
    (hdel : 0 < del) (hl : 0 < lr) (hK : 0 < Kr) (hc : 0 < cST) (hdP : 0 < dP)
    (hnc : ncr ≤ (1 - en) * yv * del ^ 2 / (lr ^ 2 * Kr ^ 2 * dP)) :
    ncr * ((1 + 1 / Kr) ^ 2 * Kr ^ 2 * dP / (del ^ 2 * cST))
      ≤ (1 - en) * (1 + 1 / Kr) ^ 2 / (lr ^ 2 * cST) * yv := by
  have hM0 : 0 ≤ (1 + 1 / Kr) ^ 2 * Kr ^ 2 * dP / (del ^ 2 * cST) := by positivity
  refine (mul_le_mul_of_nonneg_right hnc hM0).trans_eq ?_
  field_simp

/-- Two prescribed sizes multiply out to at most `(1 + 1/K)²` times their ideal value. -/
private theorem sz_prod_bound {Kr del da db sa sb : ℝ} (hdel : 0 < del) (hK : 0 < Kr)
    (hda : del ≤ da) (hdb : del ≤ db) (hsa : sa < Kr * da / del + 1) (hsb : sb < Kr * db / del + 1)
    (hsb0 : 0 ≤ sb) :
    sa * sb ≤ (1 + 1 / Kr) ^ 2 * (Kr ^ 2 * (da * db) / del ^ 2) := by
  have hd1 : 1 ≤ da / del := (one_le_div hdel).mpr hda
  have hd2 : 1 ≤ db / del := (one_le_div hdel).mpr hdb
  have h1 : sa ≤ (1 + 1 / Kr) * (Kr * da / del) := by
    have he : (1 + 1 / Kr) * (Kr * da / del) = Kr * da / del + da / del := by field_simp
    rw [he]; linarith only [hsa, hd1]
  have h2 : sb ≤ (1 + 1 / Kr) * (Kr * db / del) := by
    have he : (1 + 1 / Kr) * (Kr * db / del) = Kr * db / del + db / del := by field_simp
    rw [he]; linarith only [hsb, hd2]
  calc sa * sb ≤ ((1 + 1 / Kr) * (Kr * da / del)) * ((1 + 1 / Kr) * (Kr * db / del)) := by
        refine mul_le_mul h1 h2 hsb0 ?_
        have : 0 ≤ da := le_trans hdel.le hda
        positivity
    _ = (1 + 1 / Kr) ^ 2 * (Kr ^ 2 * (da * db) / del ^ 2) := by field_simp

/-- The margin of the pair capacity: the two relative losses `1/K` and `2/P` are absorbed by the
factor `1 - e/8` of the number of copies. -/
private theorem capacity_core {en u v : ℝ} (he0 : 0 < en) (he1 : en ≤ 1) (hu0 : 0 ≤ u)
    (hu : u ≤ en / 640) (hv0 : 0 ≤ v) (hv : v ≤ en / 400) :
    (1 - en / 8) * ((1 + u) * (1 + v)) ^ 2 ≤ 1 - en / 64 := by
  have hs : (1 + u) * (1 + v) ≤ 1 + en / 200 := by nlinarith only [he1, hu, hv0, hv]
  have hs0 : (0:ℝ) ≤ (1 + u) * (1 + v) := by nlinarith only [hu0, hv0]
  have hsq : ((1 + u) * (1 + v)) ^ 2 ≤ (1 + en / 200) ^ 2 := by nlinarith only [hs, hs0]
  have h8 : (0:ℝ) ≤ 1 - en / 8 := by linarith only [he1]
  have hmul := mul_le_mul_of_nonneg_left hsq h8
  have hen2 : en ^ 2 ≤ en := by nlinarith only [he0, he1]
  have hen3 : (0:ℝ) ≤ en ^ 3 := by positivity
  have key : (1 - en / 8) * (1 + en / 200) ^ 2 ≤ 1 - en / 64 := by nlinarith only [hen2]
  linarith only [hmul, key]

/-- **The pair capacity of the coarse-cell grid.** -/
private theorem capacity_bound {en u Pnr lr mmaxr : ℝ} (he0 : 0 < en) (he1 : en ≤ 1)
    (hu0 : 0 ≤ u) (hu : u ≤ en / 640) (hP0 : 0 < Pnr) (hl0 : 0 < lr)
    (hv : 2 / Pnr ≤ en / 400) (hmm0 : 0 ≤ mmaxr) (hmm : mmaxr ≤ (Pnr + 2) * lr) :
    (1 - en / 8) * (1 + u) ^ 2 * mmaxr ^ 2 ≤ (1 - en / 64) * (Pnr * lr) ^ 2 := by
  have hv0 : (0:ℝ) ≤ 2 / Pnr := by positivity
  have hPv : Pnr * (1 + 2 / Pnr) = Pnr + 2 := by field_simp
  have hmm2 : mmaxr ^ 2 ≤ (Pnr * (1 + 2 / Pnr)) ^ 2 * lr ^ 2 := by
    rw [hPv]; nlinarith only [hmm0, hmm]
  have hcore := capacity_core he0 he1 hu0 hu hv0 hv
  have hnn : (0:ℝ) ≤ (1 - en / 8) * (1 + u) ^ 2 := by nlinarith only [he1]
  calc (1 - en / 8) * (1 + u) ^ 2 * mmaxr ^ 2
      ≤ (1 - en / 8) * (1 + u) ^ 2 * ((Pnr * (1 + 2 / Pnr)) ^ 2 * lr ^ 2) :=
        mul_le_mul_of_nonneg_left hmm2 hnn
    _ = ((1 - en / 8) * ((1 + u) * (1 + 2 / Pnr)) ^ 2) * (Pnr * lr) ^ 2 := by ring
    _ ≤ (1 - en / 64) * (Pnr * lr) ^ 2 := mul_le_mul_of_nonneg_right hcore (by positivity)

/-- **The pair capacity of the cluster pair, transported to the grid of the pair.** -/
private theorem cap_to_Pn {en Kr lr cST cardS cardT Pnr mmaxr : ℝ}
    (he0 : 0 < en) (he1 : en ≤ 1) (hK : 0 < Kr) (hl : 0 < lr) (hc : 0 < cST)
    (hu : 1 / Kr ≤ en / 640) (hP0 : 0 < Pnr) (hv : 2 / Pnr ≤ en / 400)
    (hmm0 : 0 ≤ mmaxr) (hmm : mmaxr ≤ (Pnr + 2) * lr)
    (hS : cardS ≤ mmaxr) (hT : cardT ≤ mmaxr) (hT0 : 0 ≤ cardT) :
    (1 - en / 8) * (1 + 1 / Kr) ^ 2 / (lr ^ 2 * cST) * (cST * cardS * cardT)
      ≤ (1 - en / 64) * Pnr ^ 2 := by
  have hprod : cardS * cardT ≤ mmaxr ^ 2 := by nlinarith only [hS, hT, hT0]
  have hbase := capacity_bound he0 he1 (by positivity : (0:ℝ) ≤ 1 / Kr) hu hP0 hl hv hmm0 hmm
  have hnn : (0:ℝ) ≤ (1 - en / 8) * (1 + 1 / Kr) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hA : (1 - en / 8) * (1 + 1 / Kr) ^ 2 / (lr ^ 2 * cST) * (cST * cardS * cardT)
      = (1 - en / 8) * (1 + 1 / Kr) ^ 2 * (cardS * cardT) / lr ^ 2 := by
    field_simp
  rw [hA]
  have h1 : (1 - en / 8) * (1 + 1 / Kr) ^ 2 * (cardS * cardT)
      ≤ (1 - en / 8) * (1 + 1 / Kr) ^ 2 * mmaxr ^ 2 := mul_le_mul_of_nonneg_left hprod hnn
  refine le_trans ((div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < lr ^ 2)).mpr
    (le_trans h1 hbase)) (le_of_eq ?_)
  field_simp

/-- The value of an unplaced copy against the cell area it demands. -/
private theorem bad_term_bound {lr Kr del d0 d1 d2 s0 s1 : ℝ} (hdel : 0 < del) (hK0 : 0 ≤ Kr)
    (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd2' : d2 ≤ 1)
    (h0 : Kr * d0 / del ≤ s0) (h1 : Kr * d1 / del ≤ s1) :
    lr ^ 2 * Kr ^ 2 / del ^ 2 * (d0 * d1 * d2) ≤ lr ^ 2 * (s0 * s1) := by
  have hnn0 : (0:ℝ) ≤ Kr * d0 / del := by positivity
  have hnn1 : (0:ℝ) ≤ Kr * d1 / del := by positivity
  have hprod : (Kr * d0 / del) * (Kr * d1 / del) ≤ s0 * s1 :=
    mul_le_mul h0 h1 hnn1 (le_trans hnn0 h0)
  have hs0 : (0:ℝ) ≤ s0 * s1 := le_trans (mul_nonneg hnn0 hnn1) hprod
  have key : lr ^ 2 * Kr ^ 2 / del ^ 2 * (d0 * d1 * d2)
      = lr ^ 2 * ((Kr * d0 / del) * (Kr * d1 / del) * d2) := by
    field_simp
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg lr)
  calc (Kr * d0 / del) * (Kr * d1 / del) * d2 ≤ (s0 * s1) * d2 :=
        mul_le_mul_of_nonneg_right hprod hd2
    _ ≤ s0 * s1 := by nlinarith only [hd2', hs0]

/-- The total block area of the construction is a small fraction of `|V|²`. -/
private theorem kp_tau_sq {kt en epsr nr : ℝ} (h0 : 0 ≤ kt) (h : kt ≤ 3 * en / 32 * nr)
    (he0 : 0 < en) (he1 : en ≤ 1) (heps : en ≤ epsr) :
    kt ^ 2 ≤ epsr * nr ^ 2 / 16 := by
  have h1 : kt ^ 2 ≤ (3 * en / 32 * nr) ^ 2 := pow_le_pow_left₀ h0 h 2
  have he2 : en ^ 2 ≤ epsr := le_trans (by nlinarith) heps
  nlinarith [mul_nonneg (sq_nonneg nr) (by linarith : (0:ℝ) ≤ 64 * epsr - 9 * en ^ 2)]

/-- The margin `k·(2τ + 1)` of the covering clause. -/
private theorem k_tau_bound {kr taur nr del epsr : ℝ} (hk0 : 0 ≤ kr) (htau1 : 1 ≤ taur)
    (hdel : 0 < del) (hk : kr * (6 * taur ^ 2 * del ^ 3) ≤ nr ^ 2)
    (htau : 192 / (epsr * del ^ 3) ≤ taur) (heps : 0 < epsr) :
    kr * (2 * taur + 1) ≤ epsr * nr ^ 2 / 8 := by
  have hde : (192:ℝ) ≤ taur * (epsr * del ^ 3) := by
    rw [div_le_iff₀ (by positivity)] at htau
    linarith only [htau]
  have hk' : kr ≤ nr ^ 2 / (6 * taur ^ 2 * del ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    linarith only [hk]
  have h3 : kr * (2 * taur + 1) ≤ 3 * taur * kr := by nlinarith only [hk0, htau1]
  have h4 : 3 * taur * kr ≤ 3 * taur * (nr ^ 2 / (6 * taur ^ 2 * del ^ 3)) :=
    mul_le_mul_of_nonneg_left hk' (by positivity)
  have h5 : 3 * taur * (nr ^ 2 / (6 * taur ^ 2 * del ^ 3)) = nr ^ 2 / (2 * taur * del ^ 3) := by
    field_simp
    ring
  have h6 : nr ^ 2 / (2 * taur * del ^ 3) ≤ epsr * nr ^ 2 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [mul_nonneg (by linarith : (0:ℝ) ≤ taur * (epsr * del ^ 3) - 4) (sq_nonneg nr)]
  linarith only [h3, h4, h5, h6]

/-! ### The reduction -/
private theorem copied_mass_lower_bound {ι : Type} [DecidableEq ι]
    (Gd : Finset ι) (nc : ι → ℕ) (y d : ι → ℝ) (e τ : ℝ)
    (hτ : 0 < τ) (hdpos : ∀ th ∈ Gd, 0 < d th) (hdle : ∀ th, d th ≤ 1)
    (hfloor : ∀ th, nc th = ⌊(1 - e / 8) * y th / (τ ^ 2 * d th)⌋₊) :
    (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2
      ≤ ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * d c.1.1 := by
  classical
  have hall : ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * d c.1.1
      = ∑ th ∈ Gd, nc th • (τ ^ 2 * d th) := by
    rw [Finset.sum_coe_sort (copySet Gd nc) (fun p => τ ^ 2 * d p.1)]
    exact sum_copySet Gd nc (fun th => τ ^ 2 * d th)
  have hallLB : (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2
      ≤ ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * d c.1.1 := by
    rw [hall]
    have hterm : ∀ th ∈ Gd, (1 - e / 8) * y th - τ ^ 2 ≤ nc th • (τ ^ 2 * d th) := by
      intro th hth
      rw [nsmul_eq_mul]
      have hdp := hdpos th hth
      have hpos : (0 : ℝ) < τ ^ 2 * d th := by positivity
      have hZ : (1 - e / 8) * y th / (τ ^ 2 * d th) - 1 ≤ (nc th : ℝ) := by
        rw [hfloor th]
        linarith only [Nat.lt_floor_add_one ((1 - e / 8) * y th / (τ ^ 2 * d th))]
      have hmul := mul_le_mul_of_nonneg_right hZ hpos.le
      have heq : ((1 - e / 8) * y th / (τ ^ 2 * d th) - 1) * (τ ^ 2 * d th)
          = (1 - e / 8) * y th - τ ^ 2 * d th := by
        field_simp
      rw [heq] at hmul
      have hdle : τ ^ 2 * d th ≤ τ ^ 2 := by
        have h1 : τ ^ 2 * d th ≤ τ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hdle th) (sq_nonneg τ)
        linarith
      linarith
    have hexp : ∑ th ∈ Gd, ((1 - e / 8) * y th - τ ^ 2)
        = (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [← hexp]
    exact Finset.sum_le_sum hterm
  exact hallLB

private theorem dense_support_value_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    (δ : ℝ) (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (hy0 : ∀ th, 0 ≤ y th) :
    clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th
      ≤ ∑ th ∈ clusterLPSupport y \ sparseTriples G Pp δ, y th := by
  classical
  let Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}) :=
    clusterLPSupport y \ sparseTriples G Pp δ
  have hGdsum : clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th ≤ ∑ th ∈ Gd, y th := by
    have hsplit : ∑ th ∈ univ \ Gd, y th + ∑ th ∈ Gd, y th = clusterLPValue y :=
      Finset.sum_sdiff (Finset.subset_univ Gd)
    have hle : ∑ th ∈ univ \ Gd, y th ≤ ∑ th ∈ sparseTriples G Pp δ, y th := by
      have hpt : ∀ th ∈ univ \ Gd, y th ≤ (if th ∈ sparseTriples G Pp δ then y th else 0) := by
        intro th hth
        by_cases hs : th ∈ sparseTriples G Pp δ
        · rw [ite_eq_left hs]
        · rw [ite_eq_right hs]
          have hy0 : y th = 0 := by
            by_contra hne
            exact (Finset.mem_sdiff.mp hth).2 (Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, hs⟩)
          rw [hy0]
      refine le_trans (Finset.sum_le_sum hpt) ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun th _ _ => by split; exacts [hy0 th, le_refl 0])) ?_
      rw [← Finset.sum_filter]
      apply le_of_eq
      congr 1
      simp
    linarith
  exact hGdsum

private theorem pair_product_le_cyclic_sum (z : ZMod 3 → ℕ) :
    (z 0 : ℝ) * (z 1 : ℝ) ≤ ∑ a : ZMod 3, (z a : ℝ) * (z (a + 1) : ℝ) := by
  have h := Finset.single_le_sum
    (f := fun a : ZMod 3 => (z a : ℝ) * (z (a + 1) : ℝ))
    (fun a _ => by positivity) (Finset.mem_univ (0 : ZMod 3))
  simpa using h

private theorem box_demand_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (ε₁ δ e : ℝ) (K l Pn mmax : ℕ)
    (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (szf : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ)
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (he0 : 0 < e) (he1 : e ≤ 1) (hδ0 : 0 < δ)
    (hyLP : IsClusterTripleLP G Pp (ε₁ / 8) (ε₁ / 4) y)
    (hGdcard : ∀ th ∈ Gd, #th = 3)
    (hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
    (hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
      ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b)
    (hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th)
    (hdOppδ : ∀ th ∈ Gd, ∀ a : ZMod 3, δ ≤ dOpp G Pp th a)
    (hszUB : ∀ th a, (szf th a : ℝ) < (K : ℝ) * dOpp G Pp th a / δ + 1)
    (hncUB : ∀ th ∈ Gd, (nc th : ℝ)
      ≤ (1 - e / 8) * y th * δ ^ 2 /
        ((l : ℝ) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th))
    (hKpos : (0 : ℝ) < (K : ℝ)) (hl0R : (0 : ℝ) < (l : ℝ))
    (hKu : 1 / (K : ℝ) ≤ e / 640) (hPn0R : (0 : ℝ) < (Pn : ℝ))
    (hPv : 2 / (Pn : ℝ) ≤ e / 400) (hmmax0R : (0 : ℝ) < (mmax : ℝ))
    (hmmPn : (mmax : ℝ) ≤ ((Pn : ℝ) + 2) * (l : ℝ))
    (hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax) :
    ∀ S T : {S : Finset V // S ∈ Pp.parts}, S ≠ T →
      boxDemand (fun (c : {p // p ∈ copySet Gd nc}) a => triPos Pp c.1.1 a)
        (fun (c : {p // p ∈ copySet Gd nc}) a => szf c.1.1 a) S T
        ≤ (1 - e / 64) * (Pn : ℝ) ^ 2 := by
  classical
  intro S T hST
  have hbd : boxDemand (fun (c : {p // p ∈ copySet Gd nc}) a => triPos Pp c.1.1 a)
      (fun (c : {p // p ∈ copySet Gd nc}) a => szf c.1.1 a) S T
      = ∑ th ∈ Gd, (nc th) • (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0) := by
    have h1 : boxDemand (fun (c : {p // p ∈ copySet Gd nc}) a => triPos Pp c.1.1 a)
        (fun (c : {p // p ∈ copySet Gd nc}) a => szf c.1.1 a) S T
        = ∑ p ∈ copySet Gd nc, (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp p.1 a = S ∧ triPos Pp p.1 b = T then
            (szf p.1 a : ℝ) * (szf p.1 b : ℝ) else 0) := by
      simp only [boxDemand]
      exact Finset.sum_coe_sort (copySet Gd nc)
        (fun p => ∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp p.1 a = S ∧ triPos Pp p.1 b = T then
            (szf p.1 a : ℝ) * (szf p.1 b : ℝ) else 0)
    rw [h1]
    exact sum_copySet Gd nc (fun th => ∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0)
  rw [hbd]
  have hPnnn : (0 : ℝ) ≤ (1 - e / 64) * (Pn : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (by positivity)
  -- a copy of a triple through the pair forces the pair to be dense
  have hnotmem : ∀ th ∈ Gd, ∀ a b : ZMod 3, triPos Pp th a = S → triPos Pp th b = T →
      a ≠ b ∧ δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) := by
    intro th hth a b ha hb
    have hab : a ≠ b := by
      intro h
      exact hST (by rw [← ha, ← hb, h])
    refine ⟨hab, ?_⟩
    have hd := hGddense th hth (triPos Pp th a) (triPos_mem Pp (hGdcard th hth) a)
      (triPos Pp th b) (triPos_mem Pp (hGdcard th hth) b) (hposne th (hGdcard th hth) a b hab)
    rwa [ha, hb] at hd
  by_cases hcST : (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) < δ
  · -- no copy uses a sparse pair
    have hzero : ∀ th ∈ Gd, (nc th) • (∑ a : ZMod 3, ∑ b : ZMod 3,
        if triPos Pp th a = S ∧ triPos Pp th b = T then
          (szf th a : ℝ) * (szf th b : ℝ) else 0) = 0 := by
      intro th hth
      have : (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ite_eq_right ?_
        rintro ⟨ha, hb⟩
        exact absurd (hnotmem th hth a b ha hb).2 (not_le.mpr hcST)
      rw [this, smul_zero]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact hPnnn
  · push Not at hcST
    have hc0 : (0 : ℝ) < (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) :=
      lt_of_lt_of_le hδ0 hcST
    -- the bound of one triple
    have hterm : ∀ th ∈ Gd, (nc th) • (∑ a : ZMod 3, ∑ b : ZMod 3,
          if triPos Pp th a = S ∧ triPos Pp th b = T then
            (szf th a : ℝ) * (szf th b : ℝ) else 0)
        ≤ (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
            / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0) := by
      intro th hth
      have hdp := hdProd0 th hth
      by_cases hmem : S ∈ th ∧ T ∈ th
      · rw [ite_eq_left hmem, nsmul_eq_mul]
        have hM0 : (0 : ℝ) ≤ (1 + 1 / (K : ℝ)) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th
            / (δ ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)) := by positivity
        have hinner : (∑ a : ZMod 3, ∑ b : ZMod 3,
            if triPos Pp th a = S ∧ triPos Pp th b = T then
              (szf th a : ℝ) * (szf th b : ℝ) else 0)
            ≤ (1 + 1 / (K : ℝ)) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th
              / (δ ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)) := by
          refine sum_pair_indicator (triPos_injective Pp (hGdcard th hth)) hM0 ?_
          intro a b ha hb
          have hab := (hnotmem th hth a b ha hb).1
          have hprod : dOpp G Pp th a * dOpp G Pp th b
              * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) = dProd G Pp th := by
            have h := dOpp_mul_dOpp_mul_dens G Pp th hab
            rwa [ha, hb] at h
          have h1 := sz_prod_bound hδ0 hKpos (hdOppδ th hth a) (hdOppδ th hth b)
            (hszUB th a) (hszUB th b) (Nat.cast_nonneg _)
          refine le_trans h1 (le_of_eq ?_)
          rw [← hprod]
          field_simp
        refine le_trans (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)) ?_
        exact copy_pair_bound hδ0 hl0R hKpos hc0 hdp (hncUB th hth)
      · rw [ite_eq_right hmem]
        have hz : (∑ a : ZMod 3, ∑ b : ZMod 3,
            if triPos Pp th a = S ∧ triPos Pp th b = T then
              (szf th a : ℝ) * (szf th b : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ite_eq_right ?_
          rintro ⟨ha, hb⟩
          refine hmem ⟨?_, ?_⟩
          · rw [← ha]; exact triPos_mem Pp (hGdcard th hth) a
          · rw [← hb]; exact triPos_mem Pp (hGdcard th hth) b
        rw [hz, smul_zero, mul_zero]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    -- the LP capacity of the pair
    have hWc0 : (0 : ℝ) ≤ (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
        / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)) := by
      have : (0:ℝ) ≤ 1 - e / 8 := by linarith
      positivity
    have hstep1 : ∑ th ∈ Gd, (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0)
        ≤ ∑ th, (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun th _ _ => ?_
      refine mul_nonneg hWc0 ?_
      split
      · exact hyLP.1 th
      · exact le_refl 0
    have hstep2 : ∑ th, (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * (if S ∈ th ∧ T ∈ th then y th else 0)
        = (1 - e / 8) * (1 + 1 / (K : ℝ)) ^ 2
          / ((l : ℝ) ^ 2 * (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
          * ∑ th ∈ triplesThrough Pp S T, y th := by
      rw [← Finset.mul_sum]
      congr 1
      rw [triplesThrough, Finset.sum_filter]
    refine le_trans hstep1 (le_trans (le_of_eq hstep2) ?_)
    refine le_trans (mul_le_mul_of_nonneg_left (hyLP.2.2 S T hST) hWc0) ?_
    rw [clusterPairCap]
    have hcS : (#(S : Finset V) : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hcardle _ S.2
    have hcT : (#(T : Finset V) : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hcardle _ T.2
    exact cap_to_Pn he0 he1 hKpos hl0R hc0 hKu hPn0R hPv hmmax0R.le hmmPn hcS hcT
      (Nat.cast_nonneg _)


private theorem coarse_cover_clause {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (ε ε₁ δ e α τ : ℝ) (K kp mmin l Pn Cn k : ℕ)
    (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (bad Good : Finset {p // p ∈ copySet Gd nc})
    (szc : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ)
    (U W X A B C : ℕ → Finset V)
    (hkpN : 0 < kp) (hkpdef : kp = #Pp.parts)
    (hmmin0 : 0 < mmin) (hnlo : kp * mmin ≤ Fintype.card V)
    (hyLP : IsClusterTripleLP G Pp (ε₁ / 8) (ε₁ / 4) y)
    (hysupp : #(clusterLPSupport y) ≤ kp ^ 2)
    (hynu : nu3star (G.regularityReduced Pp (ε₁ / 8) (ε₁ / 4))
      ≤ clusterLPValue y + 1)
    (hδ0 : 0 < δ)
    (hGddef : Gd = clusterLPSupport y \ sparseTriples G Pp δ)
    (hsumGood : (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
        * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ)))
      = ∑ c ∈ Good, τ ^ 2 * dProd G Pp c.1.1)
    (hτ0 : 0 < τ)
    (hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th)
    (hdProdUB : ∀ th, dProd G Pp th ≤ 1)
    (hncdef : nc = fun th => ⌊(1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th)⌋₊)
    (hbadterm : ∀ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1
      ≤ (l : ℝ) ^ 2 * ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ))
    (hIbad : (∑ c ∈ bad, ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ))
      ≤ e / 64 * (Fintype.card {S : Finset V // S ∈ Pp.parts} : ℝ) ^ 2 * (Pn : ℝ) ^ 2)
    (hPnl : Pn * l ≤ mmin)
    (hGooddef : Good = (univ : Finset {p // p ∈ copySet Gd nc}) \ bad)
    (hkle : k ≤ #Good)
    (hdProdLB : ∀ th ∈ Gd, δ ^ 3 ≤ dProd G Pp th)
    (hτ1 : (1 : ℝ) ≤ τ) (hτ192 : 192 / (ε * δ ^ 3) ≤ τ)
    (hε : 0 < ε) (hτdef : τ = (l : ℝ) * (K : ℝ) / δ)
    (hl3 : (l : ℝ) ≤ 3 * α * (mmin : ℝ)) (hKpos : (0 : ℝ) < (K : ℝ))
    (hα0 : 0 < α)
    (hαδ : α ≤ δ * e / (32 * K))
    (he0 : 0 < e) (he1 : e ≤ 1) (heε : e ≤ ε)
    (hCndef : Cn = ⌈16 / ε⌉₊) (hnCn : Cn ≤ Fintype.card V) (hδε : δ ≤ ε)
    (hgrid : ∀ i < k, IsGridSubTriple G Pp (ε₁ / 8) δ α τ
      (U i) (W i) (X i) (A i) (B i) (C i)) :
    nu3star (G.regularityReduced Pp (ε₁ / 8) (ε₁ / 4))
      ≤ (∑ i ∈ Finset.range k,
          ((G.edgeDensity (U i) (W i) : ℝ) * (#(A i) : ℝ) * (#(B i) : ℝ)
            + (G.edgeDensity (U i) (X i) : ℝ) * (#(A i) : ℝ) * (#(C i) : ℝ)
            + (G.edgeDensity (W i) (X i) : ℝ) * (#(B i) : ℝ) * (#(C i) : ℝ))) / 3
        + ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  -- ### the covering clause
  have hcardV0 : 0 < Fintype.card V := lt_of_lt_of_le (Nat.mul_pos hkpN hmmin0) hnlo
  have hn0R : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hcardV0
  have hLPle : 6 * clusterLPValue y ≤ (Fintype.card V : ℝ) ^ 2 :=
    clusterLPValue_le_sq G Pp (ε₁ / 8) (ε₁ / 4) hyLP
  have hLP0 : 0 ≤ clusterLPValue y := Finset.sum_nonneg fun th _ => hyLP.1 th
  have hSs0 : 0 ≤ ∑ th ∈ sparseTriples G Pp δ, y th :=
    Finset.sum_nonneg fun th _ => hyLP.1 th
  have hsparse : 2 * ∑ th ∈ sparseTriples G Pp δ, y th ≤ δ * (Fintype.card V : ℝ) ^ 2 :=
    sum_sparse_triples_le G Pp (ε₁ / 8) (ε₁ / 4) hδ0.le hyLP
  have hGdsum : clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th ≤ ∑ th ∈ Gd, y th := by
    simpa only [hGddef] using dense_support_value_le G Pp δ y hyLP.1
  -- the value of the placed copies
  have hallLB : (1 - e / 8) * (∑ th ∈ Gd, y th) - (#Gd : ℝ) * τ ^ 2
      ≤ ∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1 := by
    exact copied_mass_lower_bound Gd nc y (dProd G Pp) e τ hτ0 hdProd0 hdProdUB
      (fun th => hncdef ▸ rfl)
  -- the copies that could not be placed
  have hkpcard : (Fintype.card {S : Finset V // S ∈ Pp.parts} : ℝ) = (kp : ℝ) := by
    rw [Fintype.card_coe, hkpdef]
  have hbadsum : ∑ c ∈ bad, τ ^ 2 * dProd G Pp c.1.1 ≤ e / 64 * (Fintype.card V : ℝ) ^ 2 := by
    have h1 : ∑ c ∈ bad, τ ^ 2 * dProd G Pp c.1.1
        ≤ ∑ c ∈ bad, (l : ℝ) ^ 2 * ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ) :=
      Finset.sum_le_sum fun c _ => hbadterm c
    have h1' : ∑ c ∈ bad, (l : ℝ) ^ 2 * ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ)
        = (l : ℝ) ^ 2 * ∑ c ∈ bad, ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1'] at h1
    have h2 : (l : ℝ) ^ 2 * (∑ c ∈ bad, ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ))
        ≤ (l : ℝ) ^ 2 * (e / 64 * (kp : ℝ) ^ 2 * (Pn : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [← hkpcard]
      exact hIbad
    have hkPl : (kp : ℝ) * ((Pn : ℝ) * (l : ℝ)) ≤ (Fintype.card V : ℝ) := by
      have h : kp * (Pn * l) ≤ Fintype.card V := le_trans (Nat.mul_le_mul_left kp hPnl) hnlo
      exact_mod_cast h
    have hsq : ((kp : ℝ) * ((Pn : ℝ) * (l : ℝ))) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hkPl 2
    have heq : (l : ℝ) ^ 2 * (e / 64 * (kp : ℝ) ^ 2 * (Pn : ℝ) ^ 2)
        = e / 64 * ((kp : ℝ) * ((Pn : ℝ) * (l : ℝ))) ^ 2 := by ring
    rw [heq] at h2
    have h3 : e / 64 * ((kp : ℝ) * ((Pn : ℝ) * (l : ℝ))) ^ 2
        ≤ e / 64 * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  have hGoodsum : ∑ c ∈ Good, τ ^ 2 * dProd G Pp c.1.1
      = (∑ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1)
        - ∑ c ∈ bad, τ ^ 2 * dProd G Pp c.1.1 := by
    rw [hGooddef, Finset.sum_sdiff_eq_sub (Finset.subset_univ bad)]
  -- the feasible point is recovered by the family
  have hGdcardle : (#Gd : ℝ) ≤ (kp : ℝ) ^ 2 := by
    have h2 : #Gd ≤ #(clusterLPSupport y) := by
      rw [hGddef]
      exact Finset.card_le_card Finset.sdiff_subset
    have h3 : #Gd ≤ kp ^ 2 := le_trans h2 hysupp
    exact_mod_cast h3
  have hGdtau : (#Gd : ℝ) * τ ^ 2 ≤ (kp : ℝ) ^ 2 * τ ^ 2 :=
    mul_le_mul_of_nonneg_right hGdcardle (sq_nonneg _)
  have hA4 : e / 8 * clusterLPValue y ≤ e * (Fintype.card V : ℝ) ^ 2 / 48 := by
    have h1 : clusterLPValue y ≤ (Fintype.card V : ℝ) ^ 2 / 6 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ e / 8)
    linarith
  have hA1 : (1 - e / 8) * (clusterLPValue y - ∑ th ∈ sparseTriples G Pp δ, y th)
      ≤ (1 - e / 8) * (∑ th ∈ Gd, y th) := mul_le_mul_of_nonneg_left hGdsum (by linarith)
  have hA3 : 0 ≤ e / 8 * ∑ th ∈ sparseTriples G Pp δ, y th := mul_nonneg (by linarith) hSs0
  have hval : clusterLPValue y
      ≤ (∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
          * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ)))
        + (e * (Fintype.card V : ℝ) ^ 2 / 48 + δ * (Fintype.card V : ℝ) ^ 2 / 2
            + (kp : ℝ) ^ 2 * τ ^ 2 + e / 64 * (Fintype.card V : ℝ) ^ 2) := by
    rw [hsumGood, hGoodsum]
    linarith
  -- ### the error budget
  have hkκ : (k : ℝ) ≤ ∑ th ∈ Gd, (nc th : ℝ) := by
    have h2 : #Good ≤ #(copySet Gd nc) := by
      have h := Finset.card_le_univ Good
      rwa [Fintype.card_coe] at h
    have h3 : #(copySet Gd nc) = ∑ th ∈ Gd, nc th := card_copySet Gd nc
    have h4 : k ≤ ∑ th ∈ Gd, nc th := by omega
    calc (k : ℝ) ≤ ((∑ th ∈ Gd, nc th : ℕ) : ℝ) := by exact_mod_cast h4
      _ = ∑ th ∈ Gd, (nc th : ℝ) := by push_cast; rfl
  have hncy : ∀ th ∈ Gd, (nc th : ℝ) * (τ ^ 2 * δ ^ 3) ≤ y th := by
    intro th hth
    have hdp := hdProd0 th hth
    have hy0 : (0 : ℝ) ≤ y th := hyLP.1 th
    have hZ : (nc th : ℝ) ≤ (1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th) := by
      rw [hncdef]
      refine Nat.floor_le ?_
      apply div_nonneg (mul_nonneg (by linarith) hy0)
      positivity
    have h1 : (nc th : ℝ) * (τ ^ 2 * dProd G Pp th) ≤ (1 - e / 8) * y th := by
      have h := mul_le_mul_of_nonneg_right hZ (by positivity : (0:ℝ) ≤ τ ^ 2 * dProd G Pp th)
      rwa [div_mul_cancel₀ _ (by positivity : (τ ^ 2 * dProd G Pp th) ≠ 0)] at h
    have h2 : (nc th : ℝ) * (τ ^ 2 * δ ^ 3) ≤ (nc th : ℝ) * (τ ^ 2 * dProd G Pp th) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (hdProdLB th hth) (sq_nonneg τ)
    have h3 : (1 - e / 8) * y th ≤ y th := by
      have h4 : (0:ℝ) ≤ e / 8 * y th := mul_nonneg (by linarith) hy0
      linarith
    linarith
  have hksum : (k : ℝ) * (6 * τ ^ 2 * δ ^ 3) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have h1 : (∑ th ∈ Gd, (nc th : ℝ)) * (τ ^ 2 * δ ^ 3) ≤ ∑ th ∈ Gd, y th := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hncy
    have h2 : ∑ th ∈ Gd, y th ≤ clusterLPValue y :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun th _ _ => hyLP.1 th
    have h3 : (k : ℝ) * (τ ^ 2 * δ ^ 3) ≤ (∑ th ∈ Gd, (nc th : ℝ)) * (τ ^ 2 * δ ^ 3) :=
      mul_le_mul_of_nonneg_right hkκ (by positivity)
    linarith
  have hkbound : (k : ℝ) * (2 * τ + 1) ≤ ε * (Fintype.card V : ℝ) ^ 2 / 8 :=
    k_tau_bound (Nat.cast_nonneg _) hτ1 hδ0 hksum hτ192 hε
  have hτmmin : τ ≤ 3 * α * (K : ℝ) / δ * (mmin : ℝ) := by
    rw [hτdef, div_le_iff₀ hδ0]
    have h1 : (l : ℝ) * (K : ℝ) ≤ 3 * α * (mmin : ℝ) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right hl3 hKpos.le
    have h2 : 3 * α * (K : ℝ) / δ * (mmin : ℝ) * δ = 3 * α * (mmin : ℝ) * (K : ℝ) := by
      field_simp
    rw [h2]
    exact h1
  have hkpτ : (kp : ℝ) * τ ≤ 3 * e / 32 * (Fintype.card V : ℝ) := by
    have hx0 : (0 : ℝ) ≤ 3 * α * (K : ℝ) / δ := by positivity
    have h1 : (kp : ℝ) * τ ≤ (kp : ℝ) * (3 * α * (K : ℝ) / δ * (mmin : ℝ)) :=
      mul_le_mul_of_nonneg_left hτmmin (Nat.cast_nonneg _)
    have h2 : (kp : ℝ) * (mmin : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hnlo
    have h3 : (kp : ℝ) * (3 * α * (K : ℝ) / δ * (mmin : ℝ))
        = (3 * α * (K : ℝ) / δ) * ((kp : ℝ) * (mmin : ℝ)) := by ring
    have h4 : (3 * α * (K : ℝ) / δ) * ((kp : ℝ) * (mmin : ℝ))
        ≤ (3 * α * (K : ℝ) / δ) * (Fintype.card V : ℝ) := mul_le_mul_of_nonneg_left h2 hx0
    have h5 : 3 * α * (K : ℝ) / δ ≤ 3 * e / 32 := by
      rw [div_le_iff₀ hδ0]
      have h6 := mul_le_mul_of_nonneg_left hαδ (by positivity : (0:ℝ) ≤ 3 * (K : ℝ))
      have h7 : 3 * (K : ℝ) * (δ * e / (32 * (K : ℝ))) = 3 * e / 32 * δ := by
        field_simp
      rw [h7] at h6
      linarith
    have h8 : (3 * α * (K : ℝ) / δ) * (Fintype.card V : ℝ)
        ≤ 3 * e / 32 * (Fintype.card V : ℝ) := mul_le_mul_of_nonneg_right h5 hn0R.le
    linarith
  have hkpsq : (kp : ℝ) ^ 2 * τ ^ 2 ≤ ε * (Fintype.card V : ℝ) ^ 2 / 16 := by
    have h := kp_tau_sq (by positivity : (0:ℝ) ≤ (kp : ℝ) * τ) hkpτ he0 he1 heε
    calc (kp : ℝ) ^ 2 * τ ^ 2 = ((kp : ℝ) * τ) ^ 2 := by ring
      _ ≤ ε * (Fintype.card V : ℝ) ^ 2 / 16 := h
  have hone : (1 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 / 16 := by
    have h1 : (16 : ℝ) / ε ≤ (Cn : ℝ) := by rw [hCndef]; exact Nat.le_ceil _
    have h2 : (Cn : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hnCn
    rw [div_le_iff₀ hε] at h1
    have h3 : (16 : ℝ) ≤ ε * (Fintype.card V : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h2 hε.le
      linarith
    have h4 : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcardV0
    have h5 : (16 : ℝ) * 1 ≤ (ε * (Fintype.card V : ℝ)) * (Fintype.card V : ℝ) :=
      mul_le_mul h3 h4 zero_le_one (by linarith)
    linarith
  have hen : e * (Fintype.card V : ℝ) ^ 2 ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right heε (sq_nonneg _)
  have hdn : δ * (Fintype.card V : ℝ) ^ 2 ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hδε (sq_nonneg _)
  have hmain := nu3star_le_cover_of_family_lp_value G Pp U W X A B C hτ0.le hgrid hynu hval
  refine le_trans hmain ?_
  linarith

private structure CoarseClusterScales {V : Type} [Fintype V] [DecidableEq V]
    (Pp : Finpartition (univ : Finset V)) (T₀ ε δ θ : ℝ)
    (s₀ K KB Mmin Cn : ℕ) (α : ℝ) where
  kp : ℕ
  mmax : ℕ
  mmin : ℕ
  l : ℕ
  Pn : ℕ
  τ : ℝ
  hkpdef : kp = #Pp.parts
  hkpN : 0 < kp
  hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax
  hnlo : kp * mmin ≤ Fintype.card V
  hnCn : Cn ≤ Fintype.card V
  hmmin0 : 0 < mmin
  hmmax0R : (0 : ℝ) < (mmax : ℝ)
  hlLB : 2 * α * (mmax : ℝ) ≤ (l : ℝ)
  hl0 : 0 < l
  hl0R : (0 : ℝ) < (l : ℝ)
  hl3 : (l : ℝ) ≤ 3 * α * (mmin : ℝ)
  hPnl : Pn * l ≤ mmin
  hPnltR : (mmin : ℝ) < ((Pn : ℝ) + 1) * (l : ℝ)
  hmmPn : (mmax : ℝ) ≤ ((Pn : ℝ) + 2) * (l : ℝ)
  hPnge : 1 / (4 * α) ≤ (Pn : ℝ)
  hPn0R : (0 : ℝ) < (Pn : ℝ)
  hPn0 : 0 < Pn
  hτdef : τ = (l : ℝ) * (K : ℝ) / δ
  hτ0 : 0 < τ
  hτT₀ : T₀ ≤ τ
  hτ192 : 192 / (ε * δ ^ 3) ≤ τ
  hτ1 : (1 : ℝ) ≤ τ
  hK1R : (1 : ℝ) ≤ (K : ℝ)
  hs₀θ : (s₀ : ℝ) ≤ θ * (Pn : ℝ)
  hfitS : ∀ S ∈ Pp.parts, Pn * l ≤ #S

private theorem coarse_cluster_scales {V : Type} [Fintype V] [DecidableEq V]
    (Pp : Finpartition (univ : Finset V)) (T₀ ε δ e θ α ε₁ : ℝ)
    (s₀ K KB Mmin Cn : ℕ)
    (hV : KB * (Mmin + 1) + Cn + 10 ≤ Fintype.card V)
    (hPeq : Pp.IsEquipartition)
    (hPl : 4 / ε₁ ≤ (#Pp.parts : ℝ))
    (hPb : (#Pp.parts : ℝ) ≤ (KB : ℝ))
    (hMdef : Mmin =
      ⌈2 / α + δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) + 800 / e⌉₊)
    (hs₀def : s₀ = ⌈(K : ℝ) / δ⌉₊)
    (hε : 0 < ε) (hε₁0 : 0 < ε₁) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (he0 : 0 < e)
    (hT₀0 : 0 < T₀) (hK1 : 1 ≤ K)
    (hα0 : 0 < α) (hα16 : α ≤ 1 / 16)
    (hαθ : α ≤ θ * δ / (16 * K)) (hθ0 : 0 < θ) :
    Nonempty (CoarseClusterScales Pp T₀ ε δ θ s₀ K KB Mmin Cn α) := by
  classical
  -- ### the clusters
  have hkpR : (0 : ℝ) < (#Pp.parts : ℝ) :=
    lt_of_lt_of_le (div_pos (by norm_num) hε₁0) hPl
  have hkpN : 0 < #Pp.parts := by exact_mod_cast hkpR
  have hpne : Pp.parts.Nonempty := Finset.card_pos.mp hkpN
  set kp : ℕ := #Pp.parts with hkpdef
  set mmax : ℕ := Pp.parts.sup' hpne Finset.card with hmmaxdef
  set mmin : ℕ := Pp.parts.inf' hpne Finset.card with hmmindef
  let Smin := Classical.choose (Finset.exists_mem_eq_inf' hpne Finset.card)
  have ⟨hSminmem, hSmineq⟩ :=
    Classical.choose_spec (Finset.exists_mem_eq_inf' hpne Finset.card)
  let Smax := Classical.choose (Finset.exists_mem_eq_sup' hpne Finset.card)
  have ⟨hSmaxmem, hSmaxeq⟩ :=
    Classical.choose_spec (Finset.exists_mem_eq_sup' hpne Finset.card)
  have hminmax : mmin ≤ mmax := by
    rw [hmmindef, hSmineq, hmmaxdef]; exact Finset.le_sup' _ hSminmem
  have hmm1 : mmax ≤ mmin + 1 := by
    rw [hmmaxdef, hSmaxeq, hmmindef, hSmineq]
    exact hPeq (Finset.mem_coe.mpr hSmaxmem) (Finset.mem_coe.mpr hSminmem)
  have hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax := fun S hS => Finset.le_sup' _ hS
  have hcardge : ∀ S ∈ Pp.parts, mmin ≤ #S := fun S hS => Finset.inf'_le _ hS
  have hsumparts : ∑ S ∈ Pp.parts, #S = Fintype.card V := by
    rw [Pp.sum_card_parts, Finset.card_univ]
  have hnhi : Fintype.card V ≤ kp * mmax := by
    calc Fintype.card V = ∑ S ∈ Pp.parts, #S := hsumparts.symm
      _ ≤ ∑ _S ∈ Pp.parts, mmax := Finset.sum_le_sum (fun S hS => hcardle S hS)
      _ = kp * mmax := by rw [Finset.sum_const, smul_eq_mul]
  have hnlo : kp * mmin ≤ Fintype.card V := by
    calc kp * mmin = ∑ _S ∈ Pp.parts, mmin := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ S ∈ Pp.parts, #S := Finset.sum_le_sum (fun S hS => hcardge S hS)
      _ = Fintype.card V := hsumparts
  have hkpKB : kp ≤ KB := by exact_mod_cast hPb
  have hKB0 : 0 < KB := lt_of_lt_of_le hkpN hkpKB
  -- the two consequences of the size threshold
  have hmminN : Mmin ≤ mmin := by
    have h1 : KB * (Mmin + 1) ≤ Fintype.card V := le_trans (by omega) hV
    have h2 : Fintype.card V ≤ KB * (mmin + 1) :=
      le_trans hnhi (Nat.mul_le_mul hkpKB (by omega))
    have h3 := Nat.le_of_mul_le_mul_left (le_trans h1 h2) hKB0
    omega
  have hnCn : Cn ≤ Fintype.card V := le_trans (by omega) hV
  -- ### the coarse cells, the block scale and the box size
  have hmminR0 : (Mmin : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hmminN
  have hceil : 2 / α + δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) + 800 / e ≤ (Mmin : ℝ) :=
    by rw [hMdef]; exact Nat.le_ceil _
  have hA : 2 / α ≤ (mmin : ℝ) := by
    have h1 : (0:ℝ) ≤ δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) := by positivity
    have h2 : (0:ℝ) ≤ 800 / e := by positivity
    linarith
  have hB : δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) ≤ (mmin : ℝ) := by
    have h1 : (0:ℝ) ≤ 2 / α := by positivity
    have h2 : (0:ℝ) ≤ 800 / e := by positivity
    linarith
  have hC : 800 / e ≤ (mmin : ℝ) := by
    have h1 : (0:ℝ) ≤ 2 / α := by positivity
    have h2 : (0:ℝ) ≤ δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) := by positivity
    linarith
  have hαmmin : (2 : ℝ) ≤ α * (mmin : ℝ) := by
    rw [div_le_iff₀ hα0] at hA
    linarith
  have hmmin0R : (0 : ℝ) < (mmin : ℝ) := by nlinarith only [hαmmin, hα0]
  have hmmin0 : 0 < mmin := by exact_mod_cast hmmin0R
  have hmminmaxR : (mmin : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hminmax
  have hmmax0R : (0 : ℝ) < (mmax : ℝ) := lt_of_lt_of_le hmmin0R hmminmaxR
  have hmmaxR : (mmax : ℝ) ≤ (mmin : ℝ) + 1 := by exact_mod_cast hmm1
  set l : ℕ := ⌈2 * α * (mmax : ℝ)⌉₊ with hldef
  have hlLB : 2 * α * (mmax : ℝ) ≤ (l : ℝ) := Nat.le_ceil _
  have hlUB : (l : ℝ) ≤ 2 * α * (mmax : ℝ) + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0:ℝ) < 2 * α * (mmax : ℝ)))
    rw [hldef]; linarith
  have hl0 : 0 < l := Nat.ceil_pos.mpr (by positivity)
  have hl0R : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
  have hlmin : 2 * α * (mmin : ℝ) ≤ (l : ℝ) := by
    nlinarith only [hlLB, hmminmaxR, hα0]
  have hl3 : (l : ℝ) ≤ 3 * α * (mmin : ℝ) := by
    nlinarith only [hlUB, hmmaxR, hαmmin, hα16, hα0]
  set Pn : ℕ := mmin / l with hPndef
  have hPnl : Pn * l ≤ mmin := Nat.div_mul_le_self _ _
  have hPnlt : mmin < (Pn + 1) * l := by
    have h1 : l * Pn + mmin % l = mmin := Nat.div_add_mod mmin l
    have h2 : mmin % l < l := Nat.mod_lt _ hl0
    calc mmin = l * Pn + mmin % l := h1.symm
      _ < l * Pn + l := by omega
      _ = (Pn + 1) * l := by ring
  have hPnlR : (Pn : ℝ) * (l : ℝ) ≤ (mmin : ℝ) := by exact_mod_cast hPnl
  have hPnltR : (mmin : ℝ) < ((Pn : ℝ) + 1) * (l : ℝ) := by exact_mod_cast hPnlt
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl0
  have hmmPn : (mmax : ℝ) ≤ ((Pn : ℝ) + 2) * (l : ℝ) := by
    have hexp : ((Pn : ℝ) + 2) * (l : ℝ) = ((Pn : ℝ) + 1) * (l : ℝ) + (l : ℝ) := by ring
    linarith
  have hPnge : 1 / (4 * α) ≤ (Pn : ℝ) := by
    have h1 : (mmin : ℝ) < ((Pn : ℝ) + 1) * (3 * α * (mmin : ℝ)) := by
      nlinarith only [hPnltR, hl3, (Nat.cast_nonneg Pn : (0:ℝ) ≤ (Pn : ℝ))]
    have h2 : 1 < ((Pn : ℝ) + 1) * (3 * α) := by
      by_contra hcon
      push Not at hcon
      nlinarith only [hcon, h1, hmmin0R]
    rw [div_le_iff₀ (by positivity)]
    linarith only [h2, hα16, hα0]
  have hPn0R : (0 : ℝ) < (Pn : ℝ) := lt_of_lt_of_le (by positivity) hPnge
  have hPn0 : 0 < Pn := by exact_mod_cast hPn0R
  set τ : ℝ := (l : ℝ) * (K : ℝ) / δ with hτdef
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le zero_lt_one hK1R
  have hτbig : T₀ + 192 / (ε * δ ^ 3) + 1 ≤ τ := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * α * (K:ℝ))] at hB
    rw [hτdef, le_div_iff₀ hδ0]
    nlinarith only [hB, hlmin, hKpos]
  have hτT₀ : T₀ ≤ τ := by
    have h1 : (0:ℝ) < 192 / (ε * δ ^ 3) := by positivity
    linarith
  have hτ192 : 192 / (ε * δ ^ 3) ≤ τ := by linarith
  have hτ1 : (1 : ℝ) ≤ τ := by
    have h1 : (0:ℝ) < 192 / (ε * δ ^ 3) := by positivity
    linarith
  have hKδ1 : (1 : ℝ) ≤ (K : ℝ) / δ := by
    rw [le_div_iff₀ hδ0]
    linarith only [hδ1, hK1R]
  have hs₀le : (s₀ : ℝ) ≤ 2 * ((K : ℝ) / δ) := by
    have h2 : (s₀ : ℝ) ≤ (K : ℝ) / δ + 1 := by
      rw [hs₀def]
      exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    linarith
  have hαθ' : 16 * (K : ℝ) * α ≤ θ * δ := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * (K:ℝ))] at hαθ
    linarith
  have hs₀θ : (s₀ : ℝ) ≤ θ * (Pn : ℝ) :=
    small_box_bound hθ0 hδ0 hα0 hK1R hαθ' hPnge hs₀le
  have hfitS : ∀ S ∈ Pp.parts, Pn * l ≤ #S := fun S hS => le_trans hPnl (hcardge S hS)
  exact ⟨⟨kp, mmax, mmin, l, Pn, τ, hkpdef, hkpN, hcardle, hnlo, hnCn,
    hmmin0, hmmax0R, hlLB, hl0, hl0R, hl3, hPnl, hPnltR, hmmPn, hPnge,
    hPn0R, hPn0, hτdef, hτ0, hτT₀, hτ192, hτ1, hK1R, hs₀θ, hfitS⟩⟩

private structure DenseTripleGeometry {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (δ : ℝ) (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts})) : Prop where
  hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
    δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)
  hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
    ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b
  hdOppδ : ∀ th ∈ Gd, ∀ a : ZMod 3, δ ≤ dOpp G Pp th a
  hdProdLB : ∀ th ∈ Gd, δ ^ 3 ≤ dProd G Pp th
  hdProdUB : ∀ th, dProd G Pp th ≤ 1
  hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th

private theorem dense_triple_geometry {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (δ : ℝ) (y : Finset {S : Finset V // S ∈ Pp.parts} → ℝ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (hGddef : Gd = clusterLPSupport y \ sparseTriples G Pp δ)
    (hGdcard : ∀ th ∈ Gd, #th = 3) (hδ0 : 0 < δ) :
    DenseTripleGeometry G Pp δ Gd := by
  classical
  have hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) := by
    intro th hth S hS T hT hST
    by_contra hcon
    push Not at hcon
    rw [hGddef] at hth
    exact (Finset.mem_sdiff.mp hth).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, hS, T, hT, hST, hcon⟩)
  have hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
      ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b :=
    fun th h3 a b hab h => hab (triPos_injective Pp h3 h)
  have hdOppδ : ∀ th ∈ Gd, ∀ a : ZMod 3, δ ≤ dOpp G Pp th a := by
    intro th hth a
    rw [dOpp]
    refine hGddense th hth _ (triPos_mem Pp (hGdcard th hth) _) _
      (triPos_mem Pp (hGdcard th hth) _) (hposne th (hGdcard th hth) _ _ ?_)
    intro hEq
    have h12 : (1 : ZMod 3) = 2 := add_left_cancel hEq
    exact absurd h12 (by decide +kernel)
  have hdProdLB : ∀ th ∈ Gd, δ ^ 3 ≤ dProd G Pp th := by
    intro th hth
    exact prod_ge_cube hδ0 (hdOppδ th hth 0) (hdOppδ th hth 1) (hdOppδ th hth 2)
  have hdProdUB : ∀ th, dProd G Pp th ≤ 1 := fun th =>
    prod_le_one (dOpp_nonneg G Pp th 0) (dOpp_nonneg G Pp th 1)
      (dOpp_nonneg G Pp th 2) (dOpp_le_one G Pp th 0)
      (dOpp_le_one G Pp th 1) (dOpp_le_one G Pp th 2)
  have hdProd0 : ∀ th ∈ Gd, 0 < dProd G Pp th := fun th hth =>
    lt_of_lt_of_le (by positivity) (hdProdLB th hth)
  exact ⟨hGddense, hposne, hdOppδ, hdProdLB, hdProdUB, hdProd0⟩

private theorem good_copy_properties {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (ε₁ δ α τ : ℝ) (mmax : ℕ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (clf : {p // p ∈ copySet Gd nc} → ZMod 3 → {S : Finset V // S ∈ Pp.parts})
    (bsc : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ)
    (bsf : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ)
    (hclfdef : clf = fun c a => triPos Pp c.1.1 a)
    (hbscdef : bsc = fun c a => bsf c.1.1 a)
    (hcGd : ∀ c : {p // p ∈ copySet Gd nc}, c.1.1 ∈ Gd)
    (hGdcard : ∀ th ∈ Gd, #th = 3)
    (hGdadj : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      (hostGraph G Pp (ε₁ / 8) (ε₁ / 4)).Adj S T)
    (hGddense : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      δ ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ))
    (hposne : ∀ (th : Finset {S : Finset V // S ∈ Pp.parts}), #th = 3 →
      ∀ a b : ZMod 3, a ≠ b → triPos Pp th a ≠ triPos Pp th b)
    (hcardle : ∀ S ∈ Pp.parts, #S ≤ mmax)
    (hα0 : 0 < α)
    (hbsrel : ∀ th ∈ Gd, ∀ a, α * (mmax : ℝ) ≤ (bsf th a : ℝ))
    (hbsLB : ∀ th a, τ * dOpp G Pp th a ≤ (bsf th a : ℝ))
    (hbsUB : ∀ th a, (bsf th a : ℝ) < τ * dOpp G Pp th a + 1) :
    (∀ c : {p // p ∈ copySet Gd nc}, GoodTriple G Pp (ε₁ / 8) δ
      (clf c 0 : Finset V) (clf c 1 : Finset V) (clf c 2 : Finset V)) ∧
    (∀ c : {p // p ∈ copySet Gd nc}, ∀ a,
      α * (#(clf c a : Finset V) : ℝ) ≤ (bsc c a : ℝ)) ∧
    (∀ c : {p // p ∈ copySet Gd nc}, ∀ a : ZMod 3,
      |(bsc c a : ℝ) - τ * (G.edgeDensity
        (clf c (a + 1) : Finset V) (clf c (a + 2) : Finset V) : ℝ)| ≤ 1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c
    have hth := hcGd c
    have h3 := hGdcard _ hth
    have hadj : ∀ a b : ZMod 3, a ≠ b →
        (hostGraph G Pp (ε₁ / 8) (ε₁ / 4)).Adj (clf c a) (clf c b) := by
      intro a b hab
      simp only [hclfdef]
      exact hGdadj _ hth _ (triPos_mem Pp h3 a) _ (triPos_mem Pp h3 b)
        (hposne _ h3 a b hab)
    have hdens : ∀ a b : ZMod 3, a ≠ b →
        δ ≤ (G.edgeDensity (clf c a : Finset V) (clf c b : Finset V) : ℝ) := by
      intro a b hab
      simp only [hclfdef]
      exact hGddense _ hth _ (triPos_mem Pp h3 a) _ (triPos_mem Pp h3 b)
        (hposne _ h3 a b hab)
    exact ⟨(clf c 0).2, (clf c 1).2, (clf c 2).2,
      (hadj 0 1 (by decide +kernel)).1, (hadj 0 2 (by decide +kernel)).1,
      (hadj 1 2 (by decide +kernel)).1,
      (hadj 0 1 (by decide +kernel)).2.1, hdens 0 1 (by decide +kernel),
      (hadj 0 2 (by decide +kernel)).2.1, hdens 0 2 (by decide +kernel),
      (hadj 1 2 (by decide +kernel)).2.1, hdens 1 2 (by decide +kernel)⟩
  · intro c a
    have h1 : (#(clf c a : Finset V) : ℝ) ≤ (mmax : ℝ) := by
      exact_mod_cast hcardle _ (clf c a).2
    have h2 : α * (#(clf c a : Finset V) : ℝ) ≤ α * (mmax : ℝ) :=
      mul_le_mul_of_nonneg_left h1 hα0.le
    simp only [hbscdef]
    exact le_trans h2 (hbsrel _ (hcGd c) a)
  · intro c a
    have hEq : (G.edgeDensity (clf c (a + 1) : Finset V)
        (clf c (a + 2) : Finset V) : ℝ) = dOpp G Pp c.1.1 a := by
      simp only [hclfdef, dOpp]
    simp only [hbscdef]
    rw [hEq, abs_le]
    exact ⟨by linarith only [hbsLB c.1.1 a], by linarith only [hbsUB c.1.1 a]⟩

private theorem bad_copy_mass_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Pp : Finpartition (univ : Finset V))
    [Nonempty {S : Finset V // S ∈ Pp.parts}]
    (δ τ : ℝ) (K l : ℕ)
    (Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}))
    (nc : Finset {S : Finset V // S ∈ Pp.parts} → ℕ)
    (szc : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ)
    (szf : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ)
    (hτsq : τ ^ 2 = (l : ℝ) ^ 2 * (K : ℝ) ^ 2 / δ ^ 2)
    (hszcdef : szc = fun c a => szf c.1.1 a)
    (hdnn : ∀ th a, (0 : ℝ) ≤ dOpp G Pp th a)
    (hszLB : ∀ th a, (K : ℝ) * dOpp G Pp th a / δ ≤ (szf th a : ℝ))
    (hδ0 : 0 < δ) (hKpos : (0 : ℝ) < (K : ℝ)) :
    ∀ c : {p // p ∈ copySet Gd nc}, τ ^ 2 * dProd G Pp c.1.1
      ≤ (l : ℝ) ^ 2 * ∑ a : ZMod 3,
        (szc c a : ℝ) * (szc c (a + 1) : ℝ) := by
  classical
  intro c
  have h1 : τ ^ 2 * dProd G Pp c.1.1
      ≤ (l : ℝ) ^ 2 * ((szc c 0 : ℝ) * (szc c 1 : ℝ)) := by
    rw [hτsq]
    simp only [dProd, hszcdef]
    exact bad_term_bound hδ0 hKpos.le (hdnn _ 0) (hdnn _ 1) (hdnn _ 2)
      (dOpp_le_one G Pp _ 2) (hszLB _ 0) (hszLB _ 1)
  have h2 : (szc c 0 : ℝ) * (szc c 1 : ℝ)
      ≤ ∑ a : ZMod 3, (szc c a : ℝ) * (szc c (a + 1) : ℝ) :=
    pair_product_le_cyclic_sum (szc c)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))

/-- **The coarse-cell reduction**: the small-box allocation residual implies the coupled
block-allocation residual. -/
theorem blockCoverResidualCoupled_of_boxAllocation (hbox : BoxAllocationResidual) :
    BlockCoverResidualCoupled := by
  classical
  intro ε δ ε₂ T₀ hε hδ0 hδ1 hδε hε₂0 hT₀0
  set e : ℝ := min 1 ε with hedef
  have he0 : 0 < e := lt_min one_pos hε
  have he1 : e ≤ 1 := min_le_left _ _
  have heε : e ≤ ε := min_le_right _ _
  set K : ℕ := ⌈640 / e⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKR : (640 : ℝ) / e ≤ (K : ℝ) := by
    have h := Nat.le_ceil (640 / e)
    have : ((⌈640 / e⌉₊ : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith only [h, this]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  -- the box bound is fixed *before* the smallness threshold `θ` is asked for
  set s₀ : ℕ := ⌈(K : ℝ) / δ⌉₊ with hs₀def
  obtain ⟨θ, hθ0, hθ1, hboxmain⟩ := hbox (e / 64) (by positivity) s₀
  set α : ℝ := min (1 / 16) (min (e / 3200) (min (θ * δ / (16 * K)) (δ * e / (32 * K)))) with hαdef
  have hα0 : 0 < α := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min ?_ ?_)) <;> positivity
  have hα16 : α ≤ 1 / 16 := min_le_left _ _
  have hαe : α ≤ e / 3200 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hαθ : α ≤ θ * δ / (16 * K) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hαδ : α ≤ δ * e / (32 * K) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨8 * α * min 1 ε₂, by positivity, ?_⟩
  intro ε₁ hε₁0 hε₁le hε₁1
  have hmin1 : min 1 ε₂ ≤ 1 := min_le_left _ _
  have hmin2 : min 1 ε₂ ≤ ε₂ := min_le_right _ _
  have hm10 : (0 : ℝ) < min 1 ε₂ := lt_min one_pos hε₂0
  have hε₁α : ε₁ / 8 ≤ α * min 1 ε₂ := by linarith only [hε₁le]
  refine ⟨α, ?_, by linarith, ?_, ?_⟩
  · have h : α * min 1 ε₂ ≤ α * 1 := mul_le_mul_of_nonneg_left hmin1 hα0.le
    rw [mul_one] at h
    linarith only [hε₁α, h]
  · rw [div_le_iff₀ hα0]
    have h : α * min 1 ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_left hmin2 hα0.le
    linarith only [hε₁α, h]
  -- ### the size threshold
  set KB : ℕ := SzemerediRegularity.bound (ε₁ / 8) ⌈4 / ε₁⌉₊ with hKBdef
  set Mmin : ℕ := ⌈2 / α + δ * (T₀ + 192 / (ε * δ ^ 3) + 1) / (2 * α * K) + 800 / e⌉₊ with hMdef
  set Cn : ℕ := ⌈16 / ε⌉₊ with hCndef
  refine ⟨KB * (Mmin + 1) + Cn + 10, ?_⟩
  intro V _ _ G _ Pp hV hPeq hPl hPb hPu
  obtain ⟨⟨kp, mmax, mmin, l, Pn, τ, hkpdef, hkpN, hcardle, hnlo, hnCn,
    hmmin0, hmmax0R, hlLB, hl0, hl0R, hl3, hPnl, hPnltR, hmmPn, hPnge,
    hPn0R, hPn0, hτdef, hτ0, hτT₀, hτ192, hτ1, hK1R, hs₀θ, hfitS⟩⟩ :=
    coarse_cluster_scales Pp T₀ ε δ e θ α ε₁ s₀ K KB Mmin Cn hV hPeq hPl
      (by simpa only [hKBdef] using hPb) hMdef hs₀def hε hε₁0 hδ0 hδ1 he0 hT₀0
      hK1 hα0 hα16 hαθ hθ0
  have hpne : Pp.parts.Nonempty := Finset.card_pos.mp (by simpa only [hkpdef] using hkpN)
  obtain ⟨Smin, hSminmem⟩ := hpne
  let : Nonempty {S : Finset V // S ∈ Pp.parts} := ⟨⟨Smin, hSminmem⟩⟩
  -- ### the LP point and the dense triples
  obtain ⟨y, hyLP, hysupp, hynu⟩ :=
    exists_sparse_clusterTripleLP_nu3star G Pp (ε₁ / 8) (ε₁ / 4) (η := 1) one_pos
  set Gd : Finset (Finset {S : Finset V // S ∈ Pp.parts}) :=
    clusterLPSupport y \ sparseTriples G Pp δ with hGddef
  have hyne : ∀ th ∈ Gd, y th ≠ 0 := by
    intro th hth
    have h := (Finset.mem_sdiff.mp hth).1
    rw [clusterLPSupport, Finset.mem_filter] at h
    exact h.2
  have hGdcard : ∀ th ∈ Gd, #th = 3 := fun th hth =>
    (SimpleGraph.mem_cliqueFinset_iff.mp (hyLP.2.1 th (hyne th hth))).card_eq
  have hGdpos : ∀ th ∈ Gd, 0 < y th := fun th hth =>
    lt_of_le_of_ne (hyLP.1 th) (Ne.symm (hyne th hth))
  obtain ⟨hGddense, hposne, hdOppδ, hdProdLB, hdProdUB, hdProd0⟩ :=
    dense_triple_geometry G Pp δ y Gd hGddef hGdcard hδ0
  have hGdadj : ∀ th ∈ Gd, ∀ S ∈ th, ∀ T ∈ th, S ≠ T →
      (hostGraph G Pp (ε₁ / 8) (ε₁ / 4)).Adj S T := fun th hth S hS T hT hST =>
    (SimpleGraph.mem_cliqueFinset_iff.mp (hyLP.2.1 th (hyne th hth))).1
      (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT) hST
  -- ### the prescribed sizes, the block sizes and the number of copies
  obtain ⟨szf, hszfdef⟩ : ∃ f : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ,
      f = fun th a => ⌈(K : ℝ) * dOpp G Pp th a / δ⌉₊ := ⟨_, rfl⟩
  obtain ⟨bsf, hbsfdef⟩ : ∃ f : Finset {S : Finset V // S ∈ Pp.parts} → ZMod 3 → ℕ,
      f = fun th a => ⌈τ * dOpp G Pp th a⌉₊ := ⟨_, rfl⟩
  obtain ⟨nc, hncdef⟩ : ∃ f : Finset {S : Finset V // S ∈ Pp.parts} → ℕ,
      f = fun th => ⌊(1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th)⌋₊ := ⟨_, rfl⟩
  have hdnn : ∀ th a, (0 : ℝ) ≤ dOpp G Pp th a := fun th a => dOpp_nonneg G Pp th a
  have hszLB : ∀ th a, (K : ℝ) * dOpp G Pp th a / δ ≤ (szf th a : ℝ) := by
    intro th a; rw [hszfdef]; exact Nat.le_ceil _
  have hszUB : ∀ th a, (szf th a : ℝ) < (K : ℝ) * dOpp G Pp th a / δ + 1 := by
    intro th a
    rw [hszfdef]
    exact Nat.ceil_lt_add_one (by have := hdnn th a; positivity)
  have hsz1 : ∀ th ∈ Gd, ∀ a, 1 ≤ szf th a := by
    intro th hth a
    rw [hszfdef]
    refine Nat.one_le_ceil_iff.mpr ?_
    exact div_pos (mul_pos hKpos (lt_of_lt_of_le hδ0 (hdOppδ th hth a))) hδ0
  have hszs₀ : ∀ th a, szf th a ≤ s₀ := by
    intro th a
    rw [hszfdef, hs₀def]
    refine Nat.ceil_le_ceil ?_
    rw [div_le_div_iff_of_pos_right hδ0]
    linarith only [mul_le_mul_of_nonneg_left (dOpp_le_one G Pp th a) hKpos.le]
  have hbsLB : ∀ th a, τ * dOpp G Pp th a ≤ (bsf th a : ℝ) := by
    intro th a; rw [hbsfdef]; exact Nat.le_ceil _
  have hbsUB : ∀ th a, (bsf th a : ℝ) < τ * dOpp G Pp th a + 1 := by
    intro th a
    rw [hbsfdef]
    exact Nat.ceil_lt_add_one (by have := hdnn th a; positivity)
  have hτd : ∀ th a, τ * dOpp G Pp th a = (l : ℝ) * ((K : ℝ) * dOpp G Pp th a / δ) := by
    intro th a
    rw [hτdef]
    field_simp
  have hbssz : ∀ th a, bsf th a ≤ szf th a * l := by
    intro th a
    rw [hbsfdef]
    refine Nat.ceil_le.mpr ?_
    push_cast
    rw [hτd th a]
    exact (mul_le_mul_of_nonneg_left (hszLB th a) hl0R.le).trans_eq (mul_comm _ _)
  have hτδ : τ * δ = (l : ℝ) * (K : ℝ) := by rw [hτdef]; field_simp
  have hbsrel : ∀ th ∈ Gd, ∀ a, α * (mmax : ℝ) ≤ (bsf th a : ℝ) := by
    intro th hth a
    have h1 : τ * δ ≤ τ * dOpp G Pp th a := mul_le_mul_of_nonneg_left (hdOppδ th hth a) hτ0.le
    have h2 := hbsLB th a
    exact bs_ge_alpha hlLB hK1R (by linarith [hτδ ▸ h1]) hmmax0R.le hα0.le
  -- ### the copies
  obtain ⟨clf, hclfdef⟩ :
      ∃ f : {p // p ∈ copySet Gd nc} → ZMod 3 → {S : Finset V // S ∈ Pp.parts},
      f = fun c a => triPos Pp c.1.1 a := ⟨_, rfl⟩
  obtain ⟨szc, hszcdef⟩ : ∃ f : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ,
      f = fun c a => szf c.1.1 a := ⟨_, rfl⟩
  obtain ⟨bsc, hbscdef⟩ : ∃ f : {p // p ∈ copySet Gd nc} → ZMod 3 → ℕ,
      f = fun c a => bsf c.1.1 a := ⟨_, rfl⟩
  have hcGd : ∀ c : {p // p ∈ copySet Gd nc}, c.1.1 ∈ Gd := fun c => (mem_copySet.mp c.2).1
  have hclinj : ∀ c, Function.Injective (clf c) := by
    intro c
    rw [hclfdef]
    exact triPos_injective Pp (hGdcard _ (hcGd c))
  have hszc1 : ∀ c a, 1 ≤ szc c a := by
    intro c a; rw [hszcdef]; exact hsz1 _ (hcGd c) a
  have hszcs₀ : ∀ c a, szc c a ≤ s₀ := by
    intro c a; rw [hszcdef]; exact hszs₀ _ a
  -- ### the three margins of the capacity
  have hKu : 1 / (K : ℝ) ≤ e / 640 := by
    have h1 : (640 : ℝ) ≤ (K : ℝ) * e := (div_le_iff₀ he0).mp hKR
    rw [div_le_div_iff₀ hKpos (by norm_num : (0:ℝ) < 640)]
    linarith
  have hPv : 2 / (Pn : ℝ) ≤ e / 400 := by
    have h1 : (1 : ℝ) ≤ (Pn : ℝ) * (4 * α) :=
      (div_le_iff₀ (by positivity : (0:ℝ) < 4 * α)).mp hPnge
    have h2 : α * (Pn : ℝ) ≤ e / 3200 * (Pn : ℝ) :=
      mul_le_mul_of_nonneg_right hαe hPn0R.le
    rw [div_le_div_iff₀ hPn0R (by norm_num : (0:ℝ) < 400)]
    linarith
  have hτsq : τ ^ 2 = (l : ℝ) ^ 2 * (K : ℝ) ^ 2 / δ ^ 2 := by
    rw [hτdef]; field_simp
  have hncUB : ∀ th ∈ Gd, (nc th : ℝ)
      ≤ (1 - e / 8) * y th * δ ^ 2 / ((l : ℝ) ^ 2 * (K : ℝ) ^ 2 * dProd G Pp th) := by
    intro th hth
    have hy0 : (0 : ℝ) ≤ y th := hyLP.1 th
    have hdp := hdProd0 th hth
    have h0 : (0 : ℝ) ≤ (1 - e / 8) * y th / (τ ^ 2 * dProd G Pp th) := by
      apply div_nonneg (mul_nonneg (by linarith) hy0)
      positivity
    rw [hncdef]
    refine le_trans (Nat.floor_le h0) (le_of_eq ?_)
    rw [hτsq]
    field_simp
  -- ### the demand of every ordered cluster pair
  have hdemand : ∀ S T : {S : Finset V // S ∈ Pp.parts}, S ≠ T →
      boxDemand clf szc S T ≤ (1 - e / 64) * (Pn : ℝ) ^ 2 := by
    simpa only [hclfdef, hszcdef] using
      (box_demand_bound G Pp ε₁ δ e K l Pn mmax y Gd szf nc he0 he1 hδ0
        hyLP hGdcard hGddense hposne hdProd0 hdOppδ hszUB hncUB hKpos
        hl0R hKu hPn0R hPv hmmax0R hmmPn hcardle)
  -- ### the placement
  obtain ⟨bad, I, hIcard, hIdisj, hIbad⟩ :=
    hboxmain Pn hPn0 hs₀θ {S : Finset V // S ∈ Pp.parts} {p // p ∈ copySet Gd nc}
      clf szc hclinj hszc1 hszcs₀ hdemand
  obtain ⟨Good, hGooddef⟩ : ∃ F : Finset {p // p ∈ copySet Gd nc},
      F = (univ : Finset {p // p ∈ copySet Gd nc}) \ bad := ⟨_, rfl⟩
  have hGoodmem : ∀ c ∈ Good, c ∉ bad := by
    intro c hc
    rw [hGooddef] at hc
    exact (Finset.mem_sdiff.mp hc).2
  have hbscsz : ∀ c a, bsc c a ≤ szc c a * l := by
    intro c a; simp only [hbscdef, hszcdef]; exact hbssz _ a
  obtain ⟨hgoodT, hrelG, hshapeG⟩ :=
    good_copy_properties G Pp ε₁ δ α τ mmax Gd nc clf bsc bsf hclfdef hbscdef
      hcGd hGdcard hGdadj hGddense hposne hcardle hα0 hbsrel hbsLB hbsUB
  obtain ⟨k, U, W, X, A, B, C, hkle, hgrid, hdisjF, hsumF⟩ :=
    exists_gridSubTriple_family_of_placement (ep := ε₁ / 8) (de := δ) (α := α) (τ := τ) (l := l)
      G Pp hl0 clf szc bsc I Good hIcard hfitS hbscsz
      (fun c hc c' hc' hne a b a' b' hab hab' h1 h2 =>
        hIdisj c (hGoodmem c hc) c' (hGoodmem c' hc') hne a b a' b' hab hab' h1 h2)
      (fun c _ => hgoodT c) (fun c _ => hrelG c) (fun c _ => hshapeG c)
  have hsumGood : ∑ i ∈ Finset.range k, τ ^ 2 * ((G.edgeDensity (U i) (W i) : ℝ)
        * (G.edgeDensity (U i) (X i) : ℝ) * (G.edgeDensity (W i) (X i) : ℝ))
      = ∑ c ∈ Good, τ ^ 2 * dProd G Pp c.1.1 := by
    rw [hsumF]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dProd_eq]
    simp only [hclfdef]
  have hbadterm :=
    bad_copy_mass_bound G Pp δ τ K l Gd nc szc szf hτsq hszcdef hdnn hszLB hδ0 hKpos
  refine ⟨τ, k, U, W, X, A, B, C, hτT₀, hgrid, hdisjF, ?_⟩
  exact coarse_cover_clause G Pp ε ε₁ δ e α τ K kp mmin l Pn Cn k y Gd nc bad Good szc U W X A B C
    hkpN hkpdef hmmin0 hnlo hyLP (by simpa only [hkpdef] using hysupp)
    hynu hδ0 hGddef hsumGood hτ0 hdProd0 hdProdUB
    hncdef hbadterm hIbad hPnl hGooddef hkle hdProdLB hτ1 hτ192 hε hτdef hl3
    hKpos hα0 hαδ he0 he1 heε hCndef hnCn hδε hgrid

/-- **AX1 from the small-box allocation residual.**  Composing the reduction of this file with
`Nibble.AX1.ax1_of_blockCoverCoupled`. -/
theorem ax1_of_boxAllocation (hbox : BoxAllocationResidual) : AX1Statement :=
  ax1_of_blockCoverCoupled (blockCoverResidualCoupled_of_boxAllocation hbox)




end Nibble.AX1
