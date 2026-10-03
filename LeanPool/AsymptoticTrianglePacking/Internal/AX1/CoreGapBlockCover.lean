/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the AX1 residual reduced to a **deterministic block-allocation** problem

This file performs the last analytic step of the deterministic (probability-free) route to AX1.

`Nibble.AX1.SubTripleDesignLocalResidual` (`Nibble.CoreGapGridLocalResidual`) asks, for every
triangle-rich regularity-reduced graph, for a whole *local sub-triple design*: uniformity,
densities, the six scale-equalisation windows, the pruning budget, the edge counts and the recovery
of `ν₃*`.  Here all of that is discharged, and what is left is a purely combinatorial statement
about **allocating blocks**:

`Nibble.AX1.BlockCoverResidual` — for every accuracy `ε`, density threshold `δ`, relative block size
`α`, scale floor `T₀` and regularity scale `ε₁`, every large enough regularity-reduced graph admits
a common block scale `τ ≥ T₀` and a finite family of block sub-triples
(`Nibble.AX1.IsGridSubTriple`: blocks of size `≈ τ·(opposite density)` and relative size at least
`α` inside the clusters of a good triple) whose **vertex-pair rectangles are pairwise disjoint**
(`Nibble.AX1.tripleRect`) and which carry the fractional optimum:
`ν₃*(reduced) ≤ (∑ᵢ dᵢ·areaᵢ)/3 + ε|V|²`.

There is no probability, no regularity argument and no counting lemma left in that statement: it is
the deterministic rectangle-packing problem of allocating, inside each cluster pair, the block
rectangles used by the cluster triples through that pair.

* `Nibble.AX1.subTripleDesignLocalResidual_of_blockCover` — **the reduction**;
* `Nibble.AX1.ax1_of_blockCover` — AX1 from the block-allocation residual.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlockShape
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridLineDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterCapacity
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapGridLocalResidual
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.TripleEdgesThree

/-! # CoreGapBlockCover -/

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
  have h4 : τ * dens ≤ τ := by nlinarith only [hτ, h2]
  have h6 : τ * δ ≤ τ := by linarith only [h3, h4]
  exact ⟨by linarith [habs.1], by linarith [habs.2]⟩

/-- The area and the support of a sub-triple, in terms of the scale. -/
private theorem area_bounds {τ δ a b c : ℝ} (hτ : 0 < τ) (_hδ : 0 < δ) (hτδ : 8 ≤ τ * δ)
    (ha : 3 / 4 * (τ * δ) ≤ a) (ha' : a ≤ 5 / 4 * τ)
    (hb : 3 / 4 * (τ * δ) ≤ b) (hb' : b ≤ 5 / 4 * τ)
    (hc : 3 / 4 * (τ * δ) ≤ c) (hc' : c ≤ 5 / 4 * τ) :
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b + a * c + b * c ≤ 5 * τ ^ 2 ∧
      0 ≤ a * b + a * c + b * c ∧ a + b + c ≤ 4 * τ ∧ 0 ≤ a + b + c := by
  have ha0 : 0 ≤ a := by linarith only [hτδ, ha]
  have hb0 : 0 ≤ b := by linarith only [hτδ, hb]
  have hc0 : 0 ≤ c := by linarith only [hτδ, hc]
  refine ⟨ha0, hb0, hc0, by nlinarith, by positivity, by linarith, by linarith⟩

/-- The `Elo` of a sub-triple is at least a quarter of `τ²δ³`. -/
private theorem elo_lower {τ δ ε₁ a b c dAB dAC dBC : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hε₁0 : 0 < ε₁) (hε₁b : ε₁ ≤ δ / 2) (hx : δ - ε₁ / 8 ≤ dAB)
    (hAC0 : 0 ≤ dAC) (hBC0 : 0 ≤ dBC)
    (ha : 3 / 4 * (τ * δ) ≤ a) (hb : 3 / 4 * (τ * δ) ≤ b) (hc0 : 0 ≤ c) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) :
    1 / 4 * (τ ^ 2 * δ ^ 3) ≤ dAB * a * b + dAC * a * c + dBC * b * c := by
  have hAB : 15 / 16 * δ ≤ dAB := by linarith only [hε₁b, hx]
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
    linarith only [h1, h4]
  have h2 : 0 ≤ dAC * a * c := by positivity
  have h3 : 0 ≤ dBC * b * c := by positivity
  linarith only [hmain, h2, h3]

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
  have hd : (0:ℝ) ≤ μ - μ₂ := by linarith only [hμ₂, hμ₂'₀]
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
  linarith only [h]

/-- Multiplying a nonnegative quantity by `δ ≤ 1` only decreases it. -/
private theorem mul_delta_le {B δ : ℝ} (hB : 0 ≤ B) (hδ1 : δ ≤ 1) (_hδ0 : 0 ≤ δ) : B * δ ≤ B := by
  nlinarith only [hB, hδ1]

/-- The block scale is large: `2 ≤ τ·μ₂δ³` and `μ₂ ≤ 1` give `2 ≤ τδ³`. -/
private theorem tau_delta3_lower {τ δ μ₂ : ℝ} (hτ : 0 < τ) (hδ3 : 0 < δ ^ 3) (hμ₂1 : μ₂ ≤ 1)
    (h : 2 ≤ τ * (μ₂ * δ ^ 3)) : 2 ≤ τ * δ ^ 3 := by
  nlinarith [mul_le_mul_of_nonneg_left hμ₂1 (le_of_lt (mul_pos hτ hδ3))]

/-- The block scale is large: `2 ≤ τδ³` and `δ ≤ 1/2` give `8 ≤ τδ`. -/
private theorem tau_delta_lower {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (h : 2 ≤ τ * δ ^ 3) : 8 ≤ τ * δ := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by nlinarith only [hδ, hδhalf]
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
    have hεS : 4 * ε₂ * S ≤ 4 * (δ ^ 3 / 160) * (5 * τ ^ 2) := by nlinarith only [hε₂0, hε₂d, hS]
    nlinarith [hεS]
  have h2 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2)
      ≤ η * (Elo - 4 * ε₂ * S) * t := by
    have hle1 : η * (1 / 8 * (τ ^ 2 * δ ^ 3)) ≤ η * (Elo - 4 * ε₂ * S) :=
      mul_le_mul_of_nonneg_left hbr hη.le
    have hnn : (0:ℝ) ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) := by positivity
    have hnn2 : (0:ℝ) ≤ μ₂ * τ * δ ^ 3 / 2 := by positivity
    exact mul_le_mul hle1 ht hnn2 (le_trans hnn hle1)
  have h3 : 160 * ε₂ * τ ^ 3 ≤ η * (1 / 8 * (τ ^ 2 * δ ^ 3)) * (μ₂ * τ * δ ^ 3 / 2) := by
    have hkey : 160 * ε₂ ≤ η * μ₂ * δ ^ 6 / 16 := by linarith only [hε₂c]
    linarith only [mul_le_mul_of_nonneg_right hkey hτ3.le]
  linarith only [h1, h2, h3]

/-- **The deterministic block-allocation residual.**  At every choice of accuracy `ε`, density
threshold `δ`, relative block size `α ≤ δ/2`, scale floor `T₀` and regularity scale `ε₁`, all large
regularity-reduced graphs carry a family of block sub-triples with pairwise disjoint vertex-pair
rectangles whose edges recover the fractional triangle-packing optimum up to `ε|V|²`.

The bound `α ≤ δ/2` on the relative size of the blocks is not cosmetic, it is forced: the sizes
`#A ≈ τ·d(W,X)`, `#B ≈ τ·d(U,X)`, `#C ≈ τ·d(U,W)` of `Nibble.AX1.IsGridSubTriple` are proportional
to the three cluster densities, and `A ⊆ U` etc., so all three of `#A/#U`, `#B/#W`, `#C/#X` can be
at least `α` only when the three densities are within a factor `1/α` of each other.  Demanding a
*constant* `α` would therefore make the statement false: a graph all of whose good cluster triples
have density profile `(1, 1/10, 1/10)` — three groups of clusters, dense across the first two,
sparse to the third — admits no sub-triple at all at `α = 1/4`, while its reduced graph has `ν₃*`
of order `|V|²`.  Since the densities are at least `δ`, `α = δ/2` is the natural scale, and that is
the value at which `Nibble.AX1.subTripleDesignLocalResidual_of_blockCover` uses the residual. -/
def BlockCoverResidual : Prop :=
  ∀ ε δ α T₀ ε₁ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 → 0 < α → α ≤ δ / 2 → 0 < T₀ → 0 < ε₁ → ε₁ ≤ 1 →
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

private theorem choose_mu2 (μ : ℝ) (hμ : 0 < μ) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ μ ∧ 2 * m ≤ μ := by
  refine ⟨min μ 1 / 2, ?_, ?_, ?_, ?_⟩
  · have : 0 < min μ 1 := lt_min hμ one_pos; linarith only [this]
  · have : min μ 1 ≤ 1 := min_le_right _ _; linarith only [this]
  · have : min μ 1 ≤ μ := min_le_left _ _; linarith only [hμ, this]
  · have : min μ 1 ≤ μ := min_le_left _ _; linarith only [this]

/-- **The reduction: the deterministic block-allocation residual gives the local design residual.**

All the analytic content of the design is discharged here: uniformity of the blocks
(`Nibble.AX1.isUniform_subblock`), their densities
(`Nibble.AX1.edgeDensity_sub_lt_of_isUniform`), the transfer to the reduced graph
(`Nibble.AX1.isUniform_regularityReduced`), the six scale windows (`Nibble.AX1.scale_window`), the
edge counts (`Nibble.AX1.three_edgeDensity_mul_le_tripleGraph_edges`), the pruning budget and the
`ν₃*` bookkeeping (`Nibble.AX1.sum_area_le_of_rect_disjoint`). -/
theorem subTripleDesignLocalResidual_of_blockCover (h : BlockCoverResidual) :
    SubTripleDesignLocalResidual := by
  classical
  intro ε hε μ hμ η hη d₀ hd₀
  -- ### the parameters of the construction
  obtain ⟨μ₂, hμ₂0, hμ₂1, hμ₂μ, hμ₂half⟩ := choose_mu2 μ hμ
  obtain ⟨δ, hδ0, hδhalf, hδε⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ d ≤ ε := by
    refine ⟨min 1 ε / 2, ?_, ?_, ?_⟩
    · have : 0 < min 1 ε := lt_min one_pos hε; linarith only [this]
    · have : min 1 ε ≤ 1 := min_le_left _ _; linarith only [this]
    · have : min 1 ε ≤ ε := min_le_right _ _; linarith only [hε, this]
  have hδ1 : δ ≤ 1 := by linarith only [hδhalf]
  have hδ3 : (0:ℝ) < δ ^ 3 := by positivity
  obtain ⟨T₀, hT₀0, hT₀1, hT₀2⟩ :
      ∃ T : ℝ, 0 < T ∧ 2 / (μ₂ * δ ^ 3) ≤ T ∧ d₀ / δ ^ 3 ≤ T := by
    refine ⟨2 / (μ₂ * δ ^ 3) + d₀ / δ ^ 3, by positivity, ?_, ?_⟩
    · have : (0:ℝ) ≤ d₀ / δ ^ 3 := by positivity
      linarith only [this]
    · have : (0:ℝ) < 2 / (μ₂ * δ ^ 3) := by positivity
      linarith only [this]
  obtain ⟨ε₁, hε₁0, hε₁1, hε₁a, hε₁c, hε₁d, hε₁e⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ μ₂ * δ ^ 3 / 24 * δ ∧
        e ≤ η * μ₂ * δ ^ 6 / 640 * δ ∧ e ≤ δ ^ 3 / 40 * δ ∧ e ≤ ε / 2 * δ := by
    refine ⟨min 1 (min (μ₂ * δ ^ 3 / 24 * δ) (min (η * μ₂ * δ ^ 6 / 640 * δ)
      (min (δ ^ 3 / 40 * δ) (ε / 2 * δ)))), ?_, min_le_left _ _, ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min (by positivity)
        (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- the derived windows for `ε₁` and for the block scale `ε₂ = (ε₁/8)/(δ/2) = ε₁/(4δ)`
  have hδ3le' : δ ^ 3 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 1 ≤ 3)
  have hε₁δ : ε₁ ≤ δ ^ 3 / 40 * δ := hε₁d
  have hε₁δ' : ε₁ ≤ δ ^ 3 / 40 :=
    le_trans hε₁δ (mul_delta_le (by positivity) hδ1 hδ0.le)
  have hε₁b : ε₁ ≤ δ / 2 := by linarith only [hε₁0, hδ3le', hε₁δ']
  have hε₁ε : ε₁ ≤ ε :=
    le_trans hε₁e (mul_delta_le (by positivity) hδ1 hδ0.le) |>.trans (by linarith)
  have hε₁4δ : ε₁ ≤ 4 * δ := by linarith only [hε₁0, hε₁b]
  refine ⟨ε₁, hε₁0, hε₁ε, hε₁1, ?_⟩
  -- ### the residual supplies the blocks
  obtain ⟨n₀, hres⟩ := h (ε / 2) δ (δ / 2) T₀ ε₁ (by linarith) hδ0 hδ1 (by positivity)
    (le_refl _) hT₀0 hε₁0 hε₁1
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu _hrich
  obtain ⟨τ, k, U, W, X, A, B, C, hτT, hgrid, hdisj, hcov⟩ := hres V G P hV hP hPl hPb hPu
  -- ### the scale `τ` is large
  have hτpos : 0 < τ := lt_of_lt_of_le hT₀0 hτT
  have hτ2 : 2 / (μ₂ * δ ^ 3) ≤ τ := le_trans hT₀1 hτT
  have hτ2' : 2 ≤ τ * (μ₂ * δ ^ 3) := by
    rw [div_le_iff₀ (by positivity)] at hτ2; linarith only [hτ2]
  have hτδ3 : 2 ≤ τ * δ ^ 3 := tau_delta3_lower hτpos hδ3 hμ₂1 hτ2'
  have hτδ8 : 8 ≤ τ * δ := tau_delta_lower hτpos hδ0 hδhalf hτδ3
  have hτd₀ : d₀ ≤ τ * δ ^ 3 := by
    have hle : d₀ / δ ^ 3 ≤ τ := le_trans hT₀2 hτT
    rw [div_le_iff₀ hδ3] at hle; linarith only [hle]
  -- ### the local clauses of the design
  have hαε : ε₁ / 8 ≤ δ / 2 := by linarith only [hε₁4δ]
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hquarter : ε₁ / 8 / (δ / 2 : ℝ) = ε₁ / (4 * δ) := by field_simp; ring
  -- the derived windows for the block uniformity scale `ε₂ = ε₁/(4δ)`
  have hε₂0 : (0:ℝ) < ε₁ / (4 * δ) := by positivity
  have hε₂1 : ε₁ / (4 * δ) ≤ 1 := by
    have := eps2_bound hδ0 hε₁4δ; linarith only [this]
  have hε₂A : ε₁ / (4 * δ) ≤ μ₂ * δ ^ 3 / 96 := by
    have := eps2_bound hδ0 hε₁a; linarith only [this]
  have hε₂C : ε₁ / (4 * δ) ≤ η * μ₂ * δ ^ 6 / 2560 := by
    have := eps2_bound hδ0 hε₁c; linarith only [this]
  have hε₂D : ε₁ / (4 * δ) ≤ δ ^ 3 / 160 := by
    have := eps2_bound hδ0 hε₁d; linarith only [this]
  have hε₂E : ε₁ / (4 * δ) ≤ ε / 8 := by
    have := eps2_bound hδ0 hε₁e; linarith only [this]
  have hδ3le : δ ^ 3 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 1 ≤ 3)
  have hμδpos : (0:ℝ) ≤ μ₂ * δ ^ 3 := by positivity
  have hErr : ε₁ / 8 + 2 * (ε₁ / 8 / (δ / 2 : ℝ)) ≤ μ₂ * δ ^ 3 / 12 := by
    rw [hquarter]
    have h1 : ε₁ / 8 ≤ μ₂ * δ ^ 3 / 96 := by
      have h0 : μ₂ * δ ^ 3 / 24 * δ ≤ μ₂ * δ ^ 3 / 24 :=
        mul_delta_le (by positivity) hδ1 hδ0.le
      linarith
    linarith
  have hdense : 2 * (ε₁ / 8 / (δ / 2 : ℝ)) + ε₁ / 8 ≤ δ := by
    rw [hquarter]
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
  refine ⟨ε₁ / 8 / (δ / 2), μ₂, (μ - μ₂) * τ * δ ^ 3 / 2, k, A, B, C,
    fun i => τ * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
      * (G.edgeDensity (W i) (X i) : ℝ)),
    fun i => ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
      * (#(A i) : ℝ) * (#(B i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
      * (#(A i) : ℝ) * (#(C i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
      * (#(B i) : ℝ) * (#(C i) : ℝ),
    hshape, by rw [hquarter]; positivity, by rw [hquarter]; linarith,
    ?_, hη.le, hμ₂μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    simp only [designBad, designSupport, hquarter]
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
          - (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 * ((#(A i) : ℝ) * (#(B i) : ℝ)
              + (#(A i) : ℝ) * (#(C i) : ℝ) + (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
              * (#(A i) : ℝ) * (#(B i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
              * (#(A i) : ℝ) * (#(C i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
              * (#(B i) : ℝ) * (#(C i) : ℝ)
            - 4 * (ε₁ / (4 * δ)) * ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
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
    have hcoef : (0:ℝ) ≤ (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hSsum hcoef
    have hV2 : (0:ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
    have hK : (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 ≤ ε := by linarith
    have h3 : (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 * ((Fintype.card V : ℝ) ^ 2 / 2)
        ≤ ε / 2 * (Fintype.card V : ℝ) ^ 2 := cover_tail hK hV2
    simp only [designBad, hquarter]
    linarith only [hcov, hsum, h2, h3]

/-- **AX1 from the deterministic block-allocation residual.** -/
theorem ax1_of_blockCover (h : BlockCoverResidual) : AX1Statement :=
  ax1_of_subTripleDesignLocal (subTripleDesignLocalResidual_of_blockCover h)


/-! ### The residual at a **fine** relative block size

`Nibble.AX1.BlockCoverResidual` above is stated at every relative block size `α ≤ δ / 2`, but the
reduction only ever uses it at the *one* value `α = δ / 2` with a density threshold `δ` that the
reduction itself chooses, and which is free to be small compared with the accuracy `ε`.  Recording
that coupling is not a cosmetic change: at `α` comparable with `δ` and `δ` comparable with `1` the
statement is **false** — the blocks are then forced to occupy a constant fraction of their cluster,
so only boundedly many rectangles fit into a cluster pair, and the resulting quantisation error is a
fixed positive multiple of `|V| ^ 2`.  This is proved in `Nibble.CoreGapBlockCoverRefute`
(`Nibble.AX1.not_blockCoverResidual`), with the explicit witness `δ = 1`, `α = 1/2`, `ε₁ = 1`,
`ε = 1/1000` and the complete graph split into five equal clusters.

`Nibble.AX1.BlockCoverResidualFine` is the same statement carrying the two side conditions the
reduction actually supplies, `δ ≤ ε` and `α ≤ ε ^ 2`; it is implied by `BlockCoverResidual`
(`Nibble.AX1.blockCoverResidualFine_of_blockCover`) and it still yields AX1
(`Nibble.AX1.ax1_of_blockCoverFine`).  Both conditions are exactly what a construction needs:
`δ ≤ ε` lets the cluster triples of density below the threshold be discarded at a cost of at most
`ε|V| ^ 2`, and `α ≤ ε ^ 2` makes the blocks small compared with their clusters, which is what
turns the rounding of a fractional cluster packing to the quantised block sizes into an `O(ε|V|^2)`
error. -/

/-- **The deterministic block-allocation residual at a fine relative block size.**  Same as
`Nibble.AX1.BlockCoverResidual`, but only for the parameter range the reduction uses: the density
threshold `δ` is below the accuracy `ε`, and the relative block size `α` is below `ε ^ 2`. -/
def BlockCoverResidualFine : Prop :=
  ∀ ε δ α T₀ ε₁ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 → δ ≤ ε → 0 < α → α ≤ δ / 2 → α ≤ ε ^ 2 →
    0 < T₀ → 0 < ε₁ → ε₁ ≤ 1 →
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

/-- The fine residual is a **special case** of the full one: it is the same statement under two
extra hypotheses. -/
theorem blockCoverResidualFine_of_blockCover (h : BlockCoverResidual) : BlockCoverResidualFine :=
  fun ε δ α T₀ ε₁ hε hδ hδ1 _ hα hαδ _ hT₀ hε₁ hε₁1 => h ε δ α T₀ ε₁ hε hδ hδ1 hα hαδ hT₀ hε₁ hε₁1

/-- **The reduction at the fine parameter range.**  Identical to
`Nibble.AX1.subTripleDesignLocalResidual_of_blockCover` except that the density threshold is chosen
as `δ = (min 1 ε) ^ 2 / 8`, which makes the two extra hypotheses of
`Nibble.AX1.BlockCoverResidualFine` available at the point of use. -/
theorem subTripleDesignLocalResidual_of_blockCoverFine (h : BlockCoverResidualFine) :
    SubTripleDesignLocalResidual := by
  classical
  intro ε hε μ hμ η hη d₀ hd₀
  -- ### the parameters of the construction
  obtain ⟨μ₂, hμ₂0, hμ₂1, hμ₂μ, hμ₂half⟩ := choose_mu2 μ hμ
  obtain ⟨δ, hδ0, hδhalf, hδε, hδsq⟩ :
      ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧ d ≤ ε / 2 ∧ d / 2 ≤ (ε / 2) ^ 2 := by
    have h0 : 0 < min 1 ε := lt_min one_pos hε
    have h1 : min 1 ε ≤ 1 := min_le_left _ _
    have h2 : min 1 ε ≤ ε := min_le_right _ _
    refine ⟨min 1 ε * min 1 ε / 8, by positivity, by nlinarith, by nlinarith, by nlinarith⟩
  have hδ1 : δ ≤ 1 := by linarith only [hδhalf]
  have hδ3 : (0:ℝ) < δ ^ 3 := by positivity
  obtain ⟨T₀, hT₀0, hT₀1, hT₀2⟩ :
      ∃ T : ℝ, 0 < T ∧ 2 / (μ₂ * δ ^ 3) ≤ T ∧ d₀ / δ ^ 3 ≤ T := by
    refine ⟨2 / (μ₂ * δ ^ 3) + d₀ / δ ^ 3, by positivity, ?_, ?_⟩
    · have : (0:ℝ) ≤ d₀ / δ ^ 3 := by positivity
      linarith only [this]
    · have : (0:ℝ) < 2 / (μ₂ * δ ^ 3) := by positivity
      linarith only [this]
  obtain ⟨ε₁, hε₁0, hε₁1, hε₁a, hε₁c, hε₁d, hε₁e⟩ :
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ μ₂ * δ ^ 3 / 24 * δ ∧
        e ≤ η * μ₂ * δ ^ 6 / 640 * δ ∧ e ≤ δ ^ 3 / 40 * δ ∧ e ≤ ε / 2 * δ := by
    refine ⟨min 1 (min (μ₂ * δ ^ 3 / 24 * δ) (min (η * μ₂ * δ ^ 6 / 640 * δ)
      (min (δ ^ 3 / 40 * δ) (ε / 2 * δ)))), ?_, min_le_left _ _, ?_, ?_, ?_, ?_⟩
    · exact lt_min one_pos (lt_min (by positivity)
        (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- the derived windows for `ε₁` and for the block scale `ε₂ = (ε₁/8)/(δ/2) = ε₁/(4δ)`
  have hδ3le' : δ ^ 3 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 1 ≤ 3)
  have hε₁δ : ε₁ ≤ δ ^ 3 / 40 * δ := hε₁d
  have hε₁δ' : ε₁ ≤ δ ^ 3 / 40 :=
    le_trans hε₁δ (mul_delta_le (by positivity) hδ1 hδ0.le)
  have hε₁b : ε₁ ≤ δ / 2 := by linarith only [hε₁0, hδ3le', hε₁δ']
  have hε₁ε : ε₁ ≤ ε :=
    le_trans hε₁e (mul_delta_le (by positivity) hδ1 hδ0.le) |>.trans (by linarith)
  have hε₁4δ : ε₁ ≤ 4 * δ := by linarith only [hε₁0, hε₁b]
  refine ⟨ε₁, hε₁0, hε₁ε, hε₁1, ?_⟩
  -- ### the residual supplies the blocks
  obtain ⟨n₀, hres⟩ := h (ε / 2) δ (δ / 2) T₀ ε₁ (by linarith) hδ0 hδ1 hδε (by positivity)
    (le_refl _) hδsq hT₀0 hε₁0 hε₁1
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ P hV hP hPl hPb hPu _hrich
  obtain ⟨τ, k, U, W, X, A, B, C, hτT, hgrid, hdisj, hcov⟩ := hres V G P hV hP hPl hPb hPu
  -- ### the scale `τ` is large
  have hτpos : 0 < τ := lt_of_lt_of_le hT₀0 hτT
  have hτ2 : 2 / (μ₂ * δ ^ 3) ≤ τ := le_trans hT₀1 hτT
  have hτ2' : 2 ≤ τ * (μ₂ * δ ^ 3) := by
    rw [div_le_iff₀ (by positivity)] at hτ2; linarith only [hτ2]
  have hτδ3 : 2 ≤ τ * δ ^ 3 := tau_delta3_lower hτpos hδ3 hμ₂1 hτ2'
  have hτδ8 : 8 ≤ τ * δ := tau_delta_lower hτpos hδ0 hδhalf hτδ3
  have hτd₀ : d₀ ≤ τ * δ ^ 3 := by
    have hle : d₀ / δ ^ 3 ≤ τ := le_trans hT₀2 hτT
    rw [div_le_iff₀ hδ3] at hle; linarith only [hle]
  -- ### the local clauses of the design
  have hαε : ε₁ / 8 ≤ δ / 2 := by linarith only [hε₁4δ]
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hquarter : ε₁ / 8 / (δ / 2 : ℝ) = ε₁ / (4 * δ) := by field_simp; ring
  -- the derived windows for the block uniformity scale `ε₂ = ε₁/(4δ)`
  have hε₂0 : (0:ℝ) < ε₁ / (4 * δ) := by positivity
  have hε₂1 : ε₁ / (4 * δ) ≤ 1 := by
    have := eps2_bound hδ0 hε₁4δ; linarith only [this]
  have hε₂A : ε₁ / (4 * δ) ≤ μ₂ * δ ^ 3 / 96 := by
    have := eps2_bound hδ0 hε₁a; linarith only [this]
  have hε₂C : ε₁ / (4 * δ) ≤ η * μ₂ * δ ^ 6 / 2560 := by
    have := eps2_bound hδ0 hε₁c; linarith only [this]
  have hε₂D : ε₁ / (4 * δ) ≤ δ ^ 3 / 160 := by
    have := eps2_bound hδ0 hε₁d; linarith only [this]
  have hε₂E : ε₁ / (4 * δ) ≤ ε / 8 := by
    have := eps2_bound hδ0 hε₁e; linarith only [this]
  have hδ3le : δ ^ 3 ≤ δ := by
    simpa using pow_le_pow_of_le_one hδ0.le hδ1 (by norm_num : 1 ≤ 3)
  have hμδpos : (0:ℝ) ≤ μ₂ * δ ^ 3 := by positivity
  have hErr : ε₁ / 8 + 2 * (ε₁ / 8 / (δ / 2 : ℝ)) ≤ μ₂ * δ ^ 3 / 12 := by
    rw [hquarter]
    have h1 : ε₁ / 8 ≤ μ₂ * δ ^ 3 / 96 := by
      have h0 : μ₂ * δ ^ 3 / 24 * δ ≤ μ₂ * δ ^ 3 / 24 :=
        mul_delta_le (by positivity) hδ1 hδ0.le
      linarith
    linarith
  have hdense : 2 * (ε₁ / 8 / (δ / 2 : ℝ)) + ε₁ / 8 ≤ δ := by
    rw [hquarter]
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
  refine ⟨ε₁ / 8 / (δ / 2), μ₂, (μ - μ₂) * τ * δ ^ 3 / 2, k, A, B, C,
    fun i => τ * ((G.edgeDensity (U i) (W i) : ℝ) * (G.edgeDensity (U i) (X i) : ℝ)
      * (G.edgeDensity (W i) (X i) : ℝ)),
    fun i => ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
      * (#(A i) : ℝ) * (#(B i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
      * (#(A i) : ℝ) * (#(C i) : ℝ)
      + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
      * (#(B i) : ℝ) * (#(C i) : ℝ),
    hshape, by rw [hquarter]; positivity, by rw [hquarter]; linarith,
    ?_, hη.le, hμ₂μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    simp only [designBad, designSupport, hquarter]
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
          - (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 * ((#(A i) : ℝ) * (#(B i) : ℝ)
              + (#(A i) : ℝ) * (#(C i) : ℝ) + (#(B i) : ℝ) * (#(C i) : ℝ))
        ≤ (((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (B i) : ℝ)
              * (#(A i) : ℝ) * (#(B i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (A i) (C i) : ℝ)
              * (#(A i) : ℝ) * (#(C i) : ℝ)
            + ((G.regularityReduced P (ε₁ / 8) (ε₁ / 4)).edgeDensity (B i) (C i) : ℝ)
              * (#(B i) : ℝ) * (#(C i) : ℝ)
            - 4 * (ε₁ / (4 * δ)) * ((#(A i) : ℝ) * (#(B i) : ℝ) + (#(A i) : ℝ) * (#(C i) : ℝ)
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
    have hcoef : (0:ℝ) ≤ (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hSsum hcoef
    have hV2 : (0:ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by positivity
    have hK : (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 ≤ ε := by linarith
    have h3 : (ε₁ / 8 + 4 * (ε₁ / (4 * δ))) / 3 * ((Fintype.card V : ℝ) ^ 2 / 2)
        ≤ ε / 2 * (Fintype.card V : ℝ) ^ 2 := cover_tail hK hV2
    simp only [designBad, hquarter]
    linarith only [hcov, hsum, h2, h3]

/-- **AX1 from the deterministic block-allocation residual at fine relative block size.** -/
theorem ax1_of_blockCoverFine (h : BlockCoverResidualFine) : AX1Statement :=
  ax1_of_subTripleDesignLocal (subTripleDesignLocalResidual_of_blockCoverFine h)

/-! ### What is left in `Nibble.AX1.BlockCoverResidual`, and what it is not

The residual is now purely a statement about **placing rectangles**, and the accounting inside it is
exact.  Writing `p = d(U,W)`, `q = d(U,X)`, `r = d(W,X)` for the three cluster densities of the
triple carrying the `i`-th sub-triple, the scale-equalisation sizes `#A ≈ τr`, `#B ≈ τq`,
`#C ≈ τp` of `Nibble.AX1.IsGridSubTriple` make the three terms of the covering clause *equal*:

`p·#A·#B = q·#A·#C = r·#B·#C = τ²·p·q·r`,

so each sub-triple contributes exactly `τ²pqr` to `(∑ᵢ covᵢ)/3`, while the rectangles it occupies in
the three cluster pairs have areas `τ²qr`, `τ²pr`, `τ²pq`.  Summing the disjointness constraint over
the cluster triples through one pair `(U, W)` therefore reads

`∑_X (number of sub-triples on (U,W,X)) · τ²·d(U,X)·d(W,X) ≤ #U·#W`,

i.e. exactly the capacity constraint `∑_X z_{UWX} ≤ e(U,W)` of the **fractional triangle packing LP
of the weighted cluster graph**, with `z_{UWX}` the value contributed by that cluster triple.  And
on the LP side a fractional triangle packing of the reduced graph respects exactly those capacities:
`Nibble.AX1.sum_fracPacking_cluster_pair_le` (`Nibble.CoreGapClusterCapacity`) bounds the weight it
puts on the triangles using a `U–W` edge by `e(U, W)`.  (That the aggregated weights are an optimal
LP solution, and hence that the LP optimum bounds `ν₃*`, is the informal reading of that constraint;
only the per-pair constraint itself is formalised.) In other words,
`Nibble.AX1.BlockCoverResidual` is precisely the statement that an (almost) optimal
solution of that cluster LP can be **realised** by an edge-disjoint family of block rectangles: the
fractional-to-integral step in a blow-up.

Three things about the shape of that residual are settled, and none of them can be traded away.

* The `ν₃*` clause cannot be replaced by "cover all but `ε|V|²` of the triangle-carrying edges".
  That stronger covering criterion is available (`Nibble.AX1.hasNearRegularFamily_of_cover`) but is
  in general unsatisfiable: as explained at the end of `Nibble.CoreGapRegularCover`, a cluster
  triple with densities `1, 1/10, 1/10` can have only about `3/10` of its edges covered by
  near-regular classes, while every one of its edges lies in a triangle.
* The *global* exceptional-edge rate of `Nibble.AX1.SubTripleDesignResidual` cannot be met by any
  construction whose sub-triples live inside clusters — see the head of
  `Nibble.CoreGapGridLocalResidual` — which is why the route here goes through
  `Nibble.AX1.SubTripleDesignLocalResidual`.
* Allocating to each cluster triple a private *piece of each cluster* (so that rectangles of
  different triples are disjoint because their blocks already are) is far too lossy.  With `m`
  clusters of size `N` and all densities `1`, the LP value is `≈ m²N²/6`, whereas maximising
  `∑_T g_T²τ²` under the per-cluster constraints `∑_{T ∋ U} g_T τ ≤ N` — there are `≈ m²/2` triples
  through each cluster — gives only `≈ 2N²/(3m)`, short by a factor `≈ m³`.  Blocks must therefore
  be **reused** by many cluster triples, disjointness coming from the *other* coordinate of the
  rectangle.

That is what the line design of `Nibble.GridLineDesign` is for.  Indexing the blocks of each cluster
by `ZMod q`, the line `L(a,b) = {(j, j+a, j+b) : j}` is a family of `q` sub-triples whose three
projections are the diagonal `a` of `(U,W)`, the diagonal `b` of `(U,X)` and the diagonal `b-a` of
`(W,X)` (`Nibble.AX1.lineTriple_UW_unique`, `Nibble.AX1.lineTriple_UX_unique`,
`Nibble.AX1.lineTriple_WX_unique`); the `q` diagonals of a pair partition its `q²` block pairs
(`Nibble.AX1.diagIndex_bijective`, the partial form of `Nibble.AX1.gridUW_bijective`); and two
cluster triples through the same pair that receive disjoint sets of diagonals never collide
(`Nibble.AX1.lineTriple_pair_disjoint`), which is where `Nibble.AX1.balanced_bucket_le` allocates.

The **simultaneous consistency** of those allocations — the diagonals handed to a cluster triple in
its three pairs have to be the three projections of one family of lines, at the same time for every
pair of the cluster graph — is now settled, in closed form and deterministically, by
`Nibble.GridTripleDesign` and `Nibble.GridTripleDesignRect`.  Indexing both the clusters and the
blocks of each cluster by a prime field `ZMod q`, give the cluster triple of vertex sum `s` the
quadratic shift `triShift s v = v ^ 2 - v * s`, so that its `j`-th sub-triple occupies the block
`j + triShift s v` of the cluster `v`.  In the pair `{a, b}` this is the diagonal of offset
`(b - a) * (a + b - s)` (`Nibble.AX1.triShift_diff`), an injective function of `s` for `a ≠ b`; two
distinct cluster triples through a common pair have different sums, so they never share a block
pair, in all three of their pairs at once (`Nibble.AX1.triPairSet_disjoint`,
`Nibble.AX1.triCells_inter_subsingleton`), and the resulting vertex-pair rectangles are pairwise
disjoint (`Nibble.AX1.tripleRect_disjoint_of_design`).  A cluster pair is filled by exactly
`q · (number of cluster triples through it)` of its `q ^ 2` block pairs
(`Nibble.AX1.card_triPairSet_biUnion`), so the allocation is feasible whenever `q` is at least the
number of clusters.

What is still missing is therefore not the consistency of the allocation but the **quantitative
realisation of the LP optimum** under the two side conditions the residual carries.

* *Sizes.* `Nibble.AX1.IsGridSubTriple` prescribes the three part sizes `#A ≈ τ·r`, `#B ≈ τ·q`,
  `#C ≈ τ·p` from a single global scale `τ`, so the rectangles of the family are not free: their
  side lengths are dictated by the cluster densities, and the fractional solution has to be rounded
  to those quantised sizes.
* *Relative size.* The same predicate asks each part to be at least an `α` fraction of its cluster
  (this is what makes the parts inherit `ε₁/(8α)`-uniformity), while `α` has to stay large compared
  with `ε₁`, and the number of clusters is at least `4/ε₁`.  Hence at most `1/α²` rectangles fit in
  a cluster pair, far fewer than the `≈ m` cluster triples through it: the family must be *sparse*,
  using few and large sub-triples rather than a fine grid.  In that regime the design above is used
  with a small number `q` of blocks per cluster, and choosing which cluster triples carry the LP
  mass becomes an **approximate weighted triangle decomposition of the cluster graph** — for the
  all-densities-`1` reduced graph it is exactly an approximate Steiner triple system on the
  clusters, each cluster pair being used once at full size.

That decomposition step, and the rounding of the LP solution to the quantised sizes, is what
`Nibble.AX1.BlockCoverResidual` still asserts. -/

end Nibble.AX1
