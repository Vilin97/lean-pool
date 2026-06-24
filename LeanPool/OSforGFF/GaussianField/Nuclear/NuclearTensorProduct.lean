/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.GaussianField.Nuclear.DyninMityagin
import LeanPool.OSforGFF.GaussianField.Nuclear.NuclearSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Nuclear Tensor Product via Köthe Sequence Spaces

Defines `RapidDecaySeq`, the Köthe sequence space s(ℕ) of rapidly decreasing
sequences, and proves it is a nuclear Fréchet space. Then defines
`NuclearTensorProduct E₁ E₂` as `RapidDecaySeq` (via Cantor pairing),
providing a `DyninMityaginSpace` instance for tensor products of nuclear spaces.

## Main definitions

- `RapidDecaySeq` — rapidly decreasing sequences on ℕ
- `rapidDecaySeminorm k` — the k-th seminorm: `∑ₘ |aₘ| (1+m)^k`
- `NuclearTensorProduct E₁ E₂` — tensor product of nuclear spaces

## Mathematical background

Every nuclear Fréchet space with a Schauder basis is isomorphic to a
Köthe sequence space s(ℕ) with rapidly decreasing weights (Dynin-Mityagin).
The tensor product s(ℕ) ⊗̂ s(ℕ) ≅ s(ℕ²) ≅ s(ℕ) via Cantor pairing.

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
-/

noncomputable section

namespace GaussianField

/-! ## Rapidly Decreasing Sequences -/

/-- A rapidly decreasing sequence: `val : ℕ → ℝ` such that
`∑ₘ |val m| · (1 + m)^k` converges for all `k : ℕ`.
-/
structure RapidDecaySeq where
  /-- The underlying sequence. -/
  val : ℕ → ℝ
  rapid_decay : ∀ k : ℕ, Summable (fun m => |val m| * (1 + (m : ℝ)) ^ k)

namespace RapidDecaySeq

@[ext]
theorem ext {a b : RapidDecaySeq} (h : ∀ m, a.val m = b.val m) : a = b := by
  cases a; cases b; congr 1; exact funext h

/-! ### Weight function lemmas -/

theorem weight_pos (m : ℕ) (k : ℕ) : (0 : ℝ) < (1 + (m : ℝ)) ^ k := by positivity

theorem weight_nonneg (m : ℕ) (k : ℕ) : (0 : ℝ) ≤ (1 + (m : ℝ)) ^ k :=
  le_of_lt (weight_pos m k)

/-! ### Algebraic structure -/

instance instZero : Zero RapidDecaySeq where
  zero := ⟨0, fun k => by simp [summable_zero]⟩

@[simp] theorem zero_val (m : ℕ) : (0 : RapidDecaySeq).val m = 0 := rfl

instance instAdd : Add RapidDecaySeq where
  add a b := ⟨a.val + b.val, fun k => by
    apply Summable.of_nonneg_of_le
    · intro m; exact mul_nonneg (abs_nonneg _) (weight_nonneg m k)
    · intro m; simp only [Pi.add_apply]
      calc |a.val m + b.val m| * (1 + ↑m) ^ k
          ≤ (|a.val m| + |b.val m|) * (1 + ↑m) ^ k :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg m k)
        _ = |a.val m| * (1 + ↑m) ^ k + |b.val m| * (1 + ↑m) ^ k := add_mul _ _ _
    · exact (a.rapid_decay k).add (b.rapid_decay k)⟩

@[simp] theorem add_val (a b : RapidDecaySeq) (m : ℕ) :
    (a + b).val m = a.val m + b.val m := rfl

instance instNeg : Neg RapidDecaySeq where
  neg a := ⟨fun m => -a.val m, fun k => by
    simp only [abs_neg]; exact a.rapid_decay k⟩

@[simp] theorem neg_val (a : RapidDecaySeq) (m : ℕ) : (-a).val m = -a.val m := rfl

instance instSMul : SMul ℝ RapidDecaySeq where
  smul r a := ⟨fun m => r * a.val m, fun k => by
    have h : (fun m => |r * a.val m| * (1 + (m : ℝ)) ^ k) =
             fun m => |r| * (|a.val m| * (1 + (m : ℝ)) ^ k) := by
      ext m; rw [abs_mul, mul_assoc]
    rw [h]
    exact (a.rapid_decay k).const_smul |r|⟩

@[simp] theorem smul_val (r : ℝ) (a : RapidDecaySeq) (m : ℕ) :
    (r • a).val m = r * a.val m := rfl

instance instAddCommGroup : AddCommGroup RapidDecaySeq where
  add_assoc a b c := ext fun m => add_assoc _ _ _
  zero_add a := ext fun m => zero_add _
  add_zero a := ext fun m => add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext fun m => neg_add_cancel _
  add_comm a b := ext fun m => add_comm _ _

instance instModule : Module ℝ RapidDecaySeq where
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/-! ### Seminorm family -/

/-- The k-th seminorm on rapid decay sequences: `∑ₘ |aₘ| · (1+m)^k`. -/
def rapidDecaySeminorm (k : ℕ) : Seminorm ℝ RapidDecaySeq where
  toFun a := ∑' m, |a.val m| * (1 + (m : ℝ)) ^ k
  map_zero' := by simp [zero_val, tsum_zero]
  add_le' a b := by
    calc ∑' m, |(a + b).val m| * (1 + ↑m) ^ k
        ≤ ∑' m, (|a.val m| * (1 + ↑m) ^ k + |b.val m| * (1 + ↑m) ^ k) := by
          exact ((a + b).rapid_decay k).tsum_le_tsum
            (fun m => by simp only [add_val]
                         calc |a.val m + b.val m| * (1 + ↑m) ^ k
                             ≤ (|a.val m| + |b.val m|) * (1 + ↑m) ^ k :=
                               mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg m k)
                           _ = _ := add_mul _ _ _)
            ((a.rapid_decay k).add (b.rapid_decay k))
      _ = ∑' m, |a.val m| * (1 + ↑m) ^ k + ∑' m, |b.val m| * (1 + ↑m) ^ k :=
          (a.rapid_decay k).tsum_add (b.rapid_decay k)
  neg' a := by
    congr 1; ext m; rw [neg_val, abs_neg]
  smul' r a := by
    change ∑' m, |r * a.val m| * (1 + ↑m) ^ k = ‖r‖ * ∑' m, |a.val m| * (1 + ↑m) ^ k
    simp_rw [abs_mul, Real.norm_eq_abs, mul_assoc]
    exact tsum_mul_left

/-! ### Topology from seminorms -/

instance instTopologicalSpace : TopologicalSpace RapidDecaySeq :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℝ) rapidDecaySeminorm).topology

theorem rapidDecay_withSeminorms :
    WithSeminorms (rapidDecaySeminorm : ℕ → Seminorm ℝ RapidDecaySeq) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup RapidDecaySeq :=
  rapidDecay_withSeminorms.topologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ RapidDecaySeq :=
  rapidDecay_withSeminorms.continuousSMul

/-- `RapidDecaySeq` is complete with respect to the right uniform structure
induced by its topological add group structure.

**Proof outline.** Given a Cauchy sequence `u : ℕ → RapidDecaySeq`:
1. Each coordinate `m ↦ (u n).val m` is Cauchy in ℝ (bounded by seminorm 0),
   hence converges to some `a m`.
2. The sequence `u` is eventually bounded in each seminorm (Cauchy property),
   so `a` inherits rapid decay: `∑ |a m| (1+m)^k ≤ B`.
3. Convergence `u n → a` in the seminorm topology follows from passing
   the Cauchy bounds through limits of partial sums.
-/
-- Helper: coordinate projection is bounded by seminorm 0
private theorem coord_le_seminorm0 (a : RapidDecaySeq) (m : ℕ) :
    |a.val m| ≤ rapidDecaySeminorm 0 a := by
  change |a.val m| ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0
  calc |a.val m|
      = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
    _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
        (a.rapid_decay 0).le_tsum m
          (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))

-- Helper: finite sum of weighted coords ≤ seminorm
private theorem finset_sum_le_seminorm (a : RapidDecaySeq) (k : ℕ) (s : Finset ℕ) :
    ∑ m ∈ s, |a.val m| * (1 + (m : ℝ)) ^ k ≤ rapidDecaySeminorm k a :=
  (a.rapid_decay k).sum_le_tsum s (fun m _ => mul_nonneg (abs_nonneg _) (weight_nonneg m k))

-- Helper: Cauchy condition for seminorms. From CauchySeq in the seminorm topology,
-- extract: for each k and ε > 0, ∃ N, ∀ n m ≥ N, seminorm k (u n - u m) < ε.
private theorem cauchySeq_seminorm_bound
    (u : ℕ → RapidDecaySeq)
    (hu : @CauchySeq RapidDecaySeq ℕ
      (IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq) _ u)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n m, N ≤ n → N ≤ m → rapidDecaySeminorm k (u n - u m) < ε := by
  letI : UniformSpace RapidDecaySeq := IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq
  -- The Cauchy condition says differences u n - u m are eventually in any nhds 0 set.
  -- We use the additive Cauchy characterization via entourages.
  -- The set {(x,y) | seminorm k (x - y) < ε} is an entourage because
  -- the uniformity = comap (fun p => p.2 - p.1) (nhds 0) for the right uniform structure,
  -- and {x | seminorm k x < ε} is a neighborhood of 0.
  have h_ent : {p : RapidDecaySeq × RapidDecaySeq | rapidDecaySeminorm k (p.1 - p.2) < ε} ∈
      uniformity RapidDecaySeq := by
    -- Rewrite using the right uniform structure definition
    show {p : RapidDecaySeq × RapidDecaySeq | rapidDecaySeminorm k (p.1 - p.2) < ε} ∈
      uniformity RapidDecaySeq
    rw [show uniformity RapidDecaySeq = Filter.comap (fun p : RapidDecaySeq × RapidDecaySeq =>
        p.2 - p.1) (nhds 0) from rfl]
    apply Filter.mem_comap.mpr
    refine ⟨{x | rapidDecaySeminorm k x < ε}, ?_, ?_⟩
    · -- {x | seminorm k x < ε} ∈ nhds 0
      exact (rapidDecay_withSeminorms.continuous_seminorm k).continuousAt.preimage_mem_nhds
        (by rw [show rapidDecaySeminorm k 0 = 0 from map_zero _]; exact Iio_mem_nhds hε)
    · intro ⟨a, b⟩ (hx : rapidDecaySeminorm k (b - a) < ε)
      change rapidDecaySeminorm k (a - b) < ε
      rwa [show a - b = -(b - a) from (neg_sub b a).symm, map_neg_eq_map]
  exact hu.mem_entourage h_ent

instance instCompleteSpace :
    @CompleteSpace RapidDecaySeq (IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq) := by
  letI : UniformSpace RapidDecaySeq := IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq
  haveI : IsUniformAddGroup RapidDecaySeq := isUniformAddGroup_of_addCommGroup
  haveI : (nhds (0 : RapidDecaySeq)).IsCountablyGenerated := by
    rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf rapidDecaySeminorm).1
      rapidDecay_withSeminorms]
    exact Filter.iInf.isCountablyGenerated _
  haveI : (uniformity RapidDecaySeq).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  -- Step 1: Extract Cauchy condition for seminorms
  have hcauchy : ∀ k ε, 0 < ε → ∃ N, ∀ n m, N ≤ n → N ≤ m →
      rapidDecaySeminorm k (u n - u m) < ε :=
    fun k ε hε => cauchySeq_seminorm_bound u hu k ε hε
  -- Step 2: Each coordinate sequence is Cauchy in ℝ, hence convergent
  have coord_cauchy : ∀ m, CauchySeq (fun n => (u n).val m) := by
    intro m
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy 0 ε hε
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]
      calc |((u n).val m - (u N).val m)|
          = |(u n - u N).val m| := by
            change _ = |((u n) + (-(u N))).val m|; simp [add_val, neg_val, sub_eq_add_neg]
        _ ≤ rapidDecaySeminorm 0 (u n - u N) := coord_le_seminorm0 _ m
        _ < ε := hN n N hn le_rfl⟩
  -- Get the pointwise limit
  choose a ha using fun m => cauchySeq_tendsto_of_complete (coord_cauchy m)
  -- Step 3: Show `a` has rapid decay
  -- From Cauchy: for each k, ∃ bound B such that all seminorm k (u n) ≤ B
  have seminorm_bound : ∀ k, ∃ B, ∀ n, rapidDecaySeminorm k (u n) ≤ B := by
    intro k
    obtain ⟨N, hN⟩ := hcauchy k 1 one_pos
    -- For n ≥ N, seminorm k (u n) ≤ seminorm k (u N) + 1 by triangle inequality
    -- For n < N, we can take the max
    have h_large : ∀ n, N ≤ n → rapidDecaySeminorm k (u n) ≤
        rapidDecaySeminorm k (u N) + 1 := by
      intro n hn
      calc rapidDecaySeminorm k (u n)
          = rapidDecaySeminorm k ((u n - u N) + u N) := by rw [sub_add_cancel]
        _ ≤ rapidDecaySeminorm k (u n - u N) + rapidDecaySeminorm k (u N) :=
            map_add_le_add _ _ _
        _ ≤ 1 + rapidDecaySeminorm k (u N) := by
            linarith [hN n N hn le_rfl]
        _ = rapidDecaySeminorm k (u N) + 1 := by ring
    -- Take the max of all values
    let B := (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
        (fun n => rapidDecaySeminorm k (u n)) ⊔ (rapidDecaySeminorm k (u N) + 1)
    refine ⟨B, fun n => ?_⟩
    by_cases hn : N ≤ n
    · exact le_sup_of_le_right (h_large n hn)
    · push Not at hn
      apply le_sup_of_le_left
      exact Finset.le_sup' (fun i => rapidDecaySeminorm k (u i))
        (Finset.mem_range.mpr (by omega))
  -- Now show a has rapid decay: for each k, ∑ |a m| * (1+m)^k converges
  -- Key: for any finite s, ∑_{m∈s} |a m| * (1+m)^k ≤ B
  -- because ∑_{m∈s} |a m| * (1+m)^k = lim_n ∑_{m∈s} |(u n).val m| * (1+m)^k ≤ B
  have a_rapid : ∀ k, Summable (fun m => |a m| * (1 + (m : ℝ)) ^ k) := by
    intro k
    obtain ⟨B, hB⟩ := seminorm_bound k
    apply summable_of_sum_le (fun m => mul_nonneg (abs_nonneg _) (weight_nonneg m k))
    · intro s
      -- ∑_{m∈s} |a m| * w m = lim_n ∑_{m∈s} |(u n).val m| * w m
      -- For each finite m, (u n).val m → a m, so |(u n).val m| → |a m|
      -- Hence the finite sum converges
      have h_sum_lim : Filter.Tendsto
          (fun n => ∑ m ∈ s, |(u n).val m| * (1 + (m : ℝ)) ^ k)
          Filter.atTop (nhds (∑ m ∈ s, |a m| * (1 + (m : ℝ)) ^ k)) := by
        apply tendsto_finsetSum
        intro m _
        exact (Filter.Tendsto.abs (ha m)).mul tendsto_const_nhds
      -- Each partial sum ≤ seminorm k (u n) ≤ B
      have h_sum_le : ∀ n, ∑ m ∈ s, |(u n).val m| * (1 + (m : ℝ)) ^ k ≤ B := by
        intro n
        exact le_trans (finset_sum_le_seminorm (u n) k s) (hB n)
      exact le_of_tendsto h_sum_lim (Filter.Eventually.of_forall h_sum_le)
  -- Construct the limit element
  let L : RapidDecaySeq := ⟨a, a_rapid⟩
  -- Step 4: Show u n → L in the seminorm topology
  refine ⟨L, ?_⟩
  rw [rapidDecay_withSeminorms.tendsto_nhds_atTop u L]
  intro k ε hε
  obtain ⟨N, hN⟩ := hcauchy k (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  -- Need: rapidDecaySeminorm k (u n - L) < ε
  -- i.e., ∑' m, |(u n).val m - a m| * (1+m)^k < ε
  -- For any finite s:
  -- ∑_{m∈s} |(u n).val m - a m| * w m
  --   = lim_j ∑_{m∈s} |(u n).val m - (u j).val m| * w m   (since (u j).val m → a m)
  --   ≤ lim_j rapidDecaySeminorm k (u n - u j)             (finite sum ≤ seminorm)
  --   But for j ≥ N, rapidDecaySeminorm k (u n - u j) < ε/2
  --   So ∑_{m∈s} |(u n).val m - a m| * w m ≤ ε/2
  -- By tsum_le_of_sum_le (taking sup over all s), ∑' m ≤ ε/2 < ε
  change rapidDecaySeminorm k (u n - L) < ε
  -- Rewrite the seminorm as a tsum of |(u n).val m - a m| * weight
  have h_eq : rapidDecaySeminorm k (u n - L) =
      ∑' m, |(u n).val m - a m| * (1 + (m : ℝ)) ^ k := by
    change ∑' m, |(u n - L).val m| * (1 + (m : ℝ)) ^ k = _
    simp only [sub_eq_add_neg, add_val, neg_val, L]
  rw [h_eq]
  -- Show the tsum ≤ ε/2
  suffices h : ∑' m, |(u n).val m - a m| * (1 + (m : ℝ)) ^ k ≤ ε / 2 by linarith
  apply Real.tsum_le_of_sum_le (fun m => mul_nonneg (abs_nonneg _) (weight_nonneg m k))
  intro s
  -- For each finite s, the partial sum ≤ ε/2
  -- ∑_{m∈s} |(u n).val m - a m| * w m = lim_j ∑_{m∈s} |(u n).val m - (u j).val m| * w m
  have h_lim : Filter.Tendsto
      (fun j => ∑ m ∈ s, |(u n).val m - (u j).val m| * (1 + (m : ℝ)) ^ k)
      Filter.atTop (nhds (∑ m ∈ s, |(u n).val m - a m| * (1 + (m : ℝ)) ^ k)) := by
    apply tendsto_finsetSum
    intro m _
    exact ((tendsto_const_nhds.sub (ha m)).abs).mul tendsto_const_nhds
  apply le_of_tendsto h_lim
  rw [Filter.eventually_atTop]
  refine ⟨N, fun j hj => ?_⟩
  calc ∑ m ∈ s, |(u n).val m - (u j).val m| * (1 + (m : ℝ)) ^ k
      = ∑ m ∈ s, |(u n - u j).val m| * (1 + (m : ℝ)) ^ k := by
        simp only [sub_eq_add_neg, add_val, neg_val]
    _ ≤ rapidDecaySeminorm k (u n - u j) := finset_sum_le_seminorm (u n - u j) k s
    _ ≤ ε / 2 := le_of_lt (hN n j hn hj)

/-! ### Standard basis and coefficients -/

/-- The m-th standard basis vector: 1 at position m, 0 elsewhere. -/
def basisVec (m : ℕ) : RapidDecaySeq where
  val n := if n = m then 1 else 0
  rapid_decay k := by
    apply summable_of_ne_finset_zero (s := {m})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]

@[simp] theorem basisVec_val_self (m : ℕ) : (basisVec m).val m = 1 := by
  simp [basisVec]

@[simp] theorem basisVec_val_ne {m n : ℕ} (h : n ≠ m) : (basisVec m).val n = 0 := by
  simp [basisVec, h]

/-- Seminorm of a basis vector is exactly `(1 + m)^k`. -/
theorem rapidDecaySeminorm_basisVec (k m : ℕ) :
    rapidDecaySeminorm k (basisVec m) = (1 + (m : ℝ)) ^ k := by
  change ∑' n, |(basisVec m).val n| * (1 + (n : ℝ)) ^ k = (1 + (m : ℝ)) ^ k
  rw [tsum_eq_single m]
  · simp [basisVec]
  · intro n hn; simp [basisVec, hn]

/-- The m-th coefficient linear map: extracts coordinate m. -/
def coeffLM (m : ℕ) : RapidDecaySeq →ₗ[ℝ] ℝ where
  toFun a := a.val m
  map_add' a b := rfl
  map_smul' r a := by simp [smul_eq_mul]

/-- The m-th coefficient as a continuous linear map.

Continuity follows from `|a.val m| ≤ rapidDecaySeminorm 0 a`:
the coordinate projection is bounded by the 0-th seminorm.
-/
def coeffCLM (m : ℕ) : RapidDecaySeq →L[ℝ] ℝ where
  toLinearMap := coeffLM m
  cont := by
    apply WithSeminorms.continuous_of_isBounded rapidDecay_withSeminorms (norm_withSeminorms ℝ ℝ)
    intro _
    refine ⟨{0}, 1, ?_⟩
    intro a
    simp only [Seminorm.comp_apply, Finset.sup_singleton, one_smul,
      coe_normSeminorm, coeffLM, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
    change |a.val m| ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0
    calc |a.val m|
        = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
      _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
          (a.rapid_decay 0).le_tsum m
            (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))

/-! ### DyninMityaginSpace instance -/

/-- The partial sums `∑_{m∈s} a.val(m) • basisVec(m)` converge to `a`.

For each seminorm `k` and `ε > 0`, the error `∑_{n ∉ s} |aₙ| · (1+n)^k` is the tail
of the convergent series `a.rapid_decay k`, hence eventually less than `ε`.
-/
private theorem sum_smul_basisVec_val (a : RapidDecaySeq) (s : Finset ℕ) (n : ℕ) :
    (∑ m ∈ s, a.val m • basisVec m).val n = if n ∈ s then a.val n else 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert m _ hm ih =>
    rw [Finset.sum_insert hm, add_val, ih]
    simp only [smul_val, basisVec, mul_ite, mul_one, mul_zero, Finset.mem_insert]
    by_cases h : n = m
    · subst h; simp [show n ∉ _ from hm]
    · simp [h]

theorem hasSum_basisVec (a : RapidDecaySeq) :
    HasSum (fun m => a.val m • basisVec m) a := by
  rw [HasSum, (rapidDecay_withSeminorms.tendsto_nhds _ a)]
  intro k ε hε
  simp only [SummationFilter.unconditional_filter]
  -- g n = |a.val n| * (1+n)^k is summable with nonneg terms
  set g : ℕ → ℝ := fun n => |a.val n| * (1 + (n : ℝ)) ^ k with hg_def
  have hg_nn : ∀ n, 0 ≤ g n := fun n => mul_nonneg (abs_nonneg _) (weight_nonneg n k)
  have hg_sum : Summable g := a.rapid_decay k
  -- Partial sums of g converge to tsum g; extract eventual bound
  have hgHS := hg_sum.hasSum
  rw [HasSum, SummationFilter.unconditional_filter] at hgHS
  have h_ev := (tendsto_order.mp hgHS).1 _ (sub_lt_self (∑' n, g n) hε)
  rw [Filter.eventually_atTop] at h_ev ⊢
  obtain ⟨s₀, hs₀⟩ := h_ev
  exact ⟨s₀, fun s hss => by
    have h_partial := hs₀ s hss
    -- Error terms: |error.val n| * (1+n)^k = if n ∈ s then 0 else g n
    have h_err_terms : ∀ n,
        |((∑ m ∈ s, a.val m • basisVec m) - a).val n| * (1 + ↑n) ^ k =
        if n ∈ s then 0 else g n := by
      intro n
      simp only [sub_eq_add_neg, add_val, neg_val, sum_smul_basisVec_val]
      split <;> simp [g, abs_neg]
    -- Show seminorm < ε
    change (rapidDecaySeminorm k) ((∑ m ∈ s, a.val m • basisVec m) - a) < ε
    change ∑' n, |((∑ m ∈ s, a.val m • basisVec m) - a).val n| * (1 + ↑n) ^ k < ε
    simp_rw [h_err_terms]
    -- ∑' n, (if n ∈ s then 0 else g n) = ∑' n, g n - ∑ n ∈ s, g n < ε
    have h_compl_summable : Summable (fun n => if (n ∈ s) then (0 : ℝ) else g n) :=
      Summable.of_nonneg_of_le
        (fun n => by split <;> simp [hg_nn])
        (fun n => by split <;> simp [hg_nn])
        hg_sum
    have h_fin_summable : Summable (fun n => if (n ∈ s) then g n else (0 : ℝ)) :=
      summable_of_ne_finset_zero (s := s) (fun n hn => if_neg hn)
    have h_split : ∑' n, g n =
        ∑' n, (if (n ∈ s) then g n else (0 : ℝ)) +
        ∑' n, (if (n ∈ s) then (0 : ℝ) else g n) := by
      rw [← h_fin_summable.tsum_add h_compl_summable]
      congr 1; ext n; split <;> simp
    have h_fin_eq : ∑' n, (if (n ∈ s) then g n else (0 : ℝ)) = ∑ n ∈ s, g n := by
      rw [tsum_eq_sum (fun n hn => if_neg hn)]
      exact Finset.sum_congr rfl (fun n hn => if_pos hn)
    linarith⟩

theorem rapidDecay_expansion (φ : RapidDecaySeq →L[ℝ] ℝ) (a : RapidDecaySeq) :
    φ a = ∑' m, (a.val m) * φ (basisVec m) := by
  have h : HasSum (fun m => φ (a.val m • basisVec m)) (φ a) :=
    (hasSum_basisVec a).mapL φ
  have h' : HasSum (fun m => a.val m * φ (basisVec m)) (φ a) := by
    convert h using 1; ext m; simp [map_smul, smul_eq_mul]
  exact h'.tsum_eq.symm

/-- `RapidDecaySeq` is T1: if `a ≠ 0`, the 0-th seminorm `∑ |a_m| > 0`. -/
instance rapidDecayT1Space : T1Space RapidDecaySeq :=
  rapidDecay_withSeminorms.T1_of_separating fun a ha => by
    refine ⟨0, ?_⟩
    -- rapidDecaySeminorm 0 a = ∑' m, |a.val m| * 1 = ∑' m, |a.val m|
    intro h
    apply ha
    -- h : rapidDecaySeminorm 0 a = 0, i.e., ∑' m, |a.val m| * 1 = 0
    have h' : ∑' m, |a.val m| = 0 := by
      have := h; simp only [rapidDecaySeminorm, pow_zero, mul_one] at this; exact this
    -- Each |a.val m| = 0 since nonneg terms sum to 0
    have hcomp : ∀ m, a.val m = 0 := by
      intro m
      have hle : |a.val m| ≤ 0 := by
        calc |a.val m| = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
          _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
              (a.rapid_decay 0).le_tsum m
                (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))
          _ = 0 := by simp [pow_zero, mul_one, h']
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    ext m; exact hcomp m

instance rapidDecayDyninMityaginSpace : DyninMityaginSpace RapidDecaySeq where
  ι := ℕ
  p := rapidDecaySeminorm
  h_with := rapidDecay_withSeminorms
  h_countable := instCountableNat
  h_completeSpace := instCompleteSpace
  basis := basisVec
  coeff := coeffCLM
  expansion := rapidDecay_expansion
  basis_growth k := ⟨1, one_pos, k, fun m => by
    rw [rapidDecaySeminorm_basisVec]; linarith⟩
  coeff_decay k := ⟨1, one_pos, {k}, fun a m => by
    simp only [Finset.sup_singleton, coeffCLM, ContinuousLinearMap.coe_mk', coeffLM,
      LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    change |a.val m| * (1 + ↑m) ^ k ≤ ∑' n, |a.val n| * (1 + ↑n) ^ k
    exact (a.rapid_decay k).le_tsum m
      (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j k))⟩

instance rapidDecayHasBiorthogonalBasis :
    DyninMityaginSpace.HasBiorthogonalBasis RapidDecaySeq where
  coeff_basis n m := by
    change (basisVec m).val n = if n = m then 1 else 0
    simp [basisVec]

/-! ### Helper lemmas for seminorm transfer -/

/-- Monotonicity of rapid-decay seminorms: for j ≤ j', seminorm j ≤ seminorm j'. -/
theorem rapidDecaySeminorm_mono {j j' : ℕ} (hjj : j ≤ j') :
    rapidDecaySeminorm j ≤ rapidDecaySeminorm j' := by
  intro a
  change ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j ≤ ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j'
  apply (a.rapid_decay j).tsum_le_tsum _ (a.rapid_decay j')
  intro m
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg m)) hjj

/-- The sup of rapid-decay seminorms over a finset is bounded by the seminorm
at the max index.
-/
theorem finset_sup_rapidDecaySeminorm_le (s : Finset ℕ) :
    s.sup rapidDecaySeminorm ≤ rapidDecaySeminorm (s.sup id) := by
  apply Finset.sup_le
  intro j hj
  exact rapidDecaySeminorm_mono (Finset.le_sup (f := id) hj)

/-- The sup of rapid-decay seminorms evaluated at a basis vector gives
polynomial growth.
-/
theorem finset_sup_rapidDecaySeminorm_basisVec_le (s : Finset ℕ) (m : ℕ) :
    (s.sup rapidDecaySeminorm) (basisVec m) ≤ (1 + (m : ℝ)) ^ (s.sup id) := by
  calc (s.sup rapidDecaySeminorm) (basisVec m)
      ≤ rapidDecaySeminorm (s.sup id) (basisVec m) :=
        finset_sup_rapidDecaySeminorm_le s (basisVec m)
    _ = (1 + (m : ℝ)) ^ (s.sup id) :=
        rapidDecaySeminorm_basisVec _ m

end RapidDecaySeq

/-! ### Transfer constructor for DyninMityaginSpace -/

/-- Transfer a `DyninMityaginSpace` structure from `RapidDecaySeq` to any space
that is continuously linearly equivalent to it. Given seminorms `p` with
`WithSeminorms p` and a CLE `equiv : E ≃L[ℝ] RapidDecaySeq`, constructs the
DyninMityaginSpace instance using `basis m := equiv.symm (basisVec m)` and
`coeff m := coeffCLM m ∘ equiv`. Countability of `ι` and completeness of `E`
(transferred from `RapidDecaySeq` via the CLE) are propagated automatically.
-/
@[reducible] noncomputable def _root_.GaussianField.DyninMityaginSpace.ofRapidDecayEquiv
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {ι : Type} [Countable ι] (p : ι → Seminorm ℝ E) (hp : WithSeminorms p)
    (equiv : E ≃L[ℝ] RapidDecaySeq) : DyninMityaginSpace E where
  toT1Space := t1Space_of_injective_of_continuous equiv.injective equiv.continuous
  ι := ι
  p := p
  h_with := hp
  h_countable := ‹Countable ι›
  h_completeSpace := by
    -- Transfer CompleteSpace from RapidDecaySeq to E via the CLE.
    -- Set up uniform spaces on both sides from rightUniformSpace.
    letI uE : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    letI uR : UniformSpace RapidDecaySeq :=
      IsTopologicalAddGroup.rightUniformSpace RapidDecaySeq
    haveI : IsUniformAddGroup RapidDecaySeq := isUniformAddGroup_of_addCommGroup
    exact (completeSpace_congr (e := equiv.toLinearEquiv.toEquiv)
      equiv.isUniformEmbedding).2 RapidDecaySeq.instCompleteSpace
  basis m := equiv.symm (RapidDecaySeq.basisVec m)
  coeff m := (RapidDecaySeq.coeffCLM m).comp equiv.toContinuousLinearMap
  expansion φ f := by
    change φ f = ∑' m, (equiv f).val m * φ (equiv.symm (RapidDecaySeq.basisVec m))
    have h := RapidDecaySeq.rapidDecay_expansion
      (φ.comp equiv.symm.toContinuousLinearMap) (equiv f)
    simp only [ContinuousLinearMap.comp_apply] at h
    rwa [show (↑equiv.symm : RapidDecaySeq →L[ℝ] E) (equiv f) = f from
      equiv.symm_apply_apply f] at h
  basis_growth i := by
    set q : Seminorm ℝ RapidDecaySeq := (p i).comp equiv.symm.toLinearMap
    have hq_cont : Continuous q :=
      (hp.continuous_seminorm i).comp equiv.symm.continuous
    obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
      Seminorm.bound_of_continuous RapidDecaySeq.rapidDecay_withSeminorms q hq_cont
    set N := s_fin.sup id
    have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
    refine ⟨(C_nn : ℝ), hC_pos, N, fun m => ?_⟩
    calc p i (equiv.symm (RapidDecaySeq.basisVec m))
        = q (RapidDecaySeq.basisVec m) := rfl
      _ ≤ C_nn • (s_fin.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m) :=
          hle (RapidDecaySeq.basisVec m)
      _ ≤ (C_nn : ℝ) * (1 + (m : ℝ)) ^ N := by
          simp only [NNReal.smul_def, smul_eq_mul]
          exact mul_le_mul_of_nonneg_left
            (RapidDecaySeq.finset_sup_rapidDecaySeminorm_basisVec_le s_fin m)
            (NNReal.coe_nonneg C_nn)
  coeff_decay k := by
    set q : Seminorm ℝ E := (RapidDecaySeq.rapidDecaySeminorm k).comp equiv.toLinearMap
    have hq_cont : Continuous q :=
      (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm k).comp equiv.continuous
    obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
      Seminorm.bound_of_continuous hp q hq_cont
    have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
    refine ⟨(C_nn : ℝ), hC_pos, s_fin, fun f m => ?_⟩
    have h_le_tsum : |(RapidDecaySeq.coeffCLM m (equiv f))| * (1 + (m : ℝ)) ^ k ≤
        RapidDecaySeq.rapidDecaySeminorm k (equiv f) := by
      change |(equiv f).val m| * (1 + (m : ℝ)) ^ k ≤
        ∑' n, |(equiv f).val n| * (1 + (n : ℝ)) ^ k
      exact ((equiv f).rapid_decay k).le_tsum m
        (fun j _ => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg j k))
    have h_bound : RapidDecaySeq.rapidDecaySeminorm k (equiv f) ≤
        (C_nn : ℝ) * (s_fin.sup p) f := by
      have := hle f
      simp only [Seminorm.smul_apply,
        NNReal.smul_def, smul_eq_mul] at this
      exact this
    change |(RapidDecaySeq.coeffCLM m (equiv f))| * (1 + (m : ℝ)) ^ k ≤
      (C_nn : ℝ) * (s_fin.sup p) f
    exact le_trans h_le_tsum h_bound

/-- `ofRapidDecayEquiv` always produces a biorthogonal DM space. -/
theorem _root_.GaussianField.DyninMityaginSpace.ofRapidDecayEquiv_hasBiorthogonalBasis
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {ι : Type} [Countable ι] (p : ι → Seminorm ℝ E) (hp : WithSeminorms p)
    (equiv : E ≃L[ℝ] RapidDecaySeq) :
    letI := DyninMityaginSpace.ofRapidDecayEquiv p hp equiv
    DyninMityaginSpace.HasBiorthogonalBasis E :=
  letI := DyninMityaginSpace.ofRapidDecayEquiv p hp equiv
  { coeff_basis := fun n m => by
      change RapidDecaySeq.coeffCLM n (equiv (equiv.symm (RapidDecaySeq.basisVec m))) =
        if n = m then 1 else 0
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change (RapidDecaySeq.basisVec m).val n = if n = m then 1 else 0
      simp [RapidDecaySeq.basisVec, eq_comm] }

/-! ## Cantor Pairing Bound -/

/-- The Cantor pairing function is bounded by a quadratic. -/
theorem nat_pair_bound (n m : ℕ) : Nat.pair n m ≤ (n + m + 1) ^ 2 := by
  have hpair : Nat.pair n m ≤ (max n m + 1) ^ 2 :=
    Nat.le_of_lt (Nat.pair_lt_max_add_one_sq n m)
  have hmax : max n m + 1 ≤ n + m + 1 := by
    exact Nat.succ_le_succ (max_le (Nat.le_add_right n m) (Nat.le_add_left m n))
  exact hpair.trans (Nat.pow_le_pow_left hmax 2)

/-- Converse bound: each component of `Nat.unpair` is bounded by the pair index. -/
theorem nat_unpair_le (p : ℕ) : (Nat.unpair p).1 ≤ p ∧ (Nat.unpair p).2 ≤ p :=
  ⟨Nat.unpair_left_le p, Nat.unpair_right_le p⟩

/-! ## Nuclear Tensor Product -/

/-- The nuclear tensor product of two nuclear spaces, realized as the Köthe
sequence space of rapidly decreasing sequences. The product basis indices
`ℕ × ℕ` are encoded into `ℕ` via `Nat.pair`.

Mathematically, if `E₁ ≅ s(ℕ)` and `E₂ ≅ s(ℕ)` as nuclear Fréchet spaces,
then `E₁ ⊗̂ E₂ ≅ s(ℕ × ℕ) ≅ s(ℕ)` via the Cantor pairing.
-/
def NuclearTensorProduct (_E₁ _E₂ : Type*) :=
  let _ := _E₁
  let _ := _E₂
  RapidDecaySeq

namespace NuclearTensorProduct

variable {E₁ E₂ : Type*}

@[ext]
theorem ext {a b : NuclearTensorProduct E₁ E₂} (h : ∀ m, a.val m = b.val m) : a = b :=
  RapidDecaySeq.ext h

instance : AddCommGroup (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (AddCommGroup RapidDecaySeq)

instance : Module ℝ (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (Module ℝ RapidDecaySeq)

@[simp] theorem add_val (a b : NuclearTensorProduct E₁ E₂) (m : ℕ) :
    (a + b).val m = a.val m + b.val m := rfl

@[simp] theorem smul_val (r : ℝ) (a : NuclearTensorProduct E₁ E₂) (m : ℕ) :
    (r • a).val m = r * a.val m := rfl

instance : TopologicalSpace (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (TopologicalSpace RapidDecaySeq)

instance : IsTopologicalAddGroup (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (IsTopologicalAddGroup RapidDecaySeq)

instance : ContinuousSMul ℝ (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (ContinuousSMul ℝ RapidDecaySeq)

/-- The nuclear tensor product is a nuclear space. -/
instance dyninMityaginSpace : DyninMityaginSpace (NuclearTensorProduct E₁ E₂) :=
  RapidDecaySeq.rapidDecayDyninMityaginSpace

/-- Map from product basis indices to the Cantor-paired linear index. -/
def fromPairIndex (n m : ℕ) : ℕ := Nat.pair n m

/-- Recover product basis indices from a linear index. -/
def toPairIndex (p : ℕ) : ℕ × ℕ := Nat.unpair p

theorem toPairIndex_fromPairIndex (n m : ℕ) :
    toPairIndex (fromPairIndex n m) = (n, m) :=
  Nat.unpair_pair n m

theorem fromPairIndex_toPairIndex (p : ℕ) :
    fromPairIndex (toPairIndex p).1 (toPairIndex p).2 = p :=
  Nat.pair_unpair p

/-! ### Pure tensor embedding -/

/-- The Cantor pairing as an equivalence `ℕ ≃ ℕ × ℕ`. -/
private def natUnpairEquiv : ℕ ≃ ℕ × ℕ where
  toFun := Nat.unpair
  invFun p := Nat.pair p.1 p.2
  left_inv := Nat.pair_unpair
  right_inv p := Nat.unpair_pair p.1 p.2

/-- `∑_n 1/(1+n)^2` converges, as a shifted version of `∑ 1/n^2`. -/
theorem summable_inv_one_add_sq :
    Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
  -- Reindex: (fun n => ((1 + n)^2)⁻¹) = (fun n => (n^2)⁻¹) ∘ (· + 1)
  have h_eq : (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) =
      (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ∘ (· + 1) := by
    ext n; simp [Function.comp, add_comm]
  rw [h_eq]
  apply Summable.comp_injective
  · exact Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)
  · exact fun a b hab => by omega

/-- The inverse-square series over Cantor-paired indices converges:
`∑_m 1/((1+fst(m))² · (1+snd(m))²)` is finite.
-/
private theorem summable_unpair_inv_sq :
    Summable (fun m : ℕ =>
      ((1 + ((Nat.unpair m).1 : ℝ)) ^ 2 * (1 + ((Nat.unpair m).2 : ℝ)) ^ 2)⁻¹) := by
  -- Rewrite as product of inverse squares, transfer to ℕ×ℕ via pairing equiv,
  -- then factor as product of two convergent series
  have h_eq : (fun m => ((1 + ((Nat.unpair m).1 : ℝ)) ^ 2 *
      (1 + ((Nat.unpair m).2 : ℝ)) ^ 2)⁻¹) =
    (fun p : ℕ × ℕ => ((1 + (p.1 : ℝ)) ^ 2)⁻¹ * ((1 + (p.2 : ℝ)) ^ 2)⁻¹) ∘
      natUnpairEquiv := by ext m; simp [natUnpairEquiv, mul_inv_rev, mul_comm]
  rw [h_eq, natUnpairEquiv.summable_iff]
  set g : ℕ × ℕ → ℝ := fun p => ((1 + (p.1 : ℝ)) ^ 2)⁻¹ * ((1 + (p.2 : ℝ)) ^ 2)⁻¹
  show Summable g
  have hg_nn : 0 ≤ g := fun p => by dsimp [g]; positivity
  have h1 : ∀ x, Summable fun y => g (x, y) := fun x => by
    dsimp [g]
    exact summable_inv_one_add_sq.mul_left _
  have h2 : Summable fun x => ∑' y, g (x, y) := by
    have : (fun x : ℕ => ∑' y, g (x, y)) = fun x : ℕ =>
        ((1 + (x : ℝ)) ^ 2)⁻¹ * ∑' (y : ℕ), ((1 + (y : ℝ)) ^ 2)⁻¹ := by
      ext x; dsimp [g]; rw [tsum_mul_left]
    rw [this]
    exact summable_inv_one_add_sq.mul_right _
  exact (summable_prod_of_nonneg hg_nn).mpr ⟨h1, h2⟩

/-- Arithmetic bound: `(1 + Nat.pair i j) ≤ (2 * (1 + i) * (1 + j)) ^ 2`.

Used to transfer rapid decay of individual coefficient sequences to rapid
decay of the tensor product sequence indexed via Cantor pairing.
-/
private theorem one_add_pair_le_sq (i j : ℕ) :
    (1 + (Nat.pair i j : ℝ)) ≤ (2 * (1 + (i : ℝ)) * (1 + (j : ℝ))) ^ 2 := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h_pair : (Nat.pair i j : ℝ) ≤ ((i : ℝ) + j + 1) ^ 2 := by
    exact_mod_cast nat_pair_bound i j
  calc (1 : ℝ) + Nat.pair i j
      ≤ 1 + (i + j + 1) ^ 2 := by linarith
    _ ≤ (i + j + 2) ^ 2 := by nlinarith
    _ ≤ (2 * (1 + i) * (1 + j)) ^ 2 := pow_le_pow_left₀ (by positivity) (by nlinarith) _

/-- The pure tensor map: given `e₁ : E₁` and `e₂ : E₂` with DM structure,
produces the sequence `m ↦ coeff(unpair(m).1, e₁) * coeff(unpair(m).2, e₂)`.

This is the bilinear embedding `E₁ × E₂ → E₁ ⊗̂ E₂` realized at the level
of Köthe sequence spaces.
-/
noncomputable def pure
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
    [DyninMityaginSpace E₁] [DyninMityaginSpace E₂]
    (e₁ : E₁) (e₂ : E₂) : NuclearTensorProduct E₁ E₂ :=
  (⟨fun m =>
    let p := Nat.unpair m
    DyninMityaginSpace.coeff p.1 e₁ * DyninMityaginSpace.coeff p.2 e₂,
  fun k => by
    -- Strategy: bound each term by B/(1+i)²(1+j)² where (i,j) = unpair m,
    -- then show the bounding series converges.
    -- Get uniform bounds from coeff_decay at exponent 2k+2
    obtain ⟨C₁, hC₁_pos, s₁, hs₁⟩ := DyninMityaginSpace.coeff_decay (E := E₁) (2 * k + 2)
    obtain ⟨C₂, hC₂_pos, s₂, hs₂⟩ := DyninMityaginSpace.coeff_decay (E := E₂) (2 * k + 2)
    set B₁ := C₁ * (s₁.sup DyninMityaginSpace.p) e₁
    set B₂ := C₂ * (s₂.sup DyninMityaginSpace.p) e₂
    have hc₁ : ∀ n, |DyninMityaginSpace.coeff n e₁| * (1 + (n : ℝ)) ^ (2 * k + 2) ≤ B₁ :=
      fun n => hs₁ e₁ n
    have hc₂ : ∀ n, |DyninMityaginSpace.coeff n e₂| * (1 + (n : ℝ)) ^ (2 * k + 2) ≤ B₂ :=
      fun n => hs₂ e₂ n
    apply Summable.of_nonneg_of_le
    · intro m; exact mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg m k)
    · intro m
      set i := (Nat.unpair m).1
      set j := (Nat.unpair m).2
      change |DyninMityaginSpace.coeff i e₁ * DyninMityaginSpace.coeff j e₂| *
        (1 + (m : ℝ)) ^ k ≤
        B₁ * B₂ * (4 : ℝ) ^ k / ((1 + (i : ℝ)) ^ 2 * (1 + (j : ℝ)) ^ 2)
      rw [abs_mul]
      have hm_eq : m = Nat.pair i j := (Nat.pair_unpair m).symm
      have hi_pos : (0 : ℝ) < 1 + (i : ℝ) := by positivity
      have hj_pos : (0 : ℝ) < 1 + (j : ℝ) := by positivity
      -- Key: (1+m)^k ≤ 4^k * (1+i)^{2k} * (1+j)^{2k}
      have h_weight : (1 + (m : ℝ)) ^ k ≤
          (4 : ℝ) ^ k * (1 + (i : ℝ)) ^ (2 * k) * (1 + (j : ℝ)) ^ (2 * k) := by
        have h1 : (1 + (m : ℝ)) ^ k ≤
            ((2 * (1 + (i : ℝ)) * (1 + (j : ℝ))) ^ 2) ^ k := by
          rw [hm_eq]
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast one_add_pair_le_sq i j) _
        have h2 : ((2 * (1 + (i : ℝ)) * (1 + (j : ℝ))) ^ 2) ^ k =
            (4 : ℝ) ^ k * (1 + (i : ℝ)) ^ (2 * k) * (1 + (j : ℝ)) ^ (2 * k) := by
          have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul]
          rw [h4, ← pow_mul, mul_pow, mul_pow]
        linarith
      -- From coeff decay: |a_i| * (1+i)^{2k} ≤ B₁ / (1+i)^2
      have h_a : |DyninMityaginSpace.coeff i e₁| * (1 + (i : ℝ)) ^ (2 * k) ≤
          B₁ / (1 + (i : ℝ)) ^ 2 := by
        rw [le_div_iff₀ (pow_pos hi_pos 2)]
        calc |DyninMityaginSpace.coeff i e₁| * (1 + ↑i) ^ (2 * k) * (1 + ↑i) ^ 2
            = |DyninMityaginSpace.coeff i e₁| * ((1 + ↑i) ^ (2 * k) * (1 + ↑i) ^ 2) :=
              by ring
          _ = |DyninMityaginSpace.coeff i e₁| * (1 + ↑i) ^ (2 * k + 2) := by
              rw [← pow_add]
          _ ≤ B₁ := hc₁ i
      have h_b : |DyninMityaginSpace.coeff j e₂| * (1 + (j : ℝ)) ^ (2 * k) ≤
          B₂ / (1 + (j : ℝ)) ^ 2 := by
        rw [le_div_iff₀ (pow_pos hj_pos 2)]
        calc |DyninMityaginSpace.coeff j e₂| * (1 + ↑j) ^ (2 * k) * (1 + ↑j) ^ 2
            = |DyninMityaginSpace.coeff j e₂| * ((1 + ↑j) ^ (2 * k) * (1 + ↑j) ^ 2) :=
              by ring
          _ = |DyninMityaginSpace.coeff j e₂| * (1 + ↑j) ^ (2 * k + 2) := by
              rw [← pow_add]
          _ ≤ B₂ := hc₂ j
      -- Combine the bounds
      calc |DyninMityaginSpace.coeff i e₁| * |DyninMityaginSpace.coeff j e₂| *
            (1 + (m : ℝ)) ^ k
          ≤ |DyninMityaginSpace.coeff i e₁| * |DyninMityaginSpace.coeff j e₂| *
            ((4 : ℝ) ^ k * (1 + ↑i) ^ (2 * k) * (1 + ↑j) ^ (2 * k)) :=
              mul_le_mul_of_nonneg_left h_weight (by positivity)
        _ = (|DyninMityaginSpace.coeff i e₁| * (1 + ↑i) ^ (2 * k)) *
            (|DyninMityaginSpace.coeff j e₂| * (1 + ↑j) ^ (2 * k)) * (4 : ℝ) ^ k := by
              ring
        _ ≤ (B₁ / (1 + ↑i) ^ 2) * (B₂ / (1 + ↑j) ^ 2) * (4 : ℝ) ^ k := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul h_a h_b
                (mul_nonneg (abs_nonneg _) (by positivity)) (by positivity)
        _ = B₁ * B₂ * (4 : ℝ) ^ k / ((1 + ↑i) ^ 2 * (1 + ↑j) ^ 2) := by
              field_simp
    · -- Summability: ∑_m B₁*B₂*4^k / ((1+i)²*(1+j)²) converges
      have hconst : (0 : ℝ) ≤ B₁ * B₂ * (4 : ℝ) ^ k := by positivity
      simp_rw [div_eq_mul_inv]
      exact (summable_unpair_inv_sq.mul_left (B₁ * B₂ * (4 : ℝ) ^ k))⟩ : RapidDecaySeq)

variable [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
    [DyninMityaginSpace E₁] [DyninMityaginSpace E₂]

@[simp] theorem pure_val (e₁ : E₁) (e₂ : E₂) (m : ℕ) :
    (pure e₁ e₂).val m =
      DyninMityaginSpace.coeff (Nat.unpair m).1 e₁ *
      DyninMityaginSpace.coeff (Nat.unpair m).2 e₂ := rfl

/-- Seminorm bound for the pure tensor: for each target seminorm index `k`,
there exist constants `C`, source seminorm index sets `s₁, s₂` such that
`rapidDecaySeminorm k (pure e₁ e₂) ≤ C * (s₁.sup p) e₁ * (s₂.sup p) e₂`.
-/
theorem pure_seminorm_bound (k : ℕ) :
    ∃ (C : NNReal) (s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _))
      (s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)),
    ∀ (e₁ : E₁) (e₂ : E₂), RapidDecaySeq.rapidDecaySeminorm k (pure e₁ e₂) ≤
      C * (s₁.sup DyninMityaginSpace.p) e₁ * (s₂.sup DyninMityaginSpace.p) e₂ := by
  obtain ⟨C₁, hC₁_pos, s₁, hs₁⟩ := DyninMityaginSpace.coeff_decay (E := E₁) (2 * k + 2)
  obtain ⟨C₂, hC₂_pos, s₂, hs₂⟩ := DyninMityaginSpace.coeff_decay (E := E₂) (2 * k + 2)
  -- The constant is C₁ * C₂ * 4^k * (tsum of inverse squares)
  set T := ∑' (m : ℕ), ((1 + ((Nat.unpair m).1 : ℝ)) ^ 2 *
      (1 + ((Nat.unpair m).2 : ℝ)) ^ 2)⁻¹
  have hT_pos : 0 < T :=
    summable_unpair_inv_sq.tsum_pos (fun m => by positivity) 0 (by positivity)
  have hC_nn : (0 : ℝ) ≤ C₁ * C₂ * (4 : ℝ) ^ k * T := by positivity
  refine ⟨⟨C₁ * C₂ * (4 : ℝ) ^ k * T, hC_nn⟩, s₁, s₂, fun e₁ e₂ => ?_⟩
  -- The seminorm is a tsum; bound each term
  change ∑' m, |(pure e₁ e₂).val m| * (1 + (m : ℝ)) ^ k ≤
    C₁ * C₂ * (4 : ℝ) ^ k * T *
    (s₁.sup DyninMityaginSpace.p) e₁ * (s₂.sup DyninMityaginSpace.p) e₂
  set B₁ := C₁ * (s₁.sup DyninMityaginSpace.p) e₁
  set B₂ := C₂ * (s₂.sup DyninMityaginSpace.p) e₂
  -- Each term is bounded by B₁*B₂*4^k / ((1+i)²*(1+j)²)
  have h_term_bound : ∀ m,
      |(pure e₁ e₂).val m| * (1 + (m : ℝ)) ^ k ≤
      B₁ * B₂ * (4 : ℝ) ^ k *
        ((1 + ((Nat.unpair m).1 : ℝ)) ^ 2 * (1 + ((Nat.unpair m).2 : ℝ)) ^ 2)⁻¹ := by
    intro m
    set i := (Nat.unpair m).1
    set j := (Nat.unpair m).2
    simp only [pure_val, abs_mul]
    have hm_eq : m = Nat.pair i j := (Nat.pair_unpair m).symm
    have hi_pos : (0 : ℝ) < 1 + (i : ℝ) := by positivity
    have hj_pos : (0 : ℝ) < 1 + (j : ℝ) := by positivity
    have h_weight : (1 + (m : ℝ)) ^ k ≤
        (4 : ℝ) ^ k * (1 + (i : ℝ)) ^ (2 * k) * (1 + (j : ℝ)) ^ (2 * k) := by
      have h1 : (1 + (m : ℝ)) ^ k ≤
          ((2 * (1 + (i : ℝ)) * (1 + (j : ℝ))) ^ 2) ^ k := by
        rw [hm_eq]
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast one_add_pair_le_sq i j) _
      have h2 : ((2 * (1 + (i : ℝ)) * (1 + (j : ℝ))) ^ 2) ^ k =
          (4 : ℝ) ^ k * (1 + (i : ℝ)) ^ (2 * k) * (1 + (j : ℝ)) ^ (2 * k) := by
        have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_mul]
        rw [h4, ← pow_mul, mul_pow, mul_pow]
      linarith
    have h_a : |DyninMityaginSpace.coeff i e₁| * (1 + (i : ℝ)) ^ (2 * k) ≤
        B₁ / (1 + (i : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hi_pos 2)]
      calc |DyninMityaginSpace.coeff i e₁| * (1 + ↑i) ^ (2 * k) * (1 + ↑i) ^ 2
          = |DyninMityaginSpace.coeff i e₁| * ((1 + ↑i) ^ (2 * k) * (1 + ↑i) ^ 2) := by ring
        _ = |DyninMityaginSpace.coeff i e₁| * (1 + ↑i) ^ (2 * k + 2) := by rw [← pow_add]
        _ ≤ B₁ := hs₁ e₁ i
    have h_b : |DyninMityaginSpace.coeff j e₂| * (1 + (j : ℝ)) ^ (2 * k) ≤
        B₂ / (1 + (j : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hj_pos 2)]
      calc |DyninMityaginSpace.coeff j e₂| * (1 + ↑j) ^ (2 * k) * (1 + ↑j) ^ 2
          = |DyninMityaginSpace.coeff j e₂| * ((1 + ↑j) ^ (2 * k) * (1 + ↑j) ^ 2) := by ring
        _ = |DyninMityaginSpace.coeff j e₂| * (1 + ↑j) ^ (2 * k + 2) := by rw [← pow_add]
        _ ≤ B₂ := hs₂ e₂ j
    calc |DyninMityaginSpace.coeff i e₁| * |DyninMityaginSpace.coeff j e₂| *
          (1 + (m : ℝ)) ^ k
        ≤ |DyninMityaginSpace.coeff i e₁| * |DyninMityaginSpace.coeff j e₂| *
          ((4 : ℝ) ^ k * (1 + ↑i) ^ (2 * k) * (1 + ↑j) ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left h_weight (by positivity)
      _ = (|DyninMityaginSpace.coeff i e₁| * (1 + ↑i) ^ (2 * k)) *
          (|DyninMityaginSpace.coeff j e₂| * (1 + ↑j) ^ (2 * k)) * (4 : ℝ) ^ k := by ring
      _ ≤ (B₁ / (1 + ↑i) ^ 2) * (B₂ / (1 + ↑j) ^ 2) * (4 : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul h_a h_b
              (mul_nonneg (abs_nonneg _) (by positivity)) (by positivity)
      _ = B₁ * B₂ * (4 : ℝ) ^ k / ((1 + ↑i) ^ 2 * (1 + ↑j) ^ 2) := by field_simp
      _ = B₁ * B₂ * (4 : ℝ) ^ k *
          ((1 + (i : ℝ)) ^ 2 * (1 + (j : ℝ)) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
  -- Sum the bound
  calc ∑' m, |(pure e₁ e₂).val m| * (1 + (m : ℝ)) ^ k
      ≤ ∑' m, B₁ * B₂ * (4 : ℝ) ^ k *
          ((1 + ((Nat.unpair m).1 : ℝ)) ^ 2 * (1 + ((Nat.unpair m).2 : ℝ)) ^ 2)⁻¹ := by
        exact ((pure e₁ e₂).rapid_decay k).tsum_le_tsum h_term_bound
          ((summable_unpair_inv_sq).mul_left _)
    _ = B₁ * B₂ * (4 : ℝ) ^ k * T := tsum_mul_left
    _ = C₁ * C₂ * (4 : ℝ) ^ k * T *
        (s₁.sup DyninMityaginSpace.p) e₁ * (s₂.sup DyninMityaginSpace.p) e₂ := by
      simp only [B₁, B₂]; ring

/-- The pure tensor map as a bilinear map. -/
def pureLin : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] NuclearTensorProduct E₁ E₂ where
  toFun e₁ :=
    { toFun := fun e₂ => pure e₁ e₂
      map_add' := fun e₂ e₂' => by
        ext m; simp only [pure_val, add_val, map_add, mul_add]
      map_smul' := fun r e₂ => by
        simp only [RingHom.id_apply]
        ext m; simp only [pure_val, smul_val, map_smul, smul_eq_mul]; ring }
  map_add' e₁ e₁' := by
    apply LinearMap.ext; intro e₂; ext m
    simp only [pure_val, add_val, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply, map_add, add_mul]
  map_smul' r e₁ := by
    apply LinearMap.ext; intro e₂; ext m
    simp only [pure_val, smul_val, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]

/-- For fixed `e₁`, the map `e₂ ↦ pure e₁ e₂` is a continuous linear map.
Continuity follows from the seminorm bound via `continuous_of_isBounded`.
-/
def pureCLMRight (e₁ : E₁) : E₂ →L[ℝ] NuclearTensorProduct E₁ E₂ where
  toLinearMap := pureLin e₁
  cont := by
    apply WithSeminorms.continuous_of_isBounded
      (DyninMityaginSpace.h_with (E := E₂))
      RapidDecaySeq.rapidDecay_withSeminorms
    intro k
    obtain ⟨C, s₁, s₂, hbound⟩ := pure_seminorm_bound (E₁ := E₁) (E₂ := E₂) k
    refine ⟨s₂, ⟨C * (s₁.sup DyninMityaginSpace.p) e₁,
      mul_nonneg (NNReal.coe_nonneg C) (apply_nonneg _ _)⟩, fun e₂ => ?_⟩
    simp only [Seminorm.comp_apply]
    exact hbound e₁ e₂

/-- For fixed `e₂`, the map `e₁ ↦ pure e₁ e₂` is continuous. -/
theorem pure_continuous_left (e₂ : E₂) :
    Continuous (fun e₁ : E₁ => pure e₁ e₂) := by
  have : (fun e₁ : E₁ => pure e₁ e₂) = (pureLin (E₁ := E₁) (E₂ := E₂)).flip e₂ := by
    ext e₁ m; simp [pureLin, pure_val]
  rw [this]
  apply WithSeminorms.continuous_of_isBounded
    (DyninMityaginSpace.h_with (E := E₁))
    RapidDecaySeq.rapidDecay_withSeminorms
  intro k
  obtain ⟨C, s₁, s₂, hbound⟩ := pure_seminorm_bound (E₁ := E₁) (E₂ := E₂) k
  refine ⟨s₁, ⟨C * (s₂.sup DyninMityaginSpace.p) e₂,
    mul_nonneg (NNReal.coe_nonneg C) (apply_nonneg _ _)⟩, fun e₁ => ?_⟩
  simp only [Seminorm.comp_apply]
  calc RapidDecaySeq.rapidDecaySeminorm k (pure e₁ e₂)
      ≤ ↑C * (s₁.sup DyninMityaginSpace.p) e₁ * (s₂.sup DyninMityaginSpace.p) e₂ :=
        hbound e₁ e₂
    _ = ↑C * (s₂.sup DyninMityaginSpace.p) e₂ * (s₁.sup DyninMityaginSpace.p) e₁ := by ring

/-- A finset sup of seminorms with `WithSeminorms` has its ball in nhds 0. -/
private theorem finsetSup_seminorm_ball_mem_nhds
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {ι' : Type} {q : ι' → Seminorm ℝ F} (hq : WithSeminorms q)
    (t : Finset ι') {ε : ℝ} (hε : 0 < ε) :
    {x : F | (t.sup q) x < ε} ∈ nhds (0 : F) := by
  have hmem : ⋂ i ∈ t, {x : F | q i x < ε} ∈ nhds (0 : F) := by
    rw [t.iInter_mem_sets]
    intro i _
    exact (hq.continuous_seminorm i).isOpen_preimage _ isOpen_Iio |>.mem_nhds
      (show (0 : F) ∈ {x | q i x < ε} by simp [map_zero, hε])
  apply Filter.mem_of_superset hmem
  intro x hx
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
  rcases Seminorm.zero_or_exists_apply_eq_finset_sup q t x with h | ⟨i, hi, heq⟩
  · linarith
  · linarith [hx i hi]

/-- The pure tensor map is jointly continuous on `E₁ × E₂`. -/
theorem pure_continuous :
    Continuous (fun p : E₁ × E₂ => pure p.1 p.2) := by
  -- Package as AddMonoidHom for continuous_of_continuousAt_zero₂
  set f : E₁ →+ E₂ →+ NuclearTensorProduct E₁ E₂ :=
    { toFun := fun e₁ => (pureLin e₁).toAddMonoidHom
      map_zero' := by
        ext e₂ m; simp [pureLin, pure_val]; rfl
      map_add' := fun e₁ e₁' => by
        ext e₂ m; simp [pureLin, pure_val, add_mul] }
  change Continuous (fun p : E₁ × E₂ => f p.1 p.2)
  apply continuous_of_continuousAt_zero₂ f
  · -- Continuity at (0, 0): use the seminorm bound
    have hf00 : f 0 0 = 0 := by ext m; simp
    rw [ContinuousAt, hf00]
    apply (RapidDecaySeq.rapidDecay_withSeminorms.tendsto_nhds _ 0).mpr
    intro k ε hε
    obtain ⟨C, s₁, s₂, hbound⟩ := pure_seminorm_bound (E₁ := E₁) (E₂ := E₂) k
    -- Pick nhds: {e₁ | s₁.sup p₁ e₁ < 1} and {e₂ | s₂.sup p₂ e₂ < ε/(C+1)}
    have h_mem₁ : {e₁ : E₁ | (s₁.sup DyninMityaginSpace.p) e₁ < 1} ∈ nhds (0 : E₁) :=
      finsetSup_seminorm_ball_mem_nhds DyninMityaginSpace.h_with s₁ one_pos
    have h_mem₂ : {e₂ : E₂ | (s₂.sup DyninMityaginSpace.p) e₂ < ε / (↑C + 1)} ∈
        nhds (0 : E₂) :=
      finsetSup_seminorm_ball_mem_nhds DyninMityaginSpace.h_with s₂
        (div_pos hε (by positivity))
    rw [nhds_prod_eq]
    apply Filter.mem_of_superset (Filter.prod_mem_prod h_mem₁ h_mem₂)
    intro ⟨e₁, e₂⟩ ⟨he₁, he₂⟩
    simp only [Set.mem_setOf_eq, sub_zero] at he₁ he₂ ⊢
    calc RapidDecaySeq.rapidDecaySeminorm k (pure e₁ e₂)
        ≤ ↑C * (s₁.sup DyninMityaginSpace.p) e₁ * (s₂.sup DyninMityaginSpace.p) e₂ :=
          hbound e₁ e₂
      _ ≤ ↑C * 1 * (ε / (↑C + 1)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left he₁.le (NNReal.coe_nonneg C))
            he₂.le (apply_nonneg _ _) (mul_nonneg (NNReal.coe_nonneg C) (by linarith))
      _ = ↑C * ε / (↑C + 1) := by ring
      _ < ε := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑C + 1)]
          linarith [NNReal.coe_nonneg C]
  · -- Continuity of f x at 0 for each x
    intro e₁
    exact (pureCLMRight e₁).continuous.continuousAt
  · -- Continuity of f · y at 0 for each y
    intro e₂
    exact (pure_continuous_left e₂).continuousAt

/-! ### Universal Property: Lift -/

section Lift

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Summability of the lifted series. Given a bilinear map `B : E₁ →ₗ E₂ →ₗ G` that is
bounded by seminorms, the series `∑ₘ aₘ • B(ψ₁ᵢ, ψ₂ⱼ)` converges for any
`a : NuclearTensorProduct E₁ E₂`, where `(i,j) = unpair(m)`.
-/
private lemma lift_summable
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂)
    (a : NuclearTensorProduct E₁ E₂) :
    Summable (fun m => a.val m •
      B (DyninMityaginSpace.basis (Nat.unpair m).1)
        (DyninMityaginSpace.basis (Nat.unpair m).2)) := by
  classical
  have hgrowth₁ : ∀ i ∈ s₁, ∃ C' > 0, ∃ t : ℕ, ∀ m,
      DyninMityaginSpace.p i (DyninMityaginSpace.basis m : E₁) ≤ C' * (1 + (m : ℝ)) ^ t :=
    fun i _ => DyninMityaginSpace.basis_growth i
  have hgrowth₂ : ∀ i ∈ s₂, ∃ C' > 0, ∃ t : ℕ, ∀ m,
      DyninMityaginSpace.p i (DyninMityaginSpace.basis m : E₂) ≤ C' * (1 + (m : ℝ)) ^ t :=
    fun i _ => DyninMityaginSpace.basis_growth i
  obtain ⟨D₁, hD₁, S₁, hbound₁⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p s₁ DyninMityaginSpace.basis hgrowth₁
  obtain ⟨D₂, hD₂, S₂, hbound₂⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p s₂ DyninMityaginSpace.basis hgrowth₂
  set K := C * D₁ * D₂ with hK_def
  apply Summable.of_norm_bounded
    (g := fun m => K * (|a.val m| * (1 + (m : ℝ)) ^ (S₁ + S₂)))
  · exact ((a.rapid_decay (S₁ + S₂)).mul_left K)
  · intro m
    set i := (Nat.unpair m).1
    set j := (Nat.unpair m).2
    rw [norm_smul, Real.norm_eq_abs]
    have hi_le : (1 + (i : ℝ)) ≤ (1 + (m : ℝ)) := by
      linarith [(Nat.cast_le (α := ℝ)).mpr (Nat.unpair_left_le m)]
    have hj_le : (1 + (j : ℝ)) ≤ (1 + (m : ℝ)) := by
      linarith [(Nat.cast_le (α := ℝ)).mpr (Nat.unpair_right_le m)]
    have h1i : (0 : ℝ) ≤ 1 + (i : ℝ) := by positivity
    have h1j : (0 : ℝ) ≤ 1 + (j : ℝ) := by positivity
    calc |a.val m| * ‖B (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j)‖
        ≤ |a.val m| * (C * (s₁.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis i) *
            (s₂.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis j)) :=
          mul_le_mul_of_nonneg_left (hB _ _) (abs_nonneg _)
      _ ≤ |a.val m| * (C * (D₁ * (1 + (i : ℝ)) ^ S₁) * (D₂ * (1 + (j : ℝ)) ^ S₂)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hbound₁ i) (le_of_lt hC))
            (hbound₂ j) (apply_nonneg _ _) (by positivity)
      _ ≤ |a.val m| * (C * (D₁ * (1 + (m : ℝ)) ^ S₁) * (D₂ * (1 + (m : ℝ)) ^ S₂)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ h1i hi_le S₁) (le_of_lt hD₁)) (le_of_lt hC))
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1j hj_le S₂) (le_of_lt hD₂))
            (by positivity) (by positivity)
      _ = K * (|a.val m| * (1 + (m : ℝ)) ^ (S₁ + S₂)) := by
          rw [hK_def, pow_add]; ring

/-- Auxiliary: the norm bound for `lift` as a term-by-term inequality.
Extracts the common calculation used in both `lift` continuity and `lift_summable`.
-/
private lemma lift_norm_bound
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂) :
    ∃ K > 0, ∃ N : ℕ, ∀ (a : NuclearTensorProduct E₁ E₂),
      ‖∑' m, a.val m • B (DyninMityaginSpace.basis (Nat.unpair m).1)
        (DyninMityaginSpace.basis (Nat.unpair m).2)‖ ≤
      K * RapidDecaySeq.rapidDecaySeminorm N a := by
  classical
  have hgrowth₁ : ∀ i ∈ s₁, ∃ C' > 0, ∃ t : ℕ, ∀ m,
      DyninMityaginSpace.p i (DyninMityaginSpace.basis m : E₁) ≤ C' * (1 + (m : ℝ)) ^ t :=
    fun i _ => DyninMityaginSpace.basis_growth i
  have hgrowth₂ : ∀ i ∈ s₂, ∃ C' > 0, ∃ t : ℕ, ∀ m,
      DyninMityaginSpace.p i (DyninMityaginSpace.basis m : E₂) ≤ C' * (1 + (m : ℝ)) ^ t :=
    fun i _ => DyninMityaginSpace.basis_growth i
  obtain ⟨D₁, hD₁, S₁, hbnd₁⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p s₁ DyninMityaginSpace.basis hgrowth₁
  obtain ⟨D₂, hD₂, S₂, hbnd₂⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p s₂ DyninMityaginSpace.basis hgrowth₂
  set K := C * D₁ * D₂
  set N := S₁ + S₂
  refine ⟨K, by positivity, N, fun a => ?_⟩
  have hsumm := lift_summable B hC hB a
  -- Pointwise norm bound
  have hpw : ∀ m, ‖a.val m • B (DyninMityaginSpace.basis (Nat.unpair m).1)
      (DyninMityaginSpace.basis (Nat.unpair m).2)‖ ≤
      K * (|a.val m| * (1 + (m : ℝ)) ^ N) := by
    intro m
    set i := (Nat.unpair m).1
    set j := (Nat.unpair m).2
    rw [norm_smul, Real.norm_eq_abs]
    have hi_le : (1 + (i : ℝ)) ≤ (1 + (m : ℝ)) :=
      add_le_add_right (Nat.cast_le.mpr (Nat.unpair_left_le m)) 1
    have hj_le : (1 + (j : ℝ)) ≤ (1 + (m : ℝ)) :=
      add_le_add_right (Nat.cast_le.mpr (Nat.unpair_right_le m)) 1
    have h1i : (0 : ℝ) ≤ 1 + (i : ℝ) := by positivity
    have h1j : (0 : ℝ) ≤ 1 + (j : ℝ) := by positivity
    calc |a.val m| * ‖B (DyninMityaginSpace.basis i)
            (DyninMityaginSpace.basis j)‖
        ≤ |a.val m| * (C * (D₁ * (1 + (m : ℝ)) ^ S₁) *
            (D₂ * (1 + (m : ℝ)) ^ S₂)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc ‖B (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j)‖
              ≤ C * (s₁.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis i) *
                (s₂.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis j) := hB _ _
            _ ≤ C * (D₁ * (1 + (i : ℝ)) ^ S₁) * (D₂ * (1 + (j : ℝ)) ^ S₂) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left (hbnd₁ i) (le_of_lt hC))
                (hbnd₂ j) (apply_nonneg _ _) (by positivity)
            _ ≤ C * (D₁ * (1 + (m : ℝ)) ^ S₁) * (D₂ * (1 + (m : ℝ)) ^ S₂) := by
              apply mul_le_mul
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ h1i hi_le S₁) (le_of_lt hD₁)) (le_of_lt hC))
                (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ h1j hj_le S₂) (le_of_lt hD₂))
                (by positivity) (by positivity)
      _ = K * (|a.val m| * (1 + (m : ℝ)) ^ N) := by
          change |a.val m| * (C * (D₁ * (1 + ↑m) ^ S₁) * (D₂ * (1 + ↑m) ^ S₂)) =
            C * D₁ * D₂ * (|a.val m| * (1 + ↑m) ^ (S₁ + S₂))
          rw [pow_add]; ring
  have hg_summ : Summable (fun m => K * (|a.val m| * (1 + (m : ℝ)) ^ N)) :=
    (a.rapid_decay N).mul_left K
  have hnorm_summ : Summable (fun m => ‖a.val m • B (DyninMityaginSpace.basis (Nat.unpair m).1)
      (DyninMityaginSpace.basis (Nat.unpair m).2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpw hg_summ
  calc ‖∑' m, a.val m • B (DyninMityaginSpace.basis (Nat.unpair m).1)
          (DyninMityaginSpace.basis (Nat.unpair m).2)‖
      ≤ ∑' m, ‖a.val m • B (DyninMityaginSpace.basis (Nat.unpair m).1)
          (DyninMityaginSpace.basis (Nat.unpair m).2)‖ :=
        norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' m, K * (|a.val m| * (1 + (m : ℝ)) ^ N) :=
        hnorm_summ.tsum_le_tsum hpw hg_summ
    _ = K * ∑' m, |a.val m| * (1 + (m : ℝ)) ^ N := tsum_mul_left
    _ = K * RapidDecaySeq.rapidDecaySeminorm N a := by rfl

/-- The underlying linear map for `lift`. -/
private def liftLM
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂) :
    NuclearTensorProduct E₁ E₂ →ₗ[ℝ] G where
  toFun := fun a => ∑' m, a.val m •
    B (DyninMityaginSpace.basis (Nat.unpair m).1)
      (DyninMityaginSpace.basis (Nat.unpair m).2)
  map_add' := fun a b => by
    have ha := lift_summable B hC hB a
    have hb := lift_summable B hC hB b
    simp only [add_val]
    simp_rw [add_smul]
    exact ha.tsum_add hb
  map_smul' := fun r a => by
    have ha := lift_summable B hC hB a
    simp only [smul_val, RingHom.id_apply]
    simp_rw [mul_smul]
    exact ha.tsum_const_smul r

/-- **Universal property of the nuclear tensor product.**

Every continuous bilinear map `B : E₁ × E₂ → G` (into a complete normed space)
factors through `pure` via a CLM `lift B : NuclearTensorProduct E₁ E₂ →L[ℝ] G`.

The definition is `lift B a = ∑' m, aₘ • B(ψ₁ᵢ, ψ₂ⱼ)` where `(i,j) = unpair(m)`.
Linearity follows from tsum linearity; continuity from a seminorm bound.
-/
def lift
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] G where
  toLinearMap := liftLM B hC hB
  cont := by
    obtain ⟨K, hK, N, hbound⟩ := lift_norm_bound B hC hB
    apply WithSeminorms.continuous_of_isBounded
      (RapidDecaySeq.rapidDecay_withSeminorms :
        WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
          ℕ → Seminorm ℝ (NuclearTensorProduct E₁ E₂)))
      (norm_withSeminorms ℝ G)
    intro _
    refine ⟨{N}, ⟨K, le_of_lt hK⟩, fun a => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton,
      coe_normSeminorm, liftLM]
    exact hbound a

/-- The lift factors through pure: `lift B (pure e₁ e₂) = B e₁ e₂`.

The proof uses the double Schauder expansion: `hasSum_basis` gives convergent
expansions `e₁ = ∑ c₁_n • ψ₁_n` and `e₂ = ∑ c₂_j • ψ₂_j`, then applies `B`
(continuous from the bound) and rearranges via Cantor pairing.
-/
theorem lift_pure
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂)
    (e₁ : E₁) (e₂ : E₂) :
    lift B hC hB (pure e₁ e₂) = B e₁ e₂ := by
  -- Unfold lift to the tsum definition
  change ∑' m, (pure e₁ e₂).val m •
    B (DyninMityaginSpace.basis (Nat.unpair m).1)
      (DyninMityaginSpace.basis (Nat.unpair m).2) = B e₁ e₂
  simp only [pure_val]
  -- Abbreviations for readability (used only in types, not in HasSum.map)
  let ψ₁ := DyninMityaginSpace.basis (E := E₁)
  let ψ₂ := DyninMityaginSpace.basis (E := E₂)
  let c₁ := DyninMityaginSpace.coeff (E := E₁)
  let c₂ := DyninMityaginSpace.coeff (E := E₂)
  -- Step 1: Continuity of B(ψ₁ n) : E₂ →ₗ G for each n
  have hBn_cont : ∀ n, Continuous (B (ψ₁ n)) := by
    intro n
    apply WithSeminorms.continuous_of_isBounded
      (DyninMityaginSpace.h_with (E := E₂)) (norm_withSeminorms ℝ G)
    intro _
    refine ⟨s₂, ⟨C * (s₁.sup DyninMityaginSpace.p) (ψ₁ n),
      mul_nonneg (le_of_lt hC) (apply_nonneg _ _)⟩, fun x => ?_⟩
    change ‖(B (ψ₁ n)) x‖ ≤
      C * (s₁.sup DyninMityaginSpace.p) (ψ₁ n) * (s₂.sup DyninMityaginSpace.p) x
    exact hB (ψ₁ n) x
  -- Step 2: Continuity of B.flip e₂ : E₁ →ₗ G
  have hBflip_cont : Continuous (B.flip e₂) := by
    apply WithSeminorms.continuous_of_isBounded
      (DyninMityaginSpace.h_with (E := E₁)) (norm_withSeminorms ℝ G)
    intro _
    refine ⟨s₁, ⟨C * (s₂.sup DyninMityaginSpace.p) e₂,
      mul_nonneg (le_of_lt hC) (apply_nonneg _ _)⟩, fun x => ?_⟩
    change ‖(B.flip e₂) x‖ ≤
      C * (s₂.sup DyninMityaginSpace.p) e₂ * (s₁.sup DyninMityaginSpace.p) x
    rw [LinearMap.flip_apply]
    calc ‖(B x) e₂‖
        ≤ C * (s₁.sup DyninMityaginSpace.p) x *
          (s₂.sup DyninMityaginSpace.p) e₂ := hB x e₂
      _ = C * (s₂.sup DyninMityaginSpace.p) e₂ *
          (s₁.sup DyninMityaginSpace.p) x := by ring
  -- Step 3: Inner HasSum: ∑ₖ c₂(k)(e₂) • B(ψ₁(n))(ψ₂(k)) → B(ψ₁(n))(e₂)
  have h_inner : ∀ n, HasSum (fun k => c₂ k e₂ • B (ψ₁ n) (ψ₂ k))
      (B (ψ₁ n) e₂) := by
    intro n
    exact ((DyninMityaginSpace.hasSum_basis e₂).map (B (ψ₁ n)) (hBn_cont n)).congr_fun
      (fun k => (map_smul (B (ψ₁ n)) (c₂ k e₂) (ψ₂ k)).symm)
  -- Step 4: Outer HasSum: ∑ₙ c₁(n)(e₁) • B(ψ₁(n))(e₂) → B(e₁)(e₂)
  have h_outer : HasSum (fun n => c₁ n e₁ • B (ψ₁ n) e₂) (B e₁ e₂) := by
    exact ((DyninMityaginSpace.hasSum_basis e₁).map (B.flip e₂) hBflip_cont).congr_fun (fun n => by
      simp only [Function.comp, LinearMap.flip_apply]
      exact (map_smul (B.flip e₂) (c₁ n e₁) (ψ₁ n)).symm)
  -- Step 5: Summability of the ℕ-indexed sum (from lift_summable via pure_val)
  have h_summ_nat : Summable (fun m =>
      (c₁ (Nat.unpair m).1 e₁ * c₂ (Nat.unpair m).2 e₂) •
      B (ψ₁ (Nat.unpair m).1) (ψ₂ (Nat.unpair m).2)) := by
    have := lift_summable B hC hB (pure e₁ e₂)
    simp only [pure_val] at this; exact this
  -- Step 6: Summability of ℕ × ℕ-indexed version (via Cantor pairing equivalence)
  have h_summ_prod : Summable (fun (p : ℕ × ℕ) =>
      (c₁ p.1 e₁ * c₂ p.2 e₂) • B (ψ₁ p.1) (ψ₂ p.2)) :=
    (Nat.pairEquiv.symm.summable_iff).mp h_summ_nat
  -- Step 7: Fiber summability (each inner sum converges)
  have h_fiber : ∀ n, Summable (fun k =>
      (c₁ n e₁ * c₂ k e₂) • B (ψ₁ n) (ψ₂ k)) := by
    intro n
    have := (h_inner n).const_smul (c₁ n e₁)
    simp only [smul_smul] at this
    exact this.summable
  -- Step 8: Double Schauder expansion via calc chain
  symm
  calc B e₁ e₂
      = ∑' n, c₁ n e₁ • B (ψ₁ n) e₂ := h_outer.tsum_eq.symm
    _ = ∑' n, c₁ n e₁ • ∑' k, c₂ k e₂ • B (ψ₁ n) (ψ₂ k) := by
        congr 1; ext n; congr 1; exact (h_inner n).tsum_eq.symm
    _ = ∑' n, ∑' k, c₁ n e₁ • (c₂ k e₂ • B (ψ₁ n) (ψ₂ k)) := by
        congr 1; ext n; exact ((h_inner n).summable.tsum_const_smul _).symm
    _ = ∑' n, ∑' k, (c₁ n e₁ * c₂ k e₂) • B (ψ₁ n) (ψ₂ k) := by
        simp_rw [mul_smul]
    _ = ∑' (p : ℕ × ℕ), (c₁ p.1 e₁ * c₂ p.2 e₂) •
          B (ψ₁ p.1) (ψ₂ p.2) :=
        (h_summ_prod.tsum_prod' h_fiber).symm
    _ = ∑' m, (c₁ (Nat.unpair m).1 e₁ * c₂ (Nat.unpair m).2 e₂) •
          B (ψ₁ (Nat.unpair m).1) (ψ₂ (Nat.unpair m).2) :=
        (Equiv.tsum_eq Nat.pairEquiv.symm _).symm

end Lift

/-! ### Bilinear evaluation: tensor product of functionals -/

/-- The bilinear multiplication form `(x, y) ↦ x * y` as a bilinear map ℝ →ₗ ℝ →ₗ ℝ. -/
private def mulBilin : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => x * y
      map_add' := fun y₁ y₂ => mul_add x y₁ y₂
      map_smul' := fun r y => by simp [mul_comm r, mul_assoc] }
  map_add' x₁ x₂ := by ext; simp [add_mul]
  map_smul' r x := by ext; simp [mul_assoc]

section Eval

/-- Compose the multiplication bilinear form with CLMs on each factor. -/
private def compBilin (φ₁ : E₁ →L[ℝ] ℝ) (φ₂ : E₂ →L[ℝ] ℝ) :
    E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] ℝ :=
  (mulBilin.comp φ₁.toLinearMap).compl₂ φ₂.toLinearMap

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
    [DyninMityaginSpace E₁] [DyninMityaginSpace E₂] in
@[simp] private theorem compBilin_apply
    (φ₁ : E₁ →L[ℝ] ℝ) (φ₂ : E₂ →L[ℝ] ℝ)
    (e₁ : E₁) (e₂ : E₂) :
    compBilin φ₁ φ₂ e₁ e₂ = φ₁ e₁ * φ₂ e₂ := rfl

/-- **Tensor product of continuous linear functionals.**

Given `φ₁ ∈ E₁'` and `φ₂ ∈ E₂'`, the tensor product functional
`φ₁ ⊗ φ₂ : E₁ ⊗̂ E₂ → ℝ` is defined via the universal property `lift`
applied to the bilinear form `(e₁, e₂) ↦ φ₁(e₁) · φ₂(e₂)`.

On pure tensors: `evalCLM φ₁ φ₂ (pure e₁ e₂) = φ₁ e₁ * φ₂ e₂`.

The bilinear bound `‖φ₁(e₁) · φ₂(e₂)‖ ≤ C · p₁(e₁) · p₂(e₂)` follows from
`Seminorm.bound_of_continuous` applied to each functional.
-/
def _root_.GaussianField.NuclearTensorProduct.evalCLM
    (φ₁ : E₁ →L[ℝ] ℝ) (φ₂ : E₂ →L[ℝ] ℝ) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] ℝ := by
  classical
  -- Extract seminorm bounds for each functional via Classical.choice
  have hq₁ : Continuous ((normSeminorm ℝ ℝ).comp φ₁.toLinearMap) :=
    continuous_norm.comp φ₁.continuous
  have hq₂ : Continuous ((normSeminorm ℝ ℝ).comp φ₂.toLinearMap) :=
    continuous_norm.comp φ₂.continuous
  choose s₁ C₁ hC₁ne hle₁ using Seminorm.bound_of_continuous
    (DyninMityaginSpace.h_with (E := E₁))
    ((normSeminorm ℝ ℝ).comp φ₁.toLinearMap) hq₁
  choose s₂ C₂ hC₂ne hle₂ using Seminorm.bound_of_continuous
    (DyninMityaginSpace.h_with (E := E₂))
    ((normSeminorm ℝ ℝ).comp φ₂.toLinearMap) hq₂
  -- The bilinear bound: ‖φ₁ e₁ * φ₂ e₂‖ ≤ (C₁ * C₂) * (s₁.sup p) e₁ * (s₂.sup p) e₂
  have hC_pos : (0 : ℝ) < C₁ * C₂ := by positivity
  exact lift (compBilin φ₁ φ₂) hC_pos (fun e₁ e₂ => by
    simp only [compBilin_apply]
    rw [Real.norm_eq_abs, abs_mul]
    have h₁ : |φ₁ e₁| ≤ C₁ * (s₁.sup DyninMityaginSpace.p) e₁ := by
      have h₁' := hle₁ e₁
      simp only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
        Real.norm_eq_abs] at h₁'
      change |φ₁ e₁| ≤ C₁ * (s₁.sup DyninMityaginSpace.p) e₁ at h₁'
      exact h₁'
    have h₂ : |φ₂ e₂| ≤ C₂ * (s₂.sup DyninMityaginSpace.p) e₂ := by
      have h₂' := hle₂ e₂
      simp only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
        Real.norm_eq_abs] at h₂'
      change |φ₂ e₂| ≤ C₂ * (s₂.sup DyninMityaginSpace.p) e₂ at h₂'
      exact h₂'
    calc |φ₁ e₁| * |φ₂ e₂|
        ≤ (↑C₁ * (s₁.sup DyninMityaginSpace.p) e₁) *
          (↑C₂ * (s₂.sup DyninMityaginSpace.p) e₂) :=
          mul_le_mul h₁ h₂ (abs_nonneg _) (by positivity)
      _ = ↑C₁ * ↑C₂ * (s₁.sup DyninMityaginSpace.p) e₁ *
          (s₂.sup DyninMityaginSpace.p) e₂ := by ring)

/-- `evalCLM` on pure tensors gives the product of evaluations. -/
theorem _root_.GaussianField.NuclearTensorProduct.evalCLM_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (φ₁ : E₁ →L[ℝ] ℝ) (φ₂ : E₂ →L[ℝ] ℝ)
    (e₁ : E₁) (e₂ : E₂) :
    evalCLM φ₁ φ₂ (pure e₁ e₂) = φ₁ e₁ * φ₂ e₂ := by
  unfold evalCLM
  rw [lift_pure]
  simp [compBilin_apply]

end Eval

/-- Under biorthogonality, basis vectors equal pure tensors of basis elements.
`basisVec m = pure (basis a) (basis b)` where `(a,b) = unpair(m)`.
-/
theorem _root_.GaussianField.NuclearTensorProduct.basisVec_eq_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (hbasis₁ : ∀ n m, DyninMityaginSpace.coeff (E := E₁) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (hbasis₂ : ∀ n m, DyninMityaginSpace.coeff (E := E₂) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (m : ℕ) :
    (RapidDecaySeq.basisVec m : NuclearTensorProduct E₁ E₂) =
    NuclearTensorProduct.pure
      (DyninMityaginSpace.basis (E := E₁) (Nat.unpair m).1)
      (DyninMityaginSpace.basis (E := E₂) (Nat.unpair m).2) := by
  ext n
  simp only [RapidDecaySeq.basisVec, pure_val, hbasis₁, hbasis₂]
  by_cases h : n = m
  · subst h; simp
  · simp only [h, if_false, mul_ite, mul_one, mul_zero]
    by_cases h₁ : (Nat.unpair n).1 = (Nat.unpair m).1
    · by_cases h₂ : (Nat.unpair n).2 = (Nat.unpair m).2
      · exfalso
        apply h
        rw [← Nat.pair_unpair n, ← Nat.pair_unpair m, h₁, h₂]
      · simp only [h₂, if_false]
    · by_cases h₂ : (Nat.unpair n).2 = (Nat.unpair m).2
      · simp only [h₁, h₂, if_false, if_true]
      · simp only [h₁, h₂, if_false]

end NuclearTensorProduct

end GaussianField
