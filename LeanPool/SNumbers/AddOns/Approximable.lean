/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Approximation
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Approximable operators

Following Pietsch, *Eigenvalues and s-numbers*, §2.11. An operator
`S : X →L[𝕜] Y` between normed `𝕜`-spaces is **approximable** if its
approximation numbers tend to zero, equivalently, if it is the
operator-norm limit of a sequence of finite-rank operators.

This file develops the basic properties of the class of approximable
operators:

* it is closed under addition, scalar multiplication, and
  pre/post-composition by bounded operators;
* it is closed in the operator-norm topology;
* every finite-rank operator is approximable;
* every approximable operator is compact (`IsApproximable.isCompactOperator`).

The converse direction (compact ⇒ approximable) holds on Hilbert spaces but
fails for general Banach spaces (Enflo, 1973). The Hilbert-space case is
treated in `AddOns.Compact` via the singular value decomposition.

## Main definitions / results

* `SVD.IsApproximable S` — `aₙ(S) → 0`.
* `SVD.isApproximable_iff_existsLimit` — equivalent characterisation as a
  uniform limit of finite-rank operators.
* `SVD.IsApproximable.isCompactOperator` — every approximable operator is
  compact; `SVD.isCompactOperator_of_rank_le` specialises this to operators of
  finite rank.
-/

universe u

open scoped Cardinal
open Filter Topology

namespace SVD

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- An operator `S : X →L[𝕜] Y` is **approximable** if its approximation
numbers tend to zero. -/
def IsApproximable (S : X →L[𝕜] Y) : Prop :=
  Tendsto (SNumbers.approximationNumber S) atTop (𝓝 0)

/-! ### Equivalent characterisation -/

/-- Equivalent characterisation: approximable iff a uniform limit of
finite-rank operators. The forward direction extracts a near-optimal
rank-`≤ n` approximant `Lₙ` with `‖S - Lₙ‖ < aₙ(S) + 1/(n+1)`; the
converse uses `approximationNumber_le_norm_sub` and squeeze. -/
theorem isApproximable_iff_existsLimit (S : X →L[𝕜] Y) :
    IsApproximable S ↔
      ∃ L : ℕ → X →L[𝕜] Y, (∀ n, (L n).rank ≤ (n : Cardinal)) ∧
        Tendsto (fun n => ‖S - L n‖) atTop (𝓝 0) := by
  constructor
  · -- Forward: pick a near-inf approximant for each `n`.
    intro hS
    have h_choose : ∀ n : ℕ, ∃ L : X →L[𝕜] Y,
        L.rank ≤ (n : Cardinal) ∧
          ‖S - L‖ < SNumbers.approximationNumber S n + 1 / (n + 1) := by
      intro n
      have hε : (0 : ℝ) < 1 / (n + 1) := by positivity
      have h_lt : SNumbers.approximationNumber S n <
                    SNumbers.approximationNumber S n + 1 / (n + 1) := by linarith
      obtain ⟨r, hr_mem, hr_lt⟩ :=
        (csInf_lt_iff (SNumbers.bddBelow_approximationSet S n)
          (SNumbers.approximationSet_nonempty S n)).mp h_lt
      obtain ⟨L, hL_rank, rfl⟩ := hr_mem
      exact ⟨L, hL_rank, hr_lt⟩
    choose L hL_rank hL_lt using h_choose
    refine ⟨L, hL_rank, ?_⟩
    -- Squeeze: 0 ≤ ‖S - Lₙ‖ ≤ aₙ(S) + 1/(n+1) → 0.
    have h_nonneg : ∀ n, (0 : ℝ) ≤ ‖S - L n‖ := fun n => norm_nonneg _
    have h_bd : ∀ n, ‖S - L n‖ ≤
                  SNumbers.approximationNumber S n + 1 / (n + 1) :=
      fun n => (hL_lt n).le
    have h_one_div : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_lim :
        Tendsto (fun n : ℕ => SNumbers.approximationNumber S n + 1 / (n + 1))
          atTop (𝓝 0) := by simpa using hS.add h_one_div
    exact squeeze_zero h_nonneg h_bd h_lim
  · -- Converse: aₙ(S) ≤ ‖S - Lₙ‖ → 0.
    rintro ⟨L, hL_rank, hL_lim⟩
    have h_nonneg : ∀ n, 0 ≤ SNumbers.approximationNumber S n :=
      fun n => SNumbers.approximationNumber_nonneg _ n
    have h_bd : ∀ n, SNumbers.approximationNumber S n ≤ ‖S - L n‖ :=
      fun n => SNumbers.approximationNumber_le_norm_sub (hL_rank n)
    exact squeeze_zero h_nonneg h_bd hL_lim

/-! ### Finite-rank operators are approximable -/

/-- Every finite-rank continuous linear map is approximable: by (S4),
`aₙ(S) = 0` for all `n ≥ rank S`, hence `aₙ(S) → 0`. -/
theorem IsApproximable.of_rank_le {S : X →L[𝕜] Y} {N : ℕ}
    (hS : S.rank ≤ (N : Cardinal)) : IsApproximable S := by
  -- `aₙ S = 0` for `n ≥ N`, so the sequence is eventually zero.
  have h_eventually :
      (fun n => SNumbers.approximationNumber S n) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact SNumbers.approximationNumber_eq_zero_of_rank_le
      (hS.trans (by exact_mod_cast hn))
  exact (tendsto_congr' h_eventually).mpr tendsto_const_nhds

/-! ### Closure under linear-space operations -/

/-- Zero is approximable. -/
theorem isApproximable_zero : IsApproximable (0 : X →L[𝕜] Y) :=
  IsApproximable.of_rank_le (N := 0) (by simp)

/-- Scaling by a constant preserves approximability. The bound
`aₙ(c • S) ≤ ‖c‖ · aₙ(S)` follows from the per-approximant inequality
`‖c • S - c • L‖ = ‖c‖ · ‖S - L‖`, taken to the infimum over rank-`≤ n`
approximants `L`. -/
theorem IsApproximable.smul (c : 𝕜) {S : X →L[𝕜] Y}
    (hS : IsApproximable S) :
    IsApproximable (c • S) := by
  -- Pointwise bound: `aₙ(c • S) ≤ ‖c‖ * aₙ(S)`.
  have h_bd : ∀ n, SNumbers.approximationNumber (c • S) n ≤
                    ‖c‖ * SNumbers.approximationNumber S n := by
    intro n
    have h_nonneg : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
    -- Per-approximant: each `L : rank ≤ n` of `S` gives `c • L` of rank ≤ n
    -- approximating `c • S`, with residual `‖c‖ · ‖S - L‖`.
    have hkey : ∀ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) →
        SNumbers.approximationNumber (c • S) n ≤ ‖c‖ * ‖S - L‖ := by
      intro L hL
      have h_range_le :
          LinearMap.range ((c • L : X →L[𝕜] Y) : X →ₗ[𝕜] Y) ≤
            LinearMap.range (L : X →ₗ[𝕜] Y) := by
        rintro y ⟨x, hx⟩
        -- `hx : (c • L) x = y` reduces to `c • (L x) = y`, so
        -- `y = c • (L x) ∈ range L` by `Submodule.smul_mem`.
        have hx' : c • (L x) = y := hx
        rw [← hx']
        exact (LinearMap.range (L : X →ₗ[𝕜] Y)).smul_mem c
          (LinearMap.mem_range_self _ x)
      have h_rank : (c • L).rank ≤ (n : Cardinal) :=
        (Submodule.rank_mono h_range_le).trans hL
      have h_eq : c • S - c • L = c • (S - L) := (smul_sub c S L).symm
      have h_norm : ‖c • S - c • L‖ = ‖c‖ * ‖S - L‖ := by
        rw [h_eq, norm_smul]
      have h_residual : SNumbers.approximationNumber (c • S) n
                          ≤ ‖c • S - c • L‖ :=
        SNumbers.approximationNumber_le_norm_sub h_rank
      rwa [h_norm] at h_residual
    -- Lift to the infimum, mirroring `approximationNumber_comp_comp_le`.
    show _ ≤ ‖c‖ • SNumbers.approximationNumber S n
    show _ ≤ ‖c‖ • sInf (SNumbers.approximationSet S n)
    rw [← Real.sInf_smul_of_nonneg h_nonneg]
    refine le_csInf ((SNumbers.approximationSet_nonempty S n).image _) ?_
    rintro _ ⟨_, ⟨L, hL, rfl⟩, rfl⟩
    exact hkey L hL
  -- Squeeze: `0 ≤ aₙ(c•S) ≤ ‖c‖ · aₙ(S) → 0`.
  have h_nonneg : ∀ n, 0 ≤ SNumbers.approximationNumber (c • S) n :=
    fun n => SNumbers.approximationNumber_nonneg _ n
  have h_lim : Tendsto (fun n => ‖c‖ * SNumbers.approximationNumber S n)
                atTop (𝓝 0) := by
    simpa using hS.const_mul ‖c‖
  exact squeeze_zero h_nonneg h_bd h_lim

/-- Negation preserves approximability, as the special case `c = -1` of
`IsApproximable.smul`. -/
theorem IsApproximable.neg {S : X →L[𝕜] Y} (hS : IsApproximable S) :
    IsApproximable (-S) := by
  have h := hS.smul (-1 : 𝕜)
  rwa [neg_one_smul] at h

/-- Sum of approximable operators is approximable. The proof goes through
the equivalent finite-rank-limit characterisation
(`isApproximable_iff_existsLimit`): given approximating sequences
`Lₘ → S` and `Kₘ → T`, the approximant
`Lₙ/₂ + Kₙ₋ₙ/₂ : X →L[𝕜] Y` has rank `≤ ⌊n/2⌋ + ⌈n/2⌉ = n` (using
`LinearMap.rank_add_le`) and residual `≤ ‖S - Lₙ/₂‖ + ‖T - Kₙ₋ₙ/₂‖ → 0`. -/
theorem IsApproximable.add {S T : X →L[𝕜] Y}
    (hS : IsApproximable S) (hT : IsApproximable T) :
    IsApproximable (S + T) := by
  rw [isApproximable_iff_existsLimit] at hS hT ⊢
  obtain ⟨L, hL_rank, hL_lim⟩ := hS
  obtain ⟨K, hK_rank, hK_lim⟩ := hT
  refine ⟨fun n => L (n / 2) + K (n - n / 2), ?_, ?_⟩
  · -- rank `Lₙ/₂ + Kₙ₋ₙ/₂` ≤ n/2 + (n - n/2) = n.
    intro n
    have h_split : n / 2 + (n - n / 2) = n :=
      Nat.add_sub_cancel' (Nat.div_le_self n 2)
    have h_rank_add :
        (L (n / 2) + K (n - n / 2)).rank ≤
          (L (n / 2)).rank + (K (n - n / 2)).rank :=
      LinearMap.rank_add_le _ _
    calc (L (n / 2) + K (n - n / 2)).rank
        ≤ (L (n / 2)).rank + (K (n - n / 2)).rank := h_rank_add
      _ ≤ ((n / 2 : ℕ) : Cardinal) + ((n - n / 2 : ℕ) : Cardinal) :=
          add_le_add (hL_rank _) (hK_rank _)
      _ = ((n / 2 + (n - n / 2) : ℕ) : Cardinal) := by push_cast; rfl
      _ = (n : Cardinal) := by rw [h_split]
  · -- ‖(S+T) - (Lₙ/₂ + Kₙ₋ₙ/₂)‖ ≤ ‖S - Lₙ/₂‖ + ‖T - Kₙ₋ₙ/₂‖ → 0.
    have h_norm_bd : ∀ n, ‖(S + T) - (L (n / 2) + K (n - n / 2))‖ ≤
                            ‖S - L (n / 2)‖ + ‖T - K (n - n / 2)‖ := by
      intro n
      have h_eq : (S + T) - (L (n / 2) + K (n - n / 2)) =
                    (S - L (n / 2)) + (T - K (n - n / 2)) := by abel
      rw [h_eq]; exact norm_add_le _ _
    -- Both subsequences `n/2` and `n - n/2` diverge to ∞.
    have h_div : Tendsto (fun n : ℕ => n / 2) atTop atTop :=
      Nat.tendsto_div_const_atTop (by norm_num)
    have h_sub : Tendsto (fun n : ℕ => n - n / 2) atTop atTop := by
      have h_dom : ∀ n : ℕ, n / 2 ≤ n - n / 2 := fun n => by omega
      exact tendsto_atTop_mono h_dom h_div
    have h_lim_L : Tendsto (fun n => ‖S - L (n / 2)‖) atTop (𝓝 0) :=
      hL_lim.comp h_div
    have h_lim_K : Tendsto (fun n => ‖T - K (n - n / 2)‖) atTop (𝓝 0) :=
      hK_lim.comp h_sub
    have h_lim_sum :
        Tendsto (fun n => ‖S - L (n / 2)‖ + ‖T - K (n - n / 2)‖)
          atTop (𝓝 0) := by simpa using h_lim_L.add h_lim_K
    exact squeeze_zero (fun _ => norm_nonneg _) h_norm_bd h_lim_sum

/-! ### Topological closure -/

/-- Approximable operators form a closed subset of `X →L[𝕜] Y`.

For any `S` in the closure of the approximable operators and `ε > 0`:
* pick approximable `T` with `‖S - T‖ < ε/2`;
* pick `N` with `aₙ(T) < ε/2` for all `n ≥ N`;
* by (S2), `aₙ(S) ≤ aₙ(T) + ‖S - T‖ < ε` for `n ≥ N`. -/
theorem isClosed_isApproximable :
    IsClosed { S : X →L[𝕜] Y | IsApproximable S } := by
  rw [← closure_subset_iff_isClosed]
  intro S hS_in_closure
  rw [Metric.mem_closure_iff] at hS_in_closure
  show IsApproximable S
  unfold IsApproximable
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: pick approximable `T` with `‖S - T‖ < ε/2`.
  obtain ⟨T, hT_approx, hT_dist⟩ := hS_in_closure (ε / 2) (by linarith)
  have h_dist_norm : ‖S - T‖ < ε / 2 := by
    rw [dist_eq_norm] at hT_dist; exact hT_dist
  -- Step 2: pick `N` such that `aₙ(T) < ε/2` for all `n ≥ N`.
  have hT_approx' : Tendsto (SNumbers.approximationNumber T) atTop (𝓝 0) :=
    hT_approx
  rw [Metric.tendsto_atTop] at hT_approx'
  obtain ⟨N, hN⟩ := hT_approx' (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  -- Step 3: combine via (S2): `aₙ(S) ≤ aₙ(T) + ‖S - T‖`.
  have h_eq : S = T + (S - T) := by abel
  have h_bd : SNumbers.approximationNumber S n ≤
                SNumbers.approximationNumber T n + ‖S - T‖ := by
    nth_rewrite 1 [h_eq]
    exact SNumbers.approximationNumber_add_le _ _ n
  have h_aT : SNumbers.approximationNumber T n < ε / 2 := by
    have h := hN n hn
    rwa [Real.dist_0_eq_abs,
         abs_of_nonneg (SNumbers.approximationNumber_nonneg _ _)] at h
  rw [Real.dist_0_eq_abs,
      abs_of_nonneg (SNumbers.approximationNumber_nonneg _ _)]
  linarith

/-! ### Closure under composition -/

/-- Pre/post-composition with bounded operators preserves approximability:
this is the *ideal property* for the class of approximable operators,
inherited from the (S3) ideal property of the approximation numbers. -/
theorem IsApproximable.comp_comp {S : X →L[𝕜] Y}
    (A : W →L[𝕜] X) (B : Y →L[𝕜] Z) (hS : IsApproximable S) :
    IsApproximable (B.comp (S.comp A)) := by
  -- Bound: aₙ(BSA) ≤ ‖B‖ · aₙ(S) · ‖A‖, then squeeze.
  have h_bd : ∀ n, SNumbers.approximationNumber (B.comp (S.comp A)) n ≤
                    ‖B‖ * SNumbers.approximationNumber S n * ‖A‖ :=
    fun n => SNumbers.approximationNumber_comp_comp_le A S B n
  have h_nonneg : ∀ n, 0 ≤ SNumbers.approximationNumber (B.comp (S.comp A)) n :=
    fun n => SNumbers.approximationNumber_nonneg _ n
  have h_lim :
      Tendsto (fun n => ‖B‖ * SNumbers.approximationNumber S n * ‖A‖)
        atTop (𝓝 0) := by
    have h1 := (hS.const_mul ‖B‖).mul_const ‖A‖
    simpa using h1
  exact squeeze_zero h_nonneg h_bd h_lim

theorem IsApproximable.comp_left {S : X →L[𝕜] Y}
    (B : Y →L[𝕜] Z) (hS : IsApproximable S) :
    IsApproximable (B.comp S) := by
  -- `B.comp S = B.comp (S.comp id_X)`, so this is a special case.
  have h := hS.comp_comp (ContinuousLinearMap.id 𝕜 X) B
  simpa using h

theorem IsApproximable.comp_right {S : X →L[𝕜] Y}
    (A : W →L[𝕜] X) (hS : IsApproximable S) :
    IsApproximable (S.comp A) := by
  -- `S.comp A = id_Y.comp (S.comp A)`, so this is a special case.
  have h := hS.comp_comp A (ContinuousLinearMap.id 𝕜 Y)
  simpa using h

/-! ### Approximable ⇒ compact -/

section ApproximableImpliesCompact
-- Need `[LocallyCompactSpace 𝕜]` so finite-dim `𝕜`-spaces are proper / locally
-- compact (via `FiniteDimensional.proper`); and `[CompleteSpace Y]` to apply
-- `isCompactOperator_of_tendsto`. Both hold automatically over `RCLike 𝕜`
-- with a Hilbert codomain.
variable [LocallyCompactSpace 𝕜] [CompleteSpace Y]

/-- **Approximable ⇒ compact.** Every operator approximable in operator
norm by finite-rank ones is compact:

* a finite-rank `Lₙ : X →L[𝕜] Y` factors as `(range Lₙ).subtypeL ∘ Lₙ'`
  where `Lₙ' : X →L[𝕜] (range Lₙ)` lands in a finite-dimensional, hence
  locally compact, subspace; hence `Lₙ` is compact
  (`isCompactOperator_of_locallyCompactSpace_dom`);
* compactness is preserved under operator-norm limits
  (`isCompactOperator_of_tendsto`).
-/
theorem IsApproximable.isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsApproximable S) : IsCompactOperator S := by
  rw [isApproximable_iff_existsLimit] at hS
  obtain ⟨L, hL_rank, hL_lim⟩ := hS
  -- Convert `‖S - L n‖ → 0` into `Tendsto L atTop (𝓝 S)` (op-norm convergence).
  have h_tendsto : Tendsto L atTop (𝓝 S) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_swap : (fun n => ‖L n - S‖) = (fun n => ‖S - L n‖) := by
      funext n; exact norm_sub_rev _ _
    rw [h_swap]; exact hL_lim
  -- Each `L n` is compact (finite-rank → compact).
  have h_each_compact : ∀ n, IsCompactOperator (L n) := by
    intro n
    -- `V := range (L n)` is finite-dim, hence proper / locally compact.
    set V : Submodule 𝕜 Y := LinearMap.range (L n : X →ₗ[𝕜] Y) with hV_def
    have h_rank_V_lt : Module.rank 𝕜 V < Cardinal.aleph0 :=
      lt_of_le_of_lt (hL_rank n) Cardinal.natCast_lt_aleph0
    have : FiniteDimensional 𝕜 V := Module.rank_lt_aleph0_iff.mp h_rank_V_lt
    have : ProperSpace V := FiniteDimensional.proper 𝕜 V
    -- Codrestrict `L n` to `V`.
    have hLn_mem : ∀ x, L n x ∈ V := fun x => ⟨x, rfl⟩
    let Ln' : X →L[𝕜] V := (L n).codRestrict V hLn_mem
    -- `Ln'` is compact (target locally compact).
    have h_Ln'_compact : IsCompactOperator Ln' :=
      isCompactOperator_of_locallyCompactSpace_dom Ln'
    -- `(V.subtypeL).comp Ln' = L n` as functions, so post-composition recovers `L n`.
    have h_compact_clm : IsCompactOperator (V.subtypeL.comp Ln') :=
      h_Ln'_compact.clm_comp V.subtypeL
    have h_eq : V.subtypeL.comp Ln' = L n := by ext x; rfl
    rw [h_eq] at h_compact_clm
    exact h_compact_clm
  -- Limit of compact operators is compact (closed-subset argument).
  exact isCompactOperator_of_tendsto h_tendsto
    (Filter.Eventually.of_forall h_each_compact)

/-- **Finite rank ⇒ compact.** An operator of rank at most `m` is approximable
(`IsApproximable.of_rank_le`), hence compact. -/
theorem isCompactOperator_of_rank_le {S : X →L[𝕜] Y} {m : ℕ}
    (hS : S.rank ≤ (m : Cardinal)) : IsCompactOperator S :=
  (IsApproximable.of_rank_le hS).isCompactOperator

end ApproximableImpliesCompact

end SVD

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
