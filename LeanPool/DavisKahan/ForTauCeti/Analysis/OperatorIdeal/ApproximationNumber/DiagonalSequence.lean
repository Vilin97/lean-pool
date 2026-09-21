/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti, roadmap topic T09.  Formalized by Claude Opus 5
(claude-opus-5[1m]).
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# The infinite-dimensional diagonal acceptance example

Acceptance example (6) of `TauCetiRoadmap/OperatorTheory/OperatorIdeals/README.md`: a
diagonal operator on `ℓ²` whose coefficients tend to zero has vanishing
approximation numbers, hence is compact.

* `TauCeti.diagOpLp` — multiplication by a bounded sequence, as an operator on
  `lp (fun _ : ℕ => 𝕜) 2`;
* `TauCeti.tendsto_approximationNumber_diagOpLp` — `cₙ → 0` gives `aₙ(T) → 0`;
* `TauCeti.isCompactOperator_diagOpLp` — hence `T` is compact.

## Which route this takes, and why

The roadmap offers two.  One builds the operator, proves it compact, and cites
`tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator`.  The other
truncates the diagonal directly: the `N`-th truncation has rank at most `N`, and
`‖T - Tₙ‖` is controlled by the tail of the coefficient sequence.

**This file takes the second**, because it is the one that tests what the example
is for.  The approximation numbers of a diagonal operator *are* its tail
suprema, so a proof that goes through compactness proves the statement without
ever touching the reason it is true.  Taking the truncation route also inverts
the dependency: compactness becomes a corollary
(`isCompactOperator_diagOpLp`, by `isCompactOperator_of_tendsto_approximationNumber`)
rather than a hypothesis, so the example exercises the finite-rank side of the
API rather than Mathlib's closure argument.

Only an upper bound is proved.  The matching lower bound `aₙ(T) = ‖c‖_{[n,∞)}`
needs the coefficients ordered, which the example does not assume; the finite
ordered case is `ContinuousLinearMap.approximationNumber_diagOp` in
`DiagonalExample.lean`.

## Sources

*Follows nothing in particular*: this is a test of the library's own API against
a concrete operator the roadmap names.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib and sibling `ForTauCeti`
  modules.
-/

public section

namespace TauCeti

open Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Multiplication of the `i`-th coordinate by `c i`, as a continuous linear map
on `𝕜`.  The building block of `diagOpLp`; separated out so that the operator and
its truncations differ only in the family, not in the construction. -/
noncomputable def diagCoord (a : 𝕜) : 𝕜 →L[𝕜] 𝕜 := a • ContinuousLinearMap.id 𝕜 𝕜

/-- The coordinate map acts by multiplication. -/
@[simp] theorem diagCoord_apply (a x : 𝕜) : diagCoord a x = a * x := by
  simp [diagCoord]

/-- The coordinate map has norm at most `‖a‖`; equality holds, but only the bound
is needed to build the operator. -/
theorem norm_diagCoord_le (a : 𝕜) : ‖diagCoord a‖ ≤ ‖a‖ := by
  refine (norm_smul_le a (ContinuousLinearMap.id 𝕜 𝕜)).trans ?_
  simp

/-- **The diagonal operator on `ℓ²` with coefficient sequence `c`.**

`K` bounds the coefficients; the operator norm is at most `K`.  The sequence is
not assumed monotone, nonnegative or real — only bounded, which is what
boundedness of the operator needs. -/
noncomputable def diagOpLp (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K) (hc : ∀ i, ‖c i‖ ≤ K) :
    lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  lp.mapCLM 2 (fun i => diagCoord (c i)) hK fun i => (norm_diagCoord_le (c i)).trans (hc i)

/-- The diagonal operator multiplies the `i`-th coordinate by `c i`. -/
@[simp] theorem diagOpLp_apply (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K) (hc : ∀ i, ‖c i‖ ≤ K)
    (x : lp (fun _ : ℕ => 𝕜) 2) (i : ℕ) :
    (diagOpLp c hK hc x) i = c i * x i := by
  simp [diagOpLp]

/-- The `N`-th truncation: the same diagonal, with every coefficient from `N` on
replaced by zero. -/
noncomputable def truncDiagOpLp (c : ℕ → 𝕜) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) :
    lp (fun _ : ℕ => 𝕜) 2 →L[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
  lp.mapCLM 2 (fun i => if i < N then diagCoord (c i) else 0) hK fun i => by
    by_cases h : i < N
    · simpa [h] using (norm_diagCoord_le (c i)).trans (hc i)
    · simpa [h] using hK

/-- The truncation agrees with the operator below `N` and vanishes from `N` on. -/
@[simp] theorem truncDiagOpLp_apply (c : ℕ → 𝕜) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (x : lp (fun _ : ℕ => 𝕜) 2) (i : ℕ) :
    (truncDiagOpLp c N hK hc x) i = if i < N then c i * x i else 0 := by
  by_cases h : i < N <;> simp [truncDiagOpLp, h]

/-- The truncation is supported on the first `N` coordinates: it is the finite
combination of the standard basis vectors there. -/
theorem truncDiagOpLp_eq_sum (c : ℕ → 𝕜) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (x : lp (fun _ : ℕ => 𝕜) 2) :
    truncDiagOpLp c N hK hc x =
      ∑ i ∈ Finset.range N, (c i * x i) • lp.single 2 i (1 : 𝕜) := by
  classical
  refine lp.ext (funext fun j => ?_)
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.coeFn_single, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    truncDiagOpLp_apply]
  rw [Finset.sum_ite_eq (Finset.range N) j fun i => c i * x i]
  simp [Finset.mem_range]

/-- **The truncation has rank at most `N`.**  Its range lies in the span of the
first `N` standard basis vectors, and a span of `N` vectors has rank at most
`N` — no basis or dimension theory beyond that. -/
theorem rank_truncDiagOpLp_le (c : ℕ → 𝕜) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) :
    (truncDiagOpLp c N hK hc).rank ≤ (N : Cardinal) := by
  classical
  set s : Finset (lp (fun _ : ℕ => 𝕜) 2) :=
    (Finset.range N).image (fun i : ℕ => lp.single 2 i (1 : 𝕜)) with hs
  have hrange : LinearMap.range (truncDiagOpLp c N hK hc).toLinearMap ≤
      Submodule.span 𝕜 (s : Set (lp (fun _ : ℕ => 𝕜) 2)) := by
    rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, truncDiagOpLp_eq_sum]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi))
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (s : Set (lp (fun _ : ℕ => 𝕜) 2))) :=
    FiniteDimensional.span_of_finite 𝕜 s.finite_toSet
  have hcard : s.card ≤ N := (Finset.card_image_le).trans (by simp)
  have hfin : Module.finrank 𝕜 (Submodule.span 𝕜 (s : Set (lp (fun _ : ℕ => 𝕜) 2))) ≤ N :=
    (finrank_span_finset_le_card s).trans hcard
  calc (truncDiagOpLp c N hK hc).rank
      ≤ Module.rank 𝕜 (Submodule.span 𝕜 (s : Set (lp (fun _ : ℕ => 𝕜) 2))) :=
        Submodule.rank_mono hrange
    _ = (Module.finrank 𝕜 (Submodule.span 𝕜 (s : Set (lp (fun _ : ℕ => 𝕜) 2))) : Cardinal) :=
        (Module.finrank_eq_rank _ _).symm
    _ ≤ (N : Cardinal) := by exact_mod_cast hfin

/-- **The truncation error is the tail of the coefficient sequence.**  If every
coefficient from `N` on is at most `ε`, the truncation approximates the operator
to within `ε`.

Only this direction is needed for `aₙ(T) → 0`, and it is where the `ℓ²`
structure does its work: the pointwise bound `‖cᵢxᵢ‖ ≤ ε‖xᵢ‖` lifts to the norm
by comparison with `ε • x`, which is what `lp.norm_mono` says. -/
theorem norm_sub_truncDiagOpLp_le (c : ℕ → 𝕜) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) {ε : ℝ} (hε : 0 ≤ ε) (htail : ∀ i, N ≤ i → ‖c i‖ ≤ ε) :
    ‖diagOpLp c hK hc - truncDiagOpLp c N hK hc‖ ≤ ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ hε fun x => ?_
  have key : ∀ i, ‖((diagOpLp c hK hc - truncDiagOpLp c N hK hc) x) i‖ ≤
      ‖(((ε : 𝕜) • x : lp (fun _ : ℕ => 𝕜) 2)) i‖ := by
    intro i
    have hsub : ((diagOpLp c hK hc - truncDiagOpLp c N hK hc) x) i =
        c i * x i - (if i < N then c i * x i else 0) := by
      simp
    have hrhs : ‖(((ε : 𝕜) • x : lp (fun _ : ℕ => 𝕜) 2)) i‖ = ε * ‖x i‖ := by
      rw [lp.coeFn_smul]
      simp [abs_of_nonneg hε]
    rw [hsub, hrhs]
    by_cases h : i < N
    · simp [h, mul_nonneg hε (norm_nonneg _)]
    · rw [ite_eq_right h, sub_zero, norm_mul]
      exact mul_le_mul_of_nonneg_right (htail i (Nat.le_of_not_lt h)) (norm_nonneg _)
  calc ‖(diagOpLp c hK hc - truncDiagOpLp c N hK hc) x‖
      ≤ ‖((ε : 𝕜) • x : lp (fun _ : ℕ => 𝕜) 2)‖ := lp.norm_mono (by norm_num) key
    _ = ε * ‖x‖ := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hε]

/-- **Acceptance example (6): a diagonal operator with coefficients tending to
zero has vanishing approximation numbers.**

The proof is the truncation argument in one step: given `ε`, the coefficients are
eventually within `ε`, and truncating there gives a competitor of rank at most
`N`, admissible at every index `n ≥ N`.  Antitonicity of `aₙ` is not needed —
the rank bound `N ≤ n` is what makes the truncation admissible at `n`. -/
theorem tendsto_approximationNumber_diagOpLp (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (hc0 : Tendsto c atTop (𝓝 0)) :
    Tendsto (diagOpLp c hK hc).approximationNumber atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hc0 (ε / 2) (half_pos hε)
  have htail : ∀ i, N ≤ i → ‖c i‖ ≤ ε / 2 := fun i hi => by
    simpa [dist_eq_norm] using (hN i hi).le
  refine ⟨N, fun n hn => ?_⟩
  have hadm : (truncDiagOpLp c N hK hc).rank ≤ (n : Cardinal) :=
    (rank_truncDiagOpLp_le c N hK hc).trans (by exact_mod_cast hn)
  have hbound : (diagOpLp c hK hc).approximationNumber n ≤ ε / 2 :=
    ((diagOpLp c hK hc).approximationNumber_le_norm_sub hadm).trans
      (norm_sub_truncDiagOpLp_le c N hK hc (half_pos hε).le htail)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg ((diagOpLp c hK hc).approximationNumber_nonneg n)]
  linarith

/-- **The same operator is compact**, and on this route that is a corollary
rather than an input: vanishing approximation numbers give compactness through
`isCompactOperator_of_tendsto_approximationNumber`, with no closure argument and
no spectral theory.

`[ProperSpace 𝕜]` is inherited from that theorem, where it is what the finite-rank
lemma needs; `ℝ` and `ℂ` both satisfy it, so it costs the example nothing. -/
theorem isCompactOperator_diagOpLp [ProperSpace 𝕜] (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (hc0 : Tendsto c atTop (𝓝 0)) :
    IsCompactOperator (diagOpLp c hK hc) :=
  (diagOpLp c hK hc).isCompactOperator_of_tendsto_approximationNumber
    (tendsto_approximationNumber_diagOpLp c hK hc hc0)

/-- **The approximation numbers of a diagonal operator are bounded by its
coefficients**, when those are antitone in norm.

The competitor is the truncation the module already builds: `truncDiagOpLp c n`
has rank at most `n` by `rank_truncDiagOpLp_le`, and misses by at most the tail
`sup_{i ≥ n} ‖cᵢ‖ = ‖cₙ‖` by `norm_sub_truncDiagOpLp_le`.

`tendsto_approximationNumber_diagOpLp` already runs exactly this argument to get
the limit; **it never records the value, which is what
`{lane:FTC-DIAGEXACT}` exists to supply.** -/
theorem approximationNumber_diagOpLp_le (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (hanti : Antitone fun i => ‖c i‖) (n : ℕ) :
    (diagOpLp c hK hc).approximationNumber n ≤ ‖c n‖ := by
  refine le_trans
    (ContinuousLinearMap.approximationNumber_le_norm_sub _ (rank_truncDiagOpLp_le c n hK hc)) ?_
  exact norm_sub_truncDiagOpLp_le c n hK hc (norm_nonneg _) fun i hi => hanti hi

/-- Coordinates beyond `n` vanish on the span of the first `n + 1` basis vectors. -/
theorem apply_eq_zero_of_mem_span_single {n : ℕ}
    {x : lp (fun _ : ℕ => 𝕜) 2}
    (hx : x ∈ Submodule.span 𝕜 (Set.range fun i : Fin (n + 1) =>
      lp.single 2 (i : ℕ) (1 : 𝕜)))
    {i : ℕ} (hi : n < i) : x i = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have hne : (j : ℕ) ≠ i := by omega
      simp [lp.single_apply, hne]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

/-- **The matching lower bound**: on the span of the first `n + 1` basis vectors
the diagonal operator is bounded below by `‖cₙ‖`.

`lp.norm_mono` does the work, one inequality reversed from
`norm_sub_truncDiagOpLp_le`: compare `‖cₙ‖ • x` against `D x` coordinatewise,
where the hypothesis holds for `i ≤ n` by antitonicity and **vacuously for
`i > n` because `x` lies in the span**. -/
theorem le_approximationNumber_diagOpLp (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (hanti : Antitone fun i => ‖c i‖) (n : ℕ) :
    ‖c n‖ ≤ (diagOpLp c hK hc).approximationNumber n := by
  classical
  refine ContinuousLinearMap.le_approximationNumber_of_linearIndependent _ n
    (fun i : Fin (n + 1) =>
      (lp.single 2 (i : ℕ) (1 : 𝕜) : lp (fun _ : ℕ => 𝕜) 2)) ?_ ?_
  · -- The basis vectors are linearly independent: they have disjoint supports.
    refine linearIndependent_iff'.2 fun s g hg j hj => ?_
    have hcoord := congrArg (fun y : lp (fun _ : ℕ => 𝕜) 2 => y (j : ℕ)) hg
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, lp.coeFn_zero, Pi.zero_apply] at hcoord
    rw [Finset.sum_eq_single j] at hcoord
    · simpa using hcoord
    · intro k _ hkj
      have hne : (k : ℕ) ≠ (j : ℕ) := fun h => hkj (Fin.ext h)
      simp [lp.single_apply, hne]
    · intro h; exact absurd hj h
  · intro x hx hx1
    have hpt : ∀ i, ‖(((‖c n‖ : 𝕜)) • x) i‖ ≤ ‖(diagOpLp c hK hc x) i‖ := by
      intro i
      rw [lp.coeFn_smul]
      simp only [Pi.smul_apply, smul_eq_mul, diagOpLp_apply, norm_mul,
        RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg (c n))]
      by_cases hi : i ≤ n
      · exact mul_le_mul_of_nonneg_right (hanti hi) (norm_nonneg _)
      · rw [apply_eq_zero_of_mem_span_single hx (Nat.lt_of_not_le hi)]
        simp
    have hnorm := lp.norm_mono (p := 2) (by norm_num) hpt
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg (c n)), hx1,
      mul_one] at hnorm
    exact hnorm

/-- **The approximation numbers of a diagonal operator are its coefficients.**

This is the identity `{lane:FTC-DIAGEXACT}` was posted for, and the one
`symmetricGaugeFamily_injective` needs: it gives, for every antitone nonnegative
bounded sequence, an operator realising it as an approximation-number sequence. -/
theorem approximationNumber_diagOpLp (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ‖c i‖ ≤ K) (hanti : Antitone fun i => ‖c i‖) (n : ℕ) :
    (diagOpLp c hK hc).approximationNumber n = ‖c n‖ :=
  le_antisymm (approximationNumber_diagOpLp_le c hK hc hanti n)
    (le_approximationNumber_diagOpLp c hK hc hanti n)

/-- **A diagonal operator with real coefficients is self-adjoint.**

The inner product on `lp (fun _ : ℕ => 𝕜) 2` is the coordinatewise sum, and on each
coordinate the operator is multiplication by `c i`, which moves across `⟪·, ·⟫` exactly
when `c i` is fixed by the star operation.  No summability argument is needed beyond the
one already inside `lp.inner_eq_tsum`, because the two sums are compared term by term. -/
theorem isSelfAdjoint_diagOpLp (c : ℕ → 𝕜) {K : ℝ} (hK : 0 ≤ K) (hc : ∀ i, ‖c i‖ ≤ K)
    (hreal : ∀ i, (starRingEnd 𝕜) (c i) = c i) :
    IsSelfAdjoint (diagOpLp c hK hc) := by
  have hsymm : (diagOpLp c hK hc).IsSymmetric := by
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    simp only [ContinuousLinearMap.coe_coe, diagOpLp_apply, RCLike.inner_apply, map_mul,
      hreal i]
    ring
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr hsymm.clm_adjoint_eq

end TauCeti
