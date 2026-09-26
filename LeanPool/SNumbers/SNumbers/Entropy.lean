/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.SNumbers.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Entropy numbers

The (dyadic) **entropy numbers** of a bounded linear operator `S : X →L[𝕜] Y`
are

`e_n S = inf { ε > 0 : S(B_X) can be covered by at most 2ⁿ closed balls of
radius ε in Y }`,

where `B_X` is the closed unit ball of `X` and the centres of the covering
balls may be arbitrary points of `Y`. As everywhere in this development the
indexing is 0-based, so `e_0` allows a single ball.

The entropy numbers measure *compactness*: their definition quantifies the
"finite subcover definition" of compactness. An operator `S` is compact
precisely when `e_n S → 0`.
This equivalence holds on arbitrary Banach spaces, and the same is true of the
Gelfand and Kolmogorov numbers (`AddOns.Compact`, via the comparisons in
`SNumbers.EntropyBounds`). For the approximation numbers the corresponding
statement fails in general: a compact operator into a space without the
approximation property need not be a limit of finite-rank operators.
But it is available on Hilbert spaces (`AddOns.Compact`).

## Entropy numbers are not s-numbers

Over `ℝ` or `ℂ`, entropy numbers satisfy all of Pietsch's axioms but two:

* (S4) rank fails: an operator `S ≠ 0` of rank `≤ n` still has `e_n S > 0`,
  because `e_n S = 0` would cover `S(B_X)` by `2ⁿ` balls of arbitrarily small
  radius and hence leave it at most `2ⁿ` points, while the image of the unit
  ball is infinite.
* (S5) norming fails from `n = 2` on: covering the Euclidean unit ball of
  `ℝ^d` by balls of radius below `1` takes `d + 1` of them but no more, and
  `2ⁿ ≥ n + 2` exactly from there, so `e_n (id_{ℓ₂ⁿ⁺¹}) < 1`.

A sequence that keeps the other properties and drops these two is called a
**pseudo-s-number** sequence (Pietsch, *Operator ideals*, 12.1.1).

Those other properties come from two inequalities, both proved below:
additivity `e_{n+m}(S + T) ≤ e_n S + e_m T` (`entropyNumber_additive`) and
multiplicativity `e_{n+m}(B ∘ S) ≤ e_n B · e_m S`
(`entropyNumber_multiplicative`). Specialising one index to `0` and using
`e_0 ≤ ‖·‖` turns them into (S2) and (S3) (`entropyNumber_add_le`,
`entropyNumber_comp_comp_le`); with (S1b) monotonicity and (S1c)
non-negativity that covers (S1b)–(S3).

Of these, only multiplicativity constrains the scalar field: it needs dense
norm values, `DenselyNormedField 𝕜`, and therefore lives in a separate
section, whereas everything else holds over an arbitrary
`NontriviallyNormedField`. The reason is that a covering of `B(B_Y)` has to be
transported to a ball of radius `δ`, so a vector `u` with `‖u‖ ≤ δ` must be
written as `u = c • w` with `‖w‖ ≤ 1` and `‖c‖` close to `δ`. Norm values are
dense in `ℝ`, `ℂ` and every `RCLike` field, and discrete in `ℚ_p`.

The remaining axiom (S1a) `e_0 S = ‖S‖` is not formalised: it holds over `ℝ`
and `ℂ`, is false in general, and only `e_n S ≤ ‖S‖` is proved below, which is
all the corollaries need. Over `ℝ` or `ℂ` it follows from the symmetry of
`S(B_X)`, as `2‖Sx‖ = ‖(Sx - y) - (-Sx - y)‖ ≤ 2ε`, and that last step divides
by `‖(2 : 𝕜)‖`, which need not be `2`. Without dense norm values the statement
itself fails: over `ℚ_p` take `X = ℚ_p²` with
`‖(a, b)‖ = max(|a|, p^{1/2}·|b|)` and `S (a, b) = b`; then `‖S‖ = p^{-1/2}`,
while `S(B_X) = p·ℤ_p` is a single ball of radius `p^{-1}`, so
`e_0 S ≤ p^{-1} < ‖S‖`.

## Main definitions

* `SNumbers.entropySet S n` — the set of admissible radii at stage `n`.
* `SNumbers.entropyNumber S n` — the `n`-th entropy number `e_n S`.

## Main results

* `SNumbers.entropyNumber_nonneg` : `0 ≤ e_n S`                           (S1c)
* `SNumbers.entropyNumber_antitone` : `e_{n+1} S ≤ e_n S`                 (S1b)
* `SNumbers.entropyNumber_le_norm` : `e_n S ≤ ‖S‖`
* `SNumbers.entropyNumber_zero_op` : `e_n 0 = 0`
* `SNumbers.entropyNumber_additive` : `e_{n+m} (S + T) ≤ e_n S + e_m T`
* `SNumbers.entropyNumber_add_le` : `e_n (S + T) ≤ e_n S + ‖T‖`           (S2)
* `SNumbers.entropyNumber_comp_le` : `e_n (B ∘ S) ≤ ‖B‖ · e_n S`
* `SNumbers.entropyNumber_multiplicative` : `e_{n+m} (B ∘ S) ≤ e_n B · e_m S`
    (densely normed scalar field)
* `SNumbers.entropyNumber_comp_comp_le` :
    `e_n (B ∘ S ∘ A) ≤ ‖B‖ · e_n S · ‖A‖`                                 (S3)
    (densely normed scalar field)
* `SNumbers.tendsto_entropyNumber_iff_totallyBounded` :
    `e_n S → 0` iff `S(B_X)` is totally bounded.
* `SNumbers.isCompactOperator_iff_tendsto_entropyNumber` :
    `S` is a compact operator iff `e_n S → 0` (complete target space).

## Implementation notes

Mathlib has a cover API (`Metric.IsCover`, `Metric.externalCoveringNumber`),
but it is `ℝ≥0`-radius and `ℕ∞`-valued, whereas the numbers of this project
are real. The definition below therefore spells the covering condition out
with a `Finset` of centres, which also hands back an explicit finite cover
where one is needed; the topological work is done by
`Metric.totallyBounded_iff`.
-/

@[expose] public section

universe u

open Filter Topology

namespace SNumbers

section General

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The set of admissible radii at stage `n`: those `ε > 0` for which the
image of the closed unit ball of `X` under `S` can be covered by at most
`2 ^ n` closed balls of radius `ε`, with arbitrary centres in `Y`. -/
def entropySet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {ε | 0 < ε ∧ ∃ N : Finset Y, N.card ≤ 2 ^ n ∧
    ⇑S '' Metric.closedBall 0 1 ⊆ ⋃ y ∈ (N : Set Y), Metric.closedBall y ε}

/-- The `n`-th **entropy number** of a continuous linear map: the infimum of
the radii `ε > 0` for which `S(B_X)` is covered by at most `2 ^ n` closed
`ε`-balls. -/
noncomputable def entropyNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (entropySet S n)

lemma entropyNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber S n = sInf (entropySet S n) := rfl

/-! ### Basic properties of `entropySet` -/

/-- Every radius strictly above the operator norm is admissible: the single
ball of radius `‖S‖ + δ` centred at the origin already covers `S(B_X)`. -/
lemma norm_add_mem_entropySet (S : X →L[𝕜] Y) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ‖S‖ + δ ∈ entropySet S n := by
  refine ⟨add_pos_of_nonneg_of_pos (norm_nonneg S) hδ, {0},
    by simpa using Nat.one_le_two_pow, ?_⟩
  simp only [Finset.coe_singleton, Set.biUnion_singleton]
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  have hSx : ‖S x‖ ≤ ‖S‖ := by
    calc ‖S x‖ ≤ ‖S‖ * ‖x‖ := S.le_opNorm x
      _ ≤ ‖S‖ * 1 := by gcongr
      _ = ‖S‖ := mul_one _
  simpa using hSx.trans (by linarith)

/-- The entropy set is non-empty: it contains `‖S‖ + 1`. -/
lemma entropySet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    (entropySet S n).Nonempty :=
  ⟨‖S‖ + 1, norm_add_mem_entropySet S n one_pos⟩

/-- The entropy set is bounded below by `0`. -/
lemma bddBelow_entropySet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (entropySet S n) :=
  ⟨0, fun _ hε => hε.1.le⟩

/-- Every admissible radius bounds the entropy number from above. -/
lemma entropyNumber_le_of_mem {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hε : ε ∈ entropySet S n) :
    entropyNumber S n ≤ ε :=
  csInf_le (bddBelow_entropySet S n) hε

/-- Conversely, below any bound strictly above `e_n S` there is an actual
admissible radius. This is how a concrete covering is extracted from a bound
on the entropy number. -/
lemma exists_mem_entropySet_lt {S : X →L[𝕜] Y} {n : ℕ} {b : ℝ}
    (hb : entropyNumber S n < b) :
    ∃ ε ∈ entropySet S n, ε < b :=
  exists_lt_of_csInf_lt (entropySet_nonempty S n) hb

/-! ### (S1c) Non-negativity -/

lemma entropyNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ entropyNumber S n :=
  le_csInf (entropySet_nonempty S n) fun _ hε => hε.1.le

/-! ### (S1b) Monotonicity in `n` -/

/-- Raising `n` allows more balls, hence more radii become admissible. -/
lemma entropySet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    entropySet S n ⊆ entropySet S m := by
  rintro ε ⟨hε, N, hN, hcov⟩
  exact ⟨hε, N, hN.trans (Nat.pow_le_pow_right (by norm_num) h), hcov⟩

/-- If `n ≤ m`, then `e_m S ≤ e_n S`. -/
lemma entropyNumber_antitone' (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    entropyNumber S m ≤ entropyNumber S n :=
  csInf_le_csInf (bddBelow_entropySet S m) (entropySet_nonempty S n)
    (entropySet_subset S h)

lemma entropyNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber S (n + 1) ≤ entropyNumber S n :=
  entropyNumber_antitone' S (Nat.le_succ n)

/-! ### The norm bound and the zero operator -/

/-- `e_n S ≤ ‖S‖`: one ball of radius just above `‖S‖` suffices. -/
lemma entropyNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber S n ≤ ‖S‖ :=
  le_of_forall_pos_le_add fun _ hδ =>
    entropyNumber_le_of_mem (norm_add_mem_entropySet S n hδ)

/-- For the zero operator every positive radius is admissible. -/
lemma entropySet_zero_op (n : ℕ) :
    entropySet (0 : X →L[𝕜] Y) n = Set.Ioi 0 := by
  ext ε
  refine ⟨fun h => h.1, fun hε => ⟨hε, {0}, by simpa using Nat.one_le_two_pow, ?_⟩⟩
  rintro _ ⟨x, -, rfl⟩
  simpa using le_of_lt hε

@[simp] lemma entropyNumber_zero_op (n : ℕ) :
    entropyNumber (0 : X →L[𝕜] Y) n = 0 := by
  rw [entropyNumber_def, entropySet_zero_op, csInf_Ioi]

/-! ### Additivity, and the subadditivity axiom (S2) -/

/-- Covering step behind additivity: if `S(B_X)` is covered by `2 ^ n` balls
of radius `ε` with centres `y`, and `T(B_X)` by `2 ^ m` balls of radius `δ`
with centres `z`, then the `2 ^ (n + m)` sums `y + z` cover `(S + T)(B_X)`
with radius `ε + δ`, by the triangle inequality. -/
lemma add_mem_entropySet_add {S T : X →L[𝕜] Y} {n m : ℕ} {ε δ : ℝ}
    (hε : ε ∈ entropySet S n) (hδ : δ ∈ entropySet T m) :
    ε + δ ∈ entropySet (S + T) (n + m) := by
  classical
  obtain ⟨hε0, N, hN, hNcov⟩ := hε
  obtain ⟨hδ0, M, hM, hMcov⟩ := hδ
  refine ⟨by linarith, Finset.image₂ (· + ·) N M, ?_, ?_⟩
  · calc (Finset.image₂ (· + ·) N M).card ≤ N.card * M.card :=
          Finset.card_image₂_le _ _ _
      _ ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul hN hM
      _ = 2 ^ (n + m) := (pow_add 2 n m).symm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp (hNcov ⟨x, hx, rfl⟩)
    obtain ⟨z, hz, hz'⟩ := Set.mem_iUnion₂.mp (hMcov ⟨x, hx, rfl⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hy' hz'
    refine Set.mem_iUnion₂.mpr ⟨y + z, ?_, ?_⟩
    · exact_mod_cast Finset.mem_image₂_of_mem (by exact_mod_cast hy) (by exact_mod_cast hz)
    · rw [Metric.mem_closedBall, dist_eq_norm, add_apply]
      calc ‖S x + T x - (y + z)‖ = ‖(S x - y) + (T x - z)‖ := by congr 1; abel
        _ ≤ ‖S x - y‖ + ‖T x - z‖ := norm_add_le _ _
        _ ≤ ε + δ := add_le_add hy' hz'

/-- **Additivity of the entropy numbers**: `e_{n+m}(S + T) ≤ e_n S + e_m T`.
The budget of balls multiplies, so the indices add. -/
lemma entropyNumber_additive (S T : X →L[𝕜] Y) (n m : ℕ) :
    entropyNumber (S + T) (n + m) ≤ entropyNumber S n + entropyNumber T m := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨ε, hε, hεlt⟩ := exists_mem_entropySet_lt
    (show entropyNumber S n < entropyNumber S n + η / 2 by linarith)
  obtain ⟨δ, hδ, hδlt⟩ := exists_mem_entropySet_lt
    (show entropyNumber T m < entropyNumber T m + η / 2 by linarith)
  calc entropyNumber (S + T) (n + m) ≤ ε + δ :=
        entropyNumber_le_of_mem (add_mem_entropySet_add hε hδ)
    _ ≤ entropyNumber S n + entropyNumber T m + η := by linarith

/-- **(S2) Subadditivity**, the case `m = 0` of additivity together with
`e_0 T ≤ ‖T‖`. -/
lemma entropyNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber (S + T) n ≤ entropyNumber S n + ‖T‖ := by
  have h := entropyNumber_additive S T n 0
  rw [Nat.add_zero] at h
  linarith [entropyNumber_le_norm T 0]

/-! ### The outer half of the ideal property -/

/-- Covering step: applying `B` to the centres turns a cover of `S(B_X)` into
a cover of `(B ∘ S)(B_X)` with the radius multiplied by `‖B‖`. This uses only
that `B` is Lipschitz, so no assumption on the scalar field is needed. -/
lemma norm_mul_mem_entropySet_comp {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hB : 0 < ‖B‖) (hε : ε ∈ entropySet S n) :
    ‖B‖ * ε ∈ entropySet (B.comp S) n := by
  classical
  obtain ⟨hε0, N, hN, hcov⟩ := hε
  refine ⟨by positivity, N.image B, (Finset.card_image_le).trans hN, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp (hcov ⟨x, hx, rfl⟩)
  rw [Metric.mem_closedBall, dist_eq_norm] at hy'
  refine Set.mem_iUnion₂.mpr ⟨B y, ?_, ?_⟩
  · exact_mod_cast Finset.mem_image_of_mem B (by exact_mod_cast hy)
  · rw [Metric.mem_closedBall, dist_eq_norm, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    calc ‖B (S x) - B y‖ = ‖B (S x - y)‖ := by rw [map_sub]
      _ ≤ ‖B‖ * ‖S x - y‖ := B.le_opNorm _
      _ ≤ ‖B‖ * ε := by gcongr

/-- `e_n (B ∘ S) ≤ ‖B‖ · e_n S`. This is the half of the ideal property (S3)
that costs nothing; see `entropyNumber_comp_comp_le` for the full statement. -/
lemma entropyNumber_comp_le (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber (B.comp S) n ≤ ‖B‖ * entropyNumber S n := by
  rcases eq_or_lt_of_le (norm_nonneg B) with hB | hB
  · have hB0 : B = 0 := by rwa [eq_comm, norm_eq_zero] at hB
    simp [hB0]
  · rw [← div_le_iff₀' hB]
    refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
    rw [div_le_iff₀' hB]
    exact entropyNumber_le_of_mem (norm_mul_mem_entropySet_comp hB hε)

/-! ### Compactness -/

/-- **The entropy numbers of `S` tend to `0` exactly when `S(B_X)` is totally
bounded.** Both statements say that the image of the unit ball admits finite
`ε`-nets for every `ε > 0`; the entropy numbers merely package the size of
those nets into a sequence. -/
lemma tendsto_entropyNumber_iff_totallyBounded (S : X →L[𝕜] Y) :
    Tendsto (entropyNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) := by
  rw [Metric.tendsto_atTop, Metric.totallyBounded_iff]
  constructor
  · intro h ε hε
    obtain ⟨m, hm⟩ := h ε hε
    have hlt : entropyNumber S m < ε := by
      have := hm m le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (entropyNumber_nonneg S m)] at this
    obtain ⟨δ, ⟨-, N, -, hcov⟩, hδε⟩ := exists_mem_entropySet_lt hlt
    exact ⟨(N : Set Y), N.finite_toSet,
      hcov.trans (Set.iUnion₂_mono fun y _ => Metric.closedBall_subset_ball hδε)⟩
  · intro h ε hε
    obtain ⟨t, ht_fin, ht_cov⟩ := h (ε / 2) (by positivity)
    have hmem : ε / 2 ∈ entropySet S ht_fin.toFinset.card := by
      refine ⟨by positivity, ht_fin.toFinset, Nat.lt_two_pow_self.le, ?_⟩
      rw [ht_fin.coe_toFinset]
      exact ht_cov.trans (Set.iUnion₂_mono fun y _ => Metric.ball_subset_closedBall)
    refine ⟨ht_fin.toFinset.card, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (entropyNumber_nonneg S n)]
    calc entropyNumber S n ≤ entropyNumber S ht_fin.toFinset.card :=
          entropyNumber_antitone' S hn
      _ ≤ ε / 2 := entropyNumber_le_of_mem hmem
      _ < ε := by linarith

/-- **A compact operator has entropy numbers tending to zero.** No
completeness assumption is needed. -/
theorem tendsto_entropyNumber_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) :
    Tendsto (entropyNumber S) atTop (𝓝 0) := by
  have hS' : IsCompactOperator ⇑(S : X →ₗ[𝕜] Y) := hS
  have h_cpt := hS'.isCompact_closure_image_closedBall (1 : ℝ)
  rw [ContinuousLinearMap.coe_coe] at h_cpt
  exact (tendsto_entropyNumber_iff_totallyBounded S).mpr
    (TotallyBounded.subset subset_closure h_cpt.totallyBounded)

/-- **Entropy numbers tending to zero force compactness**, provided the target
space is complete: a totally bounded set then has compact closure. -/
theorem isCompactOperator_of_tendsto_entropyNumber [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : Tendsto (entropyNumber S) atTop (𝓝 0)) :
    IsCompactOperator S :=
  (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image ⇑S).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos,
      ((tendsto_entropyNumber_iff_totallyBounded S).mp hS).closure.isCompact_of_isClosed
        isClosed_closure⟩

/-- **Compactness is measured by the entropy numbers**: for a complete target
space, `S` is a compact operator if and only if `e_n S → 0`. -/
theorem isCompactOperator_iff_tendsto_entropyNumber [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (entropyNumber S) atTop (𝓝 0) :=
  ⟨tendsto_entropyNumber_of_isCompactOperator, isCompactOperator_of_tendsto_entropyNumber⟩

end General

/-!
### Multiplicativity, and the ideal property (S3)

Here the scalar field is assumed **densely normed**, i.e. its norm values are
dense in `[0, ∞)`. This is what allows a vector of norm at most `δ` to be
written as `c • w` with `‖w‖ ≤ 1` and `‖c‖` arbitrarily close to `δ`, which is
the one step where a covering of the unit ball has to be transported to a
covering of a ball of radius `δ`. Every `RCLike` field, in particular `ℝ` and
`ℂ`, is densely normed.
-/

section Densely

variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- Covering step behind multiplicativity. Let `B(B_Y)` be covered by `2 ^ n`
balls of radius `β` with centres `z`, let `S(B_X)` be covered by `2 ^ m` balls
of radius `δ` with centres `y`, and let `c` be a scalar with `‖c‖ > δ`. Then
the `2 ^ (n + m)` points `B y + c • z` cover `(B ∘ S)(B_X)` with radius
`‖c‖ · β`: the difference `S x - y` has norm at most `δ < ‖c‖`, so
`c⁻¹ • (S x - y)` lies in `B_Y` and its image under `B` is `β`-close to some
centre `z`; multiplying back by `c` scales that estimate by `‖c‖`. -/
lemma mul_mem_entropySet_comp {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n m : ℕ} {β δ : ℝ}
    (hβ : β ∈ entropySet B n) (hδ : δ ∈ entropySet S m) {c : 𝕜} (hc : δ < ‖c‖) :
    ‖c‖ * β ∈ entropySet (B.comp S) (n + m) := by
  classical
  obtain ⟨hβ0, N, hN, hNcov⟩ := hβ
  obtain ⟨hδ0, M, hM, hMcov⟩ := hδ
  have hc0 : (0 : ℝ) < ‖c‖ := hδ0.trans hc
  have hcne : c ≠ 0 := by simpa [norm_pos_iff] using hc0
  refine ⟨by positivity, Finset.image₂ (fun z y => B y + c • z) N M, ?_, ?_⟩
  · calc (Finset.image₂ (fun z y => B y + c • z) N M).card ≤ N.card * M.card :=
          Finset.card_image₂_le _ _ _
      _ ≤ 2 ^ n * 2 ^ m := Nat.mul_le_mul hN hM
      _ = 2 ^ (n + m) := (pow_add 2 n m).symm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hy'⟩ := Set.mem_iUnion₂.mp (hMcov ⟨x, hx, rfl⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hy'
    -- the rescaled difference lies in the unit ball of `Y`
    have hw : c⁻¹ • (S x - y) ∈ Metric.closedBall (0 : Y) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
      calc ‖c‖⁻¹ * ‖S x - y‖ ≤ ‖c‖⁻¹ * ‖c‖ := by gcongr; exact hy'.trans hc.le
        _ = 1 := inv_mul_cancel₀ hc0.ne'
    obtain ⟨z, hz, hz'⟩ := Set.mem_iUnion₂.mp (hNcov ⟨_, hw, rfl⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz'
    refine Set.mem_iUnion₂.mpr ⟨B y + c • z, ?_, ?_⟩
    · have hmem : B y + c • z ∈ Finset.image₂ (fun z y => B y + c • z) N M :=
        Finset.mem_image₂_of_mem (f := fun z y => B y + c • z)
          (by exact_mod_cast hz) (by exact_mod_cast hy)
      exact_mod_cast hmem
    · rw [Metric.mem_closedBall, dist_eq_norm, ContinuousLinearMap.coe_comp,
        Function.comp_apply]
      have hBv : c • B (c⁻¹ • (S x - y)) = B (S x) - B y := by
        rw [← ContinuousLinearMap.map_smul, smul_inv_smul₀ hcne, map_sub]
      calc ‖B (S x) - (B y + c • z)‖
          = ‖c • (B (c⁻¹ • (S x - y)) - z)‖ := by rw [smul_sub, hBv]; congr 1; abel
        _ = ‖c‖ * ‖B (c⁻¹ • (S x - y)) - z‖ := norm_smul c _
        _ ≤ ‖c‖ * β := by gcongr

/-- Intermediate form of multiplicativity: for a fixed admissible radius `δ`
of `S` and a scalar `c` of norm above `δ`, the infimum over the radii for `B`
gives `e_{n+m}(B ∘ S) ≤ ‖c‖ · e_n B`. -/
lemma entropyNumber_comp_le_of_mem {B : Y →L[𝕜] Z} {S : X →L[𝕜] Y} {n m : ℕ} {δ : ℝ}
    (hδ : δ ∈ entropySet S m) {c : 𝕜} (hc : δ < ‖c‖) :
    entropyNumber (B.comp S) (n + m) ≤ ‖c‖ * entropyNumber B n := by
  have hc0 : (0 : ℝ) < ‖c‖ := hδ.1.trans hc
  rw [← div_le_iff₀' hc0]
  refine le_csInf (entropySet_nonempty B n) fun β hβ => ?_
  rw [div_le_iff₀' hc0]
  exact entropyNumber_le_of_mem (mul_mem_entropySet_comp hβ hδ hc)

/-- **Multiplicativity of the entropy numbers**:
`e_{n+m}(B ∘ S) ≤ e_n B · e_m S`. Again the budgets of balls multiply, so the
indices add. -/
lemma entropyNumber_multiplicative (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (n m : ℕ) :
    entropyNumber (B.comp S) (n + m) ≤ entropyNumber B n * entropyNumber S m := by
  -- first: the bound with an arbitrary slack `t > 0` on the factor for `S`
  have key : ∀ t : ℝ, 0 < t →
      entropyNumber (B.comp S) (n + m) ≤ entropyNumber B n * (entropyNumber S m + t) := by
    intro t ht
    obtain ⟨δ, hδ, hδlt⟩ := exists_mem_entropySet_lt
      (show entropyNumber S m < entropyNumber S m + t / 2 by linarith)
    obtain ⟨c, hc1, hc2⟩ :=
      NormedField.exists_lt_norm_lt 𝕜 hδ.1.le (show δ < δ + t / 2 by linarith)
    calc entropyNumber (B.comp S) (n + m) ≤ ‖c‖ * entropyNumber B n :=
          entropyNumber_comp_le_of_mem hδ hc1
      _ ≤ (entropyNumber S m + t) * entropyNumber B n := by
          gcongr
          · exact entropyNumber_nonneg B n
          · linarith
      _ = entropyNumber B n * (entropyNumber S m + t) := mul_comm _ _
  -- then: let the slack tend to `0`
  refine le_of_forall_pos_le_add fun κ hκ => ?_
  rcases eq_or_lt_of_le (entropyNumber_nonneg B n) with hB | hB
  · have h0 := key 1 one_pos
    rw [← hB] at h0 ⊢
    simp only [zero_mul] at h0 ⊢
    linarith
  · have h := key (κ / entropyNumber B n) (by positivity)
    rwa [mul_add, mul_div_cancel₀ _ hB.ne'] at h

/-- **(S3) Ideal property**, a corollary of multiplicativity applied twice
(once in each slot) together with `e_0 ≤ ‖·‖`. -/
lemma entropyNumber_comp_comp_le (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (A : W →L[𝕜] X)
    (n : ℕ) :
    entropyNumber (B.comp (S.comp A)) n ≤ ‖B‖ * entropyNumber S n * ‖A‖ := by
  have hSA : entropyNumber (S.comp A) n ≤ entropyNumber S n * ‖A‖ := by
    have h := entropyNumber_multiplicative S A n 0
    rw [Nat.add_zero] at h
    exact h.trans
      (mul_le_mul_of_nonneg_left (entropyNumber_le_norm A 0) (entropyNumber_nonneg S n))
  have h := entropyNumber_multiplicative B (S.comp A) 0 n
  rw [Nat.zero_add] at h
  calc entropyNumber (B.comp (S.comp A)) n
      ≤ entropyNumber B 0 * entropyNumber (S.comp A) n := h
    _ ≤ ‖B‖ * (entropyNumber S n * ‖A‖) :=
        mul_le_mul (entropyNumber_le_norm B 0) hSA (entropyNumber_nonneg _ _) (norm_nonneg B)
    _ = ‖B‖ * entropyNumber S n * ‖A‖ := (mul_assoc _ _ _).symm

end Densely

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
