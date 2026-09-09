/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Diagonal cutoff scales from actual logarithmic limits

This module proves the numerical cutoff-selection step in Lemma 11.3 of the
candidate manuscript. The decay of powers times logarithms is proved using
Mathlib's exponential asymptotic, not assumed as a cutoff-schedule hypothesis.
The resulting schedule enforces every requested finite collection of jet bounds.
It does not construct the analytic increments or prove their PDE estimates.
-/

namespace NavierStokes.DiagonalScale

open Set Filter
open scoped Topology BigOperators

noncomputable section

/-- The scalar expression whose smallness is needed at each correction stage. -/
def logPowerWeight (C p r q : ℝ) : ℝ :=
  C * (1 + |Real.log q|) ^ p * q ^ r

/-- Any positive real power beats any fixed real logarithmic power at zero. -/
theorem tendsto_logPowerWeight (C p r : ℝ) (hr : 0 < r) :
    Tendsto (logPowerWeight C p r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscale : Tendsto (fun q : ℝ => 1 - Real.log q) (𝓝[>] 0) atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [Real.tendsto_log_nhdsGT_zero.eventually
      (eventually_le_atBot (1 - b))] with q hq
    linarith
  have hexp :=
    ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p r hr).comp hscale).const_mul
      (C * Real.exp r)
  simp only [mul_zero] at hexp
  apply hexp.congr'
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with q hq
  have hidentity : Real.exp r * Real.exp (-r * (1 - Real.log q)) =
      Real.exp (Real.log q * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [Function.comp_apply, logPowerWeight]
  rw [abs_of_nonpos (Real.log_nonpos hq.1.le hq.2),
    Real.rpow_def_of_pos hq.1 r]
  rw [← hidentity]
  ring_nf

/-- Absorbing half the positive power into the chosen small coefficient gives
exactly the stage bound used in the manuscript's tail estimate. -/
theorem absorb_logarithmic_weight (C p g L q ε : ℝ) (hq : 0 < q)
    (hsmall : |logPowerWeight C p (g / 2) q| ≤ ε) :
    |C * (1 + |Real.log q|) ^ p * q ^ (g - L)| ≤
      ε * q ^ (g / 2 - L) := by
  have hexp : g - L = g / 2 + (g / 2 - L) := by ring
  rw [hexp, Real.rpow_add hq, ← mul_assoc, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hq.le _)]
  exact mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hq.le _)

/-- A common integer scale controls an arbitrary finite family, uniformly on
the entire punctured interval through its reciprocal. -/
theorem exists_integer_scale {ι : Type*} (s : Finset ι) (C p : ι → ℝ)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    ∃ a : ℕ, 0 < a ∧
      ∀ i ∈ s, ∀ q : ℝ, 0 < q → q ≤ 1 / (a : ℝ) →
        |logPowerWeight (C i) (p i) r q| ≤ ε := by
  have hsmall : ∀ᶠ q in 𝓝[>] (0 : ℝ),
      ∀ i ∈ s, |logPowerWeight (C i) (p i) r q| < ε := by
    apply (eventually_all_finset s).2
    intro i hi
    have hlim := (tendsto_logPowerWeight (C i) (p i) r hr).abs
    simp only [abs_zero] at hlim
    exact hlim.eventually (gt_mem_nhds hε)
  rcases mem_nhdsGT_iff_exists_Ioo_subset.1 hsmall with ⟨δ, hδ, hbound⟩
  change (0 : ℝ) < δ at hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  intro i hi q hq hqa
  have hrecip : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < δ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  exact (hbound ⟨hq, lt_of_le_of_lt hqa hrecip⟩ i hi).le

/-- A recursive integer sequence dominating prescribed local scales and at
least doubling on every step. -/
def doublingEnvelope (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => max 1 (b 0)
  | n + 1 => max (b (n + 1)) (2 * doublingEnvelope b n)

theorem doublingEnvelope_ge (b : ℕ → ℕ) (n : ℕ) :
    b n ≤ doublingEnvelope b n := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact le_max_left _ _

theorem doublingEnvelope_growth (b : ℕ → ℕ) (n : ℕ) :
    2 * doublingEnvelope b n ≤ doublingEnvelope b (n + 1) := by
  exact le_max_right _ _

theorem doublingEnvelope_pos (b : ℕ → ℕ) (n : ℕ) :
    0 < doublingEnvelope b n := by
  induction n with
  | zero => exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  | succ n ih =>
      exact lt_of_lt_of_le (Nat.mul_pos (by norm_num) ih) (doublingEnvelope_growth b n)

theorem doublingEnvelope_lower_bound (b : ℕ → ℕ) (n : ℕ) :
    n + 1 ≤ doublingEnvelope b n := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
      have hp := doublingEnvelope_pos b n
      have hg := doublingEnvelope_growth b n
      omega

theorem doublingEnvelope_strictMono (b : ℕ → ℕ) :
    StrictMono (doublingEnvelope b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := doublingEnvelope_pos b n
  have hg := doublingEnvelope_growth b n
  omega

/-- Consequently only finitely many cutoff supports can reach a fixed q > 0. -/
theorem doublingEnvelope_reciprocal_eventually_small (b : ℕ → ℕ)
    (q : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ∀ j ≥ N, 1 / (doublingEnvelope b j : ℝ) < q := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hq
  refine ⟨N, ?_⟩
  intro j hj
  have hn : (N : ℝ) + 1 ≤ (doublingEnvelope b j : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right hj 1).trans (doublingEnvelope_lower_bound b j)
  exact lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hn) hN

/-- The indices whose numerical cutoff support reaches a fixed positive scale
form a finite set. This is the local-finiteness input, before introducing fields. -/
theorem doublingEnvelope_finite_active (b : ℕ → ℕ) (q : ℝ) (hq : 0 < q) :
    {j : ℕ | q ≤ 1 / (doublingEnvelope b j : ℝ)}.Finite := by
  obtain ⟨N, hN⟩ := doublingEnvelope_reciprocal_eventually_small b q hq
  apply (Finset.range N).finite_toSet.subset
  intro j hj
  change j ∈ Finset.range N
  apply Finset.mem_range.mpr
  by_contra hlt
  exact (not_lt_of_ge hj) (hN j (Nat.le_of_not_gt hlt))

/-- The numerical cutoff schedule of Lemma 11.3. Stage zero is exempt from a
positive decay exponent, as in the source. Every positive stage enforces all
jet requirements m ≤ j+2, with one schedule shared by all those requirements.
The optional integer B gives an arbitrary lower bound on the initial scale. -/
theorem exists_diagonal_scales (C p : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hg : ∀ j, 1 ≤ j → 0 < g j) (B : ℕ) :
    ∃ a : ℕ → ℕ,
      B ≤ a 0 ∧
      (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧
      StrictMono a ∧
      (∀ q : ℝ, 0 < q → ∃ N : ℕ, ∀ j ≥ N, 1 / (a j : ℝ) < q) ∧
      (∀ j, 1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
        0 < q → q ≤ 1 / (a j : ℝ) →
          |logPowerWeight (C j m) (p j m) (g j / 2) q| ≤ (1 / 2 : ℝ) ^ j) := by
  classical
  have hlocal : ∀ j : ℕ, ∃ b : ℕ, 0 < b ∧
      (j = 0 → B ≤ b) ∧
      (1 ≤ j → ∀ m, m ≤ j + 2 → ∀ q : ℝ,
        0 < q → q ≤ 1 / (b : ℝ) →
          |logPowerWeight (C j m) (p j m) (g j / 2) q| ≤ (1 / 2 : ℝ) ^ j) := by
    intro j
    by_cases hj : j = 0
    · refine ⟨max 1 B, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_, ?_⟩
      · intro _
        exact le_max_right _ _
      · intro hpos
        omega
    · have hjpos : 1 ≤ j := by omega
      obtain ⟨b, hb, hbound⟩ := exists_integer_scale (Finset.range (j + 3))
        (C j) (p j) (g j / 2) ((1 / 2 : ℝ) ^ j)
        (by linarith [hg j hjpos]) (by positivity)
      refine ⟨b, hb, ?_, ?_⟩
      · intro hzero
        exact False.elim (hj hzero)
      · intro _ m hm q hq hqb
        exact hbound m (Finset.mem_range.mpr (by omega)) q hq hqb
  choose b hbpos hbzero hbbound using hlocal
  refine ⟨doublingEnvelope b, ?_, doublingEnvelope_pos b,
    doublingEnvelope_growth b, doublingEnvelope_strictMono b,
    doublingEnvelope_reciprocal_eventually_small b, ?_⟩
  · exact (hbzero 0 rfl).trans (doublingEnvelope_ge b 0)
  · intro j hj m hm q hq hqa
    apply hbbound j hj m hm q hq
    apply hqa.trans
    apply one_div_le_one_div_of_le
    · exact_mod_cast hbpos j
    · exact_mod_cast doublingEnvelope_ge b j

/-- The exact dyadic tail used to sum the scalar majorants. -/
theorem dyadic_tail_sum (J : ℕ) (A : ℝ) :
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (J + 1 + n) * A) = (1 / 2 : ℝ) ^ J * A := by
  simp only [pow_add, pow_succ, mul_assoc, tsum_mul_left, tsum_mul_right, tsum_geometric_two]
  ring

/-- The scalar tail bound printed in Lemma 11.3, valid uniformly for every
`0 < q ≤ 1`. The sum indexes the tail by `j = J + 1 + n`. -/
theorem weighted_tail_bound (g : ℕ → ℝ) (hg : Monotone g) (L q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (J : ℕ) :
    Summable (fun n : ℕ =>
      (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) / 2 - L)) ∧
    (∑' n : ℕ, (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) / 2 - L)) ≤
      (1 / 2 : ℝ) ^ J * q ^ (g (J + 1) / 2 - L) := by
  let A := q ^ (g (J + 1) / 2 - L)
  have hmajor : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (J + 1 + n) * A) := by
    simpa only [pow_add] using
      (summable_geometric_two.mul_left ((1 / 2 : ℝ) ^ (J + 1))).mul_right A
  have hnonneg : ∀ n : ℕ,
      0 ≤ (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) / 2 - L) := by
    intro n
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hq.le _)
  have hdom : ∀ n : ℕ,
      (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) / 2 - L) ≤
        (1 / 2 : ℝ) ^ (J + 1 + n) * A := by
    intro n
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    have hgn := hg (Nat.le_add_right (J + 1) n)
    linarith
  have hsum := Summable.of_nonneg_of_le hnonneg hdom hmajor
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ (J + 1 + n) * A :=
      Summable.tsum_le_tsum hdom hsum hmajor
    _ = (1 / 2 : ℝ) ^ J * A := dyadic_tail_sum J A

/-- If the prescribed order gains increase without bound, a single tail index
works for an arbitrary target power and for every `q` in the unit interval.
This concerns scalar majorants; it does not assert flatness of a PDE residual. -/
theorem exists_uniform_tail_order (g : ℕ → ℝ) (hg : Monotone g)
    (hgtop : Tendsto g atTop atTop) (L N : ℝ) (m : ℕ) :
    ∃ J : ℕ, m ≤ J ∧ ∀ q : ℝ, 0 < q → q ≤ 1 →
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (J + 1 + n) * q ^ (g (J + 1 + n) / 2 - L)) ≤
        (1 / 2 : ℝ) ^ J * q ^ N := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (hgtop.eventually (eventually_ge_atTop (2 * (N + L))))
  let J := max m J₀
  refine ⟨J, le_max_left _ _, ?_⟩
  intro q hq hq1
  have hgain := hJ₀ (J + 1) (by dsimp [J]; omega)
  have hpower : q ^ (g (J + 1) / 2 - L) ≤ q ^ N := by
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    linarith
  exact (weighted_tail_bound g hg L q hq hq1 J).2.trans
    (mul_le_mul_of_nonneg_left hpower (by positivity))

end

end NavierStokes.DiagonalScale
