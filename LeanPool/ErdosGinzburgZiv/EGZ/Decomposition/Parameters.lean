/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Parameters for the Flag Decomposition Lemma

The explicit initial scale `ε² / (16 * 3^(d+1))` satisfies the parameter
choices in the paper.  The geometric estimates include arbitrary tails,
so they also control every finite execution of the refinement procedure.
-/

namespace EGZ.DecompositionParameters

open scoped BigOperators

/-- The constant in the mass loss of a complete-element refinement. -/
def refinementConstant (d : ℕ) : ℝ := (3 : ℝ) ^ (d + 1)

/-- The ratio between two consecutive scales. -/
noncomputable def decayRatio (d : ℕ) : ℝ := (3 : ℝ)⁻¹ ^ (2 * d)

/-- The scale `δ_i = δ₀ 3^(-2di)`. -/
noncomputable def scale (d : ℕ) (δ₀ : ℝ) (i : ℕ) : ℝ := δ₀ * decayRatio d ^ i

/-- A bound for the mass lost at one stage, divided by the input mass. -/
noncomputable def lossBudget (d : ℕ) (ε δ₀ : ℝ) (i : ℕ) : ℝ :=
  ε * scale d δ₀ i ^ 2 + refinementConstant d * scale d δ₀ i

/-- A choice depending only on the dimension and retained-mass tolerance. -/
noncomputable def initialScale (d : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 / (16 * refinementConstant d)

theorem refinementConstant_pos (d : ℕ) : 0 < refinementConstant d := by
  unfold refinementConstant
  positivity

theorem one_le_refinementConstant (d : ℕ) : 1 ≤ refinementConstant d :=
  one_le_pow₀ (by norm_num)

theorem decayRatio_pos (d : ℕ) : 0 < decayRatio d := by
  unfold decayRatio
  positivity

theorem decayRatio_le_half {d : ℕ} (hd : 1 ≤ d) : decayRatio d ≤ 1 / 2 := by
  calc
    decayRatio d ≤ (3 : ℝ)⁻¹ :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ 1 / 2 := by norm_num

theorem scale_eq_inv_pow (d : ℕ) (δ₀ : ℝ) (i : ℕ) :
    scale d δ₀ i = δ₀ * (3 : ℝ)⁻¹ ^ (2 * d * i) := by
  simp only [scale, decayRatio, pow_mul]

@[simp] theorem scale_zero (d : ℕ) (δ₀ : ℝ) : scale d δ₀ 0 = δ₀ := by
  simp [scale]

theorem scale_pos (d : ℕ) {δ₀ : ℝ} (hδ : 0 < δ₀) (i : ℕ) :
    0 < scale d δ₀ i :=
  mul_pos hδ (pow_pos (decayRatio_pos d) i)

theorem scale_antitone {d : ℕ} (hd : 1 ≤ d) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) :
    Antitone (scale d δ₀) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (decayRatio_pos d).le
      ((decayRatio_le_half hd).trans (by norm_num)) hij) hδ

theorem scale_le_geometric {d : ℕ} (hd : 1 ≤ d) {δ₀ : ℝ} (hδ : 0 ≤ δ₀)
    (i : ℕ) : scale d δ₀ i ≤ δ₀ * (1 / 2 : ℝ) ^ i := by
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (decayRatio_pos d).le (decayRatio_le_half hd) i) hδ

theorem initialScale_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < initialScale d ε := by
  unfold initialScale
  exact div_pos (sq_pos_of_pos hε) (mul_pos (by norm_num) (refinementConstant_pos d))

theorem refinementConstant_mul_initialScale (d : ℕ) (ε : ℝ) :
    refinementConstant d * initialScale d ε = ε ^ 2 / 16 := by
  unfold initialScale
  field_simp [ne_of_gt (refinementConstant_pos d)]

/-- Basic inequalities for the explicit initial scale. -/
theorem initialScale_bounds (d : ℕ) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    refinementConstant d * initialScale d ε < 1 ∧
      initialScale d ε ≤ 1 ∧
      ε * initialScale d ε ≤ refinementConstant d ∧
      initialScale d ε ≤ ε * (3 : ℝ)⁻¹ ^ d := by
  have hδ := initialScale_pos d hε
  have hC := one_le_refinementConstant d
  have hmul := refinementConstant_mul_initialScale d ε
  have hεone : ε ≤ 1 := by linarith
  have hεsq : ε ^ 2 ≤ ε := by nlinarith
  have hprod : refinementConstant d * initialScale d ε < 1 := by
    nlinarith
  have hδone : initialScale d ε ≤ 1 := by nlinarith
  refine ⟨hprod, hδone, ?_, ?_⟩
  · nlinarith
  · rw [inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) d)).mpr
    have hpow : refinementConstant d = (3 : ℝ) ^ d * 3 := by
      simp [refinementConstant, pow_succ]
    rw [hpow] at hmul
    nlinarith

theorem initialScale_scale_bound {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (i : ℕ) :
    scale d (initialScale d ε) i ≤ ε * (3 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ i := by
  calc
    scale d (initialScale d ε) i ≤ initialScale d ε * (1 / 2 : ℝ) ^ i :=
      scale_le_geometric hd (initialScale_pos d hε).le i
    _ ≤ ε * (3 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ i := by
      rw [one_div]
      exact mul_le_mul_of_nonneg_right (initialScale_bounds d hε hεhalf).2.2.2
        (by positivity)

theorem lossBudget_nonneg (d : ℕ) {ε δ₀ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ₀)
    (i : ℕ) : 0 ≤ lossBudget d ε δ₀ i := by
  unfold lossBudget scale
  have := (refinementConstant_pos d).le
  have := (decayRatio_pos d).le
  positivity

theorem lossBudget_le_geometric {d : ℕ} (hd : 1 ≤ d) {ε δ₀ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ₀) (hsmall : ε * δ₀ ≤ refinementConstant d) (i : ℕ) :
    lossBudget d ε δ₀ i ≤
      (2 * refinementConstant d * δ₀) * (1 / 2 : ℝ) ^ i := by
  have hscale : 0 ≤ scale d δ₀ i := by
    unfold scale
    exact mul_nonneg hδ (pow_nonneg (decayRatio_pos d).le i)
  have hscaleδ : scale d δ₀ i ≤ δ₀ := by
    simpa using scale_antitone hd hδ (Nat.zero_le i)
  have hεscale : ε * scale d δ₀ i ≤ refinementConstant d :=
    (mul_le_mul_of_nonneg_left hscaleδ hε).trans hsmall
  calc
    lossBudget d ε δ₀ i ≤ 2 * refinementConstant d * scale d δ₀ i := by
      unfold lossBudget
      nlinarith [mul_le_mul_of_nonneg_right hεscale hscale]
    _ ≤ 2 * refinementConstant d * (δ₀ * (1 / 2 : ℝ) ^ i) :=
      mul_le_mul_of_nonneg_left (scale_le_geometric hd hδ i) (by
        have := refinementConstant_pos d
        positivity)
    _ = _ := by ring

theorem lossBudget_summable {d : ℕ} (hd : 1 ≤ d) {ε δ₀ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ₀) (hsmall : ε * δ₀ ≤ refinementConstant d) :
    Summable (lossBudget d ε δ₀) := by
  exact Summable.of_nonneg_of_le (lossBudget_nonneg d hε hδ)
    (lossBudget_le_geometric hd hε hδ hsmall)
    (summable_geometric_two.mul_left (2 * refinementConstant d * δ₀))

private theorem tsum_half_succ (A : ℝ) :
    (∑' i : ℕ, A * (1 / 2 : ℝ) ^ (i + 1)) = A := by
  simp_rw [pow_succ]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_two]
  ring

/-- Every tail of the loss budgets has a geometric bound. -/
theorem lossBudget_tsum_tail_le {d : ℕ} (hd : 1 ≤ d) {ε δ₀ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ₀) (hsmall : ε * δ₀ ≤ refinementConstant d) (s : ℕ) :
    (∑' i : ℕ, lossBudget d ε δ₀ (i + s + 1)) ≤
      (2 * refinementConstant d * δ₀) * (1 / 2 : ℝ) ^ s := by
  have hs : Summable (fun i => lossBudget d ε δ₀ (i + s + 1)) :=
    (lossBudget_summable hd hε hδ hsmall).comp_injective (by
      intro i j hij
      change i + s + 1 = j + s + 1 at hij
      omega)
  have hgeom : Summable (fun i : ℕ =>
      ((2 * refinementConstant d * δ₀) * (1 / 2 : ℝ) ^ s) * (1 / 2 : ℝ) ^ (i + 1)) :=
    (summable_geometric_two.mul_left
      ((2 * refinementConstant d * δ₀) * (1 / 2 : ℝ) ^ s)).comp_injective Nat.succ_injective
  calc
    (∑' i : ℕ, lossBudget d ε δ₀ (i + s + 1)) ≤
        ∑' i : ℕ, ((2 * refinementConstant d * δ₀) * (1 / 2 : ℝ) ^ s) *
          (1 / 2 : ℝ) ^ (i + 1) := by
      apply hs.tsum_le_tsum _ hgeom
      intro i
      calc
        lossBudget d ε δ₀ (i + s + 1) ≤
            (2 * refinementConstant d * δ₀) * (1 / 2 : ℝ) ^ (i + s + 1) :=
          lossBudget_le_geometric hd hε hδ hsmall (i + s + 1)
        _ = _ := by simp only [pow_add, pow_one]; ring
    _ = _ := tsum_half_succ _

/-- For the chosen scale, the total future budget after stage `s` is at
most `ε² / 8 * 2^(-s)`.  In particular, `s = 0` is the parameter-choice
inequality in the paper. -/
theorem initialScale_tsum_tail_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (s : ℕ) :
    (∑' i : ℕ, lossBudget d ε (initialScale d ε) (i + s + 1)) ≤
      ε ^ 2 / 8 * (2 : ℝ)⁻¹ ^ s := by
  have h := lossBudget_tsum_tail_le hd hε.le (initialScale_pos d hε).le
    (initialScale_bounds d hε hεhalf).2.2.1 s
  convert h using 1
  rw [one_div, mul_assoc 2, refinementConstant_mul_initialScale]
  ring

theorem initialScale_summable {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    Summable (lossBudget d ε (initialScale d ε)) :=
  lossBudget_summable hd hε.le (initialScale_pos d hε).le
    (initialScale_bounds d hε hεhalf).2.2.1

/-- The same bound applies to any finite subset of future stages. -/
theorem initialScale_sum_tail_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (s : ℕ) (t : Finset ℕ) :
    (∑ i ∈ t, lossBudget d ε (initialScale d ε) (i + s + 1)) ≤
      ε ^ 2 / 8 * (2 : ℝ)⁻¹ ^ s := by
  have hs : Summable (fun i => lossBudget d ε (initialScale d ε) (i + s + 1)) :=
    (initialScale_summable hd hε hεhalf).comp_injective (by
      intro i j hij
      change i + s + 1 = j + s + 1 at hij
      omega)
  exact (hs.sum_le_tsum t (fun i _ =>
    lossBudget_nonneg d hε.le (initialScale_pos d hε).le _)).trans
      (initialScale_tsum_tail_le hd hε hεhalf s)

/-- All three parameter requirements, with the dependence on `d` and `ε`
made explicit by the witness `initialScale d ε`. -/
theorem exists_parameter_choice {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ refinementConstant d * δ₀ < 1 ∧
      Summable (fun i : ℕ => lossBudget d ε δ₀ (i + 1)) ∧
      (∑' i : ℕ, lossBudget d ε δ₀ (i + 1)) ≤ ε ^ 2 / 8 ∧
      ∀ i : ℕ, scale d δ₀ i ≤ ε * (3 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ i := by
  refine ⟨initialScale d ε, initialScale_pos d hε,
    (initialScale_bounds d hε hεhalf).1,
    (initialScale_summable hd hε hεhalf).comp_injective Nat.succ_injective, ?_,
    initialScale_scale_bound hd hε hεhalf⟩
  simpa using initialScale_tsum_tail_le hd hε hεhalf 0

/-- Telescoping the individual stage estimates gives a bound for every
finite interval of an iteration. -/
theorem mass_loss_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (mass : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hstep : ∀ i, mass i - mass (i + 1) ≤
      lossBudget d ε (initialScale d ε) (i + 1) * M) (s n : ℕ) :
    mass s - mass (n + s) ≤ ε ^ 2 / 8 * (2 : ℝ)⁻¹ ^ s * M := by
  have hsum : mass s - mass (n + s) ≤
      (∑ i ∈ Finset.range n, lossBudget d ε (initialScale d ε) (i + s + 1)) * M := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hnext := hstep (n + s)
      have hind : n + 1 + s = n + s + 1 := by omega
      rw [hind]
      nlinarith
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (initialScale_sum_tail_le hd hε hεhalf s (Finset.range n)) hM)

/-- The mass-and-tail invariant in the paper, and the final retained-mass
bound, follow directly from the explicit budgets.  This theorem applies to
every finite prefix; an infinite execution is not required. -/
theorem mass_and_tail {d : ℕ} (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (mass : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hmass : mass 0 = M)
    (hstep : ∀ i, mass i - mass (i + 1) ≤
      lossBudget d ε (initialScale d ε) (i + 1) * M) :
    (∀ s, M / 2 ≤ mass s ∧ (1 - ε) * M ≤ mass s) ∧
      ∀ s n, mass s - mass (n + s) ≤ ε ^ 2 / 4 * mass s := by
  have hloss (s : ℕ) : M - mass s ≤ ε ^ 2 / 8 * M := by
    simpa [hmass] using mass_loss_le hd hε hεhalf mass hM hstep 0 s
  have hhalf : ε ^ 2 / 8 ≤ 1 / 2 := by nlinarith
  have hεcoef : ε ^ 2 / 8 ≤ ε := by nlinarith
  have hret (s : ℕ) : M / 2 ≤ mass s ∧ (1 - ε) * M ≤ mass s := by
    have hhalfM := mul_le_mul_of_nonneg_right hhalf hM
    have hεM := mul_le_mul_of_nonneg_right hεcoef hM
    constructor <;> nlinarith [hloss s]
  refine ⟨hret, ?_⟩
  intro s n
  have hpow : (2 : ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    mass s - mass (n + s) ≤ ε ^ 2 / 8 * (2 : ℝ)⁻¹ ^ s * M :=
      mass_loss_le hd hε hεhalf mass hM hstep s n
    _ ≤ ε ^ 2 / 8 * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      simpa using mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ε ^ 2 / 8)
    _ ≤ ε ^ 2 / 4 * mass s := by
      nlinarith [mul_le_mul_of_nonneg_left (hret s).1 (sq_nonneg ε)]

/-- Equation (26): a cleanup at stage `i` establishes the gap trigger at
its own scale.  There are at most `2^(i-1)` nodes before stage `i`; the
additional factor `1/2` from retained mass gives exactly `2^(-i)`.

`N` is the number of old nodes, regarded as a real number.  Its strict
positivity is needed when taking its reciprocal. -/
theorem gap_threshold_of_cleanup {d i : ℕ} (hi : 1 ≤ i)
    {ε δ K N M M' G : ℝ} (hε : 0 ≤ ε) (hK : 1 ≤ K)
    (hN : 0 < N) (hNcard : N ≤ (2 : ℝ) ^ (i - 1))
    (hM : 0 ≤ M) (hretained : M / 2 ≤ M')
    (hscale : δ ≤ ε * (3 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ i)
    (hgap : ε * δ ^ 2 * (2 * K + 1)⁻¹ ^ d * N⁻¹ * M' ≤ G) :
    δ ^ 3 * K⁻¹ ^ d * M ≤ G := by
  have hKpos : 0 < K := by linarith
  have hdenom : 2 * K + 1 ≤ 3 * K := by linarith
  have hdenompos : 0 < 2 * K + 1 := by linarith
  have hcoord : (3 : ℝ)⁻¹ ^ d * K⁻¹ ^ d ≤ (2 * K + 1)⁻¹ ^ d := by
    have hinv : (3 * K)⁻¹ ≤ (2 * K + 1)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hdenompos hdenom
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (3 * K)⁻¹) hinv d
    simpa only [mul_inv_rev, mul_pow, mul_comm] using hpow
  have hNinv : (2 : ℝ)⁻¹ ^ (i - 1) ≤ N⁻¹ := by
    simpa only [one_div, inv_pow] using one_div_le_one_div_of_le hN hNcard
  have hmass : (2 : ℝ)⁻¹ ^ i * M ≤ N⁻¹ * M' := by
    calc
      (2 : ℝ)⁻¹ ^ i * M = (2 : ℝ)⁻¹ ^ (i - 1) * (M / 2) := by
        conv_lhs => rw [show i = (i - 1) + 1 by omega, pow_succ]
        ring
      _ ≤ N⁻¹ * M' := mul_le_mul hNinv hretained
        (div_nonneg hM (by norm_num)) (inv_nonneg.mpr hN.le)
  calc
    δ ^ 3 * K⁻¹ ^ d * M = (δ ^ 2 * (K⁻¹ ^ d * M)) * δ := by ring
    _ ≤ (δ ^ 2 * (K⁻¹ ^ d * M)) *
        (ε * (3 : ℝ)⁻¹ ^ d * (2 : ℝ)⁻¹ ^ i) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (ε * δ ^ 2) * ((3 : ℝ)⁻¹ ^ d * K⁻¹ ^ d) *
        ((2 : ℝ)⁻¹ ^ i * M) := by ring
    _ ≤ (ε * δ ^ 2) * (2 * K + 1)⁻¹ ^ d * (N⁻¹ * M') := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hcoord (mul_nonneg hε (sq_nonneg δ)))
        hmass (by positivity) (by positivity)
    _ = ε * δ ^ 2 * (2 * K + 1)⁻¹ ^ d * N⁻¹ * M' := by ring
    _ ≤ G := hgap

/-- The gap-trigger estimate specialized to the explicit parameter choice. -/
theorem initialScale_gap_threshold {d i : ℕ} (hd : 1 ≤ d) (hi : 1 ≤ i)
    {ε K N M M' G : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K)
    (hN : 0 < N) (hNcard : N ≤ (2 : ℝ) ^ (i - 1))
    (hM : 0 ≤ M) (hretained : M / 2 ≤ M')
    (hgap : ε * scale d (initialScale d ε) i ^ 2 * (2 * K + 1)⁻¹ ^ d * N⁻¹ * M' ≤ G) :
    scale d (initialScale d ε) i ^ 3 * K⁻¹ ^ d * M ≤ G :=
  gap_threshold_of_cleanup hi hε.le hK hN hNcard hM hretained
    (initialScale_scale_bound hd hε hεhalf i) hgap

end EGZ.DecompositionParameters
