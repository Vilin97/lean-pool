/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc
-/
import LeanPool.Erdos1196.Normalization
import LeanPool.Erdos1196.Preliminaries

/-!
# Markov-chain lemmas for primitive sets above `x`

This file proves the main analytic estimates for the Markov-chain construction: the asymptotic
control of `R_Y(m)`, the eventual sub-Markov bound on the transition rows, the eventual estimate
for the normalization constant `B_x`, and the explicit closed formula for the visiting
probabilities.

## Main statements

* `subMarkovRowSumBound`
* `normalizationEstimate`
* `visitProbabilityFormula`
-/

/- ! Markov-chain identities and row-sum bounds used in the proof. -/
open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- If a summand vanishes off the divisors of `n`, its infinite sum is the finite sum over
`n.divisors`. -/
lemma tsum_eq_sum_divisors_of_nondivisors_zero {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {n : ℕ} (hn : 0 < n) (f : ℕ → α) (hf : ∀ q, ¬ q ∣ n → f q = 0) :
    (∑' q : ℕ, f q) = n.divisors.sum f := by
  refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := n.divisors) ?_
  intro q hq
  exact hf q (by grind only [= Nat.mem_divisors])

/-- If a divisor condition is bundled into the summand, the `tsum` reduces to the finite divisor
sum with that condition removed. -/
lemma tsum_eq_sum_divisors_of_dvd_and {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {n : ℕ} (hn : 0 < n) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → α) :
    (∑' q : ℕ, if q ∣ n ∧ P q then f q else 0) =
      n.divisors.sum (fun q => if P q then f q else 0) := by
  calc
    (∑' q : ℕ, if q ∣ n ∧ P q then f q else 0) =
        n.divisors.sum (fun q => if q ∣ n ∧ P q then f q else 0) := by
          refine tsum_eq_sum_divisors_of_nondivisors_zero (n := n) hn _ ?_
          intro q hq
          simp [hq]
    _ = n.divisors.sum (fun q => if P q then f q else 0) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          grind only [= Nat.mem_divisors]

/-- Rewriting `R_Y(m)` as `log m` times the tail sum isolates the input from `tailEstimate`. -/
private lemma ryEqLogMulTailSum (Y m : ℕ) :
    ry Y m = Real.log (m : ℝ) * tailSum m Y := by
  calc
    ry Y m =
        ∑' q : ℕ,
          Real.log (m : ℝ) *
            (if Y ≤ q then Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2) else 0) := by
          refine tsum_congr ?_
          intro q
          by_cases hq : Y ≤ q <;>
            simp [hq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = Real.log (m : ℝ) * tailSum m Y := by
          rw [tailSum, tsum_mul_left]

/-- Rewriting the main term gives `R_Y(m) = 1 - log Y / log (mY) + O(1 / log m)`. -/
private lemma ryApproximation :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃Y m : ℕ⦄, 2 ≤ Y → 2 ≤ m →
        |ry Y m - (1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ))| ≤
          C / Real.log (m : ℝ) := by
  rcases tailEstimate with ⟨C, hCpos, htail⟩
  refine ⟨C, hCpos, ?_⟩
  intro Y m hY hm
  have hm1 : 1 ≤ m := le_trans (by decide : 1 ≤ 2) hm
  have hm_log_nonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hm_log_pos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm))
  have hlogMY_pos : 0 < Real.log ((m * Y : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 4) (show 4 ≤ m * Y by
      simpa using Nat.mul_le_mul hm hY)))
  have hsq : (Real.log (m : ℝ)) ^ 2 ≤ (Real.log ((m * Y : ℕ) : ℝ)) ^ 2 := by
    have hlog_le : Real.log (m : ℝ) ≤ Real.log ((m * Y : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm))
        (by exact_mod_cast (show m ≤ m * Y by
          simpa using Nat.mul_le_mul_left m (le_trans (by decide : 1 ≤ 2) hY)))
    nlinarith
  have hmain :
      Real.log (m : ℝ) * (1 / Real.log ((m * Y : ℕ) : ℝ)) =
        1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ) := by
    have hlogMY_ne : Real.log ((m * Y : ℕ) : ℝ) ≠ 0 := hlogMY_pos.ne'
    have hlog_mul :
        Real.log ((m * Y : ℕ) : ℝ) = Real.log (m : ℝ) + Real.log (Y : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul]
      all_goals positivity
    field_simp [hlogMY_ne]
    linarith
  rw [ryEqLogMulTailSum]
  calc
    |Real.log (m : ℝ) * tailSum m Y - (1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ))|
      = |Real.log (m : ℝ) * (tailSum m Y - 1 / Real.log ((m * Y : ℕ) : ℝ))| := by
          rw [← hmain, mul_sub]
    _ = |Real.log (m : ℝ)| * |tailSum m Y - 1 / Real.log ((m * Y : ℕ) : ℝ)| := by
      rw [abs_mul]
    _ ≤ |Real.log (m : ℝ)| * (C / Real.log ((m * Y : ℕ) : ℝ) ^ 2) := by
      gcongr
      exact htail hm1 hY
    _ ≤ C / Real.log (m : ℝ) := by
      rw [abs_of_nonneg hm_log_nonneg]
      have hm_log_ne : Real.log (m : ℝ) ≠ 0 := hm_log_pos.ne'
      have hlogMY_ne : Real.log ((m * Y : ℕ) : ℝ) ≠ 0 := hlogMY_pos.ne'
      field_simp [hm_log_ne, hlogMY_ne]
      exact hsq

/-- Choosing the cutoff `Y` large enough makes every sufficiently late transition row sum at most
`1`, so the outgoing weights define an eventual sub-Markov chain. -/
lemma subMarkovRowSumBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃Y : ℕ⦄, Real.exp (2 * C) < (Y : ℝ) →
        ∃ x₀ : ℕ, Y ≤ x₀ ∧
          ∀ ⦃m : ℕ⦄, x₀ ≤ m → (∑' q : ℕ, transitionWeight Y m q) ≤ 1 := by
  rcases ryApproximation with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro Y hYlarge
  refine ⟨Y, le_rfl, ?_⟩
  intro m hm
  have hY_gt_one : (1 : ℝ) < (Y : ℝ) :=
    lt_trans (by simpa using Real.one_lt_exp_iff.2 (by nlinarith [hCpos])) hYlarge
  have hY2 : 2 ≤ Y := Nat.succ_le_iff.mpr (by exact_mod_cast hY_gt_one)
  have hm2 : 2 ≤ m := le_trans hY2 hm
  have hm_log_pos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm2))
  have hmY_ge_four : 4 ≤ m * Y := Nat.mul_le_mul hm2 hY2
  have hlogMY_pos : 0 < Real.log ((m * Y : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 4) hmY_ge_four))
  have hupper : ry Y m ≤ 1 - Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ) +
      C / Real.log (m : ℝ) := by
    linarith [(abs_le.mp (hC hY2 hm2)).2]
  rw [show (∑' q : ℕ, transitionWeight Y m q) = ry Y m by simp [transitionWeight, ry]]
  refine hupper.trans ?_
  have hmul_le_sq : (m * Y : ℕ) ≤ m * m := Nat.mul_le_mul_left m hm
  have hlogMY_le : Real.log ((m * Y : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    calc
      Real.log ((m * Y : ℕ) : ℝ) ≤ Real.log ((m : ℝ) * m) :=
        Real.log_le_log
          (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hmY_ge_four))
          (by exact_mod_cast hmul_le_sq)
      _ = 2 * Real.log (m : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]; ring
  have htwoC_lt_logY : 2 * C < Real.log (Y : ℝ) := by
    simpa [Real.log_exp] using (Real.log_lt_log (Real.exp_pos _) hYlarge)
  have herror :
      C / Real.log (m : ℝ) ≤ Real.log (Y : ℝ) / Real.log ((m * Y : ℕ) : ℝ) := by
    have hm_log_ne : Real.log (m : ℝ) ≠ 0 := hm_log_pos.ne'
    have hlogMY_ne : Real.log ((m * Y : ℕ) : ℝ) ≠ 0 := hlogMY_pos.ne'
    field_simp [hm_log_ne, hlogMY_ne]
    nlinarith
  linarith

/-- For each fixed `Y ≥ 2`, the normalizing constants satisfy the asymptotic estimate
`B_x = 1 + O(1 / log x)`. -/
lemma normalizationEstimate {Y : ℕ} (hY : 2 ≤ Y) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        |normalizationConstant x Y - 1| ≤ C / Real.log (x : ℝ) := by
  let S : ℝ := ∑ q ∈ Finset.Ico 1 Y, Λ q / (q : ℝ)
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun q hq =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  rcases normalizationFirstEntryPart_estimate (Y := Y) hY with
    ⟨Centry, hCentry_pos, xentry, hentry⟩
  refine ⟨2 * S + Centry, by nlinarith, max 3 xentry, ?_⟩
  intro x hxx
  have hx3 : 3 ≤ x := le_trans (le_max_left 3 xentry) hxx
  have hsmall := summable_normalizationSmallPrimePart_and_tsum_le (x := x) (Y := Y) hx3
  have hxentry : xentry ≤ x := le_trans (le_max_right 3 xentry) hxx
  have hfirst := hentry hxentry
  have hsmall_nonneg : 0 ≤ ∑' n : ℕ, normalizationSmallPrimePart x Y n :=
    tsum_nonneg fun n => by
      by_cases hn : x ≤ n <;> simp [normalizationSmallPrimePart, hn, smallPrimeEntryWeight_nonneg]
  have hdecomp :
      normalizationConstant x Y =
        (∑' n : ℕ, normalizationSmallPrimePart x Y n) +
          (∑' n : ℕ, normalizationFirstEntryPart x Y n) := by
    rw [normalizationConstant_eq_tsum_parts, Summable.tsum_add hsmall.1 hfirst.1]
  calc
    |normalizationConstant x Y - 1|
      = |(∑' n : ℕ, normalizationSmallPrimePart x Y n) +
          ((∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1)| := by
            rw [hdecomp]
            congr 1
            ring_nf
    _ ≤ ∑' n : ℕ, normalizationSmallPrimePart x Y n +
          |(∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1| := by
            simpa [abs_of_nonneg hsmall_nonneg] using
              abs_add_le (∑' n : ℕ, normalizationSmallPrimePart x Y n)
                ((∑' n : ℕ, normalizationFirstEntryPart x Y n) - 1)
    _ ≤ (2 * S) / Real.log (x : ℝ) + Centry / Real.log (x : ℝ) :=
          add_le_add hsmall.2 hfirst.2
    _ = (2 * S + Centry) / Real.log (x : ℝ) := by ring

/--
Reindexing the last-jump recurrence by the parent state shows that only divisors `m ∣ n` can
contribute to the probability of visiting `n`.
-/
lemma visitProbabilityRecurrence_sum_parents {x Y : ℕ} (chain : MarkovLayer x Y) {n : ℕ}
    (hxn : x ≤ n) (hn : 0 < n) :
    chain.visitProbability n =
      initialDistribution x Y n +
        n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            chain.visitProbability m * transitionWeight Y m (n / m)
          else 0) := by
  have hswap :
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then
          chain.visitProbability (n / q) * transitionWeight Y (n / q) q
        else 0) =
        n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            chain.visitProbability m * transitionWeight Y m (n / m)
          else 0) := by
    simpa [and_left_comm, and_comm] using
      ((Nat.sum_divisorsAntidiagonal'
          (n := n)
          (f := fun m q =>
            if x ≤ m ∧ Y ≤ q then
              chain.visitProbability m * transitionWeight Y m q
            else 0)).symm.trans
        (Nat.sum_divisorsAntidiagonal
          (n := n)
          (f := fun m q =>
            if x ≤ m ∧ Y ≤ q then
              chain.visitProbability m * transitionWeight Y m q
            else 0)))
  calc
    chain.visitProbability n =
        initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              chain.visitProbability (n / q) * transitionWeight Y (n / q) q
            else 0 := by
              simpa using (chain.visitProbabilityRecurrence (n := n) hxn)
    _ = initialDistribution x Y n +
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              chain.visitProbability (n / q) * transitionWeight Y (n / q) q
            else 0) := by
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and (n := n) hn
              (P := fun q => Y ≤ q ∧ x ≤ n / q)
              (fun q => chain.visitProbability (n / q) * transitionWeight Y (n / q) q))
    _ = initialDistribution x Y n +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              chain.visitProbability m * transitionWeight Y m (n / m)
            else 0) := by
          rw [hswap]

/--
For a proper parent `n / q`, any last-jump term with the explicit parent value simplifies to the
common factor `(1 / B_x) * (Λ(q) / (n log^2 n))`.
-/
lemma lastJumpContribution_eq_of_formula {x Y : ℕ} (hx : 2 ≤ x) {n q : ℕ}
    (hq : q ∈ n.divisors) (hqx : Y ≤ q ∧ x ≤ n / q) {v : ℝ}
    (hvisit :
      v = 1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) :
    v * transitionWeight Y (n / q) q =
      (1 / normalizationConstant x Y) *
        ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q) := by
  rcases hqx with ⟨hYq, hxq⟩
  have hdvd : q ∣ n := Nat.dvd_of_mem_divisors hq
  have hq_pos : 0 < q := Nat.pos_of_mem_divisors hq
  have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
    Nat.cast_div hdvd (by exact_mod_cast hq_pos.ne')
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hlog_ne : Real.log ((n : ℝ) / q) ≠ 0 := by
    rw [← hcast_div]
    have hnq2 : 2 ≤ n / q := le_trans hx hxq
    exact (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hnq2))).ne'
  rw [hvisit, transitionWeight, if_pos hYq, hcast_div]
  calc
    (1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) *
        ((Real.log ((n : ℝ) / q) / (Real.log (((n / q) * q : ℕ) : ℝ)) ^ 2) *
          (Λ q / (q : ℝ))) =
        (1 / normalizationConstant x Y) *
          ((1 / (((n : ℝ) / q) * Real.log ((n : ℝ) / q))) *
            ((Real.log ((n : ℝ) / q) / (Real.log (n : ℝ)) ^ 2) *
              (Λ q / (q : ℝ)))) := by
          grind only [Nat.div_mul_cancel hdvd]
    _ = (1 / normalizationConstant x Y) *
          ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q) := by
          congr 1
          field_simp [hlog_ne, hqR]

/--
The divisor decomposition of `log n` rewrites the explicit target formula as the normalized initial
mass plus the filtered von Mangoldt divisor sum.
-/
lemma formula_eq_initialDistribution_add_filteredVonMangoldt {x Y n : ℕ} :
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
      initialDistribution x Y n +
        (1 / normalizationConstant x Y) *
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
            else 0) := by
  calc
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
        (1 / normalizationConstant x Y) *
          ((1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) *
            (n.divisors.sum fun q => Λ q)) := by
          rw [ArithmeticFunction.vonMangoldt_sum (n := n)]
          grind only
    _ = (1 / normalizationConstant x Y) *
          (entryWeight x Y n +
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0)) := by
          congr 1
          simpa [entryWeightFactor] using
            (entryWeight_add_filtered_vonMangoldt_eq_entryWeightFactor_sum_divisors x Y n).symm
    _ = initialDistribution x Y n +
          (1 / normalizationConstant x Y) *
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0) := by
          simp [initialDistribution, div_eq_mul_inv, mul_add, mul_assoc, mul_left_comm, mul_comm]

/--
If every last-jump parent already has the explicit value `1 / (B_x n log n)`, then the recurrence
right-hand side collapses to the closed formula for the visit probability at `n`.
-/
lemma explicitFormula_eq_recurrence_rhs {x Y n : ℕ} (hx : 2 ≤ x) (hn : x ≤ n) {f : ℕ → ℝ}
    (hvisit :
      ∀ ⦃q : ℕ⦄, q ∈ n.divisors → Y ≤ q ∧ x ≤ n / q → q ≠ 1 →
        f (n / q) =
          1 / (normalizationConstant x Y * ((n : ℝ) / q) * Real.log ((n : ℝ) / q))) :
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
      initialDistribution x Y n +
        ∑' q : ℕ,
          if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
            f (n / q) * transitionWeight Y (n / q) q
          else 0 := by
  have hn_pos : 0 < n := by omega
  have hrec :
      n.divisors.sum (fun q =>
        if Y ≤ q ∧ x ≤ n / q then
          f (n / q) * transitionWeight Y (n / q) q
        else 0) =
        (1 / normalizationConstant x Y) *
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
            else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro q hq
    by_cases hqx : Y ≤ q ∧ x ≤ n / q
    · by_cases hq1 : q = 1
      · subst hq1
        simp [transitionWeight, hqx]
      · simpa [hqx] using
          (lastJumpContribution_eq_of_formula (x := x) (Y := Y) (n := n) (q := q)
            hx hq hqx (v := f (n / q)) (hvisit hq hqx hq1))
    · simp [hqx]
  calc
    1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) =
        initialDistribution x Y n +
          (1 / normalizationConstant x Y) *
            n.divisors.sum (fun q =>
              if Y ≤ q ∧ x ≤ n / q then
                (1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * Λ q
              else 0) := by
            simpa using
              formula_eq_initialDistribution_add_filteredVonMangoldt (x := x) (Y := Y) (n := n)
    _ = initialDistribution x Y n +
          n.divisors.sum (fun q =>
            if Y ≤ q ∧ x ≤ n / q then
              f (n / q) * transitionWeight Y (n / q) q
            else 0) := by
          rw [hrec]
    _ = initialDistribution x Y n +
          ∑' q : ℕ,
            if Y ≤ q ∧ q ∣ n ∧ x ≤ n / q then
              f (n / q) * transitionWeight Y (n / q) q
            else 0 := by
          congr 1
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and (n := n) hn_pos
              (P := fun q => Y ≤ q ∧ x ≤ n / q)
              (fun q => f (n / q) * transitionWeight Y (n / q) q)).symm

/--
The Markov layer visits each state `n ≥ x` with the explicit probability
`1 / (B_x n log n)`. The lower bound `2 ≤ x` guarantees that the logarithms in this formula are
positive.
-/
lemma visitProbabilityFormula {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x) {n : ℕ}
    (hn : x ≤ n) :
    chain.visitProbability n =
      1 / (normalizationConstant x Y * (n : ℝ) * Real.log (n : ℝ)) := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  rw [chain.visitProbabilityRecurrence (n := n) hn]
  symm
  refine explicitFormula_eq_recurrence_rhs (x := x) (Y := Y) (n := n) hx hn
    (f := chain.visitProbability) ?_
  intro q hq hqx hq1
  have hn_pos : 0 < n := by omega
  have hq_ne_zero : q ≠ 0 := (Nat.pos_of_mem_divisors hq).ne'
  have hlt : n / q < n := by
    have hq_gt_one : 1 < q := by omega
    exact Nat.div_lt_self hn_pos hq_gt_one
  have hcast_div : ((n / q : ℕ) : ℝ) = (n : ℝ) / q :=
    Nat.cast_div (Nat.dvd_of_mem_divisors hq) (by exact_mod_cast hq_ne_zero)
  simpa [hcast_div] using ih (n / q) hlt hqx.2

/-- Under the standing hypotheses `2 ≤ x` and `B_x > 0`, the visiting probabilities are
nonnegative on the state space `n ≥ x`. -/
lemma visitProbability_nonneg {x Y : ℕ} (chain : MarkovLayer x Y) (hx : 2 ≤ x)
    (hB : 0 < normalizationConstant x Y) {n : ℕ} (hn : x ≤ n) :
    0 ≤ chain.visitProbability n := by
  rw [visitProbabilityFormula chain hx hn]
  positivity

end PrimitiveSetsAboveX
