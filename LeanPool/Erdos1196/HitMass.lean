/-
Copyright (c) 2026 Math Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math Inc.
-/
import LeanPool.Erdos1196.Markov
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Hit mass and final reductions

This file develops the `ENNReal` mass-flow layer behind the Markov-chain argument. It defines
exact-step arrival mass, surviving mass before the first hit of a set `A`, and the total first-hit
mass of `A`.

The central estimate is a telescope: if the restricted initial mass is at most `1` and each row of
the transition kernel has total mass at most `1`, then the total first-hit mass of `A` is at most
`1`. For primitive `A`, this is the visit-mass inequality used in the final argument, because finite
paths in the multiplicative chain can meet `A` at most once.

## Main definitions

* `initialMass`
* `transitionKernel`
* `arrivalMass`
* `survivingArrivalMass`
* `firstHitMassAtStep`
* `visitMass`

## Main statements

* `MarkovLayer.kernelRowBound`
* `tsum_initialMass_eq_one`
* `visitMass_le_of_bounds`
* `PrimitiveSet.summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one`
-/

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The normalized initial mass restricted to the state space `n ≥ x`. -/
noncomputable def initialMass (x Y n : ℕ) : ENNReal :=
  ENNReal.ofReal (if x ≤ n then initialDistribution x Y n else 0)

/--
The transition kernel on states `n ≥ x`, viewed as an `ENNReal`-valued mass function.

The state `m` can send mass to `n` only when `m ≥ x`, `m ∣ n`, and the quotient `n / m` is a
valid jump factor `q ≥ Y`.
-/
noncomputable def transitionKernel (x Y m n : ℕ) : ENNReal :=
  if x ≤ m ∧ m ∣ n ∧ Y ≤ n / m then
    ENNReal.ofReal (transitionWeight Y m (n / m))
  else
    0

/-- Exact-step arrival mass at state `n` after `k` steps in the multiplicative chain. -/
noncomputable def arrivalMass {x Y : ℕ} (chain : MarkovLayer x Y) : ℕ → ℕ → ENNReal
  | 0, n => initialMass x Y n
  | k + 1, n => ∑' m : ℕ, arrivalMass chain k m * transitionKernel x Y m n

/--
The surviving mass at state `n` after `k` steps, obtained by discarding every path that has already
hit `A`.
-/
noncomputable def survivingArrivalMass {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ℕ → ENNReal
  | 0, n => Aᶜ.indicator (initialMass x Y) n
  | k + 1, n =>
      Aᶜ.indicator
        (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

/--
The mass that first hits `A` exactly at step `k`.

For `k = 0` this is the initial mass already inside `A`, and for `k + 1` it is the mass
propagated from the surviving mass at step `k` into `A`.
-/
noncomputable def firstHitMassAtStep {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ENNReal
  | 0 => ∑' n : ℕ, A.indicator (initialMass x Y) n
  | k + 1 =>
      ∑' n : ℕ,
        A.indicator
          (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

/--
The total visit mass of `A`, counted by the first hit of `A` along each path. For primitive sets,
this agrees with the usual total mass of visits because finite multiplicative paths meet `A` at
most once.
-/
noncomputable def visitMass {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) : ENNReal :=
  ∑' k : ℕ, firstHitMassAtStep chain A k

/-- The jump weights are nonnegative termwise. -/
private lemma transitionWeight_nonneg (Y m q : ℕ) : 0 ≤ transitionWeight Y m q := by
  by_cases hYq : Y ≤ q
  · by_cases hm : m = 0
    · simp [transitionWeight, hYq, hm]
    · have hm1 : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
      have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := by
        positivity
      rw [transitionWeight, if_pos hYq]
      refine mul_nonneg ?_ ?_
      · exact div_nonneg hlog_nonneg (sq_nonneg _)
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · simp [transitionWeight, hYq]

/--
For a fixed parent state `m`, the faithful kernel is the divisor-indicator reindexing of the jump
weights along the multiples of `m`.
-/
private lemma transitionKernel_eq_indicator {x Y m n : ℕ} (hm : x ≤ m) :
    transitionKernel x Y m n =
      Set.indicator {n : ℕ | m ∣ n}
        (fun n => ENNReal.ofReal (transitionWeight Y m (n / m))) n := by
  by_cases hdiv : m ∣ n
  · by_cases hYnm : Y ≤ n / m
    · simp [transitionKernel, hm, hdiv, hYnm, Set.indicator, transitionWeight]
    · simp [transitionKernel, hm, hdiv, hYnm, Set.indicator, transitionWeight]
  · simp [transitionKernel, hm, hdiv, Set.indicator]

/--
Reindexing the faithful kernel row along the multiples of `m` turns its `ENNReal` row sum into the
corresponding series of jump weights.
-/
private lemma tsum_transitionKernel_eq {x Y m : ℕ} (hm : x ≤ m) :
    (∑' n : ℕ, transitionKernel x Y m n) = ∑' q : ℕ, ENNReal.ofReal (transitionWeight Y m q) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hx0 : x = 0 := le_antisymm hm (Nat.zero_le _)
    subst hx0
    simp [transitionKernel, transitionWeight]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    let e : ℕ ≃ {n : ℕ // m ∣ n} :=
      { toFun := fun q => ⟨m * q, dvd_mul_right m q⟩
        invFun := fun n => n.1 / m
        left_inv := by
          intro q
          simpa [Nat.mul_comm] using Nat.mul_div_left q hmpos
        right_inv := by
          intro n
          apply Subtype.ext
          simpa [Nat.mul_comm] using Nat.div_mul_cancel n.2 }
    calc
      (∑' n : ℕ, transitionKernel x Y m n)
        = ∑' n : {n : ℕ // m ∣ n}, ENNReal.ofReal (transitionWeight Y m (n.1 / m)) := by
            rw [show (fun n => transitionKernel x Y m n) =
              Set.indicator {n : ℕ | m ∣ n}
                (fun n => ENNReal.ofReal (transitionWeight Y m (n / m))) by
                  funext n
                  exact transitionKernel_eq_indicator (x := x) (Y := Y) (m := m) hm]
            simpa using (tsum_subtype {n : ℕ | m ∣ n}
              (fun n => ENNReal.ofReal (transitionWeight Y m (n / m)))).symm
      _ = ∑' q : ℕ, ENNReal.ofReal (transitionWeight Y m ((e q).1 / m)) := by
            simpa [e] using (Equiv.tsum_eq e
              (fun n : {n : ℕ // m ∣ n} => ENNReal.ofReal (transitionWeight Y m (n.1 / m)))).symm
      _ = ∑' q : ℕ, ENNReal.ofReal (transitionWeight Y m q) := by
            grind only [= Equiv.coe_fn_mk]

/--
The tail summand underlying `transitionWeight` is summable for every `m ≥ 1`. The proof uses
`tailEstimate` at a sufficiently large cutoff and then restores the finitely many missing terms.
-/
private lemma summable_transitionTailSummand (Y m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ =>
      if Y ≤ q then
        Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
      else
        0) := by
  rcases tailEstimate with ⟨C, hCpos, htail⟩
  let N : ℕ := max Y (Nat.ceil (Real.exp C) + 1)
  have hN_ge_Y : Y ≤ N := le_max_left Y (Nat.ceil (Real.exp C) + 1)
  have hN_ge_two : 2 ≤ N := by
    have hceil_pos : 0 < Nat.ceil (Real.exp C) := Nat.ceil_pos.2 (Real.exp_pos _)
    have hN0_ge_two : 2 ≤ Nat.ceil (Real.exp C) + 1 := by
      omega
    exact le_trans hN0_ge_two (le_max_right Y (Nat.ceil (Real.exp C) + 1))
  have hN_log_large : C < Real.log ((m * N : ℕ) : ℝ) := by
    calc
      C = Real.log (Real.exp C) := by rw [Real.log_exp]
      _ < Real.log ((m * N : ℕ) : ℝ) := by
        apply Real.log_lt_log (Real.exp_pos _)
        calc
          Real.exp C ≤ (Nat.ceil (Real.exp C) : ℝ) := by exact_mod_cast Nat.le_ceil _
          _ < (Nat.ceil (Real.exp C) + 1 : ℕ) := by
              exact_mod_cast Nat.lt_succ_self (Nat.ceil (Real.exp C))
          _ ≤ (N : ℝ) := by
              exact_mod_cast (le_max_right Y (Nat.ceil (Real.exp C) + 1))
          _ ≤ (((m * N : ℕ) : ℝ)) := by
              exact_mod_cast (by
                simpa [one_mul, Nat.mul_comm] using Nat.mul_le_mul_right N hm)
  have hN_log_pos : 0 < Real.log ((m * N : ℕ) : ℝ) := lt_trans hCpos hN_log_large
  have h_err_lt :
      C / Real.log ((m * N : ℕ) : ℝ) ^ 2 < 1 / Real.log ((m * N : ℕ) : ℝ) := by
    have hlog_ne : Real.log ((m * N : ℕ) : ℝ) ≠ 0 := hN_log_pos.ne'
    field_simp [hlog_ne]
    nlinarith
  have htail_pos : 0 < tailSum m N := by
    grind only [= abs.eq_1, = max_def]
  have hsN :
      Summable (fun q : ℕ =>
        if N ≤ q then
          Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
        else
          0) := by
    by_contra hsN
    have hzero : tailSum m N = 0 := by
      simpa [tailSum] using (tsum_eq_zero_of_not_summable hsN)
    exact htail_pos.ne' hzero
  rw [← Finset.summable_compl_iff (s := Finset.range N)]
  refine (hsN.subtype {q : ℕ | q ∉ Finset.range N}).congr ?_
  intro q
  have hq : N ≤ q := by
    simpa [Finset.mem_range, not_lt] using q.2
  have hYq : Y ≤ q := le_trans hN_ge_Y hq
  simp [hq, hYq]

/-- The transition-weight series is summable for every `m ≥ 1`. -/
private lemma summable_transitionWeight (Y m : ℕ) (hm : 1 ≤ m) :
    Summable (fun q : ℕ => transitionWeight Y m q) := by
  let g : ℕ → ℝ := fun q =>
    if Y ≤ q then
      Λ q / ((q : ℝ) * Real.log ((m * q : ℕ) : ℝ) ^ 2)
    else
      0
  simpa [g, transitionWeight, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (summable_transitionTailSummand Y m hm).mul_left (Real.log (m : ℝ))

namespace MarkovLayer

/--
The real row-sum bound `∑_{q ≥ Y} p(m, mq) ≤ 1` transfers directly to the `ENNReal` kernel
`transitionKernel`, which is the form needed in the first-hit mass argument.
-/
theorem kernelRowBound {x Y : ℕ} (chain : MarkovLayer x Y) :
    ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1 := by
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    have hzero : ∀ n : ℕ, transitionKernel x Y 0 n = 0 := by
      intro n
      simp [transitionKernel, transitionWeight]
    rw [show (∑' n : ℕ, transitionKernel x Y 0 n) = 0 by
      exact (ENNReal.tsum_eq_zero).2 hzero]
    simp
  · have hmpos : 0 < m := Nat.pos_iff_ne_zero.mpr hm0
    have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have hs : Summable (fun q : ℕ => transitionWeight Y m q) :=
      summable_transitionWeight Y m hm1
    rw [tsum_transitionKernel_eq hm,
      ← ENNReal.ofReal_tsum_of_nonneg (transitionWeight_nonneg Y m) hs]
    exact_mod_cast chain.transitionSubMarkov hm

end MarkovLayer

/-- Once `B_x > 0`, the restricted initial mass has total mass exactly `1`. -/
lemma tsum_initialMass_eq_one {x Y : ℕ} (hB : 0 < normalizationConstant x Y) :
    (∑' n : ℕ, initialMass x Y n) = 1 := by
  let f : ℕ → ℝ := fun n => if x ≤ n then entryWeight x Y n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hn : x ≤ n
    · simpa [f, hn, entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight] using
        add_nonneg (smallPrimeEntryWeight_nonneg Y n) (firstEntryEntryWeight_nonneg x Y n)
    · simp [f, hn]
  have hf_summable : Summable f := by
    by_contra hf
    exact hB.ne' (by simpa [normalizationConstant, f] using (tsum_eq_zero_of_not_summable hf))
  calc
    ∑' n : ℕ, initialMass x Y n = ∑' n : ℕ, ENNReal.ofReal (f n / normalizationConstant x Y) := by
      refine tsum_congr ?_
      intro n
      by_cases hn : x ≤ n <;> simp [initialMass, f, initialDistribution, hn]
    _ = ENNReal.ofReal (∑' n : ℕ, f n / normalizationConstant x Y) := by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun n => div_nonneg (hf_nonneg n) hB.le)
        (by simpa [div_eq_mul_inv] using hf_summable.mul_right ((normalizationConstant x Y)⁻¹))]
    _ = ENNReal.ofReal ((∑' n : ℕ, f n) / normalizationConstant x Y) := by
      congr 1
      rw [show (fun n : ℕ => f n / normalizationConstant x Y) =
        fun n => f n * (normalizationConstant x Y)⁻¹ by
          funext n
          simp [div_eq_mul_inv]]
      rw [tsum_mul_right]
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [show ∑' n : ℕ, f n = normalizationConstant x Y by simp [normalizationConstant, f]]
      field_simp [hB.ne']
      simp
/-- A kernel term landing below `x` is zero once `Y ≥ 1` and `x > 0`. -/
private lemma transitionKernel_eq_zero_of_lt {x Y m n : ℕ} (hY : 1 ≤ Y) (hn : n < x) :
    transitionKernel x Y m n = 0 := by
  by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
  · have hqm : 1 ≤ n / m := le_trans hY hcond.2.2
    have hm_le_prod : m ≤ m * (n / m) := by
      simpa [one_mul] using Nat.mul_le_mul_left m hqm
    have hprod_le_n : m * (n / m) ≤ n := Nat.mul_div_le n m
    lia
  · simp [transitionKernel, hcond]

/-- States below `x` carry no surviving mass either. -/
private lemma survivingArrivalMass_eq_zero_of_lt {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ)
    (hx : 0 < x) (hY : 1 ≤ Y) :
    ∀ k {n : ℕ}, n < x → survivingArrivalMass chain A k n = 0
  | 0, n, hn => by
      by_cases hnA : n ∈ A <;> simp [survivingArrivalMass, initialMass, hnA, hn.not_ge]
  | k + 1, n, hn => by
      by_cases hnA : n ∈ A
      · simp [survivingArrivalMass, Set.indicator, hnA]
      · rw [survivingArrivalMass]
        have hnAc : n ∈ Aᶜ := by simpa using hnA
        rw [Set.indicator_of_mem hnAc]
        apply (ENNReal.tsum_eq_zero).2
        intro m
        by_cases hm : x ≤ m
        · simp [transitionKernel_eq_zero_of_lt (m := m) hY hn]
        · simp [survivingArrivalMass_eq_zero_of_lt chain A hx hY k (lt_of_not_ge hm)]

/-- The initial distribution is nonnegative once `B_x` is positive. -/
private lemma initialDistribution_nonneg {x Y n : ℕ} (hB : 0 < normalizationConstant x Y) :
    0 ≤ initialDistribution x Y n := by
  have hentry : 0 ≤ entryWeight x Y n := by
    rw [entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight]
    exact add_nonneg (smallPrimeEntryWeight_nonneg Y n) (firstEntryEntryWeight_nonneg x Y n)
  exact div_nonneg hentry hB.le

/--
If no element of `A` divides `n`, then every path arriving at `n` has avoided `A`, so the
surviving mass at `n` agrees with the unrestricted arrival mass.
-/
private lemma survivingArrivalMass_eq_arrivalMass_of_no_dvd {x Y : ℕ} (chain : MarkovLayer x Y)
    (A : Set ℕ) :
    ∀ k {n : ℕ}, (∀ ⦃a : ℕ⦄, a ∈ A → a ∣ n → False) →
      survivingArrivalMass chain A k n = arrivalMass chain k n
  | 0, n, hNo => by
      have hnA : n ∉ A := by
        intro hnA
        exact hNo hnA dvd_rfl
      simp [survivingArrivalMass, arrivalMass, hnA]
  | k + 1, n, hNo => by
      have hnA : n ∉ A := by
        intro hnA
        exact hNo hnA dvd_rfl
      simpa [survivingArrivalMass, arrivalMass, hnA] using
        (tsum_congr fun m => by
          by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
          · have hNo_m : ∀ ⦃a : ℕ⦄, a ∈ A → a ∣ m → False := by
              intro a haA hadivm
              exact hNo haA (dvd_trans hadivm hcond.2.1)
            simp [transitionKernel, hcond,
              survivingArrivalMass_eq_arrivalMass_of_no_dvd chain A k hNo_m]
          · simp [transitionKernel, hcond])

/--
For a fixed target `n`, the only possible parents are the divisors `m ∣ n`, so the step
`k + 1` arrival mass is a finite parent sum.
-/
private lemma arrivalMass_succ_sum_parents {x Y : ℕ} (chain : MarkovLayer x Y) {k n : ℕ}
    (hn : 0 < n) :
    arrivalMass chain (k + 1) n =
      n.divisors.sum (fun m =>
        if x ≤ m ∧ Y ≤ n / m then
          arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
        else 0) := by
  calc
    arrivalMass chain (k + 1) n =
        ∑' m : ℕ,
          if x ≤ m ∧ m ∣ n ∧ Y ≤ n / m then
            arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
      else 0 := by
            simp [arrivalMass, transitionKernel, and_left_comm, mul_comm]
    _ = n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
          else 0) := by
          simpa [and_assoc, and_left_comm, and_comm] using
            (tsum_eq_sum_divisors_of_dvd_and hn
              (P := fun m => x ≤ m ∧ Y ≤ n / m)
              (fun m =>
                arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))))

/--
The total arrival mass at `n` satisfies the same parent-state recurrence as the visit
probability, but now as an `ENNReal` identity.
-/
private lemma tsum_arrivalMass_eq_initial_add_parentSum {x Y : ℕ} (chain : MarkovLayer x Y)
    {n : ℕ}
    (hn : 0 < n) :
    (∑' k : ℕ, arrivalMass chain k n) =
      initialMass x Y n +
        n.divisors.sum (fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            (∑' k : ℕ, arrivalMass chain k m) * ENNReal.ofReal (transitionWeight Y m (n / m))
          else 0) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  calc
    arrivalMass chain 0 n + ∑' k : ℕ, arrivalMass chain (k + 1) n
      = initialMass x Y n + ∑' k : ℕ, arrivalMass chain (k + 1) n := by
          simp [arrivalMass]
    _ = initialMass x Y n +
          ∑' k : ℕ,
            n.divisors.sum (fun m =>
              if x ≤ m ∧ Y ≤ n / m then
                arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
              else 0) := by
            congr 1
            apply tsum_congr
            intro k
            exact arrivalMass_succ_sum_parents chain hn
    _ = initialMass x Y n +
          n.divisors.sum (fun m =>
            ∑' k : ℕ,
              if x ≤ m ∧ Y ≤ n / m then
                arrivalMass chain k m * ENNReal.ofReal (transitionWeight Y m (n / m))
              else 0) := by
            congr 1
            exact Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)
    _ = initialMass x Y n +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              (∑' k : ℕ, arrivalMass chain k m) * ENNReal.ofReal (transitionWeight Y m (n / m))
            else 0) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hcond : x ≤ m ∧ Y ≤ n / m
            · simp [hcond, ENNReal.tsum_mul_right]
            · simp [hcond]

private lemma lt_of_dvd_of_two_le_div {m n Y : ℕ} (hmn : m ∣ n) (hY : 2 ≤ Y)
    (hYm : Y ≤ n / m) : m < n := by
  have hm_pos : 0 < m := by
    by_contra hm_pos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm_pos
    have : Y ≤ 0 := by simpa [hm0] using hYm
    omega
  have hmul : m * 2 ≤ n := by
    calc
      m * 2 ≤ m * (n / m) := Nat.mul_le_mul_left _ (le_trans hY hYm)
      _ = n := Nat.mul_div_cancel' hmn
  omega

/--
Summing the exact-step arrival masses recovers the visit probability. This is the bridge from the
mass-flow formalism to `visitProbability`.
-/
private lemma tsum_arrivalMass_eq_ofReal_visitProbability {x Y : ℕ} (chain : MarkovLayer x Y)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hB : 0 < normalizationConstant x Y) {n : ℕ} (hn : x ≤ n) :
    (∑' k : ℕ, arrivalMass chain k n) = ENNReal.ofReal (chain.visitProbability n) := by
  refine Nat.strong_induction_on n ?_ hn
  intro n ih hn
  have hn_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) (le_trans hx hn)
  have hinit :
      initialMass x Y n = ENNReal.ofReal (initialDistribution x Y n) := by
    simp [initialMass, hn]
  have harr :=
    tsum_arrivalMass_eq_initial_add_parentSum chain hn_pos
  rw [hinit] at harr
  have hterm_nonneg :
      ∀ m ∈ n.divisors, 0 ≤
        if x ≤ m ∧ Y ≤ n / m then
          chain.visitProbability m * transitionWeight Y m (n / m)
        else 0 := by
    intro m hm
    by_cases hcond : x ≤ m ∧ Y ≤ n / m
    · simpa [hcond] using
        mul_nonneg (visitProbability_nonneg chain hx hB hcond.1)
          (transitionWeight_nonneg Y m (n / m))
    · simp [hcond]
  have hsum_nonneg :
      0 ≤ n.divisors.sum (fun m =>
        if x ≤ m ∧ Y ≤ n / m then
          chain.visitProbability m * transitionWeight Y m (n / m)
        else 0) :=
    Finset.sum_nonneg fun m hm => hterm_nonneg m hm
  have hvisit :
      ENNReal.ofReal (chain.visitProbability n) =
        ENNReal.ofReal (initialDistribution x Y n) +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              ENNReal.ofReal (chain.visitProbability m * transitionWeight Y m (n / m))
            else 0) := by
    simpa [apply_ite ENNReal.ofReal,
      ENNReal.ofReal_add (initialDistribution_nonneg hB) hsum_nonneg,
      ENNReal.ofReal_sum_of_nonneg
        (s := n.divisors)
        (f := fun m =>
          if x ≤ m ∧ Y ≤ n / m then
            chain.visitProbability m * transitionWeight Y m (n / m)
          else 0)
        hterm_nonneg] using
      congrArg ENNReal.ofReal (visitProbabilityRecurrence_sum_parents chain hn hn_pos)
  calc
    (∑' k : ℕ, arrivalMass chain k n) =
        ENNReal.ofReal (initialDistribution x Y n) +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              (∑' k : ℕ, arrivalMass chain k m) *
                ENNReal.ofReal (transitionWeight Y m (n / m))
            else 0) := harr
    _ = ENNReal.ofReal (initialDistribution x Y n) +
          n.divisors.sum (fun m =>
            if x ≤ m ∧ Y ≤ n / m then
              ENNReal.ofReal (chain.visitProbability m * transitionWeight Y m (n / m))
            else 0) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hcond : x ≤ m ∧ Y ≤ n / m
            · have hm_lt_n : m < n := by
                exact lt_of_dvd_of_two_le_div (Nat.dvd_of_mem_divisors hm) hY hcond.2
              rw [ih m hm_lt_n hcond.1]
              rw [ENNReal.ofReal_mul (visitProbability_nonneg chain hx hB hcond.1)]
            · simp [hcond]
    _ = ENNReal.ofReal (chain.visitProbability n) := hvisit.symm

namespace PrimitiveSet

/--
For a primitive set, every arrival in `A` is already a first hit of `A`, because a multiplicative
path cannot contain two distinct elements of a primitive set.
-/
private lemma firstHitMassAtStep_eq_tsum_indicator_arrivalMass {x Y : ℕ}
    (chain : MarkovLayer x Y) {A : Set ℕ} (hA : PrimitiveSet A) (hY : 2 ≤ Y) :
    ∀ k : ℕ,
      firstHitMassAtStep chain A k = ∑' n : ℕ, A.indicator (arrivalMass chain k) n
  | 0 => by
      rfl
  | k + 1 => by
      apply tsum_congr
      intro n
      by_cases hnA : n ∈ A
      · simpa [firstHitMassAtStep, arrivalMass, hnA] using
          (tsum_congr fun m => by
            by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
            · have hNo_m : ∀ ⦃a : ℕ⦄, a ∈ A → a ∣ m → False := by
                intro a haA hadivm
                have hmn : m = n := by
                  apply Nat.dvd_antisymm hcond.2.1
                  simpa [hA haA hnA (dvd_trans hadivm hcond.2.1)] using hadivm
                exact (lt_of_dvd_of_two_le_div hcond.2.1 hY hcond.2.2).ne hmn
              simp [transitionKernel, hcond,
                survivingArrivalMass_eq_arrivalMass_of_no_dvd chain A k hNo_m]
            · simp [transitionKernel, hcond])
      · simp [hnA]

/--
For a primitive set `A ⊆ Ici x`, the `ENNReal` sum of the indicator visit probabilities is exactly
the first-hit mass `visitMass chain A`.
-/
private theorem tsum_indicator_ofReal_visitProbability_eq_visitMass {x Y : ℕ}
    (chain : MarkovLayer x Y) {A : Set ℕ} (hA : PrimitiveSet A) (hAx : A ⊆ Set.Ici x)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hB : 0 < normalizationConstant x Y) :
    (∑' n : ℕ, A.indicator (fun n => ENNReal.ofReal (chain.visitProbability n)) n) =
      visitMass chain A := by
  calc
    (∑' n : ℕ, A.indicator (fun n => ENNReal.ofReal (chain.visitProbability n)) n) =
        ∑' n : ℕ, ∑' k : ℕ, A.indicator (arrivalMass chain k) n := by
          apply tsum_congr
          intro n
          by_cases hnA : n ∈ A
          · simpa [hnA] using
              (tsum_arrivalMass_eq_ofReal_visitProbability chain hx hY hB (hAx hnA)).symm
          · simp [hnA]
    _ = ∑' k : ℕ, ∑' n : ℕ, A.indicator (arrivalMass chain k) n := by
          rw [ENNReal.tsum_comm]
    _ = ∑' k : ℕ, firstHitMassAtStep chain A k := by
          apply tsum_congr
          intro k
          simpa using
            (PrimitiveSet.firstHitMassAtStep_eq_tsum_indicator_arrivalMass chain hA hY k).symm
    _ = visitMass chain A := by rw [visitMass]

/--
If the first-hit mass budget of a primitive set `A` is at most `1`, then the real indicator
series of visit probabilities is summable and its total mass is at most `1`.
-/
theorem summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one
    {x Y : ℕ} (chain : MarkovLayer x Y) {A : Set ℕ} (hA : PrimitiveSet A) (hAx : A ⊆ Set.Ici x)
    (hx : 2 ≤ x) (hY : 2 ≤ Y) (hB : 0 < normalizationConstant x Y)
    (hVisitMass : visitMass chain A ≤ 1) :
    Summable (A.indicator (chain.visitProbability)) ∧
      (∑' n : ℕ, A.indicator (chain.visitProbability) n) ≤ 1 := by
  let f : ℕ → ENNReal := fun n =>
    A.indicator (fun n => ENNReal.ofReal (chain.visitProbability n)) n
  have hmass :
      (∑' n : ℕ, f n) = visitMass chain A := by
    simpa [f] using
      PrimitiveSet.tsum_indicator_ofReal_visitProbability_eq_visitMass chain hA hAx hx hY hB
  have htop :
      (∑' n : ℕ, f n) ≠ ⊤ := by
    rw [hmass]
    exact ne_of_lt <| lt_of_le_of_lt hVisitMass (by simp)
  have hseries :
      HasSum (A.indicator (chain.visitProbability))
        (visitMass chain A).toReal := by
    convert (ENNReal.hasSum_toReal (f := f) htop) using 1
    · funext n
      by_cases hnA : n ∈ A
      · simp [f, hnA, ENNReal.toReal_ofReal, visitProbability_nonneg chain hx hB (hAx hnA)]
      · simp [f, hnA]
    · rw [← hmass, ENNReal.tsum_toReal_eq]
      intro n
      by_cases hnA : n ∈ A <;> simp [f, hnA]
  refine ⟨hseries.summable, ?_⟩
  rw [hseries.tsum_eq]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hVisitMass)

end PrimitiveSet

/-- Splitting a series into the part supported on `A` and the part supported on `Aᶜ` recovers the
original total mass. -/
private lemma tsum_indicator_add_tsum_indicator_compl (A : Set ℕ) (f : ℕ → ENNReal) :
    (∑' n : ℕ, A.indicator f n) + (∑' n : ℕ, Aᶜ.indicator f n) = ∑' n : ℕ, f n := by
  rw [← ENNReal.tsum_add]
  exact congrArg (fun g : ℕ → ENNReal => ∑' n : ℕ, g n) (Set.indicator_self_add_compl A f)

/-- The step-0 hit mass together with the step-0 surviving mass is exactly the initial mass. -/
private lemma firstHitMassAtStep_zero_add_tsum_survivingArrivalMass_zero {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) :
    firstHitMassAtStep chain A 0 + (∑' n : ℕ, survivingArrivalMass chain A 0 n) =
      ∑' n : ℕ, initialMass x Y n := by
  simpa [firstHitMassAtStep, survivingArrivalMass] using
    tsum_indicator_add_tsum_indicator_compl A (initialMass x Y)

/--
At step `k + 1`, the first-hit mass together with the surviving mass is exactly the mass
propagated from the surviving mass at step `k`.
-/
private lemma firstHitMassAtStep_succ_add_tsum_survivingArrivalMass {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (k : ℕ) :
    firstHitMassAtStep chain A (k + 1) +
        (∑' n : ℕ, survivingArrivalMass chain A (k + 1) n) =
      ∑' n : ℕ, ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n := by
  simpa [firstHitMassAtStep, survivingArrivalMass] using
    tsum_indicator_add_tsum_indicator_compl A
      (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n)

/--
The next first-hit mass together with the next surviving mass is bounded by the current surviving
mass.
-/
private lemma firstHitMassAtStep_succ_add_tsum_survivingArrivalMass_le {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (hx : 0 < x) (hY : 1 ≤ Y)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) (k : ℕ) :
    firstHitMassAtStep chain A (k + 1) +
        (∑' n : ℕ, survivingArrivalMass chain A (k + 1) n) ≤
      ∑' n : ℕ, survivingArrivalMass chain A k n := by
  rw [firstHitMassAtStep_succ_add_tsum_survivingArrivalMass]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc
    ∑' m : ℕ, survivingArrivalMass chain A k m * (∑' n : ℕ, transitionKernel x Y m n)
      ≤ ∑' m : ℕ, survivingArrivalMass chain A k m * 1 := by
          refine ENNReal.tsum_le_tsum ?_
          intro m
          by_cases hm : x ≤ m
          · gcongr
            exact hkernel hm
          · rw [survivingArrivalMass_eq_zero_of_lt chain A hx hY k (lt_of_not_ge hm)]
            simp
    _ = ∑' m : ℕ, survivingArrivalMass chain A k m := by simp

/--
The partial first-hit mass up to step `N`, together with the surviving mass at time `N`, stays
within the initial mass budget.
-/
private lemma sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
    {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (hx : 0 < x) (hY : 1 ≤ Y)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) :
    ∀ N : ℕ,
      (∑ k ∈ Finset.range (N + 1), firstHitMassAtStep chain A k) +
          (∑' n : ℕ, survivingArrivalMass chain A N n) ≤
        ∑' n : ℕ, initialMass x Y n
  | 0 => by
      simpa using (firstHitMassAtStep_zero_add_tsum_survivingArrivalMass_zero chain A).le
  | N + 1 => by
      exact le_trans
        (by
          simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm] using
            add_le_add_left
              (firstHitMassAtStep_succ_add_tsum_survivingArrivalMass_le
                chain A hx hY hkernel N)
              (∑ k ∈ Finset.range (N + 1), firstHitMassAtStep chain A k))
        (sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
          chain A hx hY hkernel N)

/-- If the initial mass is at most `1` and every kernel row is sub-Markov, then the total
first-hit mass is at most `1`. -/
lemma visitMass_le_of_bounds {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ)
    (hx : 0 < x) (hY : 1 ≤ Y)
    (hinit : (∑' n : ℕ, initialMass x Y n) ≤ 1)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) :
    visitMass chain A ≤ 1 := by
  rw [visitMass]
  exact le_trans
    (by
      refine ENNReal.tsum_le_of_sum_range_le ?_
      intro N
      cases N with
      | zero => simp
      | succ N =>
          exact le_trans (le_add_right le_rfl)
            (sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
              chain A hx hY hkernel N))
    hinit

end PrimitiveSetsAboveX
