/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Tree
import LeanPool.FullyDynamicMatching.FD1D.Drift

/-! # Potential -/

namespace FD1D

noncomputable section

/-!
# Global harmonic-potential bookkeeping

This file lifts the one-coordinate identity from `FD1D.Drift` to all
nonroot nodes of a finite dyadic tree.  The stochastic input is deliberately
minimal: at a node, deletion and arrival are independent Bernoulli events
with probabilities `q` and `p`.  Linearity then gives the global identity;
no independence between different tree nodes is needed.
-/

open scoped BigOperators

/-! ## One-node deletion/arrival experiment -/

/-- Probability mass of a Bernoulli outcome. -/
def bernoulliMass (r : ℝ) (outcome : Bool) : ℝ :=
  if outcome then r else 1 - r

/--
The new count after a deletion followed by an arrival.  The hypotheses used
below ensure that deletion has probability zero when the old count is zero.
-/
def updateCount (N : ℕ) (deleted arrived : Bool) : ℕ :=
  if deleted then
    if arrived then N else N - 1
  else
    if arrived then N + 1 else N

/-- Expected change of one harmonic potential under independent Bernoulli events. -/
def expectedNodePotentialChange
    (a : ℝ) (N : ℕ) (p q : ℝ) : ℝ :=
  ∑ deleted : Bool, ∑ arrived : Bool,
    bernoulliMass q deleted * bernoulliMass p arrived *
      (harmonicPotential a (updateCount N deleted arrived) -
        harmonicPotential a N)

theorem expectedNodePotentialChange_eq
    {a p q : ℝ} {N : ℕ}
    (hzero : N = 0 → q = 0) :
    expectedNodePotentialChange a N p q =
      p * (1 - q) / (N + a + 1) -
        q * (1 - p) / (N + a) := by
  rcases N with _ | N
  · simp [expectedNodePotentialChange, bernoulliMass, updateCount, hzero rfl,
      harmonicPotential_succ]
    simp [div_eq_mul_inv, add_comm]
  · simp [expectedNodePotentialChange, bernoulliMass, updateCount,
      harmonicPotential_succ]
    ring

/-! ## Global potential, drift, and remainder -/

/-- `Phi = sum_{v ≠ root} p_v² phi(N_v)`. -/
def globalHarmonicPotential
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ) : ℝ :=
  ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
    (nodeMass (d + 1) v) ^ 2 * harmonicPotential a (N (d + 1) v)

/-- `D`, with natural inventory counts coerced to reals. -/
def potentialDrift
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ)
    (q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  bellmanDrift L a (fun d v => N d v) q

/-- The nonnegative remainder `R` in the exact harmonic-potential drift. -/
def potentialRemainder
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ)
    (q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
    (nodeMass (d + 1) v) ^ 3 * (1 - q (d + 1) v) /
      (((N (d + 1) v : ℝ) + a) *
        ((N (d + 1) v : ℝ) + a + 1))

/--
The conditional expected global change, obtained by summing the independent
one-node deletion/arrival experiment.  Correlations between distinct nodes
do not enter this expression.
-/
def expectedGlobalPotentialChange
    (L : ℕ) (a : ℝ) (N : ∀ d, DyadicNode d → ℕ)
    (q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
    (nodeMass (d + 1) v) ^ 2 *
      expectedNodePotentialChange a (N (d + 1) v)
        (nodeMass (d + 1) v) (q (d + 1) v)

/-- Exact global identity `E[Delta Phi | state] = D - R`. -/
theorem expectedGlobalPotentialChange_eq_drift_sub_remainder
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hzero : ∀ d v, N d v = 0 → q d v = 0) :
    expectedGlobalPotentialChange L a N q =
      potentialDrift L a N q - potentialRemainder L a N q := by
  have hden (d : ℕ) (v : DyadicNode d) :
      (N d v : ℝ) + a ≠ 0 := by positivity
  have hden1 (d : ℕ) (v : DyadicNode d) :
      (N d v : ℝ) + a + 1 ≠ 0 := by positivity
  simp_rw [expectedGlobalPotentialChange, expectedNodePotentialChange_eq
    (hzero _ _), node_harmonic_drift_identity _ _ _ _
      (hden _ _) (hden1 _ _)]
  simp only [potentialDrift, bellmanDrift, potentialRemainder]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro v hv
    ring
  · apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro v hv
    ring

/-! ## Remainder estimates -/

theorem potentialRemainder_nonneg
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a) (hq : ∀ d v, q d v ≤ 1) :
    0 ≤ potentialRemainder L a N q := by
  unfold potentialRemainder
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro v hv
  have hp : 0 ≤ nodeMass (d + 1) v := nodeMass_nonneg _ _
  have h1q : 0 ≤ 1 - q (d + 1) v := sub_nonneg.mpr (hq _ _)
  positivity

/-- Every summand of `R` is at most `p_v h_v²`. -/
theorem potentialRemainder_summand_le
    {a N q h p : ℝ}
    (hp : 0 ≤ p) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (haN : 0 < N + a) (hmajor : p ≤ (N + a) * h) :
    p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ≤ p * h ^ 2 :=
  (node_remainder_le hp hq0 hq1 haN hmajor).2

/-- `R ≤ sum_{ell=1}^L H_ell`. -/
theorem potentialRemainder_le_sum_hazardEnergy
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q h : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hq0 : ∀ d v, 0 ≤ q d v)
    (hq1 : ∀ d v, q d v ≤ 1)
    (hmajor : ∀ d v,
      nodeMass d v ≤ ((N d v : ℝ) + a) * h d v) :
    potentialRemainder L a N q ≤
      ∑ d ∈ Finset.range L, hazardEnergy h (d + 1) := by
  unfold potentialRemainder
  apply Finset.sum_le_sum
  intro d hd
  simp only [hazardEnergy, weightedLevel]
  apply Finset.sum_le_sum
  intro v hv
  exact potentialRemainder_summand_le
    (nodeMass_nonneg _ _) (hq0 _ _) (hq1 _ _) (by positivity)
    (hmajor _ _)

/-- A nondecreasing hazard energy gives `sum_{ell=1}^L H_ell ≤ L H_L`. -/
theorem sum_hazardEnergy_le_depth_mul
    {L : ℕ} {h : ∀ d, DyadicNode d → ℝ}
    (hmono : Monotone (hazardEnergy h)) :
    (∑ d ∈ Finset.range L, hazardEnergy h (d + 1)) ≤
      (L : ℝ) * hazardEnergy h L := by
  calc
    (∑ d ∈ Finset.range L, hazardEnergy h (d + 1))
        ≤ ∑ _d ∈ Finset.range L, hazardEnergy h L := by
          apply Finset.sum_le_sum
          intro d hd
          have hdL := Finset.mem_range.mp hd
          exact hmono (by omega)
    _ = (L : ℝ) * hazardEnergy h L := by simp

/-- Equation (10): `0 ≤ R ≤ sum H_ell ≤ L H_L`. -/
theorem potentialRemainder_bounds
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q h : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hq0 : ∀ d v, 0 ≤ q d v)
    (hq1 : ∀ d v, q d v ≤ 1)
    (hmajor : ∀ d v,
      nodeMass d v ≤ ((N d v : ℝ) + a) * h d v)
    (hmono : Monotone (hazardEnergy h)) :
    0 ≤ potentialRemainder L a N q ∧
      potentialRemainder L a N q ≤
        ∑ d ∈ Finset.range L, hazardEnergy h (d + 1) ∧
      (∑ d ∈ Finset.range L, hazardEnergy h (d + 1)) ≤
        (L : ℝ) * hazardEnergy h L := by
  exact ⟨potentialRemainder_nonneg ha hq1,
    potentialRemainder_le_sum_hazardEnergy ha hq0 hq1 hmajor,
    sum_hazardEnergy_le_depth_mul hmono⟩

/-! ## Stationary finite laws -/

/--
Explicit finite-state stationarity: `K` has row sum one, `mu K = mu`, and
its conditional potential drift is `D-R`.  Then `E_mu D = E_mu R`.
-/
theorem stationary_expect_drift_eq_remainder
    {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (K : α → α → ℝ)
    (Phi D R : α → ℝ)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hstationary : ∀ y, ∑ x, μ.mass x * K x y = μ.mass y)
    (hdrift : ∀ x, ∑ y, K x y * (Phi y - Phi x) = D x - R x) :
    μ.expect D = μ.expect R := by
  have hnext :
      ∑ x, μ.mass x * (∑ y, K x y * Phi y) =
        ∑ y, μ.mass y * Phi y := by
    calc
      ∑ x, μ.mass x * (∑ y, K x y * Phi y)
          = ∑ x, ∑ y, μ.mass x * K x y * Phi y := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = ∑ y, ∑ x, μ.mass x * K x y * Phi y := Finset.sum_comm
      _ = ∑ y, (∑ x, μ.mass x * K x y) * Phi y := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Finset.sum_mul]
      _ = ∑ y, μ.mass y * Phi y := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [hstationary]
  have hcurrent :
      ∑ x, μ.mass x * (∑ y, K x y * Phi x) =
        ∑ x, μ.mass x * Phi x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_mul, hrow, one_mul]
  have hzero :
      ∑ x, μ.mass x * (∑ y, K x y * (Phi y - Phi x)) = 0 := by
    calc
      ∑ x, μ.mass x * (∑ y, K x y * (Phi y - Phi x))
          = (∑ x, μ.mass x * (∑ y, K x y * Phi y)) -
              ∑ x, μ.mass x * (∑ y, K x y * Phi x) := by
                simp_rw [mul_sub, Finset.sum_sub_distrib]
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hnext, hcurrent]; ring
  have hdriftZero : μ.expect (fun x => D x - R x) = 0 := by
    rw [FiniteLaw.expect]
    calc
      ∑ x, μ.mass x * (D x - R x) =
          ∑ x, μ.mass x *
            (∑ y, K x y * (Phi y - Phi x)) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [hdrift]
      _ = 0 := hzero
  have heq :
      (∑ x, μ.mass x * D x) - (∑ x, μ.mass x * R x) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [FiniteLaw.expect, mul_sub] using hdriftZero
  change (∑ x, μ.mass x * D x) = ∑ x, μ.mass x * R x
  exact sub_eq_zero.mp heq

/-! ## Finite-time telescope -/

/-- Exact summation of the one-step expected drift identities. -/
theorem finite_time_drift_telescope
    (T : ℕ) (Phi D R : ℕ → ℝ)
    (hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t) :
    ∑ t ∈ Finset.range T, D t =
      ∑ t ∈ Finset.range T, R t + Phi T - Phi 0 := by
  have hsum :
      ∑ t ∈ Finset.range T, (Phi (t + 1) - Phi t) =
        ∑ t ∈ Finset.range T, (D t - R t) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hdrift t (Finset.mem_range.mp ht)
  rw [Finset.sum_range_sub, Finset.sum_sub_distrib] at hsum
  linarith

/--
The finite-`T` inequality used in Section 5.  Here `Phi`, `D`, `R`, and `H`
are already expectations at time `t`; the preceding theorem supplies their
telescoped drift equation.
-/
theorem finite_time_hazard_drift_inequality
    {T : ℕ} {a L c B : ℝ} (Phi D R H : ℕ → ℝ)
    (hT : 0 < T)
    (hdrift : ∀ t < T, Phi (t + 1) - Phi t = D t - R t)
    (hD : ∀ t < T, a * (H t / 100 - c) ≤ D t)
    (hR : ∀ t < T, R t ≤ L * H t)
    (hPhi0 : 0 ≤ Phi 0) (hPhiT : Phi T ≤ B) :
    (a / 100 - L) *
        ((∑ t ∈ Finset.range T, H t) / T) ≤
      a * c + B / T := by
  have htel := finite_time_drift_telescope T Phi D R hdrift
  have hDsum :
      ∑ t ∈ Finset.range T, a * (H t / 100 - c) ≤
        ∑ t ∈ Finset.range T, D t := by
    apply Finset.sum_le_sum
    intro t ht
    exact hD t (Finset.mem_range.mp ht)
  have hRsum :
      ∑ t ∈ Finset.range T, R t ≤
        ∑ t ∈ Finset.range T, L * H t := by
    apply Finset.sum_le_sum
    intro t ht
    exact hR t (Finset.mem_range.mp ht)
  have hraw :
      ∑ t ∈ Finset.range T, a * (H t / 100 - c) ≤
        ∑ t ∈ Finset.range T, L * H t + B := by
    linarith
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hexpand :
      ∑ t ∈ Finset.range T, a * (H t / 100 - c) =
        a / 100 * (∑ t ∈ Finset.range T, H t) -
          (T : ℝ) * (a * c) := by
    have hterm : ∀ t, a * (H t / 100 - c) =
        a / 100 * H t - a * c := by
      intro t
      ring
    simp_rw [hterm, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    simp
  have hLexpand :
      ∑ t ∈ Finset.range T, L * H t =
        L * ∑ t ∈ Finset.range T, H t := by
    rw [Finset.mul_sum]
  rw [hexpand, hLexpand] at hraw
  have htarget :
      (a / 100 - L) * (∑ t ∈ Finset.range T, H t) ≤
        (T : ℝ) * (a * c) + B := by
    nlinarith
  calc
    (a / 100 - L) * ((∑ t ∈ Finset.range T, H t) / T) =
        ((a / 100 - L) * (∑ t ∈ Finset.range T, H t)) / T := by ring
    _ ≤ ((T : ℝ) * (a * c) + B) / T :=
      div_le_div_of_nonneg_right htarget hTreal.le
    _ = a * c + B / T := by
      field_simp

end

end FD1D
