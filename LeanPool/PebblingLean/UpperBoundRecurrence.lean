/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.HypercubeProduct
import LeanPool.PebblingLean.UpperBoundProbability

/-!
# Recurrence bridge for the upper bound

This file connects the probabilistic high-demand construction to the
deterministic product recursion.  It is still parameterized by the numerical
annulus estimates; once those are instantiated, this theorem is the formal
recursion step used in the upper bound.
-/

namespace PebblingLean

namespace Hypercube

/-- Ordinary upper-bound target for optimal pebbling of hypercubes: for each
dimension `n`, there is a solvable distribution on `Q_n` of size at most
`costBound n`. -/
def HasHypercubePebblingUpperBound (costBound : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, Pebbling.HasSolvableAtMostSize (graph n) 1 (costBound n)

/-- Forget the strengthened high-demand invariant and retain only the ordinary
one-pebble solvability upper bound. -/
theorem hasHypercubePebblingUpperBound_of_highDemandDistribution
    {costBound minPile : ℕ → ℕ}
    (h : ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n)) :
    HasHypercubePebblingUpperBound costBound := by
  intro n
  exact (h n).to_hasSolvableAtMostSize

/-- Abstract strong-induction wrapper for recursive high-demand constructions.
The actual upper bound will instantiate `costBound` and `minPile` with the
chosen recursive dimension split and parameter estimates. -/
theorem highDemandDistribution_of_recursive_step
    {costBound minPile : ℕ → ℕ} {n0 : ℕ}
    (hbase :
      ∀ n : ℕ, n < n0 →
        HasHighDemandDistribution n 1 (costBound n) (minPile n))
    (hstep :
      ∀ n : ℕ, n0 ≤ n →
        (∀ m : ℕ, m < n →
          HasHighDemandDistribution m 1 (costBound m) (minPile m)) →
        HasHighDemandDistribution n 1 (costBound n) (minPile n)) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < n0
      · exact hbase n hn
      · exact hstep n (Nat.le_of_not_gt hn) ih

/-- Base-case helper: the trivial distribution with one pebble on every vertex
solves demand `1`, and can be weakened to any larger cost bound and any
minimum-pile lower bound at most `1`. -/
theorem hasHighDemandDistribution_constant_base
    {n costBound minPile : ℕ}
    (hcost : 2 ^ n ≤ costBound)
    (hminPile : minPile ≤ 1) :
    HasHighDemandDistribution n 1 costBound minPile :=
  (hasHighDemandDistribution_constant n 1).mono (by simpa using hcost) hminPile

/-- Base-case helper with large occupied piles: putting `S` pebbles on every
vertex gives ordinary solvability when `S ≥ 1`, while retaining any requested
minimum-pile lower bound at most `S`. -/
theorem hasHighDemandDistribution_constant_base_with_minPile
    {n S costBound minPile : ℕ}
    (hS : 1 ≤ S)
    (hcost : 2 ^ n * S ≤ costBound)
    (hminPile : minPile ≤ S) :
    HasHighDemandDistribution n 1 costBound minPile := by
  rcases hasHighDemandDistribution_constant n S with ⟨D, hDsize, hDsolv, hDmin⟩
  exact ⟨D, hDsize.trans hcost, Pebbling.solvableAtLeast_mono hS hDsolv,
    fun v hv => hminPile.trans (hDmin v hv)⟩

/-- One formal recursion step from the optimized chord high-demand construction.

The probabilistic construction supplies a `Tbase`-solvable distribution on
`Q_m` of size at most `N * 2^rOut`, with occupied piles of size at least
`2^rOut`.  If `Q_a` can solve demand `N * 2^rOut` at cost `2^rOut * K`, then
the product step gives a solvable distribution on `Q_(a+m)` of cost
`(N * 2^rOut) * K`. -/
theorem hasSolvableAtMostSize_split_product_of_optimized_chord
    {a m N rIn rOut Tbase K : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hgap_pos : 0 < gap)
    (hmean :
      (Tbase : ℝ) + gap ≤
        (N : ℝ) * (annulusMean m rIn rOut : ℝ))
    (hlog :
      ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean m rIn rOut : ℝ))))
    (hfiber :
      Pebbling.HasSolvableAtMostSize (graph a)
        (N * 2 ^ rOut) (2 ^ rOut * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      ((N * 2 ^ rOut) * K) := by
  have hhigh :
      HasHighDemandDistribution m Tbase (N * 2 ^ rOut) (2 ^ rOut) :=
    hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
      (n := m) (N := N) (rIn := rIn) (rOut := rOut)
      (T := Tbase) (gap := gap)
      hgap_pos hmean hlog
  exact hasSolvableAtMostSize_split_product_of_highDemand
    (a := a) (m := m) (Tbase := Tbase)
    (costBound := N * 2 ^ rOut) (S := 2 ^ rOut) (K := K)
    hTbase hhigh hfiber

/-- Recursive high-demand step with an optimized-chord fiber construction.

An existing high-demand construction on `Q_m` supplies the demands.  The
optimized-chord construction on `Q_a` solves the largest possible demand
`costBound`, with fiber cost bounded by `S * K`; occupied-pile compression then
gives a high-demand distribution on `Q_(a+m)` with cost `costBound * K` and new
minimum pile size `2^rOut`. -/
theorem hasHighDemandDistribution_split_product_of_optimized_chord_fiber
    {a m Tbase costBound S K N rIn rOut : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos : 0 < gap)
    (hmean :
      (costBound : ℝ) + gap ≤
        (N : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost : N * 2 ^ rOut ≤ S * K) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) (2 ^ rOut) := by
  have hfiber_raw :
      HasHighDemandDistribution a costBound (N * 2 ^ rOut) (2 ^ rOut) :=
    hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
      (n := a) (N := N) (rIn := rIn) (rOut := rOut)
      (T := costBound) (gap := gap)
      hgap_pos hmean hlog
  have hfiber : HasHighDemandDistribution a costBound (S * K) (2 ^ rOut) :=
    hfiber_raw.mono_cost hfiberCost
  exact hasHighDemandDistribution_split_product_of_highDemand
    (a := a) (m := m) (Tbase := Tbase)
    (costBound := costBound) (S := S) (K := K) (Snew := 2 ^ rOut)
    hTbase hbase hfiber

/-- Same recursive high-demand step, with the new pile-size invariant weakened
to any specified lower bound below `2^rOut`. -/
theorem hasHighDemandDistribution_split_product_of_optimized_chord_fiber_min
    {a m Tbase costBound S K N rIn rOut minNext : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos : 0 < gap)
    (hmean :
      (costBound : ℝ) + gap ≤
        (N : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost : N * 2 ^ rOut ≤ S * K)
    (hminNext : minNext ≤ 2 ^ rOut) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) minNext :=
  (hasHighDemandDistribution_split_product_of_optimized_chord_fiber
    (a := a) (m := m) (Tbase := Tbase) (costBound := costBound)
    (S := S) (K := K) (N := N) (rIn := rIn) (rOut := rOut)
    (gap := gap) hTbase hbase hgap_pos hmean hlog hfiberCost).mono_minPile
      hminNext

/-- Variable-demand version of the optimized-chord product step.

For every occupied pile size `t ≥ S` in the recursive `Q_m` distribution, the
optimized-chord construction supplies a `t`-solvable fiber in `Q_a` of cost
`t*K`.  This is the recurrence used in the paper: costs add as
`∑_z E z * K = |E|*K`, rather than paying for a worst-case demand in every
occupied fiber. -/
theorem hasHighDemandDistribution_split_product_of_optimized_chord_fiber_variable_min
    {a m Tbase costBound S K rIn rOut minNext : ℕ}
    {N : ℕ → ℕ} {gap : ℕ → ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos :
      ∀ t : ℕ, S ≤ t → 0 < gap t)
    (hmean :
      ∀ t : ℕ, S ≤ t →
        (t : ℝ) + gap t ≤
          (N t : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ∀ t : ℕ, S ≤ t →
        ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap t) ^ 2 /
            (4 * (2 ^ (rOut - rIn) : ℝ) *
              ((N t : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost :
      ∀ t : ℕ, S ≤ t → N t * 2 ^ rOut ≤ t * K)
    (hminNext : minNext ≤ 2 ^ rOut) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) minNext := by
  refine
    hasHighDemandDistribution_split_product_of_highDemand_variable
      (a := a) (m := m) (Tbase := Tbase) (costBound := costBound)
      (S := S) (K := K) (Snew := minNext)
      hTbase hbase ?_
  intro t ht
  have hfiber_raw :
      HasHighDemandDistribution a t (N t * 2 ^ rOut) (2 ^ rOut) :=
    hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
      (n := a) (N := N t) (rIn := rIn) (rOut := rOut)
      (T := t) (gap := gap t)
      (hgap_pos t ht) (hmean t ht) (hlog t ht)
  exact (hfiber_raw.mono_cost (hfiberCost t ht)).mono_minPile hminNext

/-- Abstract recursive split schedule for the upper bound.

For every large dimension `n`, the schedule chooses a split
`Q_n ≃ Q_{splitA n} □ Q_{splitM n}`.  The inductive hypothesis supplies the
base high-demand distribution on `Q_{splitM n}`; the optimized-chord annulus
construction supplies the fiber distribution on `Q_{splitA n}` for demand
`costBound (splitM n)`.  The hypotheses here are exactly the numerical
conditions that remain after all graph-theoretic, probabilistic, and product
bookkeeping has been formalized. -/
theorem highDemandDistribution_of_recursive_split_schedule
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase :
      ∀ n : ℕ, n < n0 →
        HasHighDemandDistribution n 1 (costBound n) (minPile n))
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) := by
  refine highDemandDistribution_of_recursive_step (n0 := n0) hbase ?_
  intro n hn ih
  have hrec_base :
      HasHighDemandDistribution (splitM n) 1
        (costBound (splitM n)) (minPile (splitM n)) :=
    ih (splitM n) (hsmaller n hn)
  have hrec :
      HasHighDemandDistribution (splitA n + splitM n) 1
        (costBound (splitM n) * K n) (2 ^ rOut n) :=
    hasHighDemandDistribution_split_product_of_optimized_chord_fiber
      (a := splitA n) (m := splitM n) (Tbase := 1)
      (costBound := costBound (splitM n)) (S := minPile (splitM n))
      (K := K n) (N := N n) (rIn := rIn n) (rOut := rOut n)
      (gap := gap n) (by decide) hrec_base
      (hgap_pos n hn) (hmean n hn) (hlog n hn) (hfiberCost n hn)
  have hrec_n :
      HasHighDemandDistribution n 1
        (costBound (splitM n) * K n) (2 ^ rOut n) := by
    simpa [hsplit n hn] using hrec
  exact hrec_n.mono (hcost n hn) (hminPile n hn)

/-- Paper-accurate recursive split schedule with variable fiber demand.

The fixed-demand schedule above asks the `Q_a` fiber construction to solve the
maximum possible pile size in every occupied fiber.  The paper instead applies
the high-demand lemma separately to each occupied pile size `t`; this theorem
packages that sharper recurrence. -/
theorem highDemandDistribution_of_recursive_split_schedule_variable
    {costBound minPile splitA splitM K rIn rOut : ℕ → ℕ}
    {N : ℕ → ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {n0 : ℕ}
    (hbase :
      ∀ n : ℕ, n < n0 →
        HasHighDemandDistribution n 1 (costBound n) (minPile n))
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t → 0 < gap n t)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          (t : ℝ) + gap n t ≤
            (N n t : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (gap n t) ^ 2 /
              (4 * (2 ^ (rOut n - rIn n) : ℝ) *
                ((N n t : ℝ) *
                  (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          N n t * 2 ^ rOut n ≤ t * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) := by
  refine highDemandDistribution_of_recursive_step (n0 := n0) hbase ?_
  intro n hn ih
  have hrec_base :
      HasHighDemandDistribution (splitM n) 1
        (costBound (splitM n)) (minPile (splitM n)) :=
    ih (splitM n) (hsmaller n hn)
  have hrec :
      HasHighDemandDistribution (splitA n + splitM n) 1
        (costBound (splitM n) * K n) (minPile n) :=
    hasHighDemandDistribution_split_product_of_optimized_chord_fiber_variable_min
      (a := splitA n) (m := splitM n) (Tbase := 1)
      (costBound := costBound (splitM n)) (S := minPile (splitM n))
      (K := K n) (N := N n) (rIn := rIn n) (rOut := rOut n)
      (minNext := minPile n) (gap := gap n)
      (by decide) hrec_base
      (hgap_pos n hn) (hmean n hn) (hlog n hn) (hfiberCost n hn)
      (hminPile n hn)
  have hrec_n :
      HasHighDemandDistribution n 1
        (costBound (splitM n) * K n) (minPile n) := by
    simpa [hsplit n hn] using hrec
  exact hrec_n.mono_cost (hcost n hn)

/-- Same recursive split schedule, with the finite base range discharged by
the constant one-pebble-per-vertex distribution. -/
theorem highDemandDistribution_of_recursive_split_schedule_constant_base
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n ≤ costBound n)
    (hbase_minPile :
      ∀ n : ℕ, n < n0 → minPile n ≤ 1)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) :=
  highDemandDistribution_of_recursive_split_schedule
    (n0 := n0)
    (hbase := fun n hn =>
      hasHighDemandDistribution_constant_base
        (hbase_cost n hn) (hbase_minPile n hn))
    hsplit hsmaller hgap_pos hmean hlog hfiberCost hcost hminPile

/-- Same recursive split schedule, with finite base cases discharged by the
constant distribution having exactly the requested minimum pile size on every
vertex.  This is the base-case form used by the paper recursion, where the
large-pile invariant is maintained even below the cutoff dimension. -/
theorem highDemandDistribution_of_recursive_split_schedule_large_constant_base
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) :=
  highDemandDistribution_of_recursive_split_schedule
    (n0 := n0)
    (hbase := fun n hn =>
      hasHighDemandDistribution_constant_base_with_minPile
        (S := minPile n) (hbase_minPile_pos n hn)
        (hbase_cost n hn) le_rfl)
    hsplit hsmaller hgap_pos hmean hlog hfiberCost hcost hminPile

/-- Variable-demand recursive split schedule, with finite base cases discharged
by the constant distribution having the requested minimum pile size on every
vertex. -/
theorem highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base
    {costBound minPile splitA splitM K rIn rOut : ℕ → ℕ}
    {N : ℕ → ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t → 0 < gap n t)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          (t : ℝ) + gap n t ≤
            (N n t : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (gap n t) ^ 2 /
              (4 * (2 ^ (rOut n - rIn n) : ℝ) *
                ((N n t : ℝ) *
                  (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          N n t * 2 ^ rOut n ≤ t * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    ∀ n : ℕ, HasHighDemandDistribution n 1 (costBound n) (minPile n) :=
  highDemandDistribution_of_recursive_split_schedule_variable
    (n0 := n0)
    (hbase := fun n hn =>
      hasHighDemandDistribution_constant_base_with_minPile
        (S := minPile n) (hbase_minPile_pos n hn)
        (hbase_cost n hn) le_rfl)
    hsplit hsmaller hgap_pos hmean hlog hfiberCost hcost hminPile

/-- Ordinary upper-bound form of the recursive split schedule with constant
base cases. -/
theorem hasHypercubePebblingUpperBound_of_recursive_split_schedule_constant_base
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n ≤ costBound n)
    (hbase_minPile :
      ∀ n : ℕ, n < n0 → minPile n ≤ 1)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    HasHypercubePebblingUpperBound costBound :=
  hasHypercubePebblingUpperBound_of_highDemandDistribution
    (highDemandDistribution_of_recursive_split_schedule_constant_base
      (n0 := n0) hbase_cost hbase_minPile hsplit hsmaller hgap_pos
      hmean hlog hfiberCost hcost hminPile)

/-- Ordinary upper-bound form of the recursive split schedule with large-pile
constant base cases. -/
theorem hasHypercubePebblingUpperBound_of_recursive_split_schedule_large_constant_base
    {costBound minPile splitA splitM K N rIn rOut : ℕ → ℕ}
    {gap : ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n → 0 < gap n)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        (costBound (splitM n) : ℝ) + gap n ≤
          (N n : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap n) ^ 2 /
            (4 * (2 ^ (rOut n - rIn n) : ℝ) *
              ((N n : ℝ) *
                (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        N n * 2 ^ rOut n ≤ minPile (splitM n) * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    HasHypercubePebblingUpperBound costBound :=
  hasHypercubePebblingUpperBound_of_highDemandDistribution
    (highDemandDistribution_of_recursive_split_schedule_large_constant_base
      (n0 := n0) hbase_minPile_pos hbase_cost hsplit hsmaller
      hgap_pos hmean hlog hfiberCost hcost hminPile)

/-- Ordinary upper-bound form of the variable-demand recursive split schedule
with large-pile constant base cases. -/
theorem hasHypercubePebblingUpperBound_of_recursive_split_schedule_variable_large_constant_base
    {costBound minPile splitA splitM K rIn rOut : ℕ → ℕ}
    {N : ℕ → ℕ → ℕ} {gap : ℕ → ℕ → ℝ} {n0 : ℕ}
    (hbase_minPile_pos :
      ∀ n : ℕ, n < n0 → 1 ≤ minPile n)
    (hbase_cost :
      ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ costBound n)
    (hsplit :
      ∀ n : ℕ, n0 ≤ n → splitA n + splitM n = n)
    (hsmaller :
      ∀ n : ℕ, n0 ≤ n → splitM n < n)
    (hgap_pos :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t → 0 < gap n t)
    (hmean :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          (t : ℝ) + gap n t ≤
            (N n t : ℝ) * (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          ((splitA n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (gap n t) ^ 2 /
              (4 * (2 ^ (rOut n - rIn n) : ℝ) *
                ((N n t : ℝ) *
                  (annulusMean (splitA n) (rIn n) (rOut n) : ℝ))))
    (hfiberCost :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM n) ≤ t →
          N n t * 2 ^ rOut n ≤ t * K n)
    (hcost :
      ∀ n : ℕ, n0 ≤ n →
        costBound (splitM n) * K n ≤ costBound n)
    (hminPile :
      ∀ n : ℕ, n0 ≤ n →
        minPile n ≤ 2 ^ rOut n) :
    HasHypercubePebblingUpperBound costBound :=
  hasHypercubePebblingUpperBound_of_highDemandDistribution
    (highDemandDistribution_of_recursive_split_schedule_variable_large_constant_base
      (n0 := n0) hbase_minPile_pos hbase_cost hsplit hsmaller
      hgap_pos hmean hlog hfiberCost hcost hminPile)

end Hypercube

end PebblingLean
