/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Tactic.Ring
import LeanPool.PebblingLean.UpperBound
import LeanPool.PebblingLean.HypercubePath

/-!
# Delivery interpretation of annulus contributions

The probabilistic upper bound counts, for each target, the quantity
`2^(rOut - dist center target)` contributed by a stack of size `2^rOut` at an
annulus center.  This file proves that the counted quantity is not just
bookkeeping: it is actually deliverable by pebbling moves.
-/

namespace PebblingLean

namespace Hypercube

open Pebbling

/-- A deterministic distribution formed by placing one stack of size `2^rOut`
at each center in a list.  Repeated centers add stacks. -/
def stackListDistribution {n : ℕ} (rOut : ℕ) :
    List (HypercubeVertex n) → Pebbling (HypercubeVertex n)
  | [] => fun _ => 0
  | center :: centers =>
      Pebbling.single center (2 ^ rOut) + stackListDistribution rOut centers

/-- A center list is good for demand `T` if every target receives annulus
contribution at least `T`.  The probabilistic estimates will prove existence of
such lists. -/
def IsGoodCenterList (n rIn rOut T : ℕ) (centers : List (HypercubeVertex n)) : Prop :=
  ∀ target : HypercubeVertex n, T ≤ annulusTotalContribution rIn rOut target centers

theorem size_stackListDistribution {n rOut : ℕ}
    (centers : List (HypercubeVertex n)) :
    size (stackListDistribution rOut centers) = centers.length * 2 ^ rOut := by
  classical
  induction centers with
  | nil =>
      simp [stackListDistribution, size]
  | cons center centers ih =>
      simp [stackListDistribution, Pebbling.size_add, ih]
      ring

/-- Every occupied pile in a stack-list distribution has at least one full
stack.  Repeated centers only increase the pile size. -/
theorem minOccupiedPileSize_stackListDistribution {n rOut : ℕ}
    (centers : List (HypercubeVertex n)) :
    MinOccupiedPileSize (stackListDistribution (n := n) rOut centers) (2 ^ rOut) := by
  classical
  intro v hv
  induction centers with
  | nil =>
      simp [stackListDistribution] at hv
  | cons center centers ih =>
      by_cases hvc : v = center
      · subst v
        simp [stackListDistribution, Pebbling.single]
      · have hsingle : Pebbling.single center (2 ^ rOut) v = 0 := by
          simp [Pebbling.single, hvc]
        have hv_tail : stackListDistribution rOut centers v ≠ 0 := by
          simpa [stackListDistribution, hsingle] using hv
        simpa [stackListDistribution, hsingle] using ih hv_tail

/-- A stack of size `2^rOut` at an annulus center can directly deliver the
annulus contribution assigned to that center. -/
theorem canReachAtLeast_annulusContribution_single {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∈ annulus n rIn rOut target) :
    CanReachAtLeast (graph n)
      (Pebbling.single center (2 ^ rOut)) target
      (annulusContribution rIn rOut target center) := by
  have hbounds := mem_annulus.mp hmem
  have hcontrib :
      annulusContribution rIn rOut target center =
        2 ^ (rOut - dist center target) :=
    annulusContribution_eq_of_mem hmem
  have hsize :
      2 ^ rOut =
        annulusContribution rIn rOut target center * 2 ^ dist center target := by
    rw [hcontrib, ← Nat.pow_add]
    rw [Nat.sub_add_cancel hbounds.2]
  rw [hsize]
  exact canReachAtLeast_single_dist center target
    (annulusContribution rIn rOut target center)

/-- The deterministic delivery interpretation of `X_t`: the stack list can
deliver at least the total annulus contribution to the fixed target. -/
theorem canReachAtLeast_annulusTotalContribution_stackList {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (centers : List (HypercubeVertex n)) :
    CanReachAtLeast (graph n)
      (stackListDistribution rOut centers) target
      (annulusTotalContribution rIn rOut target centers) := by
  induction centers with
  | nil =>
      exact Pebbling.canReachAtLeast_zero (graph n) (stackListDistribution rOut []) target
  | cons center centers ih =>
      have hhead :
          CanReachAtLeast (graph n)
            (Pebbling.single center (2 ^ rOut)) target
            (annulusContribution rIn rOut target center) := by
        by_cases hmem : center ∈ annulus n rIn rOut target
        · exact canReachAtLeast_annulusContribution_single hmem
        · rw [annulusContribution_eq_zero_of_notMem hmem]
          exact Pebbling.canReachAtLeast_zero (graph n)
            (Pebbling.single center (2 ^ rOut)) target
      have hsum := Pebbling.canReachAtLeast_add hhead ih
      simpa [stackListDistribution, annulusTotalContribution, Nat.add_assoc] using hsum

/-- Deterministic probabilistic-method interface: once a center list is good
for every target, the corresponding stack distribution is `T`-solvable. -/
theorem solvableAtLeast_stackListDistribution_of_good {n rIn rOut T : ℕ}
    {centers : List (HypercubeVertex n)}
    (hgood : IsGoodCenterList n rIn rOut T centers) :
    SolvableAtLeast (graph n) (stackListDistribution rOut centers) T := by
  intro target
  exact Pebbling.canReachAtLeast_mono (hgood target)
    (canReachAtLeast_annulusTotalContribution_stackList target centers)

/-- Costed form of the deterministic interface for the high-demand lemma. -/
theorem hasSolvableAtMostSize_of_goodCenterList {n rIn rOut T : ℕ}
    {centers : List (HypercubeVertex n)}
    (hgood : IsGoodCenterList n rIn rOut T centers) :
    HasSolvableAtMostSize (graph n) T (centers.length * 2 ^ rOut) := by
  refine ⟨stackListDistribution rOut centers, ?_, ?_⟩
  · rw [size_stackListDistribution]
  · exact solvableAtLeast_stackListDistribution_of_good hgood

/-- High-demand form of the deterministic interface: a good center list gives
a `T`-solvable distribution with controlled size and occupied piles of size at
least `2^rOut`. -/
theorem hasHighDemandDistribution_of_goodCenterList {n rIn rOut T : ℕ}
    {centers : List (HypercubeVertex n)}
    (hgood : IsGoodCenterList n rIn rOut T centers) :
    HasHighDemandDistribution n T (centers.length * 2 ^ rOut) (2 ^ rOut) := by
  refine ⟨stackListDistribution rOut centers, ?_, ?_, ?_⟩
  · rw [size_stackListDistribution]
  · exact solvableAtLeast_stackListDistribution_of_good hgood
  · exact minOccupiedPileSize_stackListDistribution centers

end Hypercube

end PebblingLean
