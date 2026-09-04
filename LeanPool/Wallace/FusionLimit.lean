/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Pointwise limits of character fusions

The fusion construction produces a sequence of circle-valued homomorphisms.  Every group
element is eventually protected, so its values form a Cauchy sequence.  This file isolates the
complete metric argument: the pointwise limit is again a homomorphism, and a geometric bound on
a tail gives an explicit bound from the first point of that tail to the limit.
-/

open Filter Topology
open scoped ENNReal

universe u

namespace Wallace

noncomputable section

variable {G : Type u} [AddGroup G]

/-- A geometric estimate after deleting a finite initial segment implies that the original
sequence is Cauchy. -/
theorem cauchySeq_of_tail_edist_le_geometric_two
    {X : Type*} [PseudoEMetricSpace X] {u : ℕ → X}
    (N : ℕ) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hstep : ∀ n, edist (u (N + n)) (u (N + n + 1)) ≤ C / 2 ^ n) :
    CauchySeq u := by
  rw [← cauchySeq_shift N]
  apply cauchySeq_of_edist_le_geometric_two C hC
  intro n
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep n

/-- Explicit distance from the beginning of a geometrically controlled tail to its limit. -/
theorem edist_le_of_tail_geometric_two_of_tendsto
    {X : Type*} [PseudoEMetricSpace X] {u : ℕ → X} {a : X}
    (N : ℕ) (C : ℝ≥0∞)
    (hstep : ∀ n, edist (u (N + n)) (u (N + n + 1)) ≤ C / 2 ^ n)
    (hu : Tendsto u atTop (nhds a)) :
    edist (u N) a ≤ 2 * C := by
  let v : ℕ → X := fun n ↦ u (N + n)
  have hvstep : ∀ n, edist (v n) (v (n + 1)) ≤ C / 2 ^ n := by
    intro n
    simpa [v, Nat.add_assoc] using hstep n
  have hvlim : Tendsto v atTop (nhds a) := by
    have hshift := hu.comp (tendsto_add_atTop_nat N)
    change Tendsto (fun n ↦ u (n + N)) atTop (nhds a) at hshift
    simpa only [v, Nat.add_comm] using hshift
  simpa [v] using
    edist_le_of_edist_le_geometric_two_of_tendsto₀ C hvstep hvlim

/-- The pointwise limit of a pointwise-Cauchy sequence of additive characters. -/
def pointwiseLimitCharacter
    (f : ℕ → G →+ UnitAddCircle)
    (hf : ∀ x, CauchySeq (fun n ↦ f n x)) : G →+ UnitAddCircle where
  toFun x := limUnder atTop (fun n ↦ f n x)
  map_zero' := by
    apply tendsto_nhds_unique (hf 0).tendsto_limUnder
    simp
  map_add' x y := by
    apply tendsto_nhds_unique (hf (x + y)).tendsto_limUnder
    have hx := (hf x).tendsto_limUnder
    have hy := (hf y).tendsto_limUnder
    simpa only [map_add] using hx.add hy

/-- The defining sequence converges pointwise to `pointwiseLimitCharacter`. -/
theorem tendsto_pointwiseLimitCharacter
    (f : ℕ → G →+ UnitAddCircle)
    (hf : ∀ x, CauchySeq (fun n ↦ f n x)) (x : G) :
    Tendsto (fun n ↦ f n x) atTop (nhds (pointwiseLimitCharacter f hf x)) :=
  (hf x).tendsto_limUnder

end

end Wallace
