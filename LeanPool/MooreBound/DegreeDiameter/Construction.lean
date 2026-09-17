/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import LeanPool.MooreBound.DegreeDiameter.Asymptotics
import LeanPool.MooreBound.DegreeDiameter.LowerBound
import LeanPool.MooreBound.DegreeDiameter.Proposition31
import Mathlib.Algebra.Field.ZMod

/-!
# The finite-field halved-flag witness

This file packages the concrete halved flag graph over `ZMod p` into the
abstract interface used by the asymptotic argument.  Its vertices are the
even partial flags in the recursively split `(2*k+1)`-dimensional space.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Module

namespace DegreeDiameter

/-- For every positive `k` and prime `p`, the halved flag graph over
`ZMod p` is a finite regular graph with the order, degree, and diameter
bounds required by the asymptotic argument. -/
theorem asymptoticHalvedWitness (k p : ℕ) (hk : 0 < k) (hp : Nat.Prime p) :
    AsymptoticHalvedWitness k p := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let K := ZMod p
  let : Field K := by
    dsimp only [K]
    infer_instance
  let W := FlagSpace K k
  let : AddCommGroup W := flagSpaceAddCommGroup K k
  let : Module K W := flagSpaceModule K k
  let : FiniteDimensional K W := flagSpaceFiniteDimensional K k
  let X := Proposition31Vertex K k
  let G : SimpleGraph X := Proposition31Graph K k
  let : Finite K := inferInstance
  let : Finite W := flagSpaceFinite K k
  let : Finite X := inferInstance
  have horder : p ^ (2 * k * k) ≤ Nat.card X := by
    simpa only [K, W, X, flagDim_eq, Nat.card_zmod] using
      (natCard_evenPartialFlag_lower (K := K) k)
  have hXpos : 0 < Nat.card X := by
    exact (pow_pos hp.pos _).trans_le horder
  let : Nonempty X := Finite.card_pos_iff.mp hXpos
  have hstrong := proposition_3_1_over_finite_field K k hk
  refine ⟨X, G, proposition31Degree K k, inferInstance, horder, ?_, ?_, ?_⟩
  · intro P
    simpa only [X, G, Nat.card_coe_set_eq] using hstrong.1 P
  · have hΔ : proposition31Degree K k ≤
        ((p + 1) ^ k) * (((p + 1) ^ k) - 1) := by
      simpa only [K, Nat.card_zmod] using hstrong.2.2.2.1
    calc
      proposition31Degree K k ≤
          ((p + 1) ^ k) * (((p + 1) ^ k) - 1) := hΔ
      _ ≤ ((p + 1) ^ k) * ((p + 1) ^ k) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (p + 1) ^ (2 * k) := by
        rw [← pow_add]
        congr 1
        omega
  · simpa only [G] using hstrong.2.2.2.2.le

/-- The concrete finite-field construction implies the abstract prime-indexed
interface used by the alternative downstream extremal-limit proof. The exact
Proposition 3.1 theorem is exported separately. -/
theorem asymptoticHalvedWitnessHypothesis : AsymptoticHalvedWitnessHypothesis :=
  asymptoticHalvedWitness

end DegreeDiameter

end MooreBound
