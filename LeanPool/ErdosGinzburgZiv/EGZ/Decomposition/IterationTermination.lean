/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationColorCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationCompleteCapacity
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationFaceCapacity

/-! # Uniform termination of certified finite refinement runs -/

@[expose] public section

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ} {N : ℕ}
    (P : ∀ i, i < N → Progress (s i) (s (i + 1)) ε (δ i) g)

theorem hasIntervalCapacity (hp : Odd p) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hδ : Antitone δ) (hδnonneg : ∀ i, 0 ≤ δ i)
    (hcard : ∀ i, i ≤ N → Fintype.card (s i).decomposition.flag.Node ≤ 2 ^ i)
    (htail : ∀ i j, i ≤ j → j ≤ N →
      ((s i).decomposition.retainedMass : ℝ) - (s j).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (s i).decomposition.retainedMass) :
    EGZ.HasIntervalCapacity (progressColor P) (intervalCapacity d ε) N := by
  apply hasIntervalCapacity_of_event_bounds P hδ hδnonneg
  · intro a b L hab hb hL hcolors
    exact (card_complete_events_interval_le P (progressColor P) (progressColor_eq P)
      hab hb hL hcolors).trans (hcard a (hab.trans hb.le))
  · intro a b L hab hb hL hcolors
    apply le_trans (card_face_events_interval_le L ε δ g P (progressColor P) (progressColor_eq P)
      hab hb hp hε hεhalf hcolors htail)
    exact Nat.mul_le_mul_right (faceCapacity d ε) (hcard a (hab.trans hb.le))

include P in
theorem length_lt_stoppingBound (hp : Odd p) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hδ : Antitone δ) (hδnonneg : ∀ i, 0 ≤ δ i)
    (hcard : ∀ i, i ≤ N → Fintype.card (s i).decomposition.flag.Node ≤ 2 ^ i)
    (htail : ∀ i j, i ≤ j → j ≤ N →
      ((s i).decomposition.retainedMass : ℝ) - (s j).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (s i).decomposition.retainedMass) : N < stoppingBound d ε :=
  length_lt_intervalCapacityBound _ _ N (progressColor P) (progressColor_lt P)
    (hasIntervalCapacity P hp hε hεhalf hδ hδnonneg hcard htail)

end EGZ.FlagDecomposition.Iteration
