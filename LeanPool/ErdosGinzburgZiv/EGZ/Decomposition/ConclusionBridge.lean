/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Conclusion
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationConstants

/-! # A finished bounded state supplies the public decomposition conclusion -/

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

theorem State.hasConclusion (s : State p d f) (hp : p.Prime)
    {ε δ : ℝ} {g : ℕ → ℕ} {Bcard BK : ℕ}
    (h : s.Finished ε δ g)
    (hcard : Fintype.card s.decomposition.flag.Node ≤ Bcard)
    (hK : s.radius ≤ BK)
    (hmass : (1 - ε) * (natMass f : ℝ) ≤ s.decomposition.retainedMass) :
    HasFlagDecompositionConclusion hp f ε δ g Bcard BK := by
  refine ⟨s.decomposition, fun _ ↦ g s.radius, fun _ ↦ s.radius,
    hcard, antitone_const, fun _ ↦ ⟨s.radius_pos, hK⟩, s.bounded,
    h.2, fun _ ↦ le_rfl, h.1, hmass⟩

theorem BoundedState.hasConclusion {g : ℕ → ℕ} {P : NormalizedOperationParameters d g}
    {ε : ℝ} {i : ℕ} (s : BoundedState (f := f) P ε i) (hp : p.Prime)
    (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hi : i ≤ stoppingBound d ε)
    (hfinished : s.toState.Finished ε (stageScale d ε i) g) :
    HasFlagDecompositionConclusion hp f ε (finalScale d ε) g
      (2 ^ stoppingBound d ε) (P.radiusHorizon 1 (stoppingBound d ε)) := by
  apply HasFlagDecompositionConclusion.mono_delta
    (s.toState.hasConclusion hp hfinished
      (s.card_bound.trans (Nat.pow_le_pow_right (by omega) hi))
      (s.radius_bound.trans (P.radiusHorizon_monotone 1 hi))
      (s.mass_bounds hd hε hεhalf).2)
    (finalScale_pos d hε).le (finalScale_le hd hε hi)

end EGZ.FlagDecomposition.Iteration
