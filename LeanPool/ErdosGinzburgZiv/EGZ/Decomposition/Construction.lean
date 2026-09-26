/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.BoundedRun
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.ConclusionBridge
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationColorCapacity

/-! # Extracting the decomposition from the bounded iteration -/

@[expose] public section

namespace EGZ.FlagDecomposition.Iteration.boundedRun

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {g : ℕ → ℕ} (P : NormalizedOperationParameters d g)
    {ε : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hg : Monotone g) (hf : f ≠ 0)
    (hprime : P.primeHorizon 1 (stoppingBound d ε) < p)

/-- The interval-capacity theorem rules out a full horizon of unfinished
steps, so one of the actual bounded states supplies the public conclusion. -/
theorem hasConclusion_of_capacity (hp : p.Prime)
    (hcapacity : ∀ Q : (i : ℕ) → i < stoppingBound d ε →
        Progress (state P hd hε hεhalf hg hf (stoppingBound d ε) hprime i)
          (state P hd hε hεhalf hg hf (stoppingBound d ε) hprime (i + 1))
          ε (stageScale d ε i) g,
      HasIntervalCapacity (progressColor Q) (intervalCapacity d ε) (stoppingBound d ε)) :
    HasFlagDecompositionConclusion hp f ε (finalScale d ε) g
      (2 ^ stoppingBound d ε) (P.radiusHorizon 1 (stoppingBound d ε)) := by
  rcases finished_or_progress P hd hε hεhalf hg hf (stoppingBound d ε) hprime with
      hfinished | hprogress
  · obtain ⟨i, hi, hfinished⟩ := hfinished
    exact (boundedRun P hd hε hεhalf hg hf (stoppingBound d ε) hprime i).hasConclusion
      hp hd hε hεhalf hi hfinished
  · obtain ⟨Q⟩ := hprogress
    have hlt : stoppingBound d ε < stoppingBound d ε :=
      length_lt_intervalCapacityBound _ _ _ (progressColor Q) (progressColor_lt Q) (hcapacity Q)
    exact (Nat.lt_irrefl _ hlt).elim

end EGZ.FlagDecomposition.Iteration.boundedRun
