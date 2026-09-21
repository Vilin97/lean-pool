/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Construction
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationTermination

/-! # The positive-dimensional Flag Decomposition Lemma -/

namespace EGZ

open FlagDecomposition.Iteration

/-- The bounded normalized iteration proves the lemma for the parameter
range used by the mass estimates. All constants are chosen before the prime
and the input weight, in the required order. -/
theorem flag_decomposition_lemma_posdim {d : ℕ} (hd : 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ (δ : ℝ) (Bcard : ℕ), 0 < δ ∧
      ∀ g : ℕ → ℕ, IsGrowing g →
        ∃ (p₀ BK : ℕ), 2 ≤ p₀ ∧ 1 ≤ BK ∧
          ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
            ∀ f : FpCoord p d → ℕ, f ≠ 0 →
              HasFlagDecompositionConclusion hp f ε δ g Bcard BK := by
  refine ⟨finalScale d ε, 2 ^ stoppingBound d ε, finalScale_pos d hε, ?_⟩
  intro g hg
  let P := normalizedOperationParameters d g hg.1
  refine ⟨P.primeHorizon 1 (stoppingBound d ε), P.radiusHorizon 1 (stoppingBound d ε),
    P.primeThreshold_ge_two _, ?_, ?_⟩
  · exact P.radiusHorizon_monotone 1 (Nat.zero_le (stoppingBound d ε))
  · intro p hp hprime f hf
    let : NeZero p := ⟨hp.ne_zero⟩
    let : Fact p.Prime := ⟨hp⟩
    have hpodd : Odd p := hp.odd_of_ne_two (by
      have htwo := P.primeThreshold_ge_two (P.radiusHorizon 1 (stoppingBound d ε))
      change P.primeThreshold (P.radiusHorizon 1 (stoppingBound d ε)) < p at hprime
      omega)
    apply boundedRun.hasConclusion_of_capacity P hd hε hεhalf hg.1 hf hprime hp
    intro Q
    apply FlagDecomposition.Iteration.hasIntervalCapacity Q hpodd hε hεhalf
      (stageScale_antitone hd hε) (fun i ↦ (stageScale_pos d hε i).le)
    · intro i _
      exact (boundedRun P hd hε hεhalf hg.1 hf (stoppingBound d ε) hprime i).card_bound
    · intro i j hij _
      simpa only [Nat.sub_add_cancel hij] using
        boundedRun.mass_loss_tail_relative P hd hε hεhalf hg.1 hf (stoppingBound d ε) hprime i (j - i)

end EGZ
