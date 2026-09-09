/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSmoothLimit

/-! Initial-data convergence for the very same correction witnesses used
in the exact packets. No correction is chosen again for this conclusion. -/

@[expose] public section


noncomputable section

namespace EulerPacketInitial

open Set Filter Finset EulerSmoothLimit EulerPhysicalL2Scaling EulerAllOrderDriftCorrection
  EulerPacketTerminalDatum EulerPacketSourceFrequency EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketUniformFrequencyScales EulerLpTranslation
open scoped Topology

namespace Input

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : Input U)

/-- Correction budget type used in packet initial exact limit. -/
abbrev correctionBudget (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) :=
  Budget period A.data.T_pos
    (initializedCorrectionData A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
        A.history
      A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement (truncation k) hn k
          hk)

/-- Exact initial, constructed using `scale`. -/
def exactInitial (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : A.correctionBudget k hk hn) :
    Space → Space :=
  scale A.parent.ell
    (initializedExactPhysicalVelocity A.meanData A.data rfl A.historyTime A.history_pos A.history_lt
      A.history A.geometry.δ A.delta_pos A.terminal A.cutoff_support A.alpha A.agreement
      (truncation k) hn k hk Q ⟨0,le_rfl,A.data.T_pos.le⟩ id)

theorem exactInitial_eq (k : ℝ) (hk : 4 ≤ k) (hn : 1 ≤ truncation k) (Q : A.correctionBudget k hk
    hn) :
    A.exactInitial k hk hn Q=A.high k+A.mean k := A.sameQ_initial k hk hn Q

end Input

variable {U : ℕ → Type} [∀ n, NormedAddCommGroup (U n)] [∀ n, InnerProductSpace ℝ (U n)]
  [∀ n, CompleteSpace (U n)] (A : ∀ n, Input (U n)) (J : ℕ) (X : ℝ)
  (hk : ∀ n, 4 ≤ frequency J X n) (hn : ∀ n, 1 ≤ truncation (frequency J X n))
  (Q : ∀ n, (A n).correctionBudget (frequency J X n) (hk n) (hn n))

/-- Exact partial, defined pointwise by `∑ n ∈ range N, (A n).exactInitial (frequency J X n) (hk
n) (hn n) (Q n) x`. -/
def exactPartial (N : ℕ) : Space → Space :=
  fun x => ∑ n ∈ range N, (A n).exactInitial (frequency J X n) (hk n) (hn n) (Q n) x

theorem exactPartial_eq (N : ℕ) : exactPartial A J X hk hn Q N=initialPartial A J X N := by
  funext x
  unfold exactPartial initialPartial
  apply sum_congr rfl
  intro n _
  rw [Input.exactInitial_eq]
  rfl

variable (hJ : 2 ≤ J) (C c : ℝ) (hC : 0 < C) (hc : 0 ≤ c)
  (p q : ℕ) (hX : 1 ≤ X)
  (hparameter : ∀ n, (A n).parameterSize ≤ parameterEnvelope J C c p q X n)
  (hscale : ∀ n, (A n).parent.ell = supportScale J X n)
  (hσ : ∀ n, (A n).frame.sigma * scaleSequence J X n ≤ 2)
  (hfrequency : ∀ n, (A n).frequencyGuard (frequency J X n))

local notation "V" => initialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency

theorem selectedQ_initial_Hm (s : ℕ) :
    Tendsto (fun N => derivativeSum s (exactPartial A J X hk hn Q N-(V).field)) atTop (𝓝 0) := by
  simpa only [exactPartial_eq] using
    initialLimit_Hm A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency s

theorem selectedQ_fullInitial_Hm (base : SmoothL2Field Space) (s : ℕ) :
    Tendsto (fun N => derivativeSum s ((base.field+exactPartial A J X hk hn Q N) -
      (fullInitialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency base).field))
      atTop (𝓝 0) := by
  simpa only [exactPartial_eq] using
    fullInitialLimit_Hm A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency base s

end EulerPacketInitial
