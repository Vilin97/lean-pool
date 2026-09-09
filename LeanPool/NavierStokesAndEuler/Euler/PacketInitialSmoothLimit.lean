/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialSummability
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Series

@[expose] public section

/-! The actual packet initial increments converge in every finite
Sobolev norm to a single smooth field with the same compact support. -/

noncomputable section

namespace EulerPacketInitial

open Set Filter Finset MeasureTheory EulerSmoothLimit EulerPhysicalL2Scaling
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketUniformFrequencyScales
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothL2Series
open scoped Topology ContDiff

namespace Input

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (A : Input U)

def increment (k : ℝ) : SmoothL2Field Space := addField (A.highField k) (A.meanField k)

theorem increment_field (k : ℝ) : (A.increment k).field=A.high k+A.mean k := rfl

theorem increment_norm_le (k : ℝ) (s : ℕ) :
    tensorNorm s (A.increment k) ≤ derivativeSum s (A.high k)+derivativeSum s (A.mean k) := by
  apply (tensorNorm_add_le (A.highField k) (A.meanField k) s).trans_eq
  rw [tensorNorm_eq_derivativeSum,tensorNorm_eq_derivativeSum,A.highField_field,A.meanField_field]

theorem increment_support (k : ℝ) : tsupport (A.increment k).field ⊆ Metric.closedBall 0 2 := by
  rw [increment_field]
  exact (tsupport_add (A.high k) (A.mean k)).trans
    (union_subset (A.initial_support k).1 (A.initial_support k).2)

end Input

variable {U : ℕ → Type} [∀ n, NormedAddCommGroup (U n)] [∀ n, InnerProductSpace ℝ (U n)]
  [∀ n, CompleteSpace (U n)] (A : ∀ n, Input (U n))
  (J : ℕ) (hJ : 2 ≤ J) (C c : ℝ) (hC : 0 < C) (hc : 0 ≤ c)
  (p q : ℕ) (X : ℝ) (hX : 1 ≤ X)
  (hparameter : ∀ n, (A n).parameterSize ≤ parameterEnvelope J C c p q X n)
  (hscale : ∀ n, (A n).parent.ell=supportScale J X n)
  (hσ : ∀ n, (A n).frame.sigma*scaleSequence J X n ≤ 2)
  (hk : ∀ n, 4 ≤ frequency J X n)
  (hfrequency : ∀ n, (A n).frequencyGuard (frequency J X n))

include hJ hC hc hX hparameter hscale hσ hk hfrequency in
theorem actual_increment_summable (s : ℕ) :
    Summable (fun n => tensorNorm s ((A n).increment (frequency J X n))) := by
  have hh := actual_high_summable A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency s
  have hm := actual_mean_summable A J hJ C c hC p q X hX hparameter hscale hσ hk hfrequency s
  exact (hh.add hm).of_nonneg_of_le (fun n => tensorNorm_nonneg s _)
    (fun n => (A n).increment_norm_le (frequency J X n) s)

def initialPartial (N : ℕ) : Space → Space :=
  fun x => ∑ n ∈ range N, ((A n).high (frequency J X n) x+(A n).mean (frequency J X n) x)

theorem initialPartial_field (N : ℕ) :
    (partialSum (fun n => (A n).increment (frequency J X n)) N).field=initialPartial A J X N := by
  funext x
  exact partialSum_field (fun n => (A n).increment (frequency J X n)) N x

def initialLimit : SmoothL2Field Space :=
  sumField (fun n => (A n).increment (frequency J X n))
    (actual_increment_summable A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency)

local notation "V" => initialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency

theorem initialLimit_Hm (s : ℕ) :
    Tendsto (fun N => derivativeSum s (initialPartial A J X N-(V).field)) atTop (𝓝 0) := by
  have h := sumField_derivativeSum_tendsto (fun n => (A n).increment (frequency J X n))
    (actual_increment_summable A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency) s
  simpa only [initialLimit,initialPartial_field] using h

theorem initialLimit_support : tsupport (V).field ⊆ Metric.closedBall 0 2 :=
  sumField_support (fun n => (A n).increment (frequency J X n))
    (actual_increment_summable A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency)
    (Metric.closedBall 0 2) Metric.isClosed_closedBall (fun n => (A n).increment_support (frequency
      J X n))

theorem initialLimit_compact : HasCompactSupport (V).field :=
  (isCompact_closedBall (0 : Space) 2).of_isClosed_subset (isClosed_tsupport _)
    (initialLimit_support A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency)

def fullInitialLimit (base : SmoothL2Field Space) : SmoothL2Field Space := addField base V

theorem fullInitialLimit_Hm (base : SmoothL2Field Space) (s : ℕ) :
    Tendsto (fun N => derivativeSum s ((base.field+initialPartial A J X N)-
      (fullInitialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency base).field))
      atTop (𝓝 0) := by
  have he (N : ℕ) : (base.field+initialPartial A J X N)-
      (fullInitialLimit A J hJ C c hC hc p q X hX hparameter hscale hσ hk hfrequency base).field=
      initialPartial A J X N-(V).field := by
    funext x
    change (base.field x+initialPartial A J X N x)-(base.field x+(V).field x)=
      initialPartial A J X N x-(V).field x
    abel
  simpa only [he] using initialLimit_Hm A J hJ C c hC hc p q X hX hparameter hscale hσ hk
    hfrequency s

end EulerPacketInitial
