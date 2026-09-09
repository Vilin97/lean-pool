/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedEnergyFamily
public import LeanPool.NavierStokesAndEuler.Euler.TimeForcingRepresentative

@[expose] public section

/-! Literal almost-everywhere representatives of the limiting actual word forcing. -/

noncomputable section

namespace EulerRegularizedForcingRepresentative

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerMildTopWord
  EulerRegularizedForcingWord EulerRegularizedEnergyFamily EulerTimeFamily EulerTimeLp
  EulerVolterraConvolution EulerWeightedForcingTime EulerFiniteMetricEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The limiting word forcing has exactly the differentiated-source plus transport plus pressure representative. -/
theorem forcingWordTime_ae {q m : ℕ} (hm : m ≤ q+1) (w : Fin m → Fin 4) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) :
    (forcingWordTime period hm w T hT A G U F P : ℝ → LiftL2 period) =ᵐ[timeMeasure T]
      fun t => word period (F t) hm w + A (projIcc 0 T hT t)
        (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w (U t)) +
        G (projIcc 0 T hT t) (word period (P t) hm w) := by
  exact timeLinearForcing_ae T hT
    (wordOperator period (⟨⟨m,Nat.lt_succ_of_le hm⟩,w⟩ : SobolevWord (q+1)))
    (boundedWordBlock period 1 m (by omega : 1+m ≤ 2+q) w) A G U F P

/-- The limiting finite family has its literal actual word forcing at every component almost everywhere. -/
theorem forcingFamilyTime_ae {α β : Type*} [Fintype β] {q : ℕ}
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hd : ∀ i j, d i j ≤ q+1)
    (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) (i : α)
      :
    (forcingFamilyTime period d w hd T hT A G U F P i : ℝ → β → LiftL2 period) =ᵐ[timeMeasure T]
      fun t j => word period (F t) (hd i j) (w i j) + A (projIcc 0 T hT t)
        (boundedWordBlock period 1 (d i j) (by have := hd i j; omega : 1+d i j ≤ 2+q) (w i j) (U
          t)) +
        G (projIcc 0 T hT t) (word period (P t) (hd i j) (w i j)) := by
  filter_upwards [familyTime_ae T (fun j => forcingWordTime period (hd i j) (w i j) T hT A G U F P),
    ae_all_iff.mpr (fun j => forcingWordTime_ae period (hd i j) (w i j) T hT A G U F P)] with t h1
      h2
  change familyTime T _ t = _
  rw [h1]
  exact funext h2

/-- The limiting weighted forcing is the genuine finite sum of norms of the literal differentiated PDE forcing. -/
theorem weighted_forcing_ae {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}
    (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4) (hd : ∀ i j, d i j ≤ q+1)
    (T : ℝ) (hT : 0 ≤ T) (weights : α → C(Icc (0 : ℝ) T, ℝ))
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) :
    (weightedForcingTime T hT weights (forcingFamilyTime period d w hd T hT A G U F P) : ℝ → ℝ)
      =ᵐ[timeMeasure T]
      fun t => ∑ i, extendPath T hT (weights i) t * familyNorm (fun j =>
        word period (F t) (hd i j) (w i j) + A (projIcc 0 T hT t)
          (boundedWordBlock period 1 (d i j) (by have := hd i j; omega : 1+d i j ≤ 2+q) (w i j) (U
            t)) +
          G (projIcc 0 T hT t) (word period (P t) (hd i j) (w i j))) := by
  filter_upwards [weightedForcingTime_ae T hT weights (forcingFamilyTime period d w hd T hT A G U F
    P),
    ae_all_iff.mpr (fun i => forcingFamilyTime_ae period d w hd T hT A G U F P i)] with t h1 h2
  rw [h1]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v : β → LiftL2 period =>
    extendPath T hT (weights i) t * familyNorm v) (h2 i))

end EulerRegularizedForcingRepresentative
