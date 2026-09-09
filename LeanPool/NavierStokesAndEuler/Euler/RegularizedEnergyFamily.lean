/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedForcingWord
public import LeanPool.NavierStokesAndEuler.Euler.TimeFamily
public import LeanPool.NavierStokesAndEuler.Euler.SobolevEnergyPaths

@[expose] public section

/-! Actual finite energy families of all required derivative words and their strong weighted
  limits. -/

noncomputable section

namespace EulerRegularizedEnergyFamily

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerRegularizedWordEquation
  EulerRegularizedForcingWord EulerRegularizedTopBlocks EulerTimeFamily EulerTimeLp
    EulerVolterraConvolution
  EulerMetricPathConvergence EulerWeightedForcingTime EulerSobolevEnergyPaths
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]
variable {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}

/-- A finite actual family of energy-order heat-regularized Sobolev word paths. -/
def regularizedFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (n : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (i : α) :
    C(Icc (0 : ℝ) T, β → SobolevSpace period 2) :=
  familyPath T (fun j => regularizedWordPath period (hd i j) n (w i j) T u)

/-- The genuine L² values of the regularized energy-word family. -/
def regularizedValueFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (n : ℕ) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (i : α) :
    C(Icc (0 : ℝ) T, β → LiftL2 period) :=
  familyPath T (fun j => (valueOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    (regularizedWordPath period (hd i j) n (w i j) T u))

/-- The actual original energy-order derivative family as a continuous L² path. -/
def energyValueFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (i : α) :
    C(Icc (0 : ℝ) T, β → LiftL2 period) :=
  familyPath T (fun j => (valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    (energyWordPath period (hd i j) (w i j) T u))

omit [Fintype α] [Fintype β] in
/-- Every actual finite family of regularized derivative values converges uniformly, including its top order. -/
theorem regularizedValueFamily_tendsto (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (T : ℝ)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) (i : α) :
    Filter.Tendsto (fun n => regularizedValueFamily period d w hd n T u i) Filter.atTop
      (𝓝 (energyValueFamily period d w hd T u i)) :=
  familyPath_tendsto T _ _ (fun j => regularizedWordPath_value_tendsto period (hd i j) (w i j) T u)

/-- The actual finite family of regularized forcing words in the differentiated PDE. -/
def regularizedForcingFamily (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (n : ℕ) (T : ℝ)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (i : α) :
    C(Icc (0 : ℝ) T, β → LiftL2 period) :=
  familyPath T (fun j => forcingWordPath period (hd i j) n (w i j) T A G u f p)

/-- The limiting actual finite forcing family represented in Bochner L² time. -/
def forcingFamilyTime (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1))) (i : α)
      :
    TimeLp T (β → LiftL2 period) :=
  familyTime T (fun j => forcingWordTime period (hd i j) (w i j) T hT A G U F P)

omit [Fintype α] in
/-- Every actual finite forcing family converges strongly by the genuine word-level maximal regularity argument. -/
theorem regularizedForcingFamily_tendsto (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (T : ℝ) (hT : 0 ≤ T)
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
      (𝓝 U))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun t => truncateOperator period q (P t)) =ᵐ[timeMeasure T] extendPath T hT p) (i : α) :
    Filter.Tendsto (fun n => pathLp T hT (regularizedForcingFamily period d w hd n T A G u f p i))
      Filter.atTop
      (𝓝 (forcingFamilyTime period d w hd T hT A G U F P i)) := by
  have h := familyTime_tendsto T _ _ (fun j =>
    forcingWordPath_time_tendsto period (hd i j) (w i j) T hT A G u f p U F P hU hF hP)
  simpa only [familyTime_pathLp, regularizedForcingFamily, forcingFamilyTime] using h

/-- Computed weighted forcing paths converge to the actual weighted norm of the limiting PDE forcing family. -/
theorem regularizedWeightedForcing_tendsto (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q+1) (T : ℝ) (hT : 0 ≤ T) (weights : α → C(Icc (0 : ℝ) T, ℝ))
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (U : TimeLp T (SobolevSpace period (2+q))) (F P : TimeLp T (SobolevSpace period (q+1)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
      (𝓝 U))
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] extendPath T hT f)
    (hP : (fun t => truncateOperator period q (P t)) =ᵐ[timeMeasure T] extendPath T hT p) :
    Filter.Tendsto (fun n => pathLp T hT (weightedForcingPath T weights
      (regularizedForcingFamily period d w hd n T A G u f p))) Filter.atTop
      (𝓝 (weightedForcingTime T hT weights (forcingFamilyTime period d w hd T hT A G U F P))) := by
  have h := weightedForcingTime_tendsto T hT weights _ _
    (regularizedForcingFamily_tendsto period d w hd T hT A G u f p U F P hU hF hP)
  simpa only [weightedForcingTime_pathLp] using h

end EulerRegularizedEnergyFamily
