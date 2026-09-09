/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevCoefficientPressure
import LeanPool.NavierStokesAndEuler.Euler.ResolventCalculus
import LeanPool.NavierStokesAndEuler.Euler.SobolevPressureResolvent

/-! Time regularity of the actual Sobolev pressure inverse, derived from its genuine resolvent. -/

@[expose] public section


noncomputable section

namespace EulerSobolevCoefficientPressure

open InnerProductSpace EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerResolventCalculus
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited normed group of Sobolev endomorphisms, named to keep instance inference shallow.
-/
local instance sobolevEndNormedGroup (q : ℕ) :
    NormedAddCommGroup (SobolevSpace period q →L[ℝ] SobolevSpace period q) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The inherited real normed-space structure of Sobolev endomorphisms. -/
local instance sobolevEndNormedSpace (q : ℕ) :
    NormedSpace ℝ (SobolevSpace period q →L[ℝ] SobolevSpace period q) :=
  ContinuousLinearMap.toNormedSpace

/-- Coefficient-multiplier continuity implies continuity of the actual pressure operator in Hq norm.
-/
theorem pressureSobolev_continuousAt {α : Type*} [TopologicalSpace α] {q : ℕ}
    (A : α → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ) (t : α)
    (hM : ContinuousAt (fun s => coefficientSobolevOperator period (K s)) t) :
    ContinuousAt (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s)) t := by
  apply continuousAt_of_resolvent
    (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s))
    (fun s => coefficientSobolevOperator period (K s)) _ t hM
  intro s r
  exact pressure_resolvent period (K s) (K r) κ m c c hc hc (hpos s) (hpos r)

/-- The actual pressure-corrected source operator is continuous whenever the coefficient multiplier
is continuous. -/
theorem projectedSource_continuousAt {α : Type*} [TopologicalSpace α] {q : ℕ}
    (A : α → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ) (t : α)
    (hM : ContinuousAt (fun s => coefficientSobolevOperator period (K s)) t) :
    ContinuousAt (fun s => projectedSourceOperator period (K s) κ m c hc (hpos s)) t := by
  have hP := pressureSobolev_continuousAt period A K κ m c hc hpos t hM
  have hMP := hM.clm_comp hP
  exact hMP.const_sub (ContinuousLinearMap.id ℝ (SobolevSpace period q))

/-- Differentiating the genuine resolvent gives the actual Hq pressure derivative −P M′ P. -/
theorem pressureSobolev_hasDerivAt {q : ℕ}
    (A : ℝ → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ)
    (t : ℝ) (M' : SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hM : HasDerivAt (fun s => coefficientSobolevOperator period (K s)) M' t) :
    HasDerivAt (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s))
      (-((pressureSobolevOperator period (K t) κ m c hc (hpos t)).comp
        (M'.comp (pressureSobolevOperator period (K t) κ m c hc (hpos t))))) t := by
  apply hasDerivAt_of_resolvent
    (fun s => pressureSobolevOperator period (K s) κ m c hc (hpos s))
    (fun s => coefficientSobolevOperator period (K s)) _ t M' hM
  intro s r
  exact pressure_resolvent period (K s) (K r) κ m c c hc hc (hpos s) (hpos r)

/-- The complete Sobolev pressure-corrected source has the actual derivative obtained by the product
rule. -/
theorem projectedSource_hasDerivAt {q : ℕ}
    (A : ℝ → SmoothCoefficient period) (K : ∀ s, CoefficientJet period standardDirection q (A s))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ s x v, c * ‖v‖ ^ 2 ≤ ⟪(A s).coefficient x v, v⟫_ℝ)
    (t : ℝ) (M' : SobolevSpace period q →L[ℝ] SobolevSpace period q)
    (hM : HasDerivAt (fun s => coefficientSobolevOperator period (K s)) M' t) :
    HasDerivAt (fun s => projectedSourceOperator period (K s) κ m c hc (hpos s))
      (-(M'.comp (pressureSobolevOperator period (K t) κ m c hc (hpos t)) +
        (coefficientSobolevOperator period (K t)).comp
          (-((pressureSobolevOperator period (K t) κ m c hc (hpos t)).comp
            (M'.comp (pressureSobolevOperator period (K t) κ m c hc (hpos t))))))) t := by
  have hP := pressureSobolev_hasDerivAt period A K κ m c hc hpos t M' hM
  have hMP := hM.clm_comp hP
  simpa only [zero_sub, Pi.sub_def, projectedSourceOperator] using
    (hasDerivAt_const t (ContinuousLinearMap.id ℝ (SobolevSpace period q))).sub hMP

end EulerSobolevCoefficientPressure
