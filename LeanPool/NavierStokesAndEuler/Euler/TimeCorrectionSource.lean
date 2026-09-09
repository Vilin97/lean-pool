/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevCorrectionCompatibility
public import LeanPool.NavierStokesAndEuler.Euler.TimeSobolevTransport
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation

@[expose] public section

/-! Actual energy-order Bochner representatives of the nonlinear correction source and pressure. -/

noncomputable section

namespace EulerTimeCorrectionSource

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevNonlinearCompatibility
  EulerSobolevCorrectionCompatibility EulerGevreyOrderZero EulerAsymmetricTransport
    EulerSobolevTransport
  EulerTimeLp EulerTimeSobolevTransport EulerVolterraConvolution EulerCorrectionOperators
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

local instance timeCorrectionGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
local instance timeCorrectionSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual order-zero source is a continuous path on the energy Sobolev level. -/
def orderZeroPath {s : ℕ} (hs : 6 ≤ s) (T : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s+1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s)) : C(Icc (0 : ℝ) T, SobolevSpace period s) :=
  ⟨fun t => orderZeroSource period hs L hL (C0 t) (fun i => C i t) (z t) (r t) (e t),
    orderZeroSource_continuous period hs L hL C0 C0.continuous (fun t i => C i t) (fun i => (C
      i).continuous)
      z r e z.continuous r.continuous e.continuous⟩

/-- The genuine energy-order raw correction source uses the constructed higher derivative only in its top transport. -/
def rawSourceTime {s : ℕ} (hs : 6 ≤ s) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s+1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (U : TimeLp T (SobolevSpace period (s+1))) : TimeLp T (SobolevSpace period s) :=
  transportTime period hs L hL T hT
    ((truncateOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) z + e) U +
      pathLp T hT (orderZeroPath period hs T L hL C0 C z r e)

/-- The Bochner raw source has exactly the actual transport-plus-order-zero representative. -/
theorem rawSourceTime_ae {s : ℕ} (hs : 6 ≤ s) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (C : Fin 3 → C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period (s+1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period s))
    (U : TimeLp T (SobolevSpace period (s+1))) :
    (rawSourceTime period hs T hT L hL C0 C z r e U : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => asymmetricTransport period hs L hL
        (truncateOperator period s (extendPath T hT z t) + extendPath T hT e t) (U t) +
          extendPath T hT (orderZeroPath period hs T L hL C0 C z r e) t := by
  let b := (truncateOperator period s).compLeftContinuous ℝ (Icc (0 : ℝ) T) z + e
  let F := orderZeroPath period hs T L hL C0 C z r e
  filter_upwards [Lp.coeFn_add (transportTime period hs L hL T hT b U) (pathLp T hT F),
    transportTime_ae period hs L hL T hT b U, pathLp_ae T hT F] with t h1 h2 h3
  simp only [Pi.add_apply] at h1
  exact h1.trans (congrArg₂ (fun x y : SobolevSpace period s => x+y) h2 h3)

/-- Restricting genuine asymmetric transport and its constructed state recovers the original lower-level nonlinearity. -/
theorem restrict_transport_state {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (b e : SobolevSpace period (q+1)) (U : SobolevSpace period ((q+1)+1))
    (hU : truncateOperator period (q+1) U = e) :
    truncateOperator period q (asymmetricTransport period (by omega : 6 ≤ q+1) L hL b U) =
      transportBilinear period hq L hL b e := by
  have hb : restrictOperator period (by omega : q ≤ q+1) b = truncateOperator period q b := by
    apply value_injective period
    rfl
  have hUr : restrictOperator period (by omega : q+1 ≤ (q+1)+1) U = e := by
    exact hU
  have h := restrict_asymmetricTransport period (by omega : 6 ≤ q+1) hq (by omega : q ≤ q+1) L hL b
    U
  have he := congrArg₂ (fun x : SobolevSpace period q => fun y : SobolevSpace period (q+1) =>
    asymmetricTransport period hq L hL x y) hb hUr
  exact h.trans (he.trans (asymmetricTransport_eq period hq L hL b e))

/-- The upgraded raw source restricts to the literal lower-order correction equation. -/
theorem restrict_raw_source {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (A0 : SmoothCoefficient period) (KP0 : CoefficientJet period standardDirection (q+1) A0)
    (KQ0 : CoefficientJet period standardDirection q A0) (A : Fin 3 → SmoothCoefficient period)
    (KP : ∀ i, CoefficientJet period standardDirection (q+1) (A i))
    (KQ : ∀ i, CoefficientJet period standardDirection q (A i))
    (z : SobolevSpace period ((q+1)+1)) (r e : SobolevSpace period (q+1))
    (U : SobolevSpace period ((q+1)+1)) (hU : truncateOperator period (q+1) U = e) :
    truncateOperator period q
      (asymmetricTransport period (by omega : 6 ≤ q+1) L hL (truncateOperator period (q+1) z+e) U +
        orderZeroSource period (by omega : 6 ≤ q+1) L hL (coefficientSobolevOperator period KP0)
          (fun i => coefficientSobolevOperator period (KP i)) z r e) =
      transportBilinear period hq L hL (truncateOperator period (q+1) z+e) e +
        orderZeroSource period hq L hL (coefficientSobolevOperator period KQ0)
          (fun i => coefficientSobolevOperator period (KQ i))
          (truncateOperator period (q+1) z) (truncateOperator period q r) (truncateOperator period
            q e) := by
  rw [map_add]
  exact congrArg₂ (fun x y : SobolevSpace period q => x+y)
    (restrict_transport_state period hq L hL _ e U hU)
    (restrict_orderZeroSource period (by omega : 6 ≤ q+1) hq (by omega : q ≤ q+1)
      L hL A0 KP0 KQ0 A KP KQ z r e)

/-- The actual positive coercive pressure operator is a continuous energy-order time path. -/
def positivePressurePath {s : ℕ} (T : ℝ) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G.coefficient t).coefficient x v,v⟫_ℝ) :
    C(Icc (0 : ℝ) T, SobolevSpace period s →L[ℝ] SobolevSpace period s) :=
  ⟨fun t => pressureSobolevOperator period (G.jet t) κ m c hc (hpos t),
    continuous_iff_continuousAt.mpr (fun t => pressureSobolev_continuousAt period G.coefficient
      G.jet κ m c hc hpos t G.continuous.continuousAt)⟩

/-- The actual signed PDE pressure belongs to the full energy-order Bochner space. -/
def pressureTime {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G.coefficient t).coefficient x v,v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) : TimeLp T (SobolevSpace period s) :=
  -(timeMultiplier T hT (positivePressurePath period T G κ m c hc hpos) F)

/-- The actual projected mild forcing belongs to the full energy-order Bochner space. -/
def projectedTime {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G.coefficient t).coefficient x v,v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) : TimeLp T (SobolevSpace period s) :=
  -(timeMultiplier T hT (pressureProjectionPath period G.coefficient G.jet κ m c hc hpos
    G.continuous) F)

/-- The signed pressure time field is the literal unique coercive pressure solve almost everywhere. -/
theorem pressureTime_ae {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G.coefficient t).coefficient x v,v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) :
    (pressureTime period T hT G κ m c hc hpos F : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => -(pressureSobolevOperator period (G.jet (projIcc 0 T hT t)) κ m c hc (hpos _) (F t))
        := by
  filter_upwards [Lp.coeFn_neg (timeMultiplier T hT (positivePressurePath period T G κ m c hc hpos)
    F),
    timeMultiplier_ae T hT (positivePressurePath period T G κ m c hc hpos) F] with t h1 h2
  simp only [Pi.neg_apply] at h1
  exact h1.trans (congrArg (fun x : SobolevSpace period s => -x) h2)

/-- The projected time field is exactly the pressure-projected nonlinear mild forcing almost everywhere. -/
theorem projectedTime_ae {s : ℕ} (T : ℝ) (hT : 0 ≤ T) (G : CoefficientPath period s (Icc (0 : ℝ) T))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c*‖v‖^2 ≤ ⟪(G.coefficient t).coefficient x v,v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period s)) :
    (projectedTime period T hT G κ m c hc hpos F : ℝ → SobolevSpace period s) =ᵐ[timeMeasure T]
      fun t => -(projectedSourceOperator period (G.jet (projIcc 0 T hT t)) κ m c hc (hpos _) (F t))
        := by
  filter_upwards [Lp.coeFn_neg (timeMultiplier T hT (pressureProjectionPath period G.coefficient
    G.jet κ m c hc hpos G.continuous) F),
    timeMultiplier_ae T hT (pressureProjectionPath period G.coefficient G.jet κ m c hc hpos
      G.continuous) F] with t h1 h2
  simp only [Pi.neg_apply] at h1
  exact h1.trans (congrArg (fun x : SobolevSpace period s => -x) h2)

end EulerTimeCorrectionSource
