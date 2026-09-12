/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSplit
public import LeanPool.NavierStokesAndEuler.Euler.TimeCorrectionSource
import LeanPool.NavierStokesAndEuler.Euler.SobolevNonlinearCompatibility

/-! The actual lower Sobolev equation and its continuous source and pressure paths. -/

section

/-! Exact almost-everywhere restriction of the actual nonlinear source and pressure time fields. -/

@[expose] public section

noncomputable section

namespace EulerTimeCorrectionSource

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevNonlinearCompatibility
  EulerGevreyOrderZero EulerSobolevTransport EulerTimeLp EulerVolterraConvolution
      EulerCorrectionOperators
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance timeRestrictGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance timeRestrictSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The literal lower-order raw correction source obtained from genuine higher coefficient data. -/
def lowerRawValue {q : ℕ} (hq : 6 ≤ q) (T : ℝ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : CoefficientPath period (q + 1) (Icc (0 : ℝ) T))
    (C : Fin 3 → CoefficientPath period (q + 1) (Icc (0 : ℝ) T))
    (K0 : ∀ t, CoefficientJet period standardDirection q (C0.coefficient t))
    (K : ∀ i t, CoefficientJet period standardDirection q ((C i).coefficient t))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) : SobolevSpace period
        q
        :=
  transportBilinear period hq L hL (truncateOperator period (q+1) (z t)+e t) (e t) +
    orderZeroSource period hq L hL (coefficientSobolevOperator period (K0 t))
      (fun i => coefficientSobolevOperator period (K i t)) (truncateOperator period (q+1) (z t))
      (truncateOperator period q (r t)) (truncateOperator period q (e t))

/-- The constructed energy-order raw source is a genuine higher regularity representative of the
original correction source. -/
theorem rawSourceTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : CoefficientPath period (q + 1) (Icc (0 : ℝ) T))
    (C : Fin 3 → CoefficientPath period (q + 1) (Icc (0 : ℝ) T))
    (K0 : ∀ t, CoefficientJet period standardDirection q (C0.coefficient t))
    (K : ∀ i t, CoefficientJet period standardDirection q ((C i).coefficient t))
    (z : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (r e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (U : TimeLp T (SobolevSpace period ((q + 1) + 1)))
    (hU : (fun t => truncateOperator period (q + 1) (U t)) =ᵐ[timeMeasure T] extendPath T hT e) :
    (fun t => truncateOperator period q
      (rawSourceTime period (by
          omega : 6 ≤ q+1) T hT L hL C0.operatorPath (fun i => (C i).operatorPath) z r e U t))
              =ᵐ[timeMeasure T]
      fun t => lowerRawValue period hq T L hL C0 C K0 K z r e (projIcc 0 T hT t) := by
  filter_upwards [rawSourceTime_ae period (by omega : 6 ≤ q+1) T hT L hL C0.operatorPath
    (fun i => (C i).operatorPath) z r e U, hU] with t ht hu
  have h := restrict_raw_source period hq L hL (C0.coefficient (projIcc 0 T hT t))
    (C0.jet (projIcc 0 T hT t)) (K0 (projIcc 0 T hT t))
    (fun i => (C i).coefficient (projIcc 0 T hT t))
    (fun i => (C i).jet (projIcc 0 T hT t)) (fun i => K i (projIcc 0 T hT t))
    (extendPath T hT z t) (extendPath T hT r t) (extendPath T hT e t) (U t) hu
  exact (congrArg (truncateOperator period q) ht).trans h

/-- Actual signed coercive pressure commutes with the energy-to-source Sobolev restriction almost
everywhere. -/
theorem pressureTime_restriction {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (G : CoefficientPath period (q + 1) (Icc (0 : ℝ) T))
    (K : ∀ t, CoefficientJet period standardDirection q (G.coefficient t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period (q + 1))) (f : ℝ → SobolevSpace period q)
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] f) :
    (fun t => truncateOperator period q (pressureTime period T hT G κ m c hc hpos F t))
        =ᵐ[timeMeasure T]
      fun t => -(pressureSobolevOperator period (K (projIcc 0 T hT t)) κ m c hc (hpos _) (f t)) :=
          by
  filter_upwards [pressureTime_ae period T hT G κ m c hc hpos F, hF] with t ht hf
  have hp := restrict_pressure period (by omega : q ≤ q+1) (G.jet (projIcc 0 T hT t))
    (K (projIcc 0 T hT t)) κ m c hc (hpos _) (F t)
  have hp' : truncateOperator period q
      (-(pressureSobolevOperator period (G.jet (projIcc 0 T hT t)) κ m c hc (hpos _) (F t))) =
      -(pressureSobolevOperator period (K (projIcc 0 T hT t)) κ m c hc (hpos _) (f t)) := by
    rw [map_neg]
    exact congrArg (fun x : SobolevSpace period q => -x)
      (hp.trans (congrArg (pressureSobolevOperator period (K (projIcc 0 T hT t)) κ m c hc (hpos _))
          hf))
  exact (congrArg (truncateOperator period q) ht).trans hp'

/-- The actual projected nonlinear mild source restricts to the original forcing almost everywhere.
-/
theorem projectedTime_restriction {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (G : CoefficientPath period (q + 1) (Icc (0 : ℝ) T))
    (K : ∀ t, CoefficientJet period standardDirection q (G.coefficient t))
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ t x v, c * ‖v‖ ^ 2 ≤ ⟪(G.coefficient t).coefficient x v, v⟫_ℝ)
    (F : TimeLp T (SobolevSpace period (q + 1))) (f : ℝ → SobolevSpace period q)
    (hF : (fun t => truncateOperator period q (F t)) =ᵐ[timeMeasure T] f) :
    (fun t => truncateOperator period q (projectedTime period T hT G κ m c hc hpos F t))
        =ᵐ[timeMeasure T]
      fun t => -(projectedSourceOperator period (K (projIcc 0 T hT t)) κ m c hc (hpos _) (f t)) :=
          by
  filter_upwards [projectedTime_ae period T hT G κ m c hc hpos F, hF] with t ht hf
  have hp := restrict_projectedSource period (by omega : q ≤ q+1) (G.jet (projIcc 0 T hT t))
    (K (projIcc 0 T hT t)) κ m c hc (hpos _) (F t)
  have hp' : truncateOperator period q
      (-(projectedSourceOperator period (G.jet (projIcc 0 T hT t)) κ m c hc (hpos _) (F t))) =
      -(projectedSourceOperator period (K (projIcc 0 T hT t)) κ m c hc (hpos _) (f t)) := by
    rw [map_neg]
    exact congrArg (fun x : SobolevSpace period q => -x)
      (hp.trans (congrArg (projectedSourceOperator period (K (projIcc 0 T hT t)) κ m c hc (hpos _))
          hf))
  exact (congrArg (truncateOperator period q) ht).trans hp'

end EulerTimeCorrectionSource

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionLowerData

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerCorrectionOperators
      EulerQuadraticSource
  EulerTimeCorrectionSource EulerGevreyOrderZero EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A local normed-group instance for the concrete lower Sobolev scale. -/
local instance lowerDataGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

/-- A local real normed-space instance for the concrete lower Sobolev scale. -/
local instance lowerDataSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The same genuine correction coefficients and background restricted by one Sobolev order. -/
def lowerData {q : ℕ} {T : ℝ} (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t))) :
    CorrectionData period q (Icc (0 : ℝ) T) where
  κ := D.κ
  direction := D.direction
  scale_bound := D.scale_bound
  direction_bound := D.direction_bound
  metric := ⟨D.metric.coefficient, KG, hG⟩
  coercivity := D.coercivity
  coercivity_pos := D.coercivity_pos
  metric_pos := D.metric_pos
  linear := ⟨D.linear.coefficient, KL, hL⟩
  quadratic i := ⟨(D.quadratic i).coefficient, KQ i, hQ i⟩
  approximation := (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      D.approximation
  residual := (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) D.residual

/-- The actual nonlinear raw source along a continuous Sobolev path is continuous. -/
def rawPath {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  ⟨fun t => D.rawSource period hq t (e t),
    (((D.coefficients period hq).forcing.continuous.add
      ((D.coefficients period hq).linear.continuous.clm_apply e.continuous)).add
      (((D.coefficients period hq).quadratic.continuous.clm_apply e.continuous).clm_apply
          e.continuous))⟩

/-- The actual projected nonlinear mild forcing along the continuous solution. -/
def forcingPath {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  ⟨fun t => (D.coefficients period hq).apply t (e t),
    ((D.coefficients period hq).projection.continuous.clm_apply (rawPath period hq D
        e).continuous).neg⟩

/-- The actual signed coercive pressure along the continuous solution is continuous. -/
def pressurePath {q : ℕ} (hq : 6 ≤ q) {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, SobolevSpace period q) :=
  ⟨fun t => D.pressure period hq t (e t),
    ((positivePressurePath period T D.metric D.κ D.direction D.coercivity D.coercivity_pos
        D.metric_pos).continuous.clm_apply
      (rawPath period hq D e).continuous).neg⟩

/-- The actual lower raw source is exactly the lower restriction used by the constructed Bochner
source. -/
theorem rawPath_lower {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    rawPath period hq (lowerData period D KG KL KQ hG hL hQ) e t =
      lowerRawValue period hq T (EulerSobolevTransport.velocityComponents D.κ D.direction)
        (EulerSobolevTransport.velocityComponents_norm D.κ D.direction D.scale_bound
            D.direction_bound)
        D.linear D.quadratic KL KQ D.approximation D.residual e t :=
  correctionData_rawSource_split period (lowerData period D KG KL KQ hG hL hQ) hq t (e t)

/-- The actual continuous pressure path lies in the genuine lifted gradient space at every time. -/
theorem pressurePath_gradient {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    value period (pressurePath period hq D e t) ∈ gradientSpace period D.κ D.direction :=
  D.pressure_mem_gradient period hq t (e t)

end EulerCorrectionLowerData
