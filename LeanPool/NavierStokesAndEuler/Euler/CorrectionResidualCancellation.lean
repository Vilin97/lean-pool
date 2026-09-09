/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation

/-! Adding the actual correction removes a genuine approximate-solution residual. -/

@[expose] public section


noncomputable section

namespace EulerCorrectionResidualCancellation

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerQuadraticSource EulerVolterraConvolution
   EulerSobolevCoefficientPressure
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev group structure for exact residual cancellation. -/
local instance residualSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- The inherited real Sobolev module structure for exact residual cancellation. -/
local instance residualSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual linear coefficient plus the full transport-and-algebraic quadratic nonlinearity. -/
def nonlinearity {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (u : SobolevSpace period (q + 1)) : SobolevSpace period q :=
  coefficientSobolevOperator period (D.linear.jet t) (truncateOperator period q u) +
    (D.coefficients period hq).quadratic t u u

/-- The actual raw correction source is exactly the prescribed residual plus the full nonlinear
increment about the prescribed approximation. -/
theorem rawSource_eq_residual_increment {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q + 1)) :
    D.rawSource period hq t e = D.residual t +
      nonlinearity period D hq t (D.approximation t+e) -
      nonlinearity period D hq t (D.approximation t) := by
  let B := (D.coefficients period hq).quadratic t
  let A := (coefficientSobolevOperator period (D.linear.jet t)).comp (truncateOperator period q)
  change D.residual t + linearize B A (D.approximation t) e + B e e =
    D.residual t + (A (D.approximation t+e) + B (D.approximation t+e) (D.approximation t+e)) -
      (A (D.approximation t) + B (D.approximation t) (D.approximation t))
  simp only [linearize_apply,map_add,add_apply]
  abel

/-- The signed approximate and correction equations cancel the residual and add their actual
pressures. -/
theorem residual_cancellation {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (e : SobolevSpace period (q + 1)) (pa : SobolevSpace period q) :
    (D.residual t-nonlinearity period D hq t (D.approximation t) -
        coefficientSobolevOperator period (D.metric.jet t) pa) +
      (-D.rawSource period hq t e -
        coefficientSobolevOperator period (D.metric.jet t) (D.pressure period hq t e)) =
      -nonlinearity period D hq t (D.approximation t+e) -
        coefficientSobolevOperator period (D.metric.jet t) (pa+D.pressure period hq t e) := by
  rw [rawSource_eq_residual_increment period D hq t e,map_add]
  abel

/-- The actual continuous corrected path is the prescribed approximation plus the constructed error.
-/
def correctedPath {q : ℕ} {T : ℝ} (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    C(Icc (0 : ℝ) T,SobolevSpace period (q+1)) := D.approximation+e

/-- A zero initial correction preserves the actual initial field. -/
theorem correctedPath_initial {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (he : e ⟨0, le_rfl, hT⟩ = 0) :
    correctedPath period D e ⟨0,le_rfl,hT⟩=D.approximation ⟨0,le_rfl,hT⟩ := by
  change D.approximation ⟨0,le_rfl,hT⟩+e ⟨0,le_rfl,hT⟩=_
  rw [he,add_zero]

/-- The corrected path retains the genuine lifted divergence constraint by addition in its closed
subspace. -/
theorem correctedPath_divergenceFree {q : ℕ} {T : ℝ}
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (he : ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) (t : Icc (0 : ℝ) T)
        :
    value period (correctedPath period D e t) ∈ divergenceFreeSpace period D.κ D.direction :=
  (divergenceFreeSpace period D.κ D.direction).add_mem (hz t) (he t)

/-- Adding a genuine approximate pressure to the actual correction pressure preserves membership in
the lifted gradient space. -/
theorem corrected_pressure_mem_gradient {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T)
    (e : SobolevSpace period (q + 1)) (pa : SobolevSpace period q)
    (hpa : value period pa ∈ gradientSpace period D.κ D.direction) :
    value period (pa+D.pressure period hq t e) ∈ gradientSpace period D.κ D.direction :=
  (gradientSpace period D.κ D.direction).add_mem hpa (D.pressure_mem_gradient period hq t e)

/-- Actual approximate and correction derivatives give the zero-residual nonlinear equation for
their sum, with the sum of their genuine pressures. -/
theorem correctedPath_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (pa : C(Icc (0 : ℝ) T, SobolevSpace period q)) (t : ℝ) (ht : t ∈ Ioo 0 T)
    (hz : HasDerivAt (fun r => truncateOperator period q (extendPath T hT D.approximation r))
      (D.residual ⟨t, ht.1.le, ht.2.le⟩ -
        nonlinearity period D hq ⟨t, ht.1.le, ht.2.le⟩ (D.approximation ⟨t, ht.1.le, ht.2.le⟩) -
        coefficientSobolevOperator period (D.metric.jet ⟨t, ht.1.le, ht.2.le⟩) (pa
            ⟨t, ht.1.le, ht.2.le⟩)) t)
    (he : HasDerivAt (fun r => truncateOperator period q (extendPath T hT e r))
      (-D.rawSource period hq ⟨t, ht.1.le, ht.2.le⟩ (e ⟨t, ht.1.le, ht.2.le⟩) -
        coefficientSobolevOperator period (D.metric.jet ⟨t, ht.1.le, ht.2.le⟩)
          (D.pressure period hq ⟨t, ht.1.le, ht.2.le⟩ (e ⟨t, ht.1.le, ht.2.le⟩))) t) :
    HasDerivAt (fun r => truncateOperator period q (extendPath T hT (correctedPath period D e) r))
      (-nonlinearity period D hq ⟨t,ht.1.le,ht.2.le⟩
        (correctedPath period D e ⟨t,ht.1.le,ht.2.le⟩) -
        coefficientSobolevOperator period (D.metric.jet ⟨t,ht.1.le,ht.2.le⟩)
          (pa ⟨t,ht.1.le,ht.2.le⟩+D.pressure period hq ⟨t,ht.1.le,ht.2.le⟩ (e
              ⟨t,ht.1.le,ht.2.le⟩))) t := by
  have h := (hz.add he).congr_deriv
    (residual_cancellation period D hq ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩) (pa
        ⟨t,ht.1.le,ht.2.le⟩))
  convert h using 1 <;> rfl

end EulerCorrectionResidualCancellation
