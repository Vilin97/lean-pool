/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
import LeanPool.NavierStokesAndEuler.Euler.InjectivePathDerivative
import LeanPool.NavierStokesAndEuler.Euler.QuadraticSourceLimit

/-! Actual finite-order Sobolev time regularity of the inviscid cylinder correction. -/

@[expose] public section


noncomputable section

namespace EulerInviscidSobolevEvolution

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerQuadraticSource EulerQuadraticSourceLimit
  EulerVolterraConvolution EulerInjectivePathDerivative EulerSobolevCoefficientPressure
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited Sobolev group structure used for the stronger time equation. -/
local instance evolutionSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance
/-- The inherited real Sobolev module used for the stronger time equation. -/
local instance evolutionSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance

/-- A genuine continuous quadratic Sobolev source upgrades the actual L² evolution to an Hq time
derivative of the truncated H(q+1) path. -/
theorem sobolev_hasDerivAt {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (A : Coefficients (Icc (0 : ℝ) T) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hd : ∀ t (ht : t ∈ Ioo 0 T), HasDerivAt (fun r => value period (extendPath T hT e r))
      (value period (A.apply ⟨t, ht.1.le, ht.2.le⟩ (e ⟨t, ht.1.le, ht.2.le⟩))) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => truncateOperator period q (extendPath T hT e r))
      (A.apply ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩)) t := by
  let u := (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) T) e
  let f := sourcePath A e
  have hweak : ∀ r ∈ Ioo 0 T,
      HasDerivAt (fun s => valueOperator period q (extendPath T hT u s))
        (valueOperator period q (extendPath T hT f r)) r := by
    intro r hr
    change HasDerivAt (fun s => value period (extendPath T hT e s))
      (value period (A.apply (projIcc 0 T hT r) (e (projIcc 0 T hT r)))) r
    simpa only [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩] using hd r hr
  have h := hasDerivAt_of_injective_map (valueOperator period q) (value_injective period)
    T hT u f hweak t ht
  change HasDerivAt (fun r => truncateOperator period q (extendPath T hT e r))
    (A.apply (projIcc 0 T hT t) (e (projIcc 0 T hT t))) t at h
  simpa only [projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩] using h

/-- The actual projected Sobolev source equals the literal non-pressure source and signed coercive
pressure already before passing to L². -/
theorem CorrectionData.source_sobolev {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (e : SobolevSpace period (q + 1)) :
    (D.coefficients period hq).apply t e = -D.rawSource period hq t e -
      coefficientSobolevOperator period (D.metric.jet t) (D.pressure period hq t e) := by
  apply value_injective period
  change value period ((D.coefficients period hq).apply t e) =
    -value period (D.rawSource period hq t e) -
      value period (coefficientSobolevOperator period (D.metric.jet t) (D.pressure period hq t e))
  rw [coefficientSobolevOperator_value]
  exact D.source_value period hq t e

/-- The actual correction equation has its literal signed-pressure time derivative in Hq whenever
its continuous H(q+1) path satisfies the constructed L² equation. -/
theorem correction_sobolev_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hd : ∀ t (ht : t ∈ Ioo 0 T), HasDerivAt (fun r => value period (extendPath T hT e r))
      (value period ((D.coefficients period hq).apply ⟨t, ht.1.le, ht.2.le⟩ (e ⟨t, ht.1.le,
          ht.2.le⟩)))
          t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => truncateOperator period q (extendPath T hT e r))
      (-D.rawSource period hq ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩) -
        coefficientSobolevOperator period (D.metric.jet ⟨t,ht.1.le,ht.2.le⟩)
          (D.pressure period hq ⟨t,ht.1.le,ht.2.le⟩ (e ⟨t,ht.1.le,ht.2.le⟩))) t := by
  simpa only [CorrectionData.source_sobolev] using
    sobolev_hasDerivAt period T hT (D.coefficients period hq) e hd t ht

end EulerInviscidSobolevEvolution
