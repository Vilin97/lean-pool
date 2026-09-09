/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoverMollification
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
import LeanPool.NavierStokesAndEuler.Euler.Foundations.CoverMollificationFubini
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SetIntegralL2
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet

/-! Actual classical smooth representatives of the strong L² cylinder mollifiers. -/

@[expose] public section

noncomputable section

namespace EulerMollifierRepresentative

open MeasureTheory EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev
open EulerLiftedGradientSpace EulerMetricTransport EulerCoverMollification
open EulerCoverMollificationFubini EulerCylinderMollifier EulerSpatialSobolevInverse
    EulerStrongSmoothJet
open scoped ContDiff ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The concrete classical convolution representing the Bochner L² mollifier. -/
noncomputable def smoothMollifier (n : ℕ) (U : LiftL2 period) : LiftDomain period → Vector3 :=
  cylinderConvolution period (mollifierBump n) U

/-- The smooth convolution and the Bochner convolution are the same almost everywhere. -/
theorem mollify_ae_smoothMollifier (n : ℕ) (U : LiftL2 period) :
    (mollify period n U : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      smoothMollifier period n U := by
  apply ae_eq_cylinderConvolution_of_setIntegrals period (mollifierBump n) U (mollify period n U)
  intro K hK hfin
  simpa only [mollifierKernel, integral_smul] using
    EulerSetIntegralL2.mollify_setIntegral period n U K hK hfin.ne

/-- Every strong L² mollifier has an actual C∞ representative on the cylinder. -/
theorem smoothMollifier_smooth (n : ℕ) (U : LiftL2 period) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period (smoothMollifier period n U) x) :=
  cylinderConvolution_smooth period (mollifierBump n) U (Lp.memLp U)

/-- Strong mollified jets are precisely the classical derivatives of the smooth convolution. -/
theorem smoothMollifier_word_ae {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    (mollify period n (J.word w) : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      iteratedFieldDerivative period w (smoothMollifier period n U) := by
  rw [← mollifyJet_word period J n w]
  exact jet_word_ae period hk _ (mollifyJet period J n) w _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

/-- All available classical derivatives of the smooth mollifier are genuinely in L². -/
theorem smoothMollifier_word_memLp {s k : ℕ} (hk : k ≤ s) (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) (w : Fin k → Fin 4) :
    MemLp (iteratedFieldDerivative period w (smoothMollifier period n U)) 2 (liftMeasure period) :=
  (Lp.memLp _).ae_eq (smoothMollifier_word_ae period hk U J n w)

/-- The strong and classical Sobolev norms of each mollifier agree exactly. -/
theorem smoothMollifier_sobolevNorm {s : ℕ} (U : LiftL2 period)
    (J : SpatialJet period standardDirection s U) (n : ℕ) :
    (mollifyJet period J n).sobolevNorm = liftSobolevNorm period s (smoothMollifier period n U) :=
  jet_sobolevNorm_eq period _ (mollifyJet period J n) _
    (mollify_ae_smoothMollifier period n U) (smoothMollifier_smooth period n U)

end EulerMollifierRepresentative
