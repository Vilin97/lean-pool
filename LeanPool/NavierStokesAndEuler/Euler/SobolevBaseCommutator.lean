/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseTransportL2
public import LeanPool.NavierStokesAndEuler.Euler.TransportL2Bilinear
public import LeanPool.NavierStokesAndEuler.Euler.SobolevTransport
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordLevel
import LeanPool.NavierStokesAndEuler.Euler.SmoothInequalityTransfer
import LeanPool.NavierStokesAndEuler.Euler.SobolevTransportCommutator

/-! The genuine base transport commutator on finite Sobolev fields, with an H⁶-only bound. -/

@[expose] public section


noncomputable section

namespace EulerSobolevBaseCommutator

open MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMetricTransport EulerTransportDerivatives EulerSobolevL2Product EulerSobolevTransport
  EulerFunctionalVelocity EulerH6Nonlinear EulerSobolevTransportCommutator EulerSobolevWordLevel
  EulerTransportL2Bilinear EulerBaseTransportL2 EulerSmoothInequalityTransfer
      EulerExternalTransportCommutator
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Cache the standard `NormedAddCommGroup (SobolevSpace period q)` instance to shorten
typeclass synthesis. -/
local instance baseCommGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace period q)` instance to shorten typeclass
synthesis. -/
local instance baseCommSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The actual base derivative commutator, evaluated in L² on its genuine H⁷ domain. -/
def baseCommutator (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1) :
    SobolevSpace period 7 →L[ℝ] SobolevSpace period 7 →L[ℝ] LiftL2 period :=
  ((ContinuousLinearMap.compL ℝ (SobolevSpace period 7) (SobolevSpace period 6) (LiftL2 period)
    ((valueOperator period 0).comp (wordAtLevel period 0 r w (by omega : r+0 ≤ 6)))).comp
      (transportBilinear period (by norm_num : 6 ≤ 6) L hL)) -
  (transportL2Bilinear period (by norm_num : 3 ≤ 7) L).bilinearComp
    (ContinuousLinearMap.id ℝ (SobolevSpace period 7)) (wordAtLevel period 1 r w (by
        omega : r+1 ≤ 7))

/-- The actual operands of the finite-Sobolev base commutator. -/
theorem baseCommutator_apply (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) :
    baseCommutator period r hr w L hL u v =
      value period (wordAtLevel period 0 r w (by
          omega : r+0 ≤ 6) (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v)) -
        transportL2Bilinear period (by
            norm_num : 3 ≤ 7) L u (wordAtLevel period 1 r w (by omega : r+1 ≤ 7) v) := rfl

/-- Its actual L² representative is the literal classical base derivative commutator. -/
theorem baseCommutator_ae (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) :
    (baseCommutator period r hr w L hL u v : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      transportCommutator period w (velocityMap L ∘ f) g := by
  let b := velocityMap L ∘ f
  have hb := EulerVectorCylinder.postcomp_smooth period (velocityMap L) f hf
  have ht := transport_ae_velocityMap period (by norm_num : 6 ≤ 6) L hL u v f g hu hv hg
  have hfirst := wordAtLevel_ae period 0 r w (by omega : r+0 ≤ 6)
    (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v) (transportField period 3 b g) ht
    (transportField_smooth period b g hb hg)
  have hw := wordAtLevel_ae period 1 r w (by omega : r+1 ≤ 7) v g hv hg
  have hsecond := transportL2Bilinear_ae period (by norm_num : 3 ≤ 7) L u
    (wordAtLevel period 1 r w (by omega) v) f (iteratedFieldDerivative period w g) hu hw
    (iteratedFieldDerivative_smooth period w g hg)
  rw [baseCommutator_apply]
  filter_upwards [Lp.coeFn_sub
    (value period (wordAtLevel period 0 r w (by
        omega) (transportBilinear period (by norm_num : 6 ≤ 6) L hL u v)))
    (transportL2Bilinear period (by
        norm_num : 3 ≤ 7) L u (wordAtLevel period 1 r w (by omega) v)), hfirst,hsecond]
    with x hx h1 h2
  simp only [Pi.sub_apply] at hx
  exact hx.trans (by rw [h1,h2]; rfl)

/-- On actual smooth representatives, the base commutator has the H⁶-only norm bound. -/
theorem baseCommutator_smooth_bound (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a f) 2 (liftMeasure
        period))
    (hgL : ∀ j, ∀ a : Fin j → Fin 4, MemLp (iteratedFieldDerivative period a g) 2 (liftMeasure
        period)) :
    ‖baseCommutator period r hr w L hL u v‖ ≤ baseTransportConstant period *
      sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) u) *
        sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) v) := by
  have heq : ‖baseCommutator period r hr w L hL u v‖ =
      (eLpNorm (transportCommutator period w (velocityMap L ∘ f) g) 2 (liftMeasure period)).toReal
          := by
    simpa only [Lp.norm_def] using congrArg ENNReal.toReal
      (eLpNorm_congr_ae (p := (2 : ℝ≥0∞)) (baseCommutator_ae period r hr w L hL u v f g hu hv hf
          hg))
  have h := (transport_base_L2 period hr w L hL f g hf hg hfL hgL).2
  rw [heq]
  conv_rhs => rw [sumNorm_eq_classical period (restrictOperator period (by
      norm_num : 6 ≤ 7) u) f hu hf,
    sumNorm_eq_classical period (restrictOperator period (by norm_num : 6 ≤ 7) v) g hv hg]
  exact h

/-- The genuine finite-Sobolev base commutator satisfies the same H⁶-only estimate, with no
smoothness hypothesis. -/
theorem baseCommutator_bound (r : ℕ) (hr : r ≤ 6) (w : Fin r → Fin 4)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period 7) :
    ‖baseCommutator period r hr w L hL u v‖ ≤ baseTransportConstant period *
      sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) u) *
        sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) v) := by
  have hS : Continuous (fun u : SobolevSpace period 7 => sumNorm period (restrictOperator period (by
      norm_num : 6 ≤ 7) u)) :=
    (continuous_sumNorm period 6).comp (restrictOperator period (by norm_num : 6 ≤ 7)).continuous
  exact binary_le_of_smooth period
    (fun p => ‖baseCommutator period r hr w L hL p.1 p.2‖)
    (fun p => baseTransportConstant period * sumNorm period (restrictOperator period (by
        norm_num : 6 ≤ 7) p.1) *
      sumNorm period (restrictOperator period (by norm_num : 6 ≤ 7) p.2))
    (baseCommutator period r hr w L hL).continuous₂.norm
    (((hS.comp continuous_fst).const_mul (baseTransportConstant period)).mul (hS.comp
        continuous_snd))
    (fun a b f g ha hb hf hg hfL hgL => baseCommutator_smooth_bound period r hr w L hL a b f g ha
        hb hf hg hfL hgL) u v

end EulerSobolevBaseCommutator
