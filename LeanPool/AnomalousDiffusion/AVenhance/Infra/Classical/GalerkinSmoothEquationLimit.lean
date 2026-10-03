/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus

/-! Continuous `L²` tests for the transport part of the limiting Fourier ODE. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Torus

local instance classicalEquationLimitOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalEquationLimitMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalEquationLimitAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalEquationLimitProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothEquationLimit.classicalEquationLimitDriftSlice_contDiff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) := by
  have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hs := hjoint.comp hpair
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x))
  exact hs.of_le (by simp)

/-- The complex `L²` test against which one component of the Galerkin gradient is paired in a
Fourier coefficient of the transport term. -/
noncomputable def classicalGalerkinTransportFourierTest
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (j : Fin 2) (t : ℝ) : ComplexScalarTorusL2 := by
  let f : Vec 2 → ℂ := fun x => AVenhance.Infra.Torus.torusCharacter k x *
    (AVenhance.streamVel φ t x j : ℂ)
  have hf : Continuous f := by
    apply (AVenhance.Infra.Torus.torusCharacter_contDiff k).continuous.mul
    exact Complex.ofRealCLM.continuous.comp
      ((contDiff_pi.1 (GalerkinSmoothEquationLimit.classicalEquationLimitDriftSlice_contDiff φ hφ
          t) j).continuous)
  exact AVenhance.Infra.Torus.periodicToTorusL2 f hf

/-- The transport test is the torus `L²` class of its explicit periodic representative. -/
theorem classicalGalerkinTransportFourierTest_eq_periodicL2
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (j : Fin 2) (t : ℝ) :
    classicalGalerkinTransportFourierTest φ hφ k j t =
      AVenhance.Infra.Torus.periodicToTorusL2
        (fun x : Vec 2 => AVenhance.Infra.Torus.torusCharacter k x *
          (AVenhance.streamVel φ t x j : ℂ)) (by
            apply (AVenhance.Infra.Torus.torusCharacter_contDiff k).continuous.mul
            exact Complex.ofRealCLM.continuous.comp
              ((contDiff_pi.1
                (GalerkinSmoothEquationLimit.classicalEquationLimitDriftSlice_contDiff φ hφ t)
                    j).continuous)) := by
  rfl

/-- A uniform bound for the transport test follows from the global velocity bound and unit
modulus of the torus character. -/
theorem classicalGalerkinTransportFourierTest_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (j : Fin 2) (t B : ℝ)
    (hB : 0 ≤ B)
    (hb : ∀ s x, ‖AVenhance.streamVel φ s x‖ ≤ B) :
    ‖classicalGalerkinTransportFourierTest φ hφ k j t‖ ≤ B := by
  let f : Vec 2 → ℂ := fun x => AVenhance.Infra.Torus.torusCharacter k x *
    (AVenhance.streamVel φ t x j : ℂ)
  have hf : Continuous f := by
    apply (AVenhance.Infra.Torus.torusCharacter_contDiff k).continuous.mul
    exact Complex.ofRealCLM.continuous.comp
      ((contDiff_pi.1 (GalerkinSmoothEquationLimit.classicalEquationLimitDriftSlice_contDiff φ hφ
          t) j).continuous)
  let fT : C(Torus, ℂ) :=
    ⟨AVenhance.Infra.Torus.periodicToTorus f,
      AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
        hf
        (by
          apply (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2
          intro z x
          simp only [f]
          have hshift : AVenhance.latticeShift z =
              AVenhance.Infra.Torus.intVector z := rfl
          rw [hshift]
          have hchar : AVenhance.Infra.Torus.torusCharacter k
              (x + AVenhance.Infra.Torus.intVector z) =
              AVenhance.Infra.Torus.torusCharacter k x :=
            AVenhance.Infra.Torus.torusCharacter_periodic k z x
          have hbper := (streamVel_smoothPeriodic φ hφ).periodic 0 z t x
          have hbper' : AVenhance.streamVel φ t
              (x + AVenhance.Infra.Torus.intVector z) j =
              AVenhance.streamVel φ t x j := by
            have hv : AVenhance.streamVel φ t
                (x + AVenhance.latticeShift z) = AVenhance.streamVel φ t x := by
              simpa [AVenhance.Infra.Flow.jointLatticeShift,
                AVenhance.latticeShift] using hbper
            simpa [hshift] using congrArg (fun v : Vec 2 => v j) hv
          calc
            _ = AVenhance.Infra.Torus.torusCharacter k x *
                (AVenhance.streamVel φ t (x + AVenhance.Infra.Torus.intVector z) j : ℂ) := by
                  rw [hchar]
            _ = _ := by rw [hbper'])⟩
  have htest : classicalGalerkinTransportFourierTest φ hφ k j t =
      ContinuousMap.toLp 2 (volume : Measure Torus) ℂ fT := by
    change AVenhance.Infra.Torus.periodicToTorusL2 f hf = _
    apply Lp.ext
    filter_upwards [
      (AVenhance.Infra.Torus.memLp_periodicToTorus hf).coeFn_toLp,
      ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℂ) fT] with x hleft hright
    calc
      _ = AVenhance.Infra.Torus.periodicToTorus f x := hleft
      _ = fT x := rfl
      _ = _ := hright.symm
  rw [htest]
  let embed : C(Torus, ℂ) →L[ℂ] ComplexScalarTorusL2 :=
    ContinuousMap.toLp 2 (volume : Measure Torus) ℂ
  change ‖embed fT‖ ≤ B
  have hfB : ‖fT‖ ≤ B := by
    apply (ContinuousMap.norm_le fT hB).2
    intro x
    change ‖AVenhance.Infra.Torus.periodicToTorus f x‖ ≤ B
    change ‖f (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)‖ ≤ B
    rw [norm_mul]
    have hchar : ‖AVenhance.Infra.Torus.torusCharacter k
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)‖ = 1 := by
      simp only [AVenhance.Infra.Torus.torusCharacter,
        UnitAddTorus.mFourier,
        ContinuousMap.coe_mk,
        AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative,
        norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]
    have hbcomp : ‖(AVenhance.streamVel φ t
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) j : ℂ)‖ ≤ B := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (norm_le_pi_norm
        (AVenhance.streamVel φ t
          (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)) j).trans (hb t _)
    rw [hchar, one_mul]
    exact hbcomp
  calc
    ‖embed fT‖ ≤ ‖embed‖ * ‖fT‖ := embed.le_opNorm fT
    _ ≤ B := by
      have hop : ‖embed‖ ≤ 1 := by
        have h := ContinuousMap.toLp_norm_le (p := (2 : ENNReal))
          (μ := (volume : Measure Torus)) (𝕜 := ℂ) (E := ℂ)
        simpa [measureUnivNNReal] using h
      calc
        _ ≤ 1 * ‖fT‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
        _ ≤ 1 * B := mul_le_mul_of_nonneg_left hfB zero_le_one
        _ = B := one_mul B

/-- Pairing a real `L²` path with the smooth transport test is bounded by the velocity bound. -/
theorem classicalGalerkinTransportFourierPairing_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (j : Fin 2) (t B : ℝ)
    (hB : 0 ≤ B)
    (hb : ∀ s x, ‖AVenhance.streamVel φ s x‖ ≤ B)
    (u : ScalarTorusL2) :
    ‖inner ℂ (classicalRealToComplexTorusCLM u)
      (classicalGalerkinTransportFourierTest φ hφ k j t)‖ ≤ B * ‖u‖ := by
  calc
    _ ≤ ‖classicalRealToComplexTorusCLM u‖ *
        ‖classicalGalerkinTransportFourierTest φ hφ k j t‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * B := by
      exact mul_le_mul
        (classicalRealToComplexTorusCLM_norm_le u)
        (classicalGalerkinTransportFourierTest_norm_le φ hφ k j t B hB hb)
        (norm_nonneg _) (norm_nonneg _)
    _ = B * ‖u‖ := by ring

end AVenhance.Infra.Classical

end
