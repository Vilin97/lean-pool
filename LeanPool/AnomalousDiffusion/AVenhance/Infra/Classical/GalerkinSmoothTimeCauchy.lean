/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTimeDerivativeLaplacian
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Uniform Cauchy convergence of the time derivatives of finite Fourier modes. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Torus

local instance classicalTimeCauchyOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalTimeCauchyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalTimeCauchyAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalTimeCauchyProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalTimeCauchyTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothTimeCauchy.classicalTimeCauchyTransport_contDiff
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.1 hb) j).mul
    ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

theorem GalerkinSmoothTimeCauchy.classicalTimeCauchyTransport_periodic
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : AVenhance.IsZ2Periodic b) (hu : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (classicalTransport b u) := by
  intro z x
  simp only [classicalTransport, Homogenization.vecDot]
  apply Finset.sum_congr rfl
  intro j hj
  have hbj := congrFun (hb z x) j
  have hgrad := AVenhance.Infra.Classical.periodic_spaceGrad_component hu j z x
  calc
    _ = b x j * AVenhance.spaceGrad u (x + AVenhance.latticeShift z) j :=
      congrArg (fun v : ℝ => v * AVenhance.spaceGrad u
        (x + AVenhance.latticeShift z) j) hbj
    _ = b x j * AVenhance.spaceGrad u x j :=
      congrArg (fun v : ℝ => b x j * v) hgrad

theorem GalerkinSmoothTimeCauchy.classicalTimeCauchySpaceLap_contDiff
    (u : Vec 2 → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap u) := by
  unfold AVenhance.spaceLap
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2,
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y j) x j)
  apply ContDiff.sum
  intro j hj
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => AVenhance.spaceGrad u y j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ u y (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ (fun y => AVenhance.spaceGrad u y j) x
      (Homogenization.basisVec j))
  exact (hgrad.fderiv_right (by simp)).clm_apply contDiff_const

theorem GalerkinSmoothTimeCauchy.classicalTimeCauchySpaceLap_periodic
    (u : Vec 2 → ℝ) (hu : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (AVenhance.spaceLap u) := by
  intro z x
  simp only [AVenhance.spaceLap]
  apply Finset.sum_congr rfl
  intro j hj
  exact AVenhance.Infra.Classical.periodic_spaceGrad_component
    (AVenhance.Infra.Classical.periodic_spaceGrad_component hu j) j z x

theorem classicalGalerkinFiniteFourierDerivativePath_eq_spatialRhs_closed
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) (k : Fin 2 → ℤ) (hk : frequencyPair k ∈ symmetricFrequencyBox N)
    (t : Icc (0 : ℝ) 1) :
    classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k t =
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 =>
            F t y + (κ * AVenhance.spaceLap
              (realFourierModeAmbientExpansion N
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)) y -
              classicalTransport (AVenhance.streamVel φ t)
                (realFourierModeAmbientExpansion N
                  (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)) y))
            x : ℝ) : ℂ)) k := by
  let c := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t
  let u := realFourierModeAmbientExpansion N c
  let b := AVenhance.streamVel φ t
  let rhs : Vec 2 → ℝ := fun y => F t y +
    (κ * AVenhance.spaceLap u y - classicalTransport b u y)
  have htime : 0 ≤ (t : ℝ) := t.property.1
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u, c] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u, c] using realFourierModeAmbientExpansion_periodic N c
  have hbSmooth : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((t : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    have hsection := hjoint.comp hpair
    simpa [b, Function.uncurry, Function.comp_def] using hsection
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z t x
  have hFslice : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF htime
  have hFperiodic : AVenhance.IsZ2Periodic (F t) := hFper t htime
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap u) :=
    GalerkinSmoothTimeCauchy.classicalTimeCauchySpaceLap_contDiff u hu
  have hlapPeriodic : AVenhance.IsZ2Periodic (AVenhance.spaceLap u) :=
    GalerkinSmoothTimeCauchy.classicalTimeCauchySpaceLap_periodic u hup
  have htransportSmooth : ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) :=
    GalerkinSmoothTimeCauchy.classicalTimeCauchyTransport_contDiff b u hbSmooth hu
  have htransportPeriodic : AVenhance.IsZ2Periodic (classicalTransport b u) :=
    GalerkinSmoothTimeCauchy.classicalTimeCauchyTransport_periodic b u hbper hup
  have hrhsSmooth : ContDiff ℝ (⊤ : ℕ∞) rhs := by
    exact hFslice.add ((contDiff_const.mul hlapSmooth).sub htransportSmooth)
  have hrhsPeriodic : AVenhance.IsZ2Periodic rhs := by
    intro z x
    change F t (x + AVenhance.latticeShift z) +
        (κ * AVenhance.spaceLap u (x + AVenhance.latticeShift z) -
          classicalTransport b u (x + AVenhance.latticeShift z)) = _
    rw [hFperiodic z x, hlapPeriodic z x, htransportPeriodic z x]
  have hrhsMem := memLp_periodicToTorus_real hrhsSmooth.continuous hrhsPeriodic
  have hrhsInt : Integrable (AVenhance.Infra.Torus.periodicToTorus rhs)
      (volume : Measure Torus) := hrhsMem.integrable (by norm_num)
  have hprojected := classicalGalerkinCoefficient_rhs_eq_projectedGenerator
    φ hφ κ hκ F hF hFper θ₀ hθ₀ N t t.property c
  have hforce : (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).forcing t =
      classicalForcingCoefficients N F t := rfl
  rw [hforce] at hprojected
  change classicalComplexFourierCoeffCLM k
      (realFourierScalarMap N
        ((classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t) +
          classicalForcingCoefficients N F t)) = _
  rw [show (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
          (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t) +
        classicalForcingCoefficients N F t =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus rhs) by
    simpa [c, rhs, u, b, classicalTransport] using hprojected]
  exact classicalComplexFourierCoeffCLM_projection N hrhsInt k hk

theorem classicalGalerkinFiniteFourierDerivativePath_eq_spatialRhs_decomp
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) (k : Fin 2 → ℤ) (hk : frequencyPair k ∈ symmetricFrequencyBox N)
    (t : Icc (0 : ℝ) 1) :
    classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k t =
      (κ : ℂ) * UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.spaceLap (realFourierModeAmbientExpansion N
              (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
              x : ℝ) : ℂ)) k -
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (classicalTransport (AVenhance.streamVel φ t)
              (realFourierModeAmbientExpansion N
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
              x : ℝ) : ℂ)) k +
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus (F t) x : ℝ) : ℂ)) k := by
  let u := realFourierModeAmbientExpansion N
    (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)
  let b := AVenhance.streamVel φ t
  let lap := AVenhance.spaceLap u
  let tr := classicalTransport b u
  let ft := F t
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)
  have hbSmooth : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((t : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    have hsection := hjoint.comp hpair
    simpa [b, Function.uncurry, Function.comp_def] using hsection
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z t x
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) lap := by
    simpa [lap] using GalerkinSmoothTimeCauchy.classicalTimeCauchySpaceLap_contDiff u hu
  have hlapPer : AVenhance.IsZ2Periodic lap := by
    simpa [lap] using GalerkinSmoothTimeCauchy.classicalTimeCauchySpaceLap_periodic u hup
  have htrSmooth : ContDiff ℝ (⊤ : ℕ∞) tr := by
    simpa [tr, b] using GalerkinSmoothTimeCauchy.classicalTimeCauchyTransport_contDiff b u
        hbSmooth hu
  have htrPer : AVenhance.IsZ2Periodic tr := by
    simpa [tr, b] using GalerkinSmoothTimeCauchy.classicalTimeCauchyTransport_periodic b u hbper hup
  have hftSmooth : ContDiff ℝ (⊤ : ℕ∞) ft :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF t.property.1
  have hftPer : AVenhance.IsZ2Periodic ft := by simpa [ft] using hFper t t.property.1
  have hqSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => κ * lap x - tr x) :=
    (contDiff_const.mul hlapSmooth).sub htrSmooth
  have hqPer : AVenhance.IsZ2Periodic (fun x => κ * lap x - tr x) := by
    intro z x
    change κ * lap (x + AVenhance.latticeShift z) -
        tr (x + AVenhance.latticeShift z) = κ * lap x - tr x
    rw [hlapPer z x, htrPer z x]
  have hmul := classicalRealPeriodicFourierCoeff_const_mul κ lap k
  have hscaledPer : AVenhance.IsZ2Periodic (fun x => κ * lap x) := by
    intro z x
    change κ * lap (x + AVenhance.latticeShift z) = κ * lap x
    rw [hlapPer z x]
  have hsub := classicalRealPeriodicFourierCoeff_sub (fun x => κ * lap x) tr
    ((contDiff_const.mul hlapSmooth).continuous) htrSmooth.continuous
    hscaledPer htrPer k
  have hadd := classicalRealPeriodicFourierCoeff_add ft (fun x => κ * lap x - tr x)
    hftSmooth.continuous hqSmooth.continuous hftPer hqPer k
  have hclosed := classicalGalerkinFiniteFourierDerivativePath_eq_spatialRhs_closed
    φ hφ κ hκ F hF hFper θ₀ hθ₀ N k hk t
  calc
    _ = UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y => ft y + (κ * lap y - tr y)) x : ℝ) : ℂ)) k := by
      simpa [u, b, lap, tr, ft] using hclosed
    _ = UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus ft x : ℝ) : ℂ)) k +
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (fun y => κ * lap y - tr y) x : ℝ) : ℂ)) k := hadd
    _ = _ := by
      rw [hsub, hmul]
      ring

private theorem classicalGalerkinFiniteFourierDerivativePath_cauchy_point1 :
  ∀ (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) (Ici 0 ×ˢ univ)),
    (∀ (t : ℝ), 0 ≤ t → IsZ2Periodic (F t)) →
      ∀ (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (k : Fin 2 → ℤ) (B : ℝ),
        0 ≤ B →
          (∀ (s : ℝ) (x : Vec 2), ‖streamVel φ s x‖ ≤ B) →
            ∀ ε > 0,
              let δ : ℝ := ε / (4 * (κ + B + 1));
              ∀ (m n : ℕ),
                frequencyPair k ∈ symmetricFrequencyBox m →
                  frequencyPair k ∈ symmetricFrequencyBox n →
                    (∀ (w : List (Fin 2)),
                        (∀ (t : ↑(Icc 0 1)),
                            dist ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w m) t)
                                ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w n) t) <
                              δ) →
                          ∀ (t : ↑(Icc 0 1)),
                            ‖(classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w m) t -
                                  (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w n) t‖ <
                              δ) →
                      (∀ (t : ↑(Icc 0 1)),
                          dist ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0, 0] m) t)
                              ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0, 0] n) t) <
                            δ) →
                        (∀ (t : ↑(Icc 0 1)),
                            dist ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1, 1] m)
                                t)
                                ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1, 1] n)
                                    t) <
                              δ) →
                          (∀ (t : ↑(Icc 0 1)),
                              dist ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0] m) t)
                                  ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0] n)
                                      t) <
                                δ) →
                            (∀ (t : ↑(Icc 0 1)),
                                dist ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1]
                                    m) t)
                                    ((classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1] n)
                                        t) <
                                  δ) →
                              ∀ (t : ↑(Icc 0 1)),
                                ‖(classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀
                                    hθ₀ m k) t -
                                      (classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF
                                          θ₀ hθ₀ n k) t‖ <
                                  ε / 2
    := by
  intro φ hφ κ hκ F hF hFper θ₀ hθ₀ k B hB hvel' ε hε δ m n hfreqM hfreqN hword h00path h11path
      h0path h1path t
  have hdecompM := classicalGalerkinFiniteFourierDerivativePath_eq_spatialRhs_decomp
    φ hφ κ hκ F hF hFper θ₀ hθ₀ m k hfreqM t
  have hdecompN := classicalGalerkinFiniteFourierDerivativePath_eq_spatialRhs_decomp
    φ hφ κ hκ F hF hFper θ₀ hθ₀ n k hfreqN t
  let cM := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ m t
  let cN := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ n t
  let lapM := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.spaceLap (realFourierModeAmbientExpansion m cM)) x : ℝ) : ℂ)) k
  let lapN := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.spaceLap (realFourierModeAmbientExpansion n cN)) x : ℝ) : ℂ)) k
  let trM := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (classicalTransport (AVenhance.streamVel φ t)
        (realFourierModeAmbientExpansion m cM)) x : ℝ) : ℂ)) k
  let trN := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (classicalTransport (AVenhance.streamVel φ t)
        (realFourierModeAmbientExpansion n cN)) x : ℝ) : ℂ)) k
  have hLapM := classicalGalerkinFiniteLaplacian_fourierCoeff_eq_sum m cM k
  have hLapN := classicalGalerkinFiniteLaplacian_fourierCoeff_eq_sum n cN k
  have hLapDiff : ‖lapM - lapN‖ ≤ 2 * δ := by
    rw [show lapM = ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
        (realFourierScalarMap m (realFourierWordDerivativeMap m [i, i] cM)) by
          simpa [lapM] using hLapM,
      show lapN = ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
        (realFourierScalarMap n (realFourierWordDerivativeMap n [i, i] cN)) by
          simpa [lapN] using hLapN]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← map_sub]
    calc
      _ ≤ ∑ i : Fin 2, ‖classicalComplexFourierCoeffCLM k
          (realFourierScalarMap m (realFourierWordDerivativeMap m [i, i] cM) -
            realFourierScalarMap n (realFourierWordDerivativeMap n [i, i] cN))‖ := by
        simpa using norm_sum_le (Finset.univ : Finset (Fin 2))
          (fun i => classicalComplexFourierCoeffCLM k
            (realFourierScalarMap m (realFourierWordDerivativeMap m [i, i] cM) -
              realFourierScalarMap n (realFourierWordDerivativeMap n [i, i] cN)))
      _ ≤ ∑ i : Fin 2, ‖realFourierScalarMap m
            (realFourierWordDerivativeMap m [i, i] cM) -
          realFourierScalarMap n (realFourierWordDerivativeMap n [i, i] cN)‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [classicalComplexFourierCoeffCLM_apply]
        exact (classicalComplexFourierCoeff_norm_le _ k).trans
          (classicalRealToComplexTorusCLM_norm_le _)
      _ ≤ ∑ i : Fin 2, δ := by
        apply Finset.sum_le_sum
        intro i hi
        fin_cases i
        · simpa [classicalGalerkinWordScalarPath_apply, cM, cN] using
            le_of_lt (hword [0, 0] h00path t)
        · simpa [classicalGalerkinWordScalarPath_apply, cM, cN] using
            le_of_lt (hword [1, 1] h11path t)
      _ = 2 * δ := by rw [Fin.sum_univ_two]; ring
  have htrDiff : ‖trM - trN‖ ≤ 2 * B * δ := by
    have htransport := classicalGalerkinTransport_fourierCoeff_diff_norm_le
      φ hφ k t B hB hvel' m n cM cN
    have hsum : ∑ j : Fin 2, B * ‖realFourierScalarMap m
        (realFourierWordDerivativeMap m [j] cM) -
        realFourierScalarMap n (realFourierWordDerivativeMap n [j] cN)‖ ≤
        ∑ j : Fin 2, B * δ := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ hB
      fin_cases j
      · simpa [classicalGalerkinWordScalarPath_apply, cM, cN] using
          le_of_lt (hword [0] h0path t)
      · simpa [classicalGalerkinWordScalarPath_apply, cM, cN] using
          le_of_lt (hword [1] h1path t)
    have hsum' : (∑ j : Fin 2, B * δ) = 2 * B * δ := by
      rw [Fin.sum_univ_two]
      ring
    change ‖UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
            (AVenhance.spaceGrad (realFourierModeAmbientExpansion m cM) y))
            x : ℝ) : ℂ)) k -
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
            (AVenhance.spaceGrad (realFourierModeAmbientExpansion n cN) y))
            x : ℝ) : ℂ)) k‖ ≤ 2 * B * δ
    calc
      _ ≤ ∑ j : Fin 2, B * ‖realFourierScalarMap m
          (realFourierWordDerivativeMap m [j] cM) -
          realFourierScalarMap n (realFourierWordDerivativeMap n [j] cN)‖ := by
        exact htransport
      _ ≤ ∑ j : Fin 2, B * δ := hsum
      _ = 2 * B * δ := hsum'
  have hcombine :
      ‖(κ : ℂ) * lapM - trM - ((κ : ℂ) * lapN - trN)‖ ≤
        2 * κ * δ + 2 * B * δ := by
    calc
      _ = ‖(κ : ℂ) * (lapM - lapN) - (trM - trN)‖ := by congr 1; ring
      _ ≤ ‖(κ : ℂ) * (lapM - lapN)‖ + ‖trM - trN‖ := norm_sub_le _ _
      _ = κ * ‖lapM - lapN‖ + ‖trM - trN‖ := by
        simp [Complex.norm_real, abs_of_pos hκ]
      _ ≤ κ * (2 * δ) + 2 * B * δ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hLapDiff (le_of_lt hκ)) htrDiff
      _ = 2 * κ * δ + 2 * B * δ := by ring
  have hreduce :
      classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ m k t -
        classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ n k t =
        (κ : ℂ) * lapM - trM - ((κ : ℂ) * lapN - trN) := by
    rw [hdecompM, hdecompN]
    simp only [lapM, lapN, trM, trN]
    ring
  have hratio : (κ + B) / (κ + B + 1) < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith
  calc
    _ = ‖(κ : ℂ) * lapM - trM - ((κ : ℂ) * lapN - trN)‖ := by rw [hreduce]
    _ ≤ 2 * κ * δ + 2 * B * δ := hcombine
    _ = (ε / 2) * ((κ + B) / (κ + B + 1)) := by
      dsimp [δ]
      field_simp; ring
    _ < ε / 2 := by
      exact (mul_lt_mul_of_pos_left hratio (by linarith)).trans_eq (by ring)

theorem classicalGalerkinFiniteFourierDerivativePath_cauchy
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ) :
    CauchySeq (fun N =>
      classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k) := by
  obtain ⟨B, hB, hvel⟩ := streamVel_global_derivative_bound φ hφ 0
  have hvel' : ∀ s x, ‖AVenhance.streamVel φ s x‖ ≤ B := by
    intro s x
    simpa using hvel (s, x)
  obtain ⟨Kfreq, hfreq⟩ := classicalFrequencyPair_mem_symmetricFrequencyBox_eventually k
  have h00 := classicalGalerkinWordScalarPath_cauchy φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [0, 0]
  have h11 := classicalGalerkinWordScalarPath_cauchy φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [1, 1]
  have h0 := classicalGalerkinWordScalarPath_cauchy φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [0]
  have h1 := classicalGalerkinWordScalarPath_cauchy φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [1]
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ : ℝ := ε / (4 * (κ + B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K00, hK00⟩ := (Metric.cauchySeq_iff.mp h00) δ hδ
  obtain ⟨K11, hK11⟩ := (Metric.cauchySeq_iff.mp h11) δ hδ
  obtain ⟨K0, hK0⟩ := (Metric.cauchySeq_iff.mp h0) δ hδ
  obtain ⟨K1, hK1⟩ := (Metric.cauchySeq_iff.mp h1) δ hδ
  let K := max Kfreq (max K00 (max K11 (max K0 K1)))
  have hKfreq : Kfreq ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hK00' : K00 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK11' : K11 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hK0' : K0 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hK1' : K1 ≤ K := by
    dsimp [K]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨K, ?_⟩
  intro m hm n hn
  have hfreqM := hfreq m (le_trans hKfreq hm)
  have hfreqN := hfreq n (le_trans hKfreq hn)
  have h00m := hK00 m (le_trans hK00' hm) n (le_trans hK00' hn)
  have h11m := hK11 m (le_trans hK11' hm) n (le_trans hK11' hn)
  have h0m := hK0 m (le_trans hK0' hm) n (le_trans hK0' hn)
  have h1m := hK1 m (le_trans hK1' hm) n (le_trans hK1' hn)
  have hword (w : List (Fin 2)) (hpath : ∀ t : Icc (0 : ℝ) 1,
        dist (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w m t)
            (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w n t) < δ) :
      ∀ t : Icc (0 : ℝ) 1,
        ‖classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w m t -
          classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w n t‖ < δ := by
    intro t
    rw [← dist_eq_norm]
    exact hpath t
  have h00path : ∀ t : Icc (0 : ℝ) 1,
      dist (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0, 0] m t)
          (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0, 0] n t) < δ := by
    intro t
    exact (ContinuousMap.dist_apply_le_dist
      (f := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0, 0] m)
      (g := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0, 0] n) t).trans_lt h00m
  have h11path : ∀ t : Icc (0 : ℝ) 1,
      dist (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1, 1] m t)
          (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1, 1] n t) < δ := by
    intro t
    exact (ContinuousMap.dist_apply_le_dist
      (f := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1, 1] m)
      (g := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1, 1] n) t).trans_lt h11m
  have h0path : ∀ t : Icc (0 : ℝ) 1,
      dist (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0] m t)
          (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0] n t) < δ := by
    intro t
    exact (ContinuousMap.dist_apply_le_dist
      (f := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0] m)
      (g := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [0] n) t).trans_lt h0m
  have h1path : ∀ t : Icc (0 : ℝ) 1,
      dist (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1] m t)
          (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1] n t) < δ := by
    intro t
    exact (ContinuousMap.dist_apply_le_dist
      (f := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1] m)
      (g := classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [1] n) t).trans_lt h1m
  have hpoint (t : Icc (0 : ℝ) 1) :
      ‖classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ m k t -
        classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ n k t‖ < ε / 2 := by
    apply classicalGalerkinFiniteFourierDerivativePath_cauchy_point1
    all_goals assumption
  have hsup : dist
      (classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ m k)
      (classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ n k) ≤ ε / 2 := by
    rw [ContinuousMap.dist_le (by linarith)]
    intro t
    rw [dist_eq_norm]
    exact (hpoint t).le
  exact hsup.trans_lt (by linarith)

/-- Limit of the time derivatives of the finite Fourier Galerkin paths. -/
noncomputable def classicalGalerkinFiniteFourierDerivativePathLimit
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ) :
    C(Icc (0 : ℝ) 1, ℂ) :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (classicalGalerkinFiniteFourierDerivativePath_cauchy
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k))

theorem classicalGalerkinFiniteFourierDerivativePathLimit_tendsto
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ) :
    Tendsto (fun N =>
      classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k)
      atTop (𝓝 (classicalGalerkinFiniteFourierDerivativePathLimit
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (classicalGalerkinFiniteFourierDerivativePath_cauchy
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k))

/-- Clamp a real time to the closed unit time interval. -/
def classicalTimeCauchyClamp (s : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 s), le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩

theorem classicalTimeCauchyClamp_eq_of_mem {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    classicalTimeCauchyClamp s = ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩ := by
  apply Subtype.ext
  simp [classicalTimeCauchyClamp, max_eq_right (le_of_lt hs.1),
    min_eq_right (le_of_lt hs.2)]

/-- The limiting Fourier coefficient is differentiable on the interior slab; its derivative is the
uniform limit of the finite Galerkin coefficient derivatives. -/
theorem classicalGalerkinLimitFourierCoeffPath_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k (classicalTimeCauchyClamp s))
      (classicalGalerkinFiniteFourierDerivativePathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k (classicalTimeCauchyClamp t)) t := by
  let f : ℕ → ℝ → ℂ := fun N s => classicalComplexFourierCoeffCLM k
    (realFourierScalarMap N (AVenhance.Infra.ODE.extendCurve (by norm_num)
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) s))
  let f' : ℕ → ℝ → ℂ := fun N s =>
    classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k
      (classicalTimeCauchyClamp s)
  let g : ℝ → ℂ := fun s => classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per k (classicalTimeCauchyClamp s)
  let g' : ℝ → ℂ := fun s => classicalGalerkinFiniteFourierDerivativePathLimit
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k (classicalTimeCauchyClamp s)
  have hDlimit := classicalGalerkinFiniteFourierDerivativePathLimit_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k
  have hDuniform : TendstoUniformly f' g' atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h := (Metric.tendstoUniformly_iff.mp
      (ContinuousMap.tendsto_iff_tendstoUniformly.mp hDlimit)) ε hε
    filter_upwards [h] with N hN
    intro s
    exact hN (classicalTimeCauchyClamp s)
  have hDuniformOn : TendstoUniformlyOn f' g' atTop (Ioo (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := (Metric.tendstoUniformly_iff.mp hDuniform) ε hε
    filter_upwards [h] with N hN
    intro s hs
    exact hN s
  have hfderiv : ∀ᶠ N : ℕ in atTop, ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (f N) (f' N s) s := by
    filter_upwards with N s hs
    have hfinite := classicalGalerkinFiniteFourierCoeffPath_hasDerivAt
      φ hφ κ hκ F hF θ₀ hθ₀ N k hs
    have hclamp := classicalTimeCauchyClamp_eq_of_mem hs
    simpa [f, f', hclamp] using hfinite
  have hfTendsto : ∀ s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
      Tendsto (fun N => f N s) atTop (𝓝 (g s)) := by
    intro s hs
    let ts : Icc (0 : ℝ) 1 := ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
    have hclamp := classicalTimeCauchyClamp_eq_of_mem hs
    have hfinite (N : ℕ) : f N s = classicalComplexFourierCoeffCLM k
        (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [] N ts) := by
      have hext := AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num)
        (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N)
        ts.property
      simp [f, ts, hext, classicalGalerkinWordScalarPath_apply,
        realFourierWordDerivativeMap]
    have hpath := classicalGalerkinWordFourierCoeff_eval_tendsto
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [] k ts
    simpa [g, ts, hclamp, hfinite, classicalGalerkinLimitFourierCoeffPath,
      classicalGalerkinWordLimitFourierCoeffPath] using hpath
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hDuniformOn hfderiv
    hfTendsto ht

end AVenhance.Infra.Classical

end
