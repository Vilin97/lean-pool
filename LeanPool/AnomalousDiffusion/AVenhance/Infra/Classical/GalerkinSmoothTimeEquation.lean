/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTimeCauchy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothInitialPointwise
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus

/-! Fourier coefficients of the smooth Galerkin representative and its time derivative. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Torus

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalTimeEquationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalTimeEquationMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalTimeEquationProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalTimeEquationTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothTimeEquation.classicalTimeEquation_smoothFourierCoeff_eq_torus
    {f : Vec 2 → ℂ} (hper : AVenhance.Infra.Torus.IsZdPeriodic f)
    (hf : Continuous f) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (⟨AVenhance.Infra.Torus.periodicToTorus f,
          AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic hf hper⟩ :
          C(Torus, ℂ)) k = AVenhance.Infra.Torus.smoothFourierCoeff f k := by
  have hchar (x : Torus) : AVenhance.Infra.Torus.torusCharacter k
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) =
      UnitAddTorus.mFourier (-k) x := by
    simp [AVenhance.Infra.Torus.torusCharacter,
      AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative]
  change (∫ x : Torus,
      UnitAddTorus.mFourier (-k) x • AVenhance.Infra.Torus.periodicToTorus f x) = _
  simp only [smul_eq_mul]
  change (∫ x : Torus,
      UnitAddTorus.mFourier (-k) x * AVenhance.Infra.Torus.periodicToTorus f x) =
    ∫ x in AVenhance.Infra.Torus.unitCell 2,
      AVenhance.Infra.Torus.torusCharacter k x * f x
  rw [← AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell
    (fun y => AVenhance.Infra.Torus.torusCharacter k y * f y)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← hchar x]
  rfl

theorem GalerkinSmoothTimeEquation.classicalTimeEquation_realL2_smoothCoeff
    (f : Vec 2 → ℝ) (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f)
    (k : Fin 2 → ℤ) :
    classicalComplexFourierCoeffCLM k
        ((memLp_periodicToTorus_real hf hper).toLp
          (AVenhance.Infra.Torus.periodicToTorus f)) =
      AVenhance.Infra.Torus.smoothFourierCoeff
        (AVenhance.Infra.Torus.realToComplex f) k := by
  rw [← classicalRealPeriodicFourierCoeff_eq_clm f hf hper k]
  have hperComplex : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex f) := by
    intro z x
    change (f (x + AVenhance.latticeShift z) : ℂ) = (f x : ℂ)
    exact congrArg (fun r : ℝ => (r : ℂ)) (hper z x)
  have htorus := GalerkinSmoothTimeEquation.classicalTimeEquation_smoothFourierCoeff_eq_torus
    hperComplex (Complex.ofRealCLM.continuous.comp hf) k
  have hfun : (fun x : Torus =>
      ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) =
      AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.Infra.Torus.realToComplex f) := by
    funext x
    rfl
  rw [hfun]
  change UnitAddTorus.mFourierCoeff
      (⟨AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.Infra.Torus.realToComplex f),
        AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
          (Complex.ofRealCLM.continuous.comp hf) hperComplex⟩ : C(Torus, ℂ)) k = _
  exact htorus

theorem GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

theorem GalerkinSmoothTimeEquation.classicalTimeEquationSpaceLap_contDiff
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

theorem GalerkinSmoothTimeEquation.classicalTimeEquationSpaceLap_periodic
    (u : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (AVenhance.spaceLap u) := by
  intro z x
  simp only [AVenhance.spaceLap]
  apply Finset.sum_congr rfl
  intro j hj
  exact AVenhance.Infra.Classical.periodic_spaceGrad_component
    (AVenhance.Infra.Classical.periodic_spaceGrad_component hper j) j z x

theorem GalerkinSmoothTimeEquation.classicalTimeEquationTransport_contDiff
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

theorem GalerkinSmoothTimeEquation.classicalTimeEquationTransport_periodic
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

/-- The Fourier coefficient of the continuous smooth representative is the coefficient path
constructed as the strong Galerkin limit. -/
theorem classicalGalerkinFourierContinuousLimit_fourierCoeff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t) k =
      classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k t := by
  let L := classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] t
  have hLp := classicalGalerkinFourierContinuousLimit_toLp
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  calc
    UnitAddTorus.mFourierCoeff
        (classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t) k =
        UnitAddTorus.mFourierCoeff
          (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L) k := by
            rw [UnitAddTorus.mFourierCoeff_toLp]
    _ = UnitAddTorus.mFourierCoeff (classicalRealToComplexTorusCLM U) k := by
      rw [show ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L =
        classicalRealToComplexTorusCLM U by simpa [L, U] using hLp]
    _ = classicalComplexFourierCoeffCLM k U :=
      (classicalComplexFourierCoeffCLM_apply k U).symm
    _ = classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k t := rfl

/-- The Fourier coefficient of the real smooth representative agrees with its Galerkin limit
coefficient, in the unit cell normalization used by the periodic calculus. -/
theorem classicalGalerkinRealSmoothLift_smoothFourierCoeff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    AVenhance.Infra.Torus.smoothFourierCoeff
        (AVenhance.Infra.Torus.realToComplex
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t)) k =
      classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k t := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  let L := classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hcomplex : ∀ x, classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t x = AVenhance.Infra.Torus.realToComplex u x := by
    intro x
    have him := classicalGalerkinSmoothLift_im_eq_zero
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t x
    change classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per t x =
      (classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per t x).re
    apply Complex.ext
    · rfl
    · exact him
  have hperComplex : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex u) := by
    intro z x
    change (u (x + AVenhance.latticeShift z) : ℂ) = (u x : ℂ)
    exact congrArg (fun r : ℝ => (r : ℂ)) (hup z x)
  have htorus :
      (⟨AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.Infra.Torus.realToComplex u),
        AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
          (Complex.ofRealCLM.continuous.comp hu.continuous)
          hperComplex⟩ : C(Torus, ℂ)) = L := by
    ext x
    change AVenhance.Infra.Torus.realToComplex u
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) = L x
    have hrep := classicalGalerkinSmoothLift_eq_continuousLimit
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
      (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
    rw [hcomplex] at hrep
    simpa [L, AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative] using hrep
  have hcoeff := GalerkinSmoothTimeEquation.classicalTimeEquation_smoothFourierCoeff_eq_torus
    hperComplex
    (Complex.ofRealCLM.continuous.comp hu.continuous) k
  calc
    AVenhance.Infra.Torus.smoothFourierCoeff
        (AVenhance.Infra.Torus.realToComplex
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t)) k =
        AVenhance.Infra.Torus.smoothFourierCoeff
          (AVenhance.Infra.Torus.realToComplex u) k := by rfl
    _ = UnitAddTorus.mFourierCoeff
        (⟨AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.Infra.Torus.realToComplex u),
          AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
            (Complex.ofRealCLM.continuous.comp hu.continuous)
            hperComplex⟩ : C(Torus, ℂ)) k := hcoeff.symm
    _ = UnitAddTorus.mFourierCoeff L k := by rw [htorus]
    _ = classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k t :=
      classicalGalerkinFourierContinuousLimit_fourierCoeff
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t k

/-- Each limiting spatial derivative path is the torus `L²` class of that derivative of the
smooth representative. -/
noncomputable def classicalGalerkinRealSmoothDerivativeL2
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) : ScalarTorusL2 :=
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  (memLp_periodicToTorus_real
    (classicalWordDerivative_contDiff w u
      (classicalGalerkinRealSmoothLift_contDiff
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t)).continuous
    (GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic w u
      (classicalGalerkinRealSmoothLift_periodic
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t))).toLp
    (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w u))

theorem classicalGalerkinWordScalarPathLimit_eq_smoothDerivative
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) :
    classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w t) =
      classicalRealToComplexTorusCLM
        (classicalGalerkinRealSmoothDerivativeL2 φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w t) := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hwordCoeff (q : Fin 2 → ℤ) (w : List (Fin 2)) :
      AVenhance.Infra.Torus.smoothFourierCoeff
          (AVenhance.Infra.Torus.realToComplex
            (classicalWordDerivative w u)) q =
        classicalGalerkinWordFourierMultiplier q w *
          AVenhance.Infra.Torus.smoothFourierCoeff
            (AVenhance.Infra.Torus.realToComplex u) q := by
    induction w with
    | nil => simp [classicalGalerkinWordFourierMultiplier, classicalWordDerivative]
    | cons i w ih =>
      have hw : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w u) :=
        classicalWordDerivative_contDiff w u hu
      have hwp : AVenhance.IsZ2Periodic (classicalWordDerivative w u) :=
        GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic w u hup
      have hformula := AVenhance.Infra.Torus.smoothFourierCoeff_spaceGrad
        (hw.of_le (by simp)) hwp i q
      rw [show classicalWordDerivative (i :: w) u =
        fun x => AVenhance.spaceGrad (classicalWordDerivative w u) x i by rfl]
      change AVenhance.Infra.Torus.smoothFourierCoeff
        (fun x => (AVenhance.spaceGrad (classicalWordDerivative w u) x i : ℂ)) q = _
      calc
        _ = (2 * Real.pi * Complex.I * (q i : ℂ)) *
            AVenhance.Infra.Torus.smoothFourierCoeff
              (AVenhance.Infra.Torus.realToComplex
                (classicalWordDerivative w u)) q := hformula
        _ = (2 * Real.pi * Complex.I * (q i : ℂ)) *
            (classicalGalerkinWordFourierMultiplier q w *
              AVenhance.Infra.Torus.smoothFourierCoeff
                (AVenhance.Infra.Torus.realToComplex u) q) := by rw [ih]
        _ = classicalGalerkinWordFourierMultiplier q (i :: w) *
            AVenhance.Infra.Torus.smoothFourierCoeff
              (AVenhance.Infra.Torus.realToComplex u) q := by
          simp [classicalGalerkinWordFourierMultiplier, List.map_cons,
            List.prod_cons, mul_assoc]
  have hcoeff (j : Fin 2 → ℤ) :
      classicalComplexFourierCoeffCLM j
          (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per w t) =
        classicalComplexFourierCoeffCLM j
          ((memLp_periodicToTorus_real
            (classicalWordDerivative_contDiff w u hu).continuous
            (GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic w u hup)).toLp
            (AVenhance.Infra.Torus.periodicToTorus
              (classicalWordDerivative w u))) := by
    have hbase := classicalGalerkinRealSmoothLift_smoothFourierCoeff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t j
    calc
      _ = classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w j t := rfl
      _ = classicalGalerkinWordFourierMultiplier j w *
          classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per j t :=
        classicalGalerkinWordLimitFourierCoeff_word
          φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w j t
      _ = classicalGalerkinWordFourierMultiplier j w *
          AVenhance.Infra.Torus.smoothFourierCoeff
            (AVenhance.Infra.Torus.realToComplex u) j := by rw [hbase]
      _ = AVenhance.Infra.Torus.smoothFourierCoeff
          (AVenhance.Infra.Torus.realToComplex
          (classicalWordDerivative w u)) j := (hwordCoeff j w).symm
      _ = classicalComplexFourierCoeffCLM j
          ((memLp_periodicToTorus_real
            (classicalWordDerivative_contDiff w u hu).continuous
            (GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic w u hup)).toLp
            (AVenhance.Infra.Torus.periodicToTorus
              (classicalWordDerivative w u))) :=
        (GalerkinSmoothTimeEquation.classicalTimeEquation_realL2_smoothCoeff
          (classicalWordDerivative w u)
          (classicalWordDerivative_contDiff w u hu).continuous
          (GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic w u hup) j).symm
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext j
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    ← classicalComplexFourierCoeffCLM_apply,
    ← classicalComplexFourierCoeffCLM_apply]
  exact hcoeff j

/-- The Fourier coefficient of a finite Galerkin transport term is the sum of the pairings of the
finite derivative paths with the smooth transport tests. -/
theorem classicalGalerkinFiniteTransportFourierCoeff_eq_sum
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (N : ℕ) (c : Coefficients (RealFourierDimension N))
    (k : Fin 2 → ℤ) (t : ℝ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot
            (AVenhance.streamVel φ t y)
            (AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) y)) x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] c)))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
  let u := realFourierModeAmbientExpansion N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using (realFourierModeAmbientExpansion_contDiff N c).of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hsum := classicalGalerkinTransport_fourierCoeff_eq_sum_inner
    φ hφ k t u hu hup
  have hsum' : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => Homogenization.vecDot
          (AVenhance.streamVel φ t y)
          (AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) y)) x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] c)))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
    calc
      _ = ∑ j : Fin 2, inner ℂ
          (classicalRealToComplexTorusCLM
            ((memLp_periodicToTorus_real
              ((classicalWordDerivative_contDiff [j] u hu).continuous)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component hup j)).toLp
                (AVenhance.Infra.Torus.periodicToTorus
                  (classicalWordDerivative [j] u))))
          (classicalGalerkinTransportFourierTest φ hφ k j t) := by
        simpa [u] using hsum
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← classicalGalerkinWordScalarMap_eq_periodicL2 N c [j]]
  exact hsum'

/-- The Laplacian coefficient of the smooth limit is the sum of the limiting second derivative
coefficients. -/
theorem classicalGalerkinSmoothLift_laplacianFourierCoeff_eq_sum
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.spaceLap (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t)) x : ℝ) : ℂ)) k =
      ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
        (classicalGalerkinRealSmoothDerivativeL2 φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [i, i] t) := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hlapEq : AVenhance.spaceLap u = fun x =>
      ∑ i : Fin 2, classicalWordDerivative [i, i] u x := by
    funext x
    simp [AVenhance.spaceLap, classicalWordDerivative, Fin.sum_univ_two]
  let d0 := classicalWordDerivative [0, 0] u
  let d1 := classicalWordDerivative [1, 1] u
  have hd0 : ContDiff ℝ (⊤ : ℕ∞) d0 := by
    simpa [d0] using classicalWordDerivative_contDiff [0, 0] u hu
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) d1 := by
    simpa [d1] using classicalWordDerivative_contDiff [1, 1] u hu
  have hdp0 : AVenhance.IsZ2Periodic d0 := by
    simpa [d0] using GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic [0, 0] u hup
  have hdp1 : AVenhance.IsZ2Periodic d1 := by
    simpa [d1] using GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic [1, 1] u hup
  have hsum := classicalRealPeriodicFourierCoeff_add d0 d1
    hd0.continuous hd1.continuous hdp0 hdp1 k
  have h0 := classicalRealPeriodicFourierCoeff_eq_clm d0 hd0.continuous hdp0 k
  have h1 := classicalRealPeriodicFourierCoeff_eq_clm d1 hd1.continuous hdp1 k
  have hrewrite : (fun y : Vec 2 => d0 y + d1 y) = AVenhance.spaceLap u := by
    simpa [d0, d1, Fin.sum_univ_two] using hlapEq.symm
  rw [hrewrite] at hsum
  rw [h0, h1] at hsum
  simpa [d0, d1, classicalGalerkinRealSmoothDerivativeL2,
    classicalWordDerivative] using hsum

/-- The smooth limit's transport coefficient is the sum of its gradient pairings with the
Galerkin transport tests. -/
theorem classicalGalerkinSmoothLift_transportFourierCoeff_eq_sum
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (classicalTransport (AVenhance.streamVel φ (t : ℝ))
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per t)) x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          (classicalGalerkinRealSmoothDerivativeL2 φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [j] t))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hbase := classicalGalerkinTransport_fourierCoeff_eq_sum_inner
    φ hφ k t u hu hup
  change UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => Homogenization.vecDot
          (AVenhance.streamVel φ (t : ℝ) y) (AVenhance.spaceGrad u y))
        x : ℝ) : ℂ)) k = _
  simpa [u, classicalGalerkinRealSmoothDerivativeL2,
    GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic] using hbase

/-- Finite Galerkin transport Fourier coefficients converge uniformly in time to those of the
smooth representative. -/
theorem classicalGalerkinFiniteTransportFourierCoeff_tendsto
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    Tendsto (fun N => UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (classicalTransport (AVenhance.streamVel φ (t : ℝ))
          (realFourierModeAmbientExpansion N
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
          x : ℝ) : ℂ)) k) atTop
      (𝓝 (UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (classicalTransport (AVenhance.streamVel φ (t : ℝ))
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per t)) x : ℝ) : ℂ)) k)) := by
  let term (N : ℕ) (j : Fin 2) : ℂ := inner ℂ
    (classicalRealToComplexTorusCLM
      (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [j] N t))
    (classicalGalerkinTransportFourierTest φ hφ k j t)
  have hterm (j : Fin 2) : Tendsto (fun N => term N j) atTop
      (𝓝 (inner ℂ
        (classicalRealToComplexTorusCLM
          (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [j] t))
        (classicalGalerkinTransportFourierTest φ hφ k j t))) := by
    have hpath := classicalGalerkinWordScalarPathLimit_tendsto
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [j]
    have heval : Tendsto
        (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [j] N t)
        atTop (𝓝 (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [j] t)) := by
      exact ((continuous_eval_const t).tendsto _).comp hpath
    have hinner : Continuous (fun v : ScalarTorusL2 => inner ℂ
        (classicalRealToComplexTorusCLM v)
        (classicalGalerkinTransportFourierTest φ hφ k j t)) := by
      exact continuous_inner.comp
        (classicalRealToComplexTorusCLM.continuous.prodMk continuous_const)
    exact hinner.continuousAt.tendsto.comp heval
  have hsum : Tendsto (fun N => ∑ j : Fin 2, term N j) atTop
      (𝓝 (∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [j] t))
        (classicalGalerkinTransportFourierTest φ hφ k j t))) := by
    simpa only [Fin.sum_univ_two] using (hterm 0).add (hterm 1)
  have hfinite (N : ℕ) :
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (classicalTransport (AVenhance.streamVel φ (t : ℝ))
            (realFourierModeAmbientExpansion N
              (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
          x : ℝ) : ℂ)) k = ∑ j : Fin 2, term N j := by
    have hcoeff := classicalGalerkinFiniteTransportFourierCoeff_eq_sum
      φ hφ N (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t) k t
    change UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot
            (AVenhance.streamVel φ (t : ℝ) y)
            (AVenhance.spaceGrad
              (realFourierModeAmbientExpansion N
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)) y))
          x : ℝ) : ℂ)) k = _
    simpa [term, classicalGalerkinWordScalarPath_apply] using hcoeff
  have hlimit := classicalGalerkinSmoothLift_transportFourierCoeff_eq_sum
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t k
  have hpathLimit : (∑ j : Fin 2, inner ℂ
      (classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [j] t))
      (classicalGalerkinTransportFourierTest φ hφ k j t)) =
    UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (classicalTransport (AVenhance.streamVel φ (t : ℝ))
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t)) x : ℝ) : ℂ)) k := by
    simpa [classicalGalerkinWordScalarPathLimit_eq_smoothDerivative] using hlimit.symm
  have hconv := hsum.congr' (Filter.Eventually.of_forall fun N => (hfinite N).symm)
  rw [hpathLimit] at hconv
  exact hconv

/-- Finite Galerkin Laplacian Fourier coefficients converge to those of the smooth representative.
-/
theorem classicalGalerkinFiniteLaplacianFourierCoeff_tendsto
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    Tendsto (fun N => UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.spaceLap
          (realFourierModeAmbientExpansion N
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
          x : ℝ) : ℂ)) k) atTop
      (𝓝 (UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.spaceLap (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t)) x : ℝ) : ℂ)) k)) := by
  let term (N : ℕ) (i : Fin 2) : ℂ :=
    classicalComplexFourierCoeffCLM k
      (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [i, i] N t)
  have hterm (i : Fin 2) : Tendsto (fun N => term N i) atTop
      (𝓝 (classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per [i, i] k t)) := by
    have hpath := classicalGalerkinWordScalarPathLimit_tendsto
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [i, i]
    have heval : Tendsto
        (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [i, i] N t)
        atTop (𝓝 (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [i, i] t)) := by
      exact ((continuous_eval_const t).tendsto _).comp hpath
    change Tendsto
      (fun N => classicalComplexFourierCoeffCLM k
        (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [i, i] N t))
      atTop
      (𝓝 (classicalComplexFourierCoeffCLM k
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per [i, i] t)))
    exact (classicalComplexFourierCoeffCLM k).continuous.continuousAt.tendsto.comp heval
  have hsum : Tendsto (fun N => ∑ i : Fin 2, term N i) atTop
      (𝓝 (∑ i : Fin 2, classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per [i, i] k t)) := by
    simpa only [Fin.sum_univ_two] using (hterm 0).add (hterm 1)
  have hfinite (N : ℕ) :
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.spaceLap
            (realFourierModeAmbientExpansion N
              (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
          x : ℝ) : ℂ)) k = ∑ i : Fin 2, term N i := by
    have hcoeff := classicalGalerkinFiniteLaplacian_fourierCoeff_eq_sum N
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t) k
    calc
      _ = ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
          (realFourierScalarMap N (realFourierWordDerivativeMap N [i, i]
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t))) := hcoeff
      _ = ∑ i : Fin 2, term N i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [term, classicalGalerkinWordScalarPath_apply]
  have hlimit := classicalGalerkinSmoothLift_laplacianFourierCoeff_eq_sum
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t k
  have hpathLimit : (∑ i : Fin 2,
      classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per [i, i] k t) =
    UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.spaceLap (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t)) x : ℝ) : ℂ)) k := by
    calc
      _ = ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
          (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [i, i] t) := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = ∑ i : Fin 2, classicalComplexFourierCoeffCLM k
          (classicalGalerkinRealSmoothDerivativeL2 φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [i, i] t) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [classicalComplexFourierCoeffCLM_apply,
          classicalComplexFourierCoeffCLM_apply]
        exact congrArg (fun v : ComplexScalarTorusL2 =>
          UnitAddTorus.mFourierCoeff v k)
          (classicalGalerkinWordScalarPathLimit_eq_smoothDerivative
            φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [i, i] t)
      _ = _ := hlimit.symm
  have hconv := hsum.congr' (Filter.Eventually.of_forall fun N => (hfinite N).symm)
  rw [hpathLimit] at hconv
  exact hconv

/-- The limiting time derivative of each Fourier coefficient is the coefficient of the smooth
spatial right-hand side. This is the coefficient-level passage from the Galerkin ODE to the
limiting PDE. -/
theorem classicalGalerkinFiniteFourierDerivativePathLimit_eq_smoothRhsFourierCoeff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    classicalGalerkinFiniteFourierDerivativePathLimit φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per k t =
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => F (t : ℝ) y +
            (κ * AVenhance.spaceLap
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per t) y -
             classicalTransport (AVenhance.streamVel φ (t : ℝ))
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per t) y)) x : ℝ) : ℂ)) k := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  let b := AVenhance.streamVel φ (t : ℝ)
  let lapCoeff (N : ℕ) := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.spaceLap
        (realFourierModeAmbientExpansion N
          (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
      x : ℝ) : ℂ)) k
  let transportCoeff (N : ℕ) := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (classicalTransport b
        (realFourierModeAmbientExpansion N
          (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)))
      x : ℝ) : ℂ)) k
  let forcingCoeff := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus (F (t : ℝ))
      x : ℝ) : ℂ)) k
  let targetCoeff := UnitAddTorus.mFourierCoeff
    (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
      (fun y : Vec 2 => F (t : ℝ) y +
        (κ * AVenhance.spaceLap u y - classicalTransport b u y))
      x : ℝ) : ℂ)) k
  have hlap := classicalGalerkinFiniteLaplacianFourierCoeff_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t k
  have htransport := classicalGalerkinFiniteTransportFourierCoeff_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t k
  have hdecomp : ∀ᶠ N : ℕ in atTop,
      classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k t =
        (κ : ℂ) * lapCoeff N - transportCoeff N + forcingCoeff := by
    obtain ⟨K, hK⟩ := classicalFrequencyPair_mem_symmetricFrequencyBox_eventually k
    filter_upwards [Filter.eventually_atTop.2 ⟨K, hK⟩] with N hN
    simpa [lapCoeff, transportCoeff, forcingCoeff] using
      classicalGalerkinFiniteFourierDerivativePath_eq_spatialRhs_decomp
        φ hφ κ hκ F hF hFper θ₀ hθ₀ N k hN t
  have hcombo : Tendsto (fun N : ℕ =>
      (κ : ℂ) * lapCoeff N - transportCoeff N + forcingCoeff)
      atTop (𝓝 ((κ : ℂ) *
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.spaceLap u) x : ℝ) : ℂ)) k -
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (classicalTransport b u) x : ℝ) : ℂ)) k + forcingCoeff)) := by
    simpa [lapCoeff, transportCoeff, forcingCoeff] using
      ((tendsto_const_nhds.mul hlap).sub htransport).add tendsto_const_nhds
  have hfiniteLimit := hcombo.congr' (hdecomp.mono fun N hN => hN.symm)
  have hderivative' : Tendsto
      (fun N : ℕ => classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀
        N k t) atTop
      (𝓝 (classicalGalerkinFiniteFourierDerivativePathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k t)) := by
    exact ((continuous_eval_const t).tendsto _).comp
        (classicalGalerkinFiniteFourierDerivativePathLimit_tendsto
          φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k)
  have hscalar := tendsto_nhds_unique hderivative' hfiniteLimit
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hbSmooth : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((t : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    simpa [b, Function.uncurry, Function.comp_def] using hjoint.comp hpair
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z x
    change AVenhance.streamVel φ (t : ℝ) (x + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z (t : ℝ) x
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap u) :=
    GalerkinSmoothTimeEquation.classicalTimeEquationSpaceLap_contDiff u hu
  have hlapPer : AVenhance.IsZ2Periodic (AVenhance.spaceLap u) :=
    GalerkinSmoothTimeEquation.classicalTimeEquationSpaceLap_periodic u hup
  have htransportSmooth : ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) :=
    GalerkinSmoothTimeEquation.classicalTimeEquationTransport_contDiff b u hbSmooth hu
  have htransportPer : AVenhance.IsZ2Periodic (classicalTransport b u) :=
    GalerkinSmoothTimeEquation.classicalTimeEquationTransport_periodic b u hbper hup
  have hforceSmooth : ContDiff ℝ (⊤ : ℕ∞) (F (t : ℝ)) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF t.property.1
  have hforcePer : AVenhance.IsZ2Periodic (F (t : ℝ)) := hFper _ t.property.1
  have hscaledPer : AVenhance.IsZ2Periodic (fun x => κ * AVenhance.spaceLap u x) := by
    intro z x
    change κ * AVenhance.spaceLap u (x + AVenhance.latticeShift z) = _
    rw [hlapPer z x]
  have hmul := classicalRealPeriodicFourierCoeff_const_mul κ (AVenhance.spaceLap u) k
  have hsub := classicalRealPeriodicFourierCoeff_sub
    (fun x => κ * AVenhance.spaceLap u x) (classicalTransport b u)
    ((contDiff_const.mul hlapSmooth).continuous) htransportSmooth.continuous
    hscaledPer htransportPer k
  have hadd := classicalRealPeriodicFourierCoeff_add (F (t : ℝ))
    (fun x => κ * AVenhance.spaceLap u x - classicalTransport b u x)
    hforceSmooth.continuous ((contDiff_const.mul hlapSmooth).sub htransportSmooth).continuous
    hforcePer (by
      intro z x
      change κ * AVenhance.spaceLap u (x + AVenhance.latticeShift z) -
        classicalTransport b u (x + AVenhance.latticeShift z) = _
      rw [hlapPer z x, htransportPer z x]) k
  have htarget :
      (κ : ℂ) * UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.spaceLap u) x : ℝ) : ℂ)) k -
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (classicalTransport b u) x : ℝ) : ℂ)) k + forcingCoeff = targetCoeff := by
    dsimp [targetCoeff, forcingCoeff]
    calc
      _ = UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (F (t : ℝ)) x : ℝ) : ℂ)) k +
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (fun y => κ * AVenhance.spaceLap u y - classicalTransport b u y)
            x : ℝ) : ℂ)) k := by
          rw [hsub, hmul]
          ring
      _ = _ := hadd.symm
  simpa [targetCoeff, u, b] using hscalar.trans htarget

/-- Clamp a real time to the interval on which the classical equation is constructed. -/
def GalerkinSmoothTimeEquation.classicalTimeEquationClamp (s : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 s), le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩

theorem GalerkinSmoothTimeEquation.classicalTimeEquationClamp_eq_of_mem {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    GalerkinSmoothTimeEquation.classicalTimeEquationClamp s = ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
        := by
  apply Subtype.ext
  simp [GalerkinSmoothTimeEquation.classicalTimeEquationClamp, max_eq_right (le_of_lt hs.1),
    min_eq_right (le_of_lt hs.2)]

/-- The time clamp agrees with the identity on the open unit interval. -/
theorem classicalGalerkinTimeEquationClamp_eq_of_mem {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    GalerkinSmoothTimeEquation.classicalTimeEquationClamp s = ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩ :=
  GalerkinSmoothTimeEquation.classicalTimeEquationClamp_eq_of_mem hs

/-- On interior times, the Fourier coefficient path of the smooth representative has derivative
equal to the corresponding coefficient of its spatial right-hand side. -/
theorem classicalGalerkinRealSmoothLift_fourierCoeff_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k (GalerkinSmoothTimeEquation.classicalTimeEquationClamp s))
      (UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => F t y +
            (κ * AVenhance.spaceLap
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y -
             classicalTransport (AVenhance.streamVel φ t)
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y))
          x : ℝ) : ℂ)) k) t := by
  have hbase := classicalGalerkinLimitFourierCoeffPath_hasDerivAt
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k ht
  have hlocal :
      (fun s => classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k (GalerkinSmoothTimeEquation.classicalTimeEquationClamp s)) =ᶠ[𝓝 t]
      (fun s => classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k (classicalTimeCauchyClamp s)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [GalerkinSmoothTimeEquation.classicalTimeEquationClamp_eq_of_mem hs,
      classicalTimeCauchyClamp_eq_of_mem hs]
  have htransferred := hbase.congr_of_eventuallyEq hlocal
  have htClamp : GalerkinSmoothTimeEquation.classicalTimeEquationClamp t =
      ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ :=
    GalerkinSmoothTimeEquation.classicalTimeEquationClamp_eq_of_mem ht
  have hvalue := classicalGalerkinFiniteFourierDerivativePathLimit_eq_smoothRhsFourierCoeff
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ k
  have hderivValue :
      classicalGalerkinFiniteFourierDerivativePathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k (GalerkinSmoothTimeEquation.classicalTimeEquationClamp t) =
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => F t y +
            (κ * AVenhance.spaceLap
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y -
             classicalTransport (AVenhance.streamVel φ t)
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y))
          x : ℝ) : ℂ)) k := by
    rw [htClamp]
    exact hvalue
  exact htransferred.congr_deriv hderivValue

theorem GalerkinSmoothTimeEquation.classicalGalerkinWordFourierMultiplier_norm_le
    (k : Fin 2 → ℤ) (w : List (Fin 2)) :
    ‖classicalGalerkinWordFourierMultiplier k w‖ ≤
      (2 * Real.pi * |(k 0 : ℝ)| + 2 * Real.pi * |(k 1 : ℝ)|) ^ w.length := by
  let x : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let y : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  have hxy : 0 ≤ x + y := by positivity
  induction w with
  | nil => simp [classicalGalerkinWordFourierMultiplier]
  | cons i w ih =>
      have hfactor : ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ ≤ x + y := by
        fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Complex.norm_mul,
            Complex.norm_ofNat, Complex.norm_real,
                                                Real.norm_eq_abs, Real.abs_pi, Complex.norm_I,
                                                    mul_one, Complex.norm_intCast,
                                                    le_add_iff_nonneg_right, x, y, Fin.mk_one,
                                                    Fin.isValue, Complex.norm_mul,
                                                    Complex.norm_ofNat, Complex.norm_real,
                                                    Real.norm_eq_abs,
                          Real.abs_pi, Complex.norm_I, mul_one, Complex.norm_intCast,
                              le_add_iff_nonneg_left, x, y] <;> positivity
      calc
        ‖classicalGalerkinWordFourierMultiplier k (i :: w)‖ =
            ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ *
              ‖classicalGalerkinWordFourierMultiplier k w‖ := by
          simp [classicalGalerkinWordFourierMultiplier, List.map_cons, List.prod_cons]
        _ ≤ (x + y) * (x + y) ^ w.length :=
          mul_le_mul hfactor (by simpa [x, y] using ih) (norm_nonneg _) hxy
        _ = (x + y) ^ (w.length + 1) := by rw [pow_succ]; ring
        _ = (2 * Real.pi * |(k 0 : ℝ)| + 2 * Real.pi * |(k 1 : ℝ)|) ^ (i :: w).length := by
          simp [x, y]

/-- A single derivative Fourier mode, continuously parameterized by time and torus position. -/
noncomputable def classicalGalerkinWordFourierJointTerm
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (k : Fin 2 → ℤ) : C(Icc (0 : ℝ) 1 × Torus, ℂ) := by
  let a := classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w k
  exact ⟨fun p => a p.1 * UnitAddTorus.mFourier k p.2,
    (a.continuous.comp continuous_fst).mul
      ((UnitAddTorus.mFourier k).continuous.comp continuous_snd)⟩

theorem GalerkinSmoothTimeEquation.classicalGalerkinWordFourierJointTerm_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (k : Fin 2 → ℤ) :
    ‖classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w k‖ ≤
      classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w.length * classicalScaledTorusFrequencyWeight k := by
  let p := w.length
  let C := classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per p
  let x : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let y : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  have hC : 0 ≤ C := classicalGalerkinFourierCoefficientBound_nonneg
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per p
  have hbound : 0 ≤ C * classicalScaledTorusFrequencyWeight k := by
    dsimp [classicalScaledTorusFrequencyWeight]
    positivity
  apply (ContinuousMap.norm_le
    (f := classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w k) hbound).2
  intro q
  unfold classicalGalerkinWordFourierJointTerm
  change ‖(classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w k q.1) * UnitAddTorus.mFourier k q.2‖ ≤ _
  rw [norm_mul]
  have hmode : ‖UnitAddTorus.mFourier k q.2‖ ≤ 1 := by
    exact (ContinuousMap.norm_coe_le_norm _ _).trans_eq UnitAddTorus.mFourier_norm
  have hcoeff := classicalGalerkinFourierCoefficientBound_spec
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per p k q.1
  have hmult := classicalGalerkinWordLimitFourierCoeff_word
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w k q.1
  have hmultNorm :
      ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k q.1‖ ≤
        (x + y) ^ w.length *
          ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per [] k q.1‖ := by
    rw [hmult, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [x, y] using
          GalerkinSmoothTimeEquation.classicalGalerkinWordFourierMultiplier_norm_le k w)
      (norm_nonneg _)
  have hdecay := classicalWeightedCoeff_frequencyPower_le p x y
    ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per [] k q.1‖ C (by positivity) (by positivity) (norm_nonneg _)
    (by simpa [p, x, y] using hcoeff)
  calc
    _ ≤ ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k q.1‖ := by
      exact mul_le_of_le_one_right (norm_nonneg _) hmode
    _ ≤ _ := by
      calc
        _ ≤ (x + y) ^ w.length *
            ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per [] k q.1‖ := hmultNorm
        _ ≤ C * classicalScaledTorusFrequencyWeight k := by
          calc
            _ = ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per [] k q.1‖ * (x + y) ^ w.length := by ring
            _ ≤ C * classicalScaledTorusFrequencyWeight k := by
              simpa [p, x, y, classicalScaledTorusFrequencyWeight] using hdecay

/-- The ordered spatial derivative Fourier series converges uniformly on the time-space slab. -/
noncomputable def classicalGalerkinWordFourierContinuousPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    C(Icc (0 : ℝ) 1 × Torus, ℂ) :=
  ∑' k : Fin 2 → ℤ, classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w k

theorem GalerkinSmoothTimeEquation.classicalGalerkinWordFourierJointTerm_summable
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    Summable (classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w) := by
  let C := classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w.length
  have hC : 0 ≤ C := classicalGalerkinFourierCoefficientBound_nonneg
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w.length
  have hmajor : Summable (fun k : Fin 2 → ℤ =>
      C * classicalScaledTorusFrequencyWeight k) :=
    classicalScaledTorusFrequencyWeight_summable.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro k
  simpa [C] using GalerkinSmoothTimeEquation.classicalGalerkinWordFourierJointTerm_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w k

theorem GalerkinSmoothTimeEquation.classicalGalerkinWordFourierSeries_toLp
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) :
    ContinuousMap.toLp 2 (volume : Measure Torus) ℂ
      ((classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry t) =
      classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w t) := by
  let g : (Fin 2 → ℤ) → C(Torus, ℂ) := fun k =>
    classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w k t • UnitAddTorus.mFourier k
  have hg : Summable g := by
    let C := classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w.length
    have hC : 0 ≤ C := classicalGalerkinFourierCoefficientBound_nonneg
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w.length
    have hmajor : Summable (fun k : Fin 2 → ℤ =>
        C * classicalScaledTorusFrequencyWeight k) :=
      classicalScaledTorusFrequencyWeight_summable.mul_left C
    have hterm (k : Fin 2 → ℤ) : g k =
        (classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k).curry t := by
      ext x
      simp [g, classicalGalerkinWordFourierJointTerm, smul_eq_mul]
    apply Summable.of_norm_bounded hmajor
    intro k
    have hbound : 0 ≤ C * classicalScaledTorusFrequencyWeight k := by
      dsimp [classicalScaledTorusFrequencyWeight]
      positivity
    apply (ContinuousMap.norm_le (f := g k) hbound).2
    intro x
    rw [hterm]
    calc
      ‖(classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k).curry t x‖ =
          ‖classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per w k (t, x)‖ := rfl
      _ ≤ ‖classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k‖ :=
        ContinuousMap.norm_coe_le_norm _ _
      _ ≤ C * classicalScaledTorusFrequencyWeight k := by
        simpa [C] using GalerkinSmoothTimeEquation.classicalGalerkinWordFourierJointTerm_norm_le
          φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w k
  have hseries : HasSum (fun k : Fin 2 → ℤ =>
      ContinuousMap.toLp 2 (volume : Measure Torus) ℂ (g k))
      (classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w t)) := by
    have hbasis := UnitAddTorus.hasSum_mFourier_series_L2
      (classicalRealToComplexTorusCLM
        (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w t))
    simpa [g, classicalGalerkinWordLimitFourierCoeffPath,
      classicalComplexFourierCoeffCLM_apply, UnitAddTorus.mFourierLp] using hbasis
  have hterms := GalerkinSmoothTimeEquation.classicalGalerkinWordFourierJointTerm_summable
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
  have hsum : (∑' k, g k) =
      (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry t := by
    have hterm (k : Fin 2 → ℤ) : g k =
        (classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k).curry t := by
      ext x
      simp [g, classicalGalerkinWordFourierJointTerm, smul_eq_mul]
    ext x
    calc
      (∑' k, g k) x = ∑' k, g k x := (ContinuousMap.tsum_apply hg x).symm
      _ = ∑' k, classicalGalerkinWordFourierJointTerm φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k (t, x) := by
        apply tsum_congr
        intro k
        rw [hterm]
        rfl
      _ = (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w) (t, x) :=
        ContinuousMap.tsum_apply hterms (t, x)
      _ = _ := rfl
  change ContinuousMap.toLp 2 (volume : Measure Torus) ℂ
    ((classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry t) = _
  rw [← hsum]
  rw [ContinuousLinearMap.map_tsum (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ)
    (by simpa [g] using hg)]
  exact hseries.tsum_eq

/-- The jointly continuous word Fourier series is the spatial derivative of the smooth lift on
each time slice. -/
theorem classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) (x : Torus) :
    classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w (t, x) =
      (classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t))
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) := by
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w t
  let L : C(Torus, ℂ) :=
    (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry t
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  let d := classicalGalerkinRealSmoothDerivativeL2 φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w t
  have hL2 := GalerkinSmoothTimeEquation.classicalGalerkinWordFourierSeries_toLp
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w t
  have hderivL2 := classicalGalerkinWordScalarPathLimit_eq_smoothDerivative
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w t
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hword : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w u) :=
    classicalWordDerivative_contDiff w u hu
  have hwordper : AVenhance.IsZ2Periodic (classicalWordDerivative w u) :=
    GalerkinSmoothTimeEquation.classicalTimeEquationWord_periodic w u hup
  have hperComplex : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex (classicalWordDerivative w u)) := by
    intro z y
    change ((classicalWordDerivative w u) (y + AVenhance.latticeShift z) : ℂ) = _
    exact congrArg (fun r : ℝ => (r : ℂ)) (hwordper z y)
  let D : C(Torus, ℂ) := ⟨
    AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.Infra.Torus.realToComplex (classicalWordDerivative w u)),
    AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.ofRealCLM.continuous.comp hword.continuous) hperComplex⟩
  have hD : ContinuousMap.toLp 2 (volume : Measure Torus) ℂ D =
      classicalRealToComplexTorusCLM d := by
    change ContinuousMap.toLp 2 (volume : Measure Torus) ℂ D =
      (Complex.ofRealCLM.compLpL (2 : ENNReal) (volume : Measure Torus)) d
    apply Lp.ext
    filter_upwards [
      Complex.ofRealCLM.coeFn_compLpL d,
      (memLp_periodicToTorus_real hword.continuous hwordper).coeFn_toLp,
      ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℂ) D] with y hcomplex hreal hD
    rw [hD, hcomplex]
    dsimp [d, classicalGalerkinRealSmoothDerivativeL2] at hreal ⊢
    rw [hreal]
    rfl
  have hLpEq : ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L =
      ContinuousMap.toLp 2 (volume : Measure Torus) ℂ D := by
    rw [hL2, hderivL2, hD]
  have hmaps : L = D :=
    ContinuousMap.toLp_injective (p := (2 : ENNReal))
      (μ := (volume : Measure Torus)) (𝕜 := ℂ) hLpEq
  have hpoint := congrArg (fun f : C(Torus, ℂ) => f x) hmaps
  change L x = D x at hpoint
  calc
    classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w (t, x) = L x := rfl
    _ = D x := hpoint
    _ = (classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per t)
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) : ℂ) := by rfl

end AVenhance.Infra.Classical

end
