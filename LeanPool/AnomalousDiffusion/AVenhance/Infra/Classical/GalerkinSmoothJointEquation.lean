/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTimeEquation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Jointly continuous periodic coefficients for the limiting spatial equation. -/

@[expose] public section

noncomputable section

open Set
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalJointMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalJointAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalJointProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalJointTorusProbability : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin 2))) := inferInstance
local instance classicalJointOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothJointEquation.classicalJointWordPeriodic (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

theorem GalerkinSmoothJointEquation.classicalToUnitTorus_isQuotientMap :
    Topology.IsQuotientMap (toUnitTorus 2) := by
  let e₀ := Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ)
  let e₁ := Homeomorph.piFinTwo (fun _ : Fin 2 => UnitAddCircle)
  let q : ℝ × ℝ → UnitAddCircle × UnitAddCircle :=
    Prod.map QuotientAddGroup.mk QuotientAddGroup.mk
  have hq : IsOpenQuotientMap q :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap
      QuotientAddGroup.isOpenQuotientMap_mk
  have hcomp : Topology.IsQuotientMap (fun x : Vec 2 => e₁.symm (q (e₀ x))) := by
    exact e₁.symm.isQuotientMap.comp (hq.isQuotientMap.comp e₀.isQuotientMap)
  have heq : (fun x : Vec 2 => e₁.symm (q (e₀ x))) = toUnitTorus 2 := by
    funext x
    apply e₁.injective
    apply Prod.ext <;> rfl
  rw [← heq]
  exact hcomp

/-- Descend a jointly continuous periodic family to the time-space torus slab. -/
noncomputable def classicalPeriodicFamilyJointPath
    {α : Type*} [TopologicalSpace α]
    (f : Icc (0 : ℝ) 1 → Vec 2 → α)
    (hf : Continuous (Function.uncurry f))
    (hper : ∀ t, AVenhance.Infra.Torus.IsZdPeriodic (f t)) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), α) := by
  let g : Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2) → α := fun p =>
    f p.1 (unitTorusRepresentative 2 p.2)
  refine ⟨g, ?_⟩
  apply GalerkinSmoothJointEquation.classicalToUnitTorus_isQuotientMap.continuous_lift_prod_right
  apply hf.congr
  intro p
  have h := congrFun (fromUnitTorus_periodicToTorus (hper p.1)) p.2
  simpa [g, Function.uncurry, fromUnitTorus, periodicToTorus] using h.symm

/-- The forcing, descended as a jointly continuous complex-valued torus path. -/
noncomputable def classicalGalerkinForcingJointPath
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t)) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let f : Icc (0 : ℝ) 1 → Vec 2 → ℂ := fun t x => (F t x : ℂ)
  have hmap : Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 => ((p.1 : ℝ), p.2)) :=
    continuous_subtype_val.prodMap continuous_id
  have hmem (p : Icc (0 : ℝ) 1 × Vec 2) :
      ((p.1 : ℝ), p.2) ∈ Ici (0 : ℝ) ×ˢ Set.univ :=
    ⟨p.1.property.1, trivial⟩
  have hfR : Continuous (Function.uncurry (fun t : Icc (0 : ℝ) 1 => F t)) := by
    exact (hF.continuousOn.comp_continuous hmap hmem)
  have hf : Continuous (Function.uncurry f) := by
    exact Complex.ofRealCLM.continuous.comp hfR
  have hper : ∀ t, IsZdPeriodic (f t) := by
    intro t z x
    exact congrArg (fun y : ℝ => (y : ℂ)) (hFper t t.property.1 z x)
  exact classicalPeriodicFamilyJointPath f hf hper

/-- A coordinate of the smooth admissible drift, descended jointly in time and space. -/
noncomputable def classicalGalerkinDriftCoordinateJointPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) (j : Fin 2) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let b := AVenhance.streamVel φ
  let f : Icc (0 : ℝ) 1 → Vec 2 → ℂ := fun t x => (b (t : ℝ) x j : ℂ)
  have hmap : Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 => ((p.1 : ℝ), p.2)) :=
    continuous_subtype_val.prodMap continuous_id
  have hb : Continuous (Function.uncurry b) :=
    (streamVel_smoothPeriodic φ hφ).smooth.continuous
  have hcoord : Continuous (fun p : ℝ × Vec 2 => ((b p.1 p.2 j : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.continuous.comp
      ((continuous_apply j).comp hb)
  have hf : Continuous (Function.uncurry f) := by
    convert hcoord.comp hmap using 1; rfl
  have hper : ∀ t, IsZdPeriodic (f t) := by
    intro t z x
    dsimp [b, f]
    have hshift : AVenhance.latticeShift z = intVector z := by
      funext i
      rfl
    rw [← hshift]
    simpa using congrArg (fun v : Vec 2 => (v j : ℂ))
      ((streamVel_smoothPeriodic φ hφ).periodic 0 z (t : ℝ) x)
  exact classicalPeriodicFamilyJointPath f hf hper

/-- The physical right-hand side of the limiting equation on the closed unit time slab. -/
noncomputable def classicalGalerkinSmoothRhsJointPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let u₀ := classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per []
  let u₀₀ := classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [0, 0]
  let u₁₁ := classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [1, 1]
  let b₀ := classicalGalerkinDriftCoordinateJointPath φ hφ 0
  let b₁ := classicalGalerkinDriftCoordinateJointPath φ hφ 1
  let du₀ := classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [0]
  let du₁ := classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [1]
  let forcing := classicalGalerkinForcingJointPath F hF hFper
  exact forcing + (ContinuousMap.const _ (κ : ℂ)) * (u₀₀ + u₁₁) -
    (b₀ * du₀ + b₁ * du₁)

theorem classicalGalerkinSmoothRhsJointPath_apply
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (x : UnitAddTorus (Fin 2)) :
    classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (t, x) =
      ((F t (unitTorusRepresentative 2 x) +
        κ * AVenhance.spaceLap
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t) (unitTorusRepresentative 2 x) -
        Homogenization.vecDot (AVenhance.streamVel φ t
          (unitTorusRepresentative 2 x))
          (AVenhance.spaceGrad
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per t) (unitTorusRepresentative 2 x))) : ℂ) := by
  let y := unitTorusRepresentative 2 x
  have h00 := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [0, 0] t x
  have h11 := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [1, 1] t x
  have h0d := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [0] t x
  have h1d := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per [1] t x
  simp [classicalGalerkinSmoothRhsJointPath,
    classicalGalerkinForcingJointPath, classicalGalerkinDriftCoordinateJointPath,
    classicalPeriodicFamilyJointPath, classicalWordDerivative,
    AVenhance.spaceLap, Homogenization.vecDot, Fin.sum_univ_two,
    h00, h11, h0d, h1d]

/-- The continuous-map Fourier coefficient is a continuous linear functional. -/
noncomputable def classicalTorusFourierCoeffCLM (k : Fin 2 → ℤ) :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] ℂ := by
  let R : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) →L[ℂ]
      lp (fun _ : Fin 2 → ℤ => ℂ) 2 :=
    UnitAddTorus.mFourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap
  let P : lp (fun _ : Fin 2 → ℤ => ℂ) 2 →L[ℂ] ℂ :=
    lp.evalCLM ℂ (fun _ : Fin 2 → ℤ => ℂ) 2 k
  exact P.comp (R.comp
    (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ))

theorem classicalTorusFourierCoeffCLM_apply
    (k : Fin 2 → ℤ) (f : C(UnitAddTorus (Fin 2), ℂ)) :
    classicalTorusFourierCoeffCLM k f = UnitAddTorus.mFourierCoeff f k := by
  simp only [classicalTorusFourierCoeffCLM, ContinuousLinearMap.comp_apply]
  change (UnitAddTorus.mFourierBasis.repr ((ContinuousMap.toLp 2
    (volume : Measure (UnitAddTorus (Fin 2))) ℂ) f)) k = _
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp]

theorem classicalJoint_mFourierCoeff_eq_smoothFourierCoeff
    {f : Vec 2 → ℂ} (hper : IsZdPeriodic f) (hf : Continuous f)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (⟨periodicToTorus f,
          AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic hf hper⟩ :
          C(UnitAddTorus (Fin 2), ℂ)) k = smoothFourierCoeff f k := by
  have hchar (x : UnitAddTorus (Fin 2)) : torusCharacter k
      (unitTorusRepresentative 2 x) = UnitAddTorus.mFourier (-k) x := by
    simp [torusCharacter, toUnitTorus_unitTorusRepresentative]
  change (∫ x : UnitAddTorus (Fin 2),
      UnitAddTorus.mFourier (-k) x • periodicToTorus f x) = _
  simp only [smul_eq_mul]
  change (∫ x : UnitAddTorus (Fin 2),
      UnitAddTorus.mFourier (-k) x * periodicToTorus f x) =
    ∫ x in unitCell 2, torusCharacter k x * f x
  rw [← integral_periodicToTorus_eq_unitCell
    (fun y => torusCharacter k y * f y)]
  apply integral_congr_ae
  filter_upwards with x
  rw [← hchar x]
  rfl

/-- The Fourier coefficient of every jointly continuous spatial derivative path is its Galerkin
limit coefficient. -/
theorem classicalGalerkinWordFourierPath_fourierCoeff_eq_limit
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        ((classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w).curry t) k =
      classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k t := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  have hu0 : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hwordCoeff (j : Fin 2 → ℤ) (v : List (Fin 2)) :
      AVenhance.Infra.Torus.smoothFourierCoeff
          (AVenhance.Infra.Torus.realToComplex (classicalWordDerivative v u)) j =
        classicalGalerkinWordFourierMultiplier j v *
          AVenhance.Infra.Torus.smoothFourierCoeff
            (AVenhance.Infra.Torus.realToComplex u) j := by
    induction v with
    | nil => simp [classicalGalerkinWordFourierMultiplier, classicalWordDerivative]
    | cons i v ih =>
      have hv : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative v u) :=
        classicalWordDerivative_contDiff v u hu
      have hvper : AVenhance.IsZ2Periodic (classicalWordDerivative v u) :=
        GalerkinSmoothJointEquation.classicalJointWordPeriodic v u hup
      have hformula := AVenhance.Infra.Torus.smoothFourierCoeff_spaceGrad
        (hv.of_le (by simp)) hvper i j
      rw [show classicalWordDerivative (i :: v) u =
        fun x => AVenhance.spaceGrad (classicalWordDerivative v u) x i by rfl]
      change AVenhance.Infra.Torus.smoothFourierCoeff
        (fun x => (AVenhance.spaceGrad (classicalWordDerivative v u) x i : ℂ)) j = _
      rw [hformula, ih]
      simp [classicalGalerkinWordFourierMultiplier, List.map_cons, List.prod_cons]
      ring
  have hwordSmooth : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w u) :=
    classicalWordDerivative_contDiff w u hu
  have hwordper : AVenhance.IsZ2Periodic (classicalWordDerivative w u) :=
    GalerkinSmoothJointEquation.classicalJointWordPeriodic w u hup
  have hperComplex : AVenhance.Infra.Torus.IsZdPeriodic
      (AVenhance.Infra.Torus.realToComplex (classicalWordDerivative w u)) := by
    intro z x
    change (classicalWordDerivative w u
      (x + AVenhance.latticeShift z) : ℂ) = _
    exact congrArg (fun r : ℝ => (r : ℂ)) (hwordper z x)
  let D : C(UnitAddTorus (Fin 2), ℂ) := ⟨
    AVenhance.Infra.Torus.periodicToTorus
      (AVenhance.Infra.Torus.realToComplex (classicalWordDerivative w u)),
    AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.ofRealCLM.continuous.comp hwordSmooth.continuous) hperComplex⟩
  have hmap :
      (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry t = D := by
    ext x
    change classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w (t, x) =
      (classicalWordDerivative w u
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) : ℂ)
    rw [classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w t x]
  have hcoefficient :
      AVenhance.Infra.Torus.smoothFourierCoeff
        (AVenhance.Infra.Torus.realToComplex (classicalWordDerivative w u)) k =
      classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k t := by
    rw [hwordCoeff]
    rw [classicalGalerkinRealSmoothLift_smoothFourierCoeff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t k]
    rw [classicalGalerkinWordLimitFourierCoeff_word]
    exact congrArg
      (fun z : ℂ => classicalGalerkinWordFourierMultiplier k w * z) (by rfl)
  rw [hmap, classicalJoint_mFourierCoeff_eq_smoothFourierCoeff hperComplex
    (Complex.ofRealCLM.continuous.comp hwordSmooth.continuous) k]
  exact hcoefficient

theorem classicalGalerkinSmoothRhsJointSlice_fourierCoeff_eq_physical
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        ((classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per).curry t) k =
      UnitAddTorus.mFourierCoeff
        (fun x : UnitAddTorus (Fin 2) =>
          ((periodicToTorus (fun y : Vec 2 =>
            F t y + (κ * AVenhance.spaceLap
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per t) y -
              Homogenization.vecDot (AVenhance.streamVel φ t y)
                (AVenhance.spaceGrad (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                  θ₀ hθ₀ hθ₀per t) y))) x : ℝ) : ℂ)) k := by
  apply congrArg (fun f : UnitAddTorus (Fin 2) → ℂ => UnitAddTorus.mFourierCoeff f k)
  funext x
  have hpoint := classicalGalerkinSmoothRhsJointPath_apply
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t x
  calc
    _ = ((F t (unitTorusRepresentative 2 x) : ℝ) : ℂ) +
        (κ : ℂ) * (AVenhance.spaceLap
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t) (unitTorusRepresentative 2 x) : ℝ) -
        (Homogenization.vecDot (AVenhance.streamVel φ t
          (unitTorusRepresentative 2 x))
          (AVenhance.spaceGrad (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t) (unitTorusRepresentative 2 x)) : ℝ) := hpoint
    _ = ((periodicToTorus (fun y : Vec 2 =>
          F t y + (κ * AVenhance.spaceLap
            (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per t) y - Homogenization.vecDot
            (AVenhance.streamVel φ t y) (AVenhance.spaceGrad
              (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
                θ₀ hθ₀ hθ₀per t) y))) x : ℝ) : ℂ) := by
      simp [periodicToTorus, Complex.ofReal_add, Complex.ofReal_sub,
        Complex.ofReal_mul]
      ring

/-- Clamp real time to the closed unit slab. -/
def classicalGalerkinUnitSlabClamp (s : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 s), le_max_left _ _,
    (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩

theorem classicalGalerkinUnitSlabClamp_eq_of_mem {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    classicalGalerkinUnitSlabClamp s = ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩ := by
  apply Subtype.ext
  simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt hs.1),
    min_eq_right (le_of_lt hs.2)]

/-- The Fourier coefficients of every spatial derivative path satisfy the differentiated limiting
equation on the interior of the unit time slab. -/
theorem classicalGalerkinWordFourierPath_fourierCoeff_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (k : Fin 2 → ℤ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => UnitAddTorus.mFourierCoeff
        ((classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w).curry (classicalGalerkinUnitSlabClamp s)) k)
      (classicalGalerkinWordFourierMultiplier k w *
        UnitAddTorus.mFourierCoeff
          ((classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per).curry ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) k) t := by
  let mult := classicalGalerkinWordFourierMultiplier k w
  have hbase := classicalGalerkinRealSmoothLift_fourierCoeff_hasDerivAt
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k ht
  have hrhs := classicalGalerkinSmoothRhsJointSlice_fourierCoeff_eq_physical
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
      ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ k
  have hscaled₀ := hbase.const_mul mult
  have hscaled := hscaled₀.congr_deriv
    (congrArg (fun z : ℂ => mult * z) hrhs.symm)
  have htransfer : HasDerivAt
      (fun s => UnitAddTorus.mFourierCoeff
        ((classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w).curry (classicalGalerkinUnitSlabClamp s)) k)
      (mult * UnitAddTorus.mFourierCoeff
        ((classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per).curry ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) k) t := by
    apply hscaled.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [classicalGalerkinUnitSlabClamp_eq_of_mem (by
      simpa only [Set.mem_Ioo] using hs),
      classicalGalerkinTimeEquationClamp_eq_of_mem hs]
    rw [classicalGalerkinWordFourierPath_fourierCoeff_eq_limit]
    rw [classicalGalerkinWordLimitFourierCoeff_word]
    rfl
  exact htransfer

theorem GalerkinSmoothJointEquation.continuous_classicalGalerkinUnitSlabClamp :
    Continuous classicalGalerkinUnitSlabClamp := by
  exact Continuous.subtype_mk
    (continuous_const.max (continuous_const.min continuous_id))
    (fun s => ⟨le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩)

end AVenhance.Infra.Classical

end
