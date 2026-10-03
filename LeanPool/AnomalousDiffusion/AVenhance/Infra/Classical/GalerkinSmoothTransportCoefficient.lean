/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothEquationLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator

/-! Fourier coefficients of smooth transport terms as `L²` pairings. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Torus

local instance classicalTransportCoefficientOneLeTwo : Fact (1 ≤ (2 : ENNReal)) :=
  ⟨by norm_num⟩
/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalTransportCoefficientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalTransportCoefficientAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalTransportCoefficientProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalTransportCoefficientTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothTransportCoefficient.classicalTransportCoefficientDriftSlice_contDiff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) := by
  have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hs := hjoint.comp hpair
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x))
  exact hs.of_le (by simp)

open GalerkinSmoothTransportCoefficient

theorem GalerkinSmoothTransportCoefficient.classicalTransportCoefficientWord_periodic (w : List
    (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

/-- A synthesized word derivative is represented by the corresponding smooth periodic field in
the scalar torus `L²` space. -/
theorem classicalGalerkinWordScalarMap_eq_periodicL2
    (N : ℕ) (c : Coefficients (RealFourierDimension N)) (w : List (Fin 2)) :
    realFourierScalarMap N (realFourierWordDerivativeMap N w c) =
      (memLp_periodicToTorus_real
        ((classicalWordDerivative_contDiff w
          (realFourierModeAmbientExpansion N c)
          ((realFourierModeAmbientExpansion_contDiff N c).of_le (by simp))).continuous)
        (GalerkinSmoothTransportCoefficient.classicalTransportCoefficientWord_periodic w
          (realFourierModeAmbientExpansion N c)
          (realFourierModeAmbientExpansion_periodic N c))).toLp
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordDerivative w (realFourierModeAmbientExpansion N c))) := by
  let u := realFourierModeAmbientExpansion N c
  let d := realFourierWordDerivativeMap N w c
  let f := classicalWordDerivative w u
  have hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    (realFourierModeAmbientExpansion_contDiff N c).of_le (by simp)
  have hword : f = realFourierModeAmbientExpansion N d := by
    simpa [f, d, realFourierWordDerivativeMap_apply] using
      classicalWordDerivative_realFourierModeAmbientExpansion N w c
  let hmem := memLp_periodicToTorus_real
    (classicalWordDerivative_contDiff w u hu).continuous
    (GalerkinSmoothTransportCoefficient.classicalTransportCoefficientWord_periodic w u
      (realFourierModeAmbientExpansion_periodic N c))
  have hmemEq : hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f) =
      realFourierScalarMap N d := by
    apply Lp.ext
    filter_upwards [hmem.coeFn_toLp, realFourierScalarMap_coeFn N d] with x hleft hright
    calc
      (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f)) x =
          AVenhance.Infra.Torus.periodicToTorus f x := hleft
      _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x := by
        rw [hword]
        exact congrFun (realFourierModeFin_expansion_eq_periodicToTorus N d).symm x
      _ = (realFourierScalarMap N d) x := hright.symm
  simpa [u, d, f, hmem] using hmemEq.symm

/-- The Fourier coefficient of a smooth real periodic field is the coefficient of its
complexification in torus `L²`. -/
theorem classicalRealPeriodicFourierCoeff_eq_clm
    (f : Vec 2 → ℝ) (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) k =
      classicalComplexFourierCoeffCLM k
        ((memLp_periodicToTorus_real hf hper).toLp
          (AVenhance.Infra.Torus.periodicToTorus f)) := by
  let hreal := memLp_periodicToTorus_real hf hper
  let fC : Vec 2 → ℂ := fun x => (f x : ℂ)
  have hfC : Continuous fC := Complex.ofRealCLM.continuous.comp hf
  let hcomplex := AVenhance.Infra.Torus.memLp_periodicToTorus hfC
  have hmap : classicalRealToComplexTorusCLM
      (hreal.toLp (AVenhance.Infra.Torus.periodicToTorus f)) =
      hcomplex.toLp (AVenhance.Infra.Torus.periodicToTorus fC) := by
    apply Lp.ext
    filter_upwards [Complex.ofRealCLM.coeFn_compLp
        (hreal.toLp (AVenhance.Infra.Torus.periodicToTorus f)),
      hreal.coeFn_toLp, hcomplex.coeFn_toLp] with x hcast hrealx hCx
    calc
      _ = Complex.ofRealCLM
          ((hreal.toLp (AVenhance.Infra.Torus.periodicToTorus f)) x) := hcast
      _ = Complex.ofRealCLM (AVenhance.Infra.Torus.periodicToTorus f x) := by rw [hrealx]
      _ = AVenhance.Infra.Torus.periodicToTorus fC x := rfl
      _ = (hcomplex.toLp (AVenhance.Infra.Torus.periodicToTorus fC)) x := hCx.symm
  rw [classicalComplexFourierCoeffCLM_apply, hmap, UnitAddTorus.mFourierCoeff]
  apply integral_congr_ae
  filter_upwards [hcomplex.coeFn_toLp] with x hx
  rw [hx]
  rfl

theorem GalerkinSmoothTransportCoefficient.classicalRealPeriodicFourierIntegrand_integrable
    (f : Vec 2 → ℝ) (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f)
    (k : Fin 2 → ℤ) : Integrable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ))
      (volume : Measure Torus) := by
  have hreal : Integrable (AVenhance.Infra.Torus.periodicToTorus f)
      (volume : Measure Torus) :=
    (memLp_periodicToTorus_real hf hper).integrable (by norm_num)
  have hcomplex : Integrable (fun x : Torus =>
      Complex.ofReal (AVenhance.Infra.Torus.periodicToTorus f x))
      (volume : Measure Torus) := Complex.ofRealCLM.integrable_comp hreal
  have hchar : AEStronglyMeasurable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x) (volume : Measure Torus) :=
    (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
  have hbound : ∀ x : Torus, ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
    intro x
    exact (ContinuousMap.norm_coe_le_norm _ x).trans_eq UnitAddTorus.mFourier_norm
  exact (hcomplex.bdd_smul 1 hchar (Filter.Eventually.of_forall hbound)).congr
    (Filter.Eventually.of_forall fun x => by rfl)

/-- Fourier coefficients of sums of smooth real periodic fields add. -/
theorem classicalRealPeriodicFourierCoeff_add
    (f g : Vec 2 → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y => f y + g y) x : ℝ) : ℂ)) k =
      UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) k +
      UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus g x : ℝ) : ℂ)) k := by
  unfold UnitAddTorus.mFourierCoeff
  rw [show (fun x : Torus => UnitAddTorus.mFourier (-k) x •
      ((AVenhance.Infra.Torus.periodicToTorus (fun y => f y + g y) x : ℝ) : ℂ)) =
      (fun x => UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) +
      (fun x => UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus g x : ℝ) : ℂ)) by
    funext x
    simp [AVenhance.Infra.Torus.periodicToTorus, Complex.ofReal_add]
    ring]
  exact integral_add
    (GalerkinSmoothTransportCoefficient.classicalRealPeriodicFourierIntegrand_integrable f hf hfp k)
    (GalerkinSmoothTransportCoefficient.classicalRealPeriodicFourierIntegrand_integrable g hg hgp k)

/-- Multiplication of a smooth real periodic field by a scalar multiplies its Fourier
coefficient by the complexified scalar. -/
theorem classicalRealPeriodicFourierCoeff_const_mul
    (a : ℝ) (f : Vec 2 → ℝ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y => a * f y) x : ℝ) : ℂ)) k =
      (a : ℂ) * UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) k := by
  unfold UnitAddTorus.mFourierCoeff
  rw [show (fun x : Torus => UnitAddTorus.mFourier (-k) x •
      ((AVenhance.Infra.Torus.periodicToTorus (fun y => a * f y) x : ℝ) : ℂ)) =
    (fun x => (a : ℂ) • (UnitAddTorus.mFourier (-k) x •
      ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ))) by
    funext x
    simp [AVenhance.Infra.Torus.periodicToTorus, smul_eq_mul]
    ring]
  rw [integral_smul]
  simp [smul_eq_mul]

/-- Fourier coefficients of differences of smooth real periodic fields subtract. -/
theorem classicalRealPeriodicFourierCoeff_sub
    (f g : Vec 2 → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y => f y - g y) x : ℝ) : ℂ)) k =
      UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) k -
      UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus g x : ℝ) : ℂ)) k := by
  have hneg : AVenhance.IsZ2Periodic (fun y => -g y) := by
    intro z x
    simpa using congrArg Neg.neg (hgp z x)
  have hadd := classicalRealPeriodicFourierCoeff_add f (fun y => -g y)
    hf hg.neg hfp hneg k
  have hnegCoeff := classicalRealPeriodicFourierCoeff_const_mul (-1) g k
  have hnegFun : (fun y : Vec 2 => (-1 : ℝ) * g y) = (fun y => -g y) := by
    funext y
    ring
  rw [hnegFun] at hnegCoeff
  have hnegCoeff' : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y => -g y) x : ℝ) : ℂ)) k =
      - UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus g x : ℝ) : ℂ)) k := by
    simpa using hnegCoeff
  have hfun : (fun y => f y + -g y) = (fun y => f y - g y) := by
    funext y
    ring
  have hleft : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y => f y - g y) x : ℝ) : ℂ)) k =
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y => f y + -g y) x : ℝ) : ℂ)) k := by
    rw [← hfun]
  calc
    _ = UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y => f y + -g y) x : ℝ) : ℂ)) k := hleft
    _ = UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) k +
        UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
            (fun y => -g y) x : ℝ) : ℂ)) k := hadd
    _ = UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus f x : ℝ) : ℂ)) k +
        -UnitAddTorus.mFourierCoeff
          (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus g x : ℝ) : ℂ)) k := by
      rw [hnegCoeff']
    _ = _ := by ring

/-- One component of the Fourier coefficient of `b · ∇u` is the `L²` pairing of the
corresponding gradient with the matching smooth transport test. -/
theorem classicalGalerkinTransportComponent_fourierCoeff_eq_inner
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (j : Fin 2) (t : ℝ)
    (u : Vec 2 → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huper : AVenhance.IsZ2Periodic u) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => ((AVenhance.streamVel φ t y j) *
            AVenhance.spaceGrad u y j : ℝ)) x : ℝ) : ℂ)) k =
      inner ℂ
        (classicalRealToComplexTorusCLM
          ((memLp_periodicToTorus_real
            ((classicalWordDerivative_contDiff [j] u hu).continuous)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component huper j)).toLp
              (AVenhance.Infra.Torus.periodicToTorus
                (classicalWordDerivative [j] u))))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
  let g : Vec 2 → ℝ := classicalWordDerivative [j] u
  have hgcont : Continuous g := (classicalWordDerivative_contDiff [j] u hu).continuous
  have hgper : AVenhance.IsZ2Periodic g :=
    AVenhance.Infra.Classical.periodic_spaceGrad_component huper j
  let hgmem := memLp_periodicToTorus_real hgcont hgper
  let gL2 : ScalarTorusL2 := hgmem.toLp (AVenhance.Infra.Torus.periodicToTorus g)
  let gComplex : ComplexScalarTorusL2 := classicalRealToComplexTorusCLM gL2
  let gc : Vec 2 → ℂ := fun x => (g x : ℂ)
  have hgc : Continuous gc := Complex.ofRealCLM.continuous.comp hgcont
  have hcomplex : gComplex = AVenhance.Infra.Torus.periodicToTorusL2 gc hgc := by
    apply Lp.ext
    filter_upwards [Complex.ofRealCLM.coeFn_compLp gL2,
      hgmem.coeFn_toLp,
      (AVenhance.Infra.Torus.memLp_periodicToTorus hgc).coeFn_toLp] with x hcast hg hsource
    calc
      gComplex x = Complex.ofRealCLM (gL2 x) := hcast
      _ = Complex.ofRealCLM (AVenhance.Infra.Torus.periodicToTorus g x) := by rw [hg]
      _ = AVenhance.Infra.Torus.periodicToTorus gc x := rfl
      _ = AVenhance.Infra.Torus.periodicToTorusL2 gc hgc x := hsource.symm
  have hgradAE : (fun x : Torus => gComplex x) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus gc := by
    filter_upwards [(AVenhance.Infra.Torus.memLp_periodicToTorus hgc).coeFn_toLp] with x hx
    have heval := congrArg (fun v : ComplexScalarTorusL2 => v x) hcomplex
    change gComplex x = AVenhance.Infra.Torus.periodicToTorus gc x
    rw [heval]
    exact hx
  rw [UnitAddTorus.mFourierCoeff, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have htest := classicalGalerkinTransportFourierTest_eq_periodicL2 φ hφ k j t
  have hf : Continuous (fun y : Vec 2 =>
      AVenhance.Infra.Torus.torusCharacter k y *
        (AVenhance.streamVel φ t y j : ℂ)) := by
    apply (AVenhance.Infra.Torus.torusCharacter_contDiff k).continuous.mul
    exact Complex.ofRealCLM.continuous.comp
      ((contDiff_pi.1 (classicalTransportCoefficientDriftSlice_contDiff φ hφ t) j).continuous)
  have htestFun : (fun x : Torus =>
      classicalGalerkinTransportFourierTest φ hφ k j t x) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => AVenhance.Infra.Torus.torusCharacter k y *
          (AVenhance.streamVel φ t y j : ℂ)) := by
    filter_upwards [(AVenhance.Infra.Torus.memLp_periodicToTorus hf).coeFn_toLp] with x hx
    have heval := congrArg (fun v : ComplexScalarTorusL2 => v x) htest
    change classicalGalerkinTransportFourierTest φ hφ k j t x =
      AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => AVenhance.Infra.Torus.torusCharacter k y *
          (AVenhance.streamVel φ t y j : ℂ)) x
    rw [heval]
    exact hx
  filter_upwards [hgradAE, htestFun] with x hgrad htest
  rw [hgrad, htest]
  simp [gc, g, classicalWordDerivative, AVenhance.Infra.Torus.torusCharacter,
    UnitAddTorus.mFourier,
    AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative,
    AVenhance.Infra.Torus.periodicToTorus, Complex.conj_ofReal]
  ring

/-- The full divergence-free drift term pairs as the sum of its componentwise gradient tests. -/
theorem classicalGalerkinTransport_fourierCoeff_eq_sum_inner
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (t : ℝ)
    (u : Vec 2 → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huper : AVenhance.IsZ2Periodic u) :
    UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot
            (AVenhance.streamVel φ t y) (AVenhance.spaceGrad u y)) x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          ((memLp_periodicToTorus_real
            ((classicalWordDerivative_contDiff [j] u hu).continuous)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component huper j)).toLp
              (AVenhance.Infra.Torus.periodicToTorus
                (classicalWordDerivative [j] u))))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
  let q : Vec 2 → ℝ := fun y => Homogenization.vecDot
    (AVenhance.streamVel φ t y) (AVenhance.spaceGrad u y)
  let qj : Fin 2 → Vec 2 → ℝ := fun j y =>
    AVenhance.streamVel φ t y j * AVenhance.spaceGrad u y j
  have hqsum : q = fun y => ∑ j : Fin 2, qj j y := by
    funext y
    simp [q, qj, Homogenization.vecDot]
  have hbcont : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) :=
    classicalTransportCoefficientDriftSlice_contDiff φ hφ t
  have hbper : AVenhance.IsZ2Periodic (AVenhance.streamVel φ t) := by
    intro z x
    simpa using (streamVel_smoothPeriodic φ hφ).periodic 0 z t x
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad u) := by
    unfold AVenhance.spaceGrad
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) := hu.fderiv_right (by simp)
    apply contDiff_pi.2
    intro i
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ u x (Homogenization.basisVec i))
    exact hf.clm_apply contDiff_const
  have hperiodSum : AVenhance.Infra.Torus.periodicToTorus q =
      fun x : Torus => ∑ j : Fin 2,
        AVenhance.Infra.Torus.periodicToTorus (qj j) x := by
    funext x
    change q (AVenhance.Infra.Torus.unitTorusRepresentative 2 x) = _
    rw [hqsum]
    rfl
  have hchar : AEStronglyMeasurable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x) (volume : Measure Torus) :=
    (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
  have hcharBound : ∀ x : Torus, ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
    intro x
    exact (ContinuousMap.norm_coe_le_norm _ x).trans_eq UnitAddTorus.mFourier_norm
  have hcomponentIntegrable (j : Fin 2) : Integrable
      (fun x : Torus => UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus (qj j) x : ℝ) : ℂ))
      (volume : Measure Torus) := by
    have hbComp : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => AVenhance.streamVel φ t y j) :=
      (contDiff_pi.1 hbcont j)
    have hgComp : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => AVenhance.spaceGrad u y j) :=
      (contDiff_pi.1 hgrad j)
    have hqcont : Continuous (qj j) := (hbComp.mul hgComp).continuous
    have hqper : AVenhance.IsZ2Periodic (qj j) := by
      intro z x
      have hbcomp := congrFun (hbper z x) j
      have hgcomp := AVenhance.Infra.Classical.periodic_spaceGrad_component huper j z x
      have hgcomp' : AVenhance.spaceGrad u (x + AVenhance.latticeShift z) j =
          AVenhance.spaceGrad u x j := by simpa using hgcomp
      change AVenhance.streamVel φ t (x + AVenhance.latticeShift z) j *
          AVenhance.spaceGrad u (x + AVenhance.latticeShift z) j = _
      calc
        _ = AVenhance.streamVel φ t x j *
            AVenhance.spaceGrad u (x + AVenhance.latticeShift z) j := by rw [hbcomp]
        _ = _ := by rw [hgcomp']
    let mem := memLp_periodicToTorus_real hqcont hqper
    have hqInt : Integrable
        (AVenhance.Infra.Torus.periodicToTorus (qj j)) (volume : Measure Torus) :=
      mem.integrable (by norm_num)
    have hqC : Integrable (fun x : Torus =>
        Complex.ofReal (AVenhance.Infra.Torus.periodicToTorus (qj j) x))
        (volume : Measure Torus) := Complex.ofRealCLM.integrable_comp hqInt
    exact (hqC.bdd_smul 1 hchar (Filter.Eventually.of_forall hcharBound)).congr
      (Filter.Eventually.of_forall fun x => by rfl)
  have hcoefficientSum : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus q x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus (qj j) x : ℝ) : ℂ)) k := by
    unfold UnitAddTorus.mFourierCoeff
    rw [show (fun x : Torus =>
        UnitAddTorus.mFourier (-k) x •
          ((AVenhance.Infra.Torus.periodicToTorus q x : ℝ) : ℂ)) =
      fun x => ∑ j : Fin 2, UnitAddTorus.mFourier (-k) x •
        ((AVenhance.Infra.Torus.periodicToTorus (qj j) x : ℝ) : ℂ) by
      funext x
      rw [hperiodSum]
      change UnitAddTorus.mFourier (-k) x •
        ((∑ j : Fin 2, AVenhance.Infra.Torus.periodicToTorus (qj j) x : ℝ) : ℂ) = _
      rw [Complex.ofReal_sum, Finset.smul_sum]]
    rw [integral_finsetSum Finset.univ (by
      intro j hj
      exact hcomponentIntegrable j)]
  rw [hcoefficientSum]
  apply Finset.sum_congr rfl
  intro j hj
  exact classicalGalerkinTransportComponent_fourierCoeff_eq_inner
    φ hφ k j t u hu huper

/-- The Fourier coefficient difference of two finite Galerkin transport terms is controlled by
the differences of their first derivative paths. -/
theorem classicalGalerkinTransport_fourierCoeff_diff_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (k : Fin 2 → ℤ) (t B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ s x, ‖AVenhance.streamVel φ s x‖ ≤ B)
    (N M : ℕ) (cN : Coefficients (RealFourierDimension N))
    (cM : Coefficients (RealFourierDimension M)) :
    ‖UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
            (AVenhance.spaceGrad
              (realFourierModeAmbientExpansion N cN) y)) x : ℝ) : ℂ)) k -
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
          (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
            (AVenhance.spaceGrad
              (realFourierModeAmbientExpansion M cM) y)) x : ℝ) : ℂ)) k‖ ≤
      ∑ j : Fin 2, B * ‖realFourierScalarMap N
          (realFourierWordDerivativeMap N [j] cN) -
        realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)‖ := by
  let uN := realFourierModeAmbientExpansion N cN
  let uM := realFourierModeAmbientExpansion M cM
  have huN : ContDiff ℝ (⊤ : ℕ∞) uN := by
    simpa [uN] using (realFourierModeAmbientExpansion_contDiff N cN).of_le (by simp)
  have huM : ContDiff ℝ (⊤ : ℕ∞) uM := by
    simpa [uM] using (realFourierModeAmbientExpansion_contDiff M cM).of_le (by simp)
  have hperN : AVenhance.IsZ2Periodic uN := by
    simpa [uN] using realFourierModeAmbientExpansion_periodic N cN
  have hperM : AVenhance.IsZ2Periodic uM := by
    simpa [uM] using realFourierModeAmbientExpansion_periodic M cM
  have hsumN := classicalGalerkinTransport_fourierCoeff_eq_sum_inner
    φ hφ k t uN huN hperN
  have hsumM := classicalGalerkinTransport_fourierCoeff_eq_sum_inner
    φ hφ k t uM huM hperM
  have hpathN : ∀ j : Fin 2,
      classicalRealToComplexTorusCLM
          ((memLp_periodicToTorus_real
            ((classicalWordDerivative_contDiff [j] uN huN).continuous)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component hperN j)).toLp
              (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative [j] uN))) =
        classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN)) := by
    intro j
    rw [← classicalGalerkinWordScalarMap_eq_periodicL2 N cN [j]]
  have hpathM : ∀ j : Fin 2,
      classicalRealToComplexTorusCLM
          ((memLp_periodicToTorus_real
            ((classicalWordDerivative_contDiff [j] uM huM).continuous)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component hperM j)).toLp
              (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative [j] uM))) =
        classicalRealToComplexTorusCLM
          (realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)) := by
    intro j
    rw [← classicalGalerkinWordScalarMap_eq_periodicL2 M cM [j]]
  have hsumN' : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
          (AVenhance.spaceGrad uN y)) x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN)))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
    calc
      _ = ∑ j : Fin 2, inner ℂ
          (classicalRealToComplexTorusCLM
            ((memLp_periodicToTorus_real
              ((classicalWordDerivative_contDiff [j] uN huN).continuous)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component hperN j)).toLp
                (AVenhance.Infra.Torus.periodicToTorus
                  (classicalWordDerivative [j] uN))))
          (classicalGalerkinTransportFourierTest φ hφ k j t) := by
        simpa [uN] using hsumN
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpathN j]
  have hsumM' : UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
          (AVenhance.spaceGrad uM y)) x : ℝ) : ℂ)) k =
      ∑ j : Fin 2, inner ℂ
        (classicalRealToComplexTorusCLM
          (realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
    calc
      _ = ∑ j : Fin 2, inner ℂ
          (classicalRealToComplexTorusCLM
            ((memLp_periodicToTorus_real
              ((classicalWordDerivative_contDiff [j] uM huM).continuous)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component hperM j)).toLp
                (AVenhance.Infra.Torus.periodicToTorus
                  (classicalWordDerivative [j] uM))))
          (classicalGalerkinTransportFourierTest φ hφ k j t) := by
        simpa [uM] using hsumM
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpathM j]
  change ‖UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
          (AVenhance.spaceGrad uN y)) x : ℝ) : ℂ)) k -
    UnitAddTorus.mFourierCoeff
      (fun x : Torus => ((AVenhance.Infra.Torus.periodicToTorus
        (fun y : Vec 2 => Homogenization.vecDot (AVenhance.streamVel φ t y)
          (AVenhance.spaceGrad uM y)) x : ℝ) : ℂ)) k‖ ≤ _
  rw [hsumN', hsumM']
  rw [← Finset.sum_sub_distrib]
  have hpair (j : Fin 2) :
      inner ℂ (classicalRealToComplexTorusCLM
        (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN)))
          (classicalGalerkinTransportFourierTest φ hφ k j t) -
      inner ℂ (classicalRealToComplexTorusCLM
        (realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
          (classicalGalerkinTransportFourierTest φ hφ k j t) =
      inner ℂ (classicalRealToComplexTorusCLM
        (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN) -
          realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
          (classicalGalerkinTransportFourierTest φ hφ k j t) := by
    rw [← inner_sub_left, ← map_sub]
  have hsumDiff :
      (∑ j : Fin 2,
        (inner ℂ (classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN)))
          (classicalGalerkinTransportFourierTest φ hφ k j t) -
        inner ℂ (classicalRealToComplexTorusCLM
          (realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
          (classicalGalerkinTransportFourierTest φ hφ k j t))) =
      ∑ j : Fin 2, inner ℂ (classicalRealToComplexTorusCLM
        (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN) -
          realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
        (classicalGalerkinTransportFourierTest φ hφ k j t) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hpair j
  rw [hsumDiff]
  calc
    ‖∑ j : Fin 2, inner ℂ (classicalRealToComplexTorusCLM
        (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN) -
          realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
          (classicalGalerkinTransportFourierTest φ hφ k j t)‖ ≤
      ∑ j : Fin 2, ‖inner ℂ (classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN) -
            realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
          (classicalGalerkinTransportFourierTest φ hφ k j t)‖ := by
      simpa using (norm_sum_le (Finset.univ : Finset (Fin 2))
        (fun j : Fin 2 => inner ℂ (classicalRealToComplexTorusCLM
          (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN) -
            realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)))
          (classicalGalerkinTransportFourierTest φ hφ k j t)))
    _ ≤ ∑ j : Fin 2, B * ‖realFourierScalarMap N
          (realFourierWordDerivativeMap N [j] cN) -
        realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM)‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact classicalGalerkinTransportFourierPairing_norm_le
        φ hφ k j t B hB hb
        (realFourierScalarMap N (realFourierWordDerivativeMap N [j] cN) -
          realFourierScalarMap M (realFourierWordDerivativeMap M [j] cM))

end AVenhance.Infra.Classical

end
