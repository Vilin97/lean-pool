/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinResidualTail
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Commutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-! Cutoff tails of smooth real periodic residuals. -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open scoped Topology
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalResidualMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalResidualMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalResidualProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

theorem GalerkinResidual.continuous_spaceGrad_component {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) := by
  change Continuous (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- For a smooth periodic real source, the difference between nested Galerkin projections is
bounded by the source's spatial Dirichlet energy, with the expected inverse-cutoff factor. -/
theorem classicalSmoothProjection_tail_norm_sq_le
    (M N : ℕ) (hMN : M ≤ N) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ 1 f) (hper : AVenhance.IsZ2Periodic f) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus f))‖ ^ 2 ≤
      (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  let mem := memLp_periodicToTorus_real hf.continuous hper
  let v : ScalarTorusL2 := mem.toLp (AVenhance.Infra.Torus.periodicToTorus f)
  have hv : v = mem.toLp (AVenhance.Infra.Torus.periodicToTorus f) := rfl
  have hcoeff (K : ℕ) :
      realFourierProjectionCoefficients K v =
        modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus f) := by
    ext i
    simp only [realFourierProjectionCoefficients, modeProjectionCoefficients,
      PiLp.toLp_apply]
    apply integral_congr_ae
    filter_upwards [mem.coeFn_toLp] with x hx
    rw [hx]
  have hcomplex : Complex.ofRealCLM.compLp v =
      AVenhance.Infra.Torus.periodicToTorusL2
        (AVenhance.Infra.Torus.realToComplex f)
        (Complex.ofRealCLM.contDiff.comp hf).continuous := by
    apply Lp.ext
    filter_upwards [Complex.ofRealCLM.coeFn_compLp v,
      mem.coeFn_toLp,
      (AVenhance.Infra.Torus.memLp_periodicToTorus
        ((Complex.ofRealCLM.contDiff.comp hf).continuous)).coeFn_toLp] with x hcast hreal hsource
    calc
      (Complex.ofRealCLM.compLp v) x = Complex.ofRealCLM (v x) := hcast
      _ = (Complex.ofRealCLM ((AVenhance.Infra.Torus.periodicToTorus f) x)) := by rw [hreal]
      _ = (AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.Infra.Torus.realToComplex f)) x := by rfl
      _ = (AVenhance.Infra.Torus.periodicToTorusL2
          (AVenhance.Infra.Torus.realToComplex f)
          (Complex.ofRealCLM.contDiff.comp hf).continuous) x := hsource.symm
  have henergy := AVenhance.Infra.Heat.hasFiniteFourierEnergy_realSmooth hf hper
  have hfinite : Heat.HasFiniteFourierEnergy (Complex.ofRealCLM.compLp v) := by
    rw [hcomplex]
    exact henergy.1
  have htail := realFourierProjectionCoefficients_tail_norm_sq_le M N hMN v hfinite
  rw [hcoeff N, hcoeff M] at htail
  rw [hcomplex, henergy.2] at htail
  exact htail

/-- A smooth projection tail has norm bounded by the square root of its Dirichlet-energy tail. -/
theorem classicalSmoothProjection_tail_norm_le
    (M N : ℕ) (hMN : M ≤ N) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ 1 f) (hper : AVenhance.IsZ2Periodic f) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus f))‖ ≤
      Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        AVenhance.gradNormSq (AVenhance.spaceGrad f)) := by
  have hsq := classicalSmoothProjection_tail_norm_sq_le M N hMN f hf hper
  have hnonneg : 0 ≤ (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
      AVenhance.gradNormSq (AVenhance.spaceGrad f) :=
    le_trans (sq_nonneg _) hsq
  have hsqrt : Real.sqrt (‖modeProjectionCoefficients
      (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus f) -
      realFourierCoefficientsLift hMN
        (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus f))‖ ^ 2) ≤
      Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        AVenhance.gradNormSq (AVenhance.spaceGrad f)) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hsqrt
  exact hsqrt

/-- Uniform bounds for all finite Fourier projections pass to the full torus `L²` norm. -/
theorem classicalL2_norm_le_of_all_projection_bounds
    (v : ScalarTorusL2) {B : ℝ}
    (hproj : ∀ N, ‖realFourierProjectionCoefficients N v‖ ≤ B) :
    ‖v‖ ≤ B := by
  have hlim := tendsto_realFourierProjection v
  have hnorm : Tendsto
      (fun N => ‖realFourierScalarMap N (realFourierProjectionCoefficients N v)‖)
      atTop (𝓝 ‖v‖) := by
    exact (continuous_norm.continuousAt.tendsto).comp hlim
  apply le_of_tendsto hnorm
  filter_upwards with N
  simpa only [realFourierScalarMap_norm] using hproj N

/-- Uniform bounds for all scalar Fourier projections of each derivative component bound the
full Dirichlet energy of a smooth periodic function. -/
theorem classicalSmoothSource_gradient_energy_le_of_projection_bounds
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ 1 f)
    (hper : AVenhance.IsZ2Periodic f) {B : ℝ} (hB : 0 ≤ B)
    (hproj : ∀ i K,
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad f x i))‖ ≤ B) :
    AVenhance.gradNormSq (AVenhance.spaceGrad f) ≤ 2 * B ^ 2 := by
  let g (i : Fin 2) : Vec 2 → ℝ := fun x => AVenhance.spaceGrad f x i
  let v (i : Fin 2) : ScalarTorusL2 :=
    (memLp_periodicToTorus_real (GalerkinResidual.continuous_spaceGrad_component hf i)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).toLp
      (AVenhance.Infra.Torus.periodicToTorus (g i))
  have hvproj (i : Fin 2) (K : ℕ) :
      realFourierProjectionCoefficients K (v i) =
        modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus (g i)) := by
    unfold realFourierProjectionCoefficients
    ext m
    simp only [modeProjectionCoefficients, PiLp.toLp_apply]
    apply integral_congr_ae
    filter_upwards [(memLp_periodicToTorus_real
      (GalerkinResidual.continuous_spaceGrad_component hf i)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).coeFn_toLp] with x hx
    rw [hx]
  have hvbound (i : Fin 2) : ‖v i‖ ≤ B := by
    apply classicalL2_norm_le_of_all_projection_bounds
    intro K
    rw [hvproj]
    simpa [g] using hproj i K
  have hcomponent (i : Fin 2) :
      ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 ≤ B ^ 2 := by
    have hnorm := AVenhance.Infra.Parabolic.FourierGalerkin.l2_norm_sq_eq_integral_sq (v i)
    have hcell : (∫ x : Torus, ‖v i x‖ ^ 2) =
        ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
      calc
        (∫ x : Torus, ‖v i x‖ ^ 2) =
            ∫ x : Torus,
              ‖AVenhance.Infra.Torus.periodicToTorus (g i) x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [(memLp_periodicToTorus_real
            (GalerkinResidual.continuous_spaceGrad_component hf i)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).coeFn_toLp]
            with x hx
          rw [show (v i) x =
            ((memLp_periodicToTorus_real
              (GalerkinResidual.continuous_spaceGrad_component hf i)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).toLp
              (AVenhance.Infra.Torus.periodicToTorus (g i))) x by rfl, hx]
        _ = ∫ x : Torus,
            AVenhance.Infra.Torus.periodicToTorus (fun y : Vec 2 => (g i y) ^ 2) x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [AVenhance.Infra.Torus.periodicToTorus]
        _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, (g i x) ^ 2 :=
          AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _
        _ = ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
          rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
    calc
      ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 = ‖v i‖ ^ 2 := by
        rw [← hcell, ← hnorm]
      _ ≤ B ^ 2 := by nlinarith [hvbound i, norm_nonneg (v i), hB]
  have hgradIdent :
      (∑ i : Fin 2, ∫ x in AVenhance.unitCube,
        (AVenhance.spaceGrad f x i) ^ 2) =
        AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
    let fc : Vec 2 → ℂ := AVenhance.Infra.Torus.realToComplex f
    have hfc : ContDiff ℝ 1 fc := Complex.ofRealCLM.contDiff.comp hf
    have hsum := AVenhance.Infra.Torus.integral_unitCell_gradSq_eq_sum_coord hfc
    have hcoord (i : Fin 2) (x : Vec 2) :
        AVenhance.Infra.Torus.coordDeriv i fc x =
          (AVenhance.spaceGrad f x i : ℂ) :=
      AVenhance.Infra.Torus.coordDeriv_realToComplex hf i x
    calc
      (∑ i : Fin 2, ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x i) ^ 2) =
          ∑ i : Fin 2, ∫ x in AVenhance.Infra.Torus.unitCell 2,
            ‖AVenhance.Infra.Torus.coordDeriv i fc x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
        apply setIntegral_congr_ae
          (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x _hx
        rw [hcoord]
        simp
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          ∑ i : Fin 2, ‖AVenhance.Infra.Torus.coordDeriv i fc x‖ ^ 2 := hsum
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) := by
        apply setIntegral_congr_ae
          (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x _hx
        simp [Homogenization.vecNormSq, Homogenization.vecDot, hcoord, pow_two]
      _ = ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) :=
        AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _
      _ = AVenhance.gradNormSq (AVenhance.spaceGrad f) := rfl
  calc
    AVenhance.gradNormSq (AVenhance.spaceGrad f) =
        ∑ i : Fin 2, ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x i) ^ 2 := hgradIdent.symm
    _ ≤ ∑ _i : Fin 2, B ^ 2 := Finset.sum_le_sum fun i hi => hcomponent i
    _ = 2 * B ^ 2 := by norm_num

/-- Projection of a bounded multiplier times a finite Fourier synthesis is controlled for every
target cutoff, including cutoffs larger than the synthesis space. -/
theorem classicalRealFourierProduct_projection_norm_le (K N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (f : Vec 2 → ℝ)
    (hf : Continuous f) {_B : ℝ} (_hB : 0 ≤ _B)
    (hbound : ∀ x, ‖f x‖ ≤ _B) :
    ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
      (AVenhance.Infra.Torus.periodicToTorus
        (fun x => f x * realFourierModeAmbientExpansion N c x))‖ ≤ _B * ‖c‖ := by
  let u := realFourierModeAmbientExpansion N c
  let gt := AVenhance.Infra.Torus.periodicToTorus u
  let q := AVenhance.Infra.Torus.periodicToTorus (fun x => f x * u x)
  have hu : Continuous u := (realFourierModeAmbientExpansion_contDiff N c).continuous
  have hgt : MemLp gt 2 (volume : Measure Torus) := by
    apply (Lp.memLp (realFourierScalarMap N c)).congr_norm
      (hu.measurable.comp
        (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)).aestronglyMeasurable
    filter_upwards [realFourierScalarMap_coeFn N c] with x hx
    rw [hx]
    exact congrArg norm
      (congrFun (realFourierModeFin_expansion_eq_periodicToTorus N c) x)
  have hqmeas : Measurable q :=
    (hf.mul hu).measurable.comp
      (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
  have hboundT : ∀ᵐ x : Torus,
      ‖AVenhance.Infra.Torus.periodicToTorus f x‖ ≤ _B := by
    filter_upwards with x
    exact hbound (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
  have hqpoint : ∀ᵐ x : Torus, ‖q x‖ ≤ _B * ‖gt x‖ := by
    filter_upwards [hboundT] with x hx
    rw [show q x =
      AVenhance.Infra.Torus.periodicToTorus f x * gt x by rfl, norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hqmem : MemLp q 2 (volume : Measure Torus) :=
    MemLp.of_le_mul hgt hqmeas.aestronglyMeasurable hqpoint
  have hqnorm : ‖hqmem.toLp q‖ ≤ _B * ‖hgt.toLp gt‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hqmem.coeFn_toLp, hgt.coeFn_toLp, hqpoint] with x hq hg h
    rw [hq, hg]
    exact h
  have hgtLp : hgt.toLp gt = realFourierScalarMap N c := by
    apply Lp.ext
    filter_upwards [hgt.coeFn_toLp, realFourierScalarMap_coeFn N c] with x hgtx hmap
    calc
      (hgt.toLp gt) x = gt x := hgtx
      _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x := by
        exact (realFourierModeFin_expansion_eq_periodicToTorus N c).symm ▸ rfl
      _ = (realFourierScalarMap N c) x := hmap.symm
  calc
    ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K) q‖ ≤
        ‖hqmem.toLp q‖ :=
      realFourierModeFin_projectionCoefficients_norm_le K hqmem
    _ ≤ _B * ‖hgt.toLp gt‖ := hqnorm
    _ = _B * ‖c‖ := by rw [hgtLp, realFourierScalarMap_norm]

theorem GalerkinResidual.classicalWordDerivative_periodic_for_residual (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

/-- The first spatial derivative of the finite-dimensional transport term has a uniform
projection bound controlled by the first two derivative levels of the coefficient vector. -/
theorem classicalTransportDerivative_projection_norm_le
    (K N : ℕ) (b : Vec 2 → Vec 2) (c : Coefficients (RealFourierDimension N))
    (i : Fin 2) {B : ℝ} (hB : 0 ≤ B)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbp : AVenhance.IsZ2Periodic b)
    (hDb : ∀ w, w.length ≤ 1 → ∀ j x,
      ‖classicalWordDerivative w (fun y => b y j) x‖ ≤ B) :
    ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
      (AVenhance.Infra.Torus.periodicToTorus
        (classicalWordDerivative [i]
          (classicalTransport b (realFourierModeAmbientExpansion N c))))‖ ≤
      B * (‖realFourierWordDerivativeMap N [0, i] c‖ +
        ‖realFourierWordDerivativeMap N [1, i] c‖ +
        ‖realFourierWordDerivativeMap N [0] c‖ +
        ‖realFourierWordDerivativeMap N [1] c‖) := by
  let u := realFourierModeAmbientExpansion N c
  let term0 : Fin 2 → Vec 2 → ℝ := fun j x =>
    b x j * classicalWordDerivative (j :: [i]) u x
  let term1 : Fin 2 → Vec 2 → ℝ := fun j x =>
    AVenhance.spaceGrad (fun y => b y j) x i *
      classicalWordDerivative [j] u x
  let terms : List (Vec 2 → ℝ) := [term0 0, term0 1, term1 0, term1 1]
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hbcomp (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x j) :=
    (contDiff_pi.1 hb) j
  have hbper (j : Fin 2) : AVenhance.IsZ2Periodic (fun x => b x j) := by
    intro k x
    exact congrFun (hbp k x) j
  have hdbcont (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad (fun y => b y j) x i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun y => b y j) x (Homogenization.basisVec i))
    exact ((hbcomp j).fderiv_right (by simp)).clm_apply contDiff_const
  have hdbper (j : Fin 2) : AVenhance.IsZ2Periodic
      (fun x => AVenhance.spaceGrad (fun y => b y j) x i) :=
    AVenhance.Infra.Classical.periodic_spaceGrad_component (hbper j) i
  have hterm0Cont (j : Fin 2) : Continuous (term0 j) := by
    exact ((hbcomp j).mul
      (classicalWordDerivative_contDiff (j :: [i]) u hu)).continuous
  have hterm1Cont (j : Fin 2) : Continuous (term1 j) := by
    exact ((hdbcont j).mul (classicalWordDerivative_contDiff [j] u hu)).continuous
  have hterm0Per (j : Fin 2) : AVenhance.IsZ2Periodic (term0 j) := by
    intro k x
    change b (x + AVenhance.latticeShift k) j *
        classicalWordDerivative (j :: [i]) u (x + AVenhance.latticeShift k) =
      b x j * classicalWordDerivative (j :: [i]) u x
    have hbs := congrFun (hbp k x) j
    rw [hbs,
      GalerkinResidual.classicalWordDerivative_periodic_for_residual (j :: [i]) u hup k x]
  have hterm1Per (j : Fin 2) : AVenhance.IsZ2Periodic (term1 j) := by
    intro k x
    change AVenhance.spaceGrad (fun y => b y j) (x + AVenhance.latticeShift k) i *
        classicalWordDerivative [j] u (x + AVenhance.latticeShift k) =
      AVenhance.spaceGrad (fun y => b y j) x i * classicalWordDerivative [j] u x
    have hdbs : AVenhance.spaceGrad (fun y => b y j)
        (x + AVenhance.latticeShift k) i =
          AVenhance.spaceGrad (fun y => b y j) x i := hdbper j k x
    rw [hdbs,
      GalerkinResidual.classicalWordDerivative_periodic_for_residual [j] u hup k x]
  have htermListCont : ∀ f ∈ terms, Continuous f := by
    intro f hf'
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl
    · exact hterm0Cont 0
    · exact hterm0Cont 1
    · exact hterm1Cont 0
    · exact hterm1Cont 1
  have htermListPer : ∀ f ∈ terms, AVenhance.IsZ2Periodic f := by
    intro f hf'
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl
    · exact hterm0Per 0
    · exact hterm0Per 1
    · exact hterm1Per 0
    · exact hterm1Per 1
  have hrepresentation :
      classicalWordDerivative [i] (classicalTransport b u) = terms.sum := by
    funext x
    have hcomm := classicalTransport_firstCommutator b u hb hu i x
    have hprincipal :
        Homogenization.vecDot (b x)
            (AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y i) x) =
          ∑ j : Fin 2, term0 j x := by
      simp [term0, Homogenization.vecDot, classicalWordDerivative]
    have hremainder :
        (∑ j : Fin 2,
          AVenhance.spaceGrad (fun y => b y j) x i *
            AVenhance.spaceGrad u x j) = ∑ j : Fin 2, term1 j x := by
      simp [term1, classicalWordDerivative]
    have hderiv := sub_eq_iff_eq_add.mp hcomm
    rw [hprincipal, hremainder] at hderiv
    simp only [Fin.sum_univ_two] at hderiv
    simp [term0, term1, classicalWordDerivative, terms] at hderiv ⊢
    linear_combination hderiv
  have hlistRaw := realFourierProjectionCoefficients_listSum_norm_le K terms
    htermListCont htermListPer
  rw [hrepresentation.symm] at hlistRaw
  have hproduct0 (j : Fin 2) :
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus (term0 j))‖ ≤
        B * ‖realFourierWordDerivativeMap N (j :: [i]) c‖ := by
    have hcoeff : classicalWordDerivative (j :: [i]) u =
        realFourierModeAmbientExpansion N
          (realFourierWordDerivativeCoefficients N c (j :: [i])) :=
      classicalWordDerivative_realFourierModeAmbientExpansion N (j :: [i]) c
    have hmul := classicalRealFourierProduct_projection_norm_le K N
      (realFourierWordDerivativeCoefficients N c (j :: [i])) (fun x => b x j)
      (hbcomp j).continuous hB (fun x => by
        simpa [classicalWordDerivative] using hDb [] (by simp) j x)
    have htermEq : term0 j = fun x => b x j *
        realFourierModeAmbientExpansion N
          (realFourierWordDerivativeCoefficients N c (j :: [i])) x := by
      funext x
      simp only [term0]
      rw [hcoeff]
    rw [htermEq]
    simpa [realFourierWordDerivativeMap_apply] using hmul
  have hproduct1 (j : Fin 2) :
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus (term1 j))‖ ≤
        B * ‖realFourierWordDerivativeMap N [j] c‖ := by
    have hcoeff : classicalWordDerivative [j] u =
        realFourierModeAmbientExpansion N
          (realFourierWordDerivativeCoefficients N c [j]) :=
      classicalWordDerivative_realFourierModeAmbientExpansion N [j] c
    have hmul := classicalRealFourierProduct_projection_norm_le K N
      (realFourierWordDerivativeCoefficients N c [j])
      (fun x => AVenhance.spaceGrad (fun y => b y j) x i)
      (hdbcont j).continuous hB (fun x => by
        simpa [classicalWordDerivative] using hDb [i] (by simp) j x)
    have htermEq : term1 j = fun x =>
        AVenhance.spaceGrad (fun y => b y j) x i *
          realFourierModeAmbientExpansion N
            (realFourierWordDerivativeCoefficients N c [j]) x := by
      funext x
      simp only [term1]
      rw [hcoeff]
    rw [htermEq]
    simpa [realFourierWordDerivativeMap_apply] using hmul
  calc
    ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordDerivative [i] (classicalTransport b u)))‖ ≤
        (terms.map fun f =>
          ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
            (AVenhance.Infra.Torus.periodicToTorus f)‖).sum := hlistRaw
    _ = ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus (term0 0))‖ +
        ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus (term0 1))‖ +
        ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus (term1 0))‖ +
        ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus (term1 1))‖ := by
          simp [terms]
          ring
    _ ≤ B * ‖realFourierWordDerivativeMap N (0 :: [i]) c‖ +
        B * ‖realFourierWordDerivativeMap N (1 :: [i]) c‖ +
        B * ‖realFourierWordDerivativeMap N [0] c‖ +
        B * ‖realFourierWordDerivativeMap N [1] c‖ := by
      have h00 := hproduct0 0
      have h01 := hproduct0 1
      have h10 := hproduct1 0
      have h11 := hproduct1 1
      linarith
    _ = B * (‖realFourierWordDerivativeMap N [0, i] c‖ +
        ‖realFourierWordDerivativeMap N [1, i] c‖ +
        ‖realFourierWordDerivativeMap N [0] c‖ +
        ‖realFourierWordDerivativeMap N [1] c‖) := by ring_nf

end AVenhance.Infra.Classical

end
