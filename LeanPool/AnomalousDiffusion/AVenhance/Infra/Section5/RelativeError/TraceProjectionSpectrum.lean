/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceAveraging
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTraceGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPairingIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTestSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ClassicalEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-! # Fourier spectral facts for the finite radial cutoff -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraSection5RelativeErrorTraceProjectionSpectrumMeasureSpace1 : MeasureSpace
    UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraSection5RelativeErrorTraceProjectionSpectrumMeasureIsAddHaarMeasure2 :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraSection5RelativeErrorTraceProjectionSpectrumIsProbabilityMeasure3 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Torus
open AVenhance.Infra.Ergodic

theorem TraceProjectionSpectrum.periodicL2FourierCoeff_smooth
    {f : Vec 2 → ℂ} (hf : Continuous f) (k : Fin 2 → ℤ) :
    periodicL2FourierCoeff (periodicToTorusL2 f hf) k = smoothFourierCoeff f k := by
  let hmem := memLp_periodicToTorus hf
  calc
    periodicL2FourierCoeff (periodicToTorusL2 f hf) k =
        ∫ y : UnitAddTorus (Fin 2),
          UnitAddTorus.mFourier (-k) y * periodicToTorus f y := by
      unfold periodicL2FourierCoeff UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with y hy
      exact congrArg (fun z : ℂ => UnitAddTorus.mFourier (-k) y * z) hy
    _ = ∫ x in unitCell 2, torusCharacter k x * f x := by
      rw [← integral_periodicToTorus_eq_unitCell
        (fun x : Vec 2 => torusCharacter k x * f x)]
      apply integral_congr_ae
      filter_upwards with y
      change UnitAddTorus.mFourier (-k) y * f (unitTorusRepresentative 2 y) =
        torusCharacter k (unitTorusRepresentative 2 y) *
          f (unitTorusRepresentative 2 y)
      rw [torusCharacter, toUnitTorus_unitTorusRepresentative]

theorem TraceProjectionSpectrum.smoothFourier_inner_hasSum
    {f g : Vec 2 → ℂ} (hf : Continuous f) (hg : Continuous g) :
    HasSum (fun k : Fin 2 → ℤ =>
      star (smoothFourierCoeff f k) * smoothFourierCoeff g k)
      (∫ x in unitCell 2, star (f x) * g x) := by
  let F := periodicToTorusL2 f hf
  let G := periodicToTorusL2 g hg
  have htorus := UnitAddTorus.hasSum_prod_mFourierCoeff F G
  have hcoeffF (k : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff (↑F) k = smoothFourierCoeff f k := by
    change periodicL2FourierCoeff F k = _
    exact TraceProjectionSpectrum.periodicL2FourierCoeff_smooth hf k
  have hcoeffG (k : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff (↑G) k = smoothFourierCoeff g k := by
    change periodicL2FourierCoeff G k = _
    exact TraceProjectionSpectrum.periodicL2FourierCoeff_smooth hg k
  have hsum := htorus.congr_fun (fun k => by
    rw [hcoeffF k, hcoeffG k])
  have hlimit :
      (∫ y : UnitAddTorus (Fin 2), star (F y) * G y) =
        ∫ x in unitCell 2, star (f x) * g x := by
    have hF := (memLp_periodicToTorus hf).coeFn_toLp
    have hG := (memLp_periodicToTorus hg).coeFn_toLp
    calc
      (∫ y : UnitAddTorus (Fin 2), star (F y) * G y) =
          ∫ y, star (periodicToTorus f y) * periodicToTorus g y := by
            apply integral_congr_ae
            filter_upwards [hF, hG] with y hfy hgy
            have hfy' : F y = periodicToTorus f y := by
              simpa [F, periodicToTorusL2] using hfy
            have hgy' : G y = periodicToTorus g y := by
              simpa [G, periodicToTorusL2] using hgy
            rw [hfy', hgy']
      _ = ∫ x in unitCell 2, star (f x) * g x := by
        rw [← integral_periodicToTorus_eq_unitCell
          (fun x : Vec 2 => star (f x) * g x)]
        apply integral_congr_ae
        filter_upwards with y
        rfl
  rw [← hlimit]
  exact hsum

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def TraceProjectionSpectrum.closedUnitCell (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem TraceProjectionSpectrum.continuous_integrableOn_complex_unitCell
    {f : Vec 2 → ℂ} (hf : Continuous f) :
    IntegrableOn f (unitCell 2) := by
  have hc : IsCompact (TraceProjectionSpectrum.closedUnitCell 2) := by
    simpa [TraceProjectionSpectrum.closedUnitCell] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  have hs : unitCell 2 ⊆ TraceProjectionSpectrum.closedUnitCell 2 := by
    intro x hx
    simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
    simp only [TraceProjectionSpectrum.closedUnitCell, Set.mem_pi]
    intro i hi
    exact ⟨le_of_lt (hx i).1, hx i |>.2⟩
  exact hf.continuousOn.integrableOn_compact hc |>.mono_set hs

theorem TraceProjectionSpectrum.smoothFourierCoeff_finsetSum
    {ι : Type*} (s : Finset ι) (f : ι → Vec 2 → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun x => ∑ i ∈ s, f i x) k =
      ∑ i ∈ s, smoothFourierCoeff (f i) k := by
  classical
  unfold smoothFourierCoeff
  change (∫ x, torusCharacter k x *
      (∑ i ∈ s, f i x) ∂(volume.restrict (unitCell 2))) = _
  have hsumPoint : (fun x => torusCharacter k x *
      (∑ i ∈ s, f i x)) =
      fun x => ∑ i ∈ s, torusCharacter k x * f i x := by
    funext x
    rw [Finset.mul_sum]
  rw [hsumPoint, integral_finsetSum]
  · intro i hi
    exact TraceProjectionSpectrum.continuous_integrableOn_complex_unitCell
      ((torusCharacter_contDiff k).continuous.mul (hf i hi))

theorem TraceProjectionSpectrum.smoothFourierCoeff_neg
  {f : Vec 2 → ℂ} (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun x => -f x) k =
      -smoothFourierCoeff f k := by
  unfold smoothFourierCoeff
  calc
    (∫ x in unitCell 2, torusCharacter k x * -f x) =
        ∫ x in unitCell 2, -(torusCharacter k x * f x) := by
          apply setIntegral_congr_fun (measurableSet_unitCell 2)
          intro x hx
          ring
    _ = -∫ x in unitCell 2, torusCharacter k x * f x := by
      rw [integral_neg]

theorem TraceProjectionSpectrum.spaceGrad_component_contDiff
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 3 f) (i : Fin 2) :
    ContDiff ℝ 2 (fun x => spaceGrad f x i) := by
  change ContDiff ℝ 2 (fun x => fderiv ℝ f x (basisVec i))
  exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem TraceProjectionSpectrum.negativeSpaceLap_fourierCoeff
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 3 f)
    (hper : IsZ2Periodic f) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (realToComplex (fun x => -spaceLap f x)) k =
      (4 * Real.pi ^ 2) * (∑ i : Fin 2, (k i : ℝ) ^ 2) *
        smoothFourierCoeff (realToComplex f) k := by
  let F : Vec 2 → ℂ := realToComplex f
  have hF : ContDiff ℝ 3 F := Complex.ofRealCLM.contDiff.comp hf
  have hFper : IsZdPeriodic F := by
    intro z x
    exact congrArg Complex.ofReal ((isZdPeriodic_iff_frozen f).2 hper z x)
  have hsecond (i : Fin 2) :
      smoothFourierCoeff (coordDeriv i (coordDeriv i F)) k =
        -((4 * Real.pi ^ 2) * (k i : ℝ) ^ 2) *
          smoothFourierCoeff F k := by
    have hi1 := smoothFourierCoeff_coordDeriv i
      (hF.of_le (by norm_num)) hFper k
    have hDi : ContDiff ℝ 2 (coordDeriv i F) := by
      change ContDiff ℝ 2
        (fun x => fderiv ℝ F x (basisVec i))
      exact (hF.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hDper : IsZdPeriodic (coordDeriv i F) := by
      intro z x
      rw [coordDeriv_realToComplex (hf.of_le (by norm_num)) i (x + intVector z),
        coordDeriv_realToComplex (hf.of_le (by norm_num)) i x]
      exact congrArg Complex.ofReal
        (Infra.Classical.periodic_spaceGrad_component hper i z x)
    have hi2 := smoothFourierCoeff_coordDeriv i
      (hDi.of_le (by norm_num)) hDper k
    rw [hi1] at hi2
    have hmul :
        (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 =
          (-((4 * Real.pi ^ 2) * (k i : ℝ) ^ 2) : ℂ) := by
      calc
        (2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2 =
            (2 * Real.pi : ℂ) ^ 2 * Complex.I ^ 2 *
              (k i : ℂ) ^ 2 := by ring
        _ = -((2 * Real.pi : ℂ) ^ 2 * (k i : ℂ) ^ 2) := by
          rw [Complex.I_sq]
          ring
        _ = (-((4 * Real.pi ^ 2) * (k i : ℝ) ^ 2) : ℂ) := by
          push_cast
          ring
    calc
      smoothFourierCoeff (coordDeriv i (coordDeriv i F)) k =
          ((2 * Real.pi * Complex.I * (k i : ℂ)) ^ 2) *
            smoothFourierCoeff F k := by
              rw [hi2]
              ring
      _ = _ := by rw [hmul]
  have hgradComponent (i : Fin 2) :
      coordDeriv i F =
        realToComplex (fun x => spaceGrad f x i) := by
    funext x
    exact coordDeriv_realToComplex (hf.of_le (by norm_num)) i x
  have hsecondReal (i : Fin 2) :
      coordDeriv i (coordDeriv i F) =
        realToComplex (fun x => spaceGrad
          (fun y => spaceGrad f y i) x i) := by
    rw [hgradComponent i]
    funext x
    exact coordDeriv_realToComplex
      ((TraceProjectionSpectrum.spaceGrad_component_contDiff hf i).of_le (by norm_num)) i x
  have hsumLap :
      (fun x => realToComplex (fun y => -spaceLap f y) x) =
        fun x => ∑ i : Fin 2,
          -(coordDeriv i (coordDeriv i F) x) := by
    funext x
    change ((-∑ i : Fin 2, spaceGrad
      (fun y => spaceGrad f y i) x i : ℝ) : ℂ) = _
    rw [Complex.ofReal_neg, Complex.ofReal_sum]
    calc
      -(∑ i : Fin 2,
          ((spaceGrad (fun y => spaceGrad f y i) x i : ℝ) : ℂ)) =
          ∑ i : Fin 2,
            -((spaceGrad (fun y => spaceGrad f y i) x i : ℂ)) := by
        rw [Finset.sum_neg_distrib]
      _ = ∑ i : Fin 2, -(coordDeriv i (coordDeriv i F) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := congrFun (hsecondReal i) x
        change coordDeriv i (coordDeriv i F) x =
          ((spaceGrad (fun y => spaceGrad f y i) x i : ℝ) : ℂ) at h
        exact congrArg (fun z : ℂ => -z) h.symm
  have hsecondComponent_contDiff (i : Fin 2) :
      ContDiff ℝ 1 (fun x => spaceGrad
        (fun y => spaceGrad f y i) x i) := by
    change ContDiff ℝ 1 (fun x => fderiv ℝ
      (fun y => spaceGrad f y i) x (basisVec i))
    exact ((TraceProjectionSpectrum.spaceGrad_component_contDiff hf i).fderiv_right
      (by norm_num)).clm_apply contDiff_const
  have hcoeffSum := TraceProjectionSpectrum.smoothFourierCoeff_finsetSum Finset.univ
    (fun i x => -coordDeriv i (coordDeriv i F) x)
    (by intro i hi
        rw [hsecondReal i]
        exact (Complex.ofRealCLM.contDiff.comp
          (hsecondComponent_contDiff i)).continuous.neg) k
  calc
    smoothFourierCoeff (realToComplex (fun x => -spaceLap f x)) k =
        smoothFourierCoeff
          (fun x => ∑ i : Fin 2,
            -coordDeriv i (coordDeriv i F) x) k :=
      congrArg (fun q => smoothFourierCoeff q k) hsumLap
    _ = ∑ i : Fin 2,
        smoothFourierCoeff (fun x =>
          -coordDeriv i (coordDeriv i F) x) k := hcoeffSum
    _ = (4 * Real.pi ^ 2) *
        (∑ i : Fin 2, (k i : ℝ) ^ 2) *
          smoothFourierCoeff (realToComplex f) k := by
      simp_rw [TraceProjectionSpectrum.smoothFourierCoeff_neg, hsecond]
      simp only [neg_mul, neg_neg]
      simp only [Fin.sum_univ_two]
      simp only [F]
      push_cast
      ring

theorem TraceProjectionSpectrum.normSq_fourierMultiplier (m : ℤ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (m : ℂ)) * z‖ ^ 2 =
      (4 * Real.pi ^ 2) * (m : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Real.abs_pi,
    Complex.norm_I, mul_one, Complex.norm_intCast]
  calc
    (2 * Real.pi * |(m : ℝ)| * ‖z‖) ^ 2 =
        (2 * Real.pi) ^ 2 * |(m : ℝ)| ^ 2 * ‖z‖ ^ 2 := by ring
    _ = (4 * Real.pi ^ 2) * (m : ℝ) ^ 2 * ‖z‖ ^ 2 := by
      rw [sq_abs]
      ring

theorem TraceProjectionSpectrum.gradientFourierTerm_eq_frequency
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hper : IsZ2Periodic f) (k : Fin 2 → ℤ) :
    (∑ i : Fin 2, ‖smoothFourierCoeff
      (coordDeriv i (realToComplex f)) k‖ ^ 2) =
      (4 * Real.pi ^ 2) * (∑ i : Fin 2, (k i : ℝ) ^ 2) *
        ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2 := by
  calc
    _ = ∑ i : Fin 2,
        (4 * Real.pi ^ 2) * (k i : ℝ) ^ 2 *
          ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      change ‖smoothFourierCoeff
          (coordDeriv i (Complex.ofRealCLM ∘ f)) k‖ ^ 2 =
        (4 * Real.pi ^ 2) * (k i : ℝ) ^ 2 *
          ‖smoothFourierCoeff (Complex.ofRealCLM ∘ f) k‖ ^ 2
      rw [smoothFourierCoeff_coordDeriv i
        (Complex.ofRealCLM.contDiff.comp hf) (by
          intro z x
          exact congrArg Complex.ofReal
            ((isZdPeriodic_iff_frozen f).2 hper z x))]
      exact TraceProjectionSpectrum.normSq_fourierMultiplier _ _
    _ = _ := by
      simp only [Fin.sum_univ_two]
      ring

/-- The initial pairing against the negative Laplacian of the radial
Fourier cutoff is exactly the squared gradient norm of that cutoff. -/
theorem lowProjection_initialPairing_eq_gradientEnergy
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ 3 g)
    (hper : IsZ2Periodic g) (M : ℕ) :
    (∫ x in unitCell 2, g x * -spaceLap (lowProjection g M) x) =
      gradNormSq (spaceGrad (lowProjection g M)) := by
  let f : Vec 2 → ℝ := lowProjection g M
  let a : (Fin 2 → ℤ) → ℂ :=
    fun k => smoothFourierCoeff (realToComplex g) k
  have hf : ContDiff ℝ 3 f := by
    exact lowProjection_contDiff M |>.of_le (by norm_num)
  have hfpZ : IsZPeriodic (lowProjection g M) :=
    lowProjection_periodic (f := g) M
  have hfp : IsZ2Periodic f := by
    exact (isZPeriodic_iff_isZ2Periodic f).1 (by
      simpa [f] using hfpZ)
  have hgC : ContDiff ℝ 3 (realToComplex g) :=
    Complex.ofRealCLM.contDiff.comp hg
  have hgpC : IsZdPeriodic (realToComplex g) := by
    intro z x
    exact congrArg Complex.ofReal ((isZdPeriodic_iff_frozen g).2 hper z x)
  have hfC : ContDiff ℝ 3 (realToComplex f) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hfpC : IsZdPeriodic (realToComplex f) := by
    intro z x
    exact congrArg Complex.ofReal ((isZdPeriodic_iff_frozen f).2 hfp z x)
  have hlowCoeff (k : Fin 2 → ℤ) :
      smoothFourierCoeff (realToComplex f) k =
        if k ∈ frequencyBall M then a k else 0 := by
    exact smoothFourierCoeff_euclideanCutoff M a
      (smoothFourierCoeff_real_neg (f := g)) k
  have hlapSmooth : ContDiff ℝ 1
      (fun x => -spaceLap f x) :=
    contDiff_neg.comp (classicalSpaceLap_contDiff_three hf)
  have hlapPer : IsZ2Periodic (fun x => -spaceLap f x) := by
    intro z x
    simp [classicalSpaceLap_periodic hfp z x]
  have hcross := TraceProjectionSpectrum.smoothFourier_inner_hasSum
    ((Complex.ofRealCLM.contDiff.comp hg).continuous)
    ((Complex.ofRealCLM.contDiff.comp hlapSmooth).continuous)
  have hgrad := Torus.hasSum_sq_realToComplexGradientFourierCoeff
    (hf.of_le (by norm_num))
  have hgrad' := hgrad.congr_fun (fun k => by
    exact (TraceProjectionSpectrum.gradientFourierTerm_eq_frequency
      (hf.of_le (by norm_num)) hfp k).symm)
  have hcrossTerm (k : Fin 2 → ℤ) :
      star (smoothFourierCoeff (realToComplex g) k) *
        smoothFourierCoeff (realToComplex (fun x => -spaceLap f x)) k =
        Complex.ofRealCLM ((4 * Real.pi ^ 2) *
          (∑ i : Fin 2, (k i : ℝ) ^ 2) *
          ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2) := by
    rw [TraceProjectionSpectrum.negativeSpaceLap_fourierCoeff
      hf
      hfp k]
    rw [hlowCoeff k]
    by_cases hk : k ∈ frequencyBall M
    · simp only [ite_eq_left hk]
      let z : ℂ := smoothFourierCoeff (realToComplex g) k
      change star z * ((4 * Real.pi ^ 2) *
        (∑ i : Fin 2, (k i : ℝ) ^ 2) * z) =
        Complex.ofRealCLM ((4 * Real.pi ^ 2) *
          (∑ i : Fin 2, (k i : ℝ) ^ 2) * ‖z‖ ^ 2)
      calc
        star z * ((4 * Real.pi ^ 2) *
            (∑ i : Fin 2, (k i : ℝ) ^ 2) * z) =
            ((4 * Real.pi ^ 2) *
              (∑ i : Fin 2, (k i : ℝ) ^ 2)) * (star z * z) := by ring
        _ = ((4 * Real.pi ^ 2) *
              (∑ i : Fin 2, (k i : ℝ) ^ 2)) *
                (Complex.normSq z : ℂ) := by
                  congr 1
                  rw [Complex.star_def]
                  exact Complex.normSq_eq_conj_mul_self.symm
        _ = _ := by
          simp [Complex.ofRealCLM_apply, Complex.normSq_eq_norm_sq]
    · simp [hk]
  have hcross' := hcross.congr_fun (fun k => (hcrossTerm k).symm)
  have hgradC := hgrad'.mapL Complex.ofRealCLM
  have hsumEq := hcross'.unique hgradC
  have hpairCast :
      (↑(∫ x in unitCell 2, g x * -spaceLap f x) : ℂ) =
        ∫ x in unitCell 2,
          star (realToComplex g x) *
            realToComplex (fun x => -spaceLap f x) x := by
    symm
    calc
      ∫ x in unitCell 2,
          star (realToComplex g x) *
            realToComplex (fun x => -spaceLap f x) x =
          ∫ x in unitCell 2,
            ((g x * -spaceLap f x : ℝ) : ℂ) := by
              apply setIntegral_congr_fun (measurableSet_unitCell 2)
              intro x hx
              simp [realToComplex]
      _ = (↑(∫ x in unitCell 2, g x * -spaceLap f x) : ℂ) :=
        integral_complex_ofReal
  apply Complex.ofReal_injective
  calc
    (↑(∫ x in unitCell 2, g x * -spaceLap f x) : ℂ) =
        ∫ x in unitCell 2,
          star (realToComplex g x) *
            realToComplex (fun x => -spaceLap f x) x := hpairCast
    _ = (↑(gradNormSq (spaceGrad f)) : ℂ) := hsumEq
    _ = _ := by rfl

/-- The square cutoff `lowProjection g M` has Euclidean Fourier support in
the ball of radius `2π√2 M`. Consequently its differentiated negative
Laplacian costs at most the square of that spectral radius. -/
theorem lowProjection_laplacianGradient_energy_le
    {g : Vec 2 → ℝ} (M : ℕ) :
    (∫ x in unitCell 2,
      vecNormSq (spaceGrad (fun y => -spaceLap (lowProjection g M) y) x)) ≤
      (2 * Real.pi * Real.sqrt 2 * (M : ℝ)) ^ 4 *
        gradNormSq (spaceGrad (lowProjection g M)) := by
  let f : Vec 2 → ℝ := lowProjection g M
  let q : Vec 2 → ℝ := fun x => -spaceLap f x
  let K : ℝ := 2 * Real.pi * Real.sqrt 2 * (M : ℝ)
  let multiplier : (Fin 2 → ℤ) → ℝ := fun k =>
    4 * Real.pi ^ 2 * (∑ i : Fin 2, (k i : ℝ) ^ 2)
  have hf : ContDiff ℝ 3 f := by
    exact lowProjection_contDiff M |>.of_le (by norm_num)
  have hfpZ : IsZPeriodic f := by
    simpa [f] using (lowProjection_periodic (f := g) M)
  have hfp : IsZ2Periodic f :=
    (isZPeriodic_iff_isZ2Periodic f).1 hfpZ
  have hq : ContDiff ℝ 1 q := by
    exact contDiff_neg.comp (classicalSpaceLap_contDiff_three hf)
  have hqper : IsZ2Periodic q := by
    intro z x
    simp [q, classicalSpaceLap_periodic hfp z x]
  have hcoeff (k : Fin 2 → ℤ) :
      smoothFourierCoeff (realToComplex q) k =
        multiplier k * smoothFourierCoeff (realToComplex f) k := by
    simpa [q, multiplier] using TraceProjectionSpectrum.negativeSpaceLap_fourierCoeff hf hfp k
  have hlowCoeff (k : Fin 2 → ℤ) :
      smoothFourierCoeff (realToComplex f) k =
        if k ∈ frequencyBall M then
          smoothFourierCoeff (realToComplex g) k else 0 := by
    exact smoothFourierCoeff_euclideanCutoff M
      (fun k => smoothFourierCoeff (realToComplex g) k)
      (smoothFourierCoeff_real_neg (f := g)) k
  have hKsq : K ^ 2 = 8 * Real.pi ^ 2 * (M : ℝ) ^ 2 := by
    dsimp [K]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hmultiplier_nonneg (k : Fin 2 → ℤ) : 0 ≤ multiplier k := by
    dsimp [multiplier]
    positivity
  have hmultiplier_bound (k : Fin 2 → ℤ) (hk : k ∈ frequencyBall M) :
      multiplier k ≤ K ^ 2 := by
    have hnorm := mem_frequencyBall.mp hk
    have hcoord (i : Fin 2) : |(k i : ℝ)| ≤ (M : ℝ) := by
      calc
        |(k i : ℝ)| = ‖(k i : ℝ)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖k‖ := norm_le_pi_norm k i
        _ ≤ (M : ℝ) := hnorm
    have hcoordSq (i : Fin 2) : (k i : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have hcoordNorm : ‖(k i : ℝ)‖ ≤ (M : ℝ) := by
        simpa [Real.norm_eq_abs] using hcoord i
      have hsq := (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg M)).2 hcoordNorm
      simpa [Real.norm_eq_abs] using hsq
    have hsum :
        (∑ i : Fin 2, (k i : ℝ) ^ 2) ≤ 2 * (M : ℝ) ^ 2 := by
      calc
        (∑ i : Fin 2, (k i : ℝ) ^ 2) =
            (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
              simp [Fin.sum_univ_two]
        _ ≤ (M : ℝ) ^ 2 + (M : ℝ) ^ 2 :=
          add_le_add (hcoordSq 0) (hcoordSq 1)
        _ = 2 * (M : ℝ) ^ 2 := by ring
    calc
      multiplier k = 4 * Real.pi ^ 2 *
          (∑ i : Fin 2, (k i : ℝ) ^ 2) := rfl
      _ ≤ 4 * Real.pi ^ 2 * (2 * (M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = K ^ 2 := by rw [hKsq]; ring
  let FTerm : (Fin 2 → ℤ) → ℝ := fun k =>
    ∑ i : Fin 2, ‖smoothFourierCoeff
      (coordDeriv i (realToComplex f)) k‖ ^ 2
  let QTerm : (Fin 2 → ℤ) → ℝ := fun k =>
    ∑ i : Fin 2, ‖smoothFourierCoeff
      (coordDeriv i (realToComplex q)) k‖ ^ 2
  have hterm (k : Fin 2 → ℤ) :
      QTerm k ≤ K ^ 4 * FTerm k := by
    change (∑ i : Fin 2, ‖smoothFourierCoeff
        (coordDeriv i (realToComplex q)) k‖ ^ 2) ≤
      K ^ 4 * (∑ i : Fin 2, ‖smoothFourierCoeff
        (coordDeriv i (realToComplex f)) k‖ ^ 2)
    rw [TraceProjectionSpectrum.gradientFourierTerm_eq_frequency hq hqper k,
      TraceProjectionSpectrum.gradientFourierTerm_eq_frequency (hf.of_le (by norm_num)) hfp k,
          hcoeff]
    by_cases hk : k ∈ frequencyBall M
    · have hmultiplierK := hmultiplier_bound k hk
      have hmultiplierSq : (multiplier k) ^ 2 ≤ (K ^ 2) ^ 2 := by
        exact (sq_le_sq₀ (hmultiplier_nonneg k) (sq_nonneg K)).2 hmultiplierK
      have hnormsq :
          ‖multiplier k * smoothFourierCoeff (realToComplex f) k‖ ^ 2 =
            (multiplier k) ^ 2 *
              ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (hmultiplier_nonneg k)]
        ring
      calc
        multiplier k *
            ‖multiplier k * smoothFourierCoeff (realToComplex f) k‖ ^ 2 =
            (multiplier k) ^ 3 *
              ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2 := by
                rw [hnormsq]
                ring
        _ ≤ ((K ^ 2) ^ 2 * multiplier k) *
              ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                calc
                  (multiplier k) ^ 3 = (multiplier k) ^ 2 * multiplier k := by ring
                  _ ≤ (K ^ 2) ^ 2 * multiplier k :=
                    mul_le_mul_of_nonneg_right hmultiplierSq
                      (hmultiplier_nonneg k)
        _ = K ^ 4 * (multiplier k *
              ‖smoothFourierCoeff (realToComplex f) k‖ ^ 2) := by ring
    · have hz : smoothFourierCoeff (realToComplex f) k = 0 := by
        rw [hlowCoeff k, ite_eq_right hk]
      rw [hz]
      simp
  have hsumF : HasSum FTerm (gradNormSq (spaceGrad f)) := by
    simpa [FTerm] using
      Torus.hasSum_sq_realToComplexGradientFourierCoeff
        (hf.of_le (by norm_num))
  have hsumQ : HasSum QTerm (gradNormSq (spaceGrad q)) := by
    simpa [QTerm] using
      Torus.hasSum_sq_realToComplexGradientFourierCoeff hq
  have hsumScaled := hsumF.mul_left (K ^ 4)
  have hsumLe := hsumQ.summable.tsum_le_tsum hterm hsumScaled.summable
  rw [hsumQ.tsum_eq, hsumScaled.tsum_eq] at hsumLe
  have hcell :
      (∫ x in unitCell 2, vecNormSq (spaceGrad q x)) =
        gradNormSq (spaceGrad q) := by
    rw [integral_unitCell_eq_unitCube]
    rfl
  change (∫ x in unitCell 2, vecNormSq (spaceGrad q x)) ≤
    K ^ 4 * gradNormSq (spaceGrad f)
  calc
    _ = gradNormSq (spaceGrad q) := hcell
    _ ≤ K ^ 4 * gradNormSq (spaceGrad f) := hsumLe

end AVenhance.Infra.Section5.RelativeError

end
