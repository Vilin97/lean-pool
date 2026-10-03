/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarFourierDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TestDensity

/-!
# Smooth periodic spatial tests from the real Fourier identities

The synchronized limit has a common full-measure set of times on which its weak spatial
derivative identity holds for every real Fourier mode. This module begins the density bridge from
those modes to the smooth periodic tests used by the solution predicate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Ergodic
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance testDensityBridgeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance testDensityBridgeMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance testDensityBridgeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance testDensityBridgeProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance avInfraParabolicFourierGalerkinTestDensityBridgeIsFiniteMeasure1 : IsFiniteMeasure
    (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem TestDensityBridge.bridge_continuous_memL2 {f : Vec 2 → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict AVenhance.unitCube) := by
  have h := continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

theorem TestDensityBridge.bridge_pairing_error_bound {g v : Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube)) (hv : Continuous v) :
    |∫ x in AVenhance.unitCube, g x * v x| ≤
      Real.sqrt (AVenhance.l2NormSq g) * Real.sqrt (AVenhance.l2NormSq v) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (f := fun x => |g x|)
    (g := fun x => |v x|) (μ := volume.restrict AVenhance.unitCube)
    Real.HolderConjugate.two_two (ae_of_all _ (fun x => abs_nonneg _))
    (ae_of_all _ (fun x => abs_nonneg _))
    (by simpa [Real.norm_eq_abs] using hg.norm)
    (by simpa [Real.norm_eq_abs] using (TestDensityBridge.bridge_continuous_memL2 hv).norm)
  have h1 : |∫ x in AVenhance.unitCube, g x * v x| ≤
      ∫ x in AVenhance.unitCube, |g x| * |v x| := by
    simpa [Real.norm_eq_abs, abs_mul] using
      norm_integral_le_integral_norm (fun x => g x * v x)
  exact h1.trans (by simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow,
    one_div, AVenhance.l2NormSq] using h)

theorem TestDensityBridge.bridge_gradientCoord_continuous {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem bridge_continuous_integrable_cube {g : Vec 2 → ℝ}
    (hg : Continuous g) : IntegrableOn g AVenhance.unitCube := by
  have hcell := continuous_unitCell_integrable hg
  have hμ : (volume : Measure (Vec 2)).restrict
      (AVenhance.Infra.Torus.unitCell 2) =
      (volume : Measure (Vec 2)).restrict AVenhance.unitCube :=
    Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube
  change Integrable g ((volume : Measure (Vec 2)).restrict AVenhance.unitCube)
  rw [← hμ]
  exact hcell

/-- The real Fourier cutoff is an `L²` contraction on the cell. This bound supplies a
time-uniform integrable majorant when the cutoff is applied slice by slice to a smooth spacetime
test. -/
theorem testFourierCutoff_l2_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (N : ℕ) :
    AVenhance.l2NormSq
        (AVenhance.Infra.Section5.testFourierCutoff f N) ≤ AVenhance.l2NormSq f := by
  let coeff : (Fin 2 → ℤ) → ℂ := fun k =>
    AVenhance.Infra.Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k
  have hcoeffReal : ∀ k, coeff (-k) = star (coeff k) := by
    intro k
    exact AVenhance.Infra.Ergodic.smoothFourierCoeff_real_neg k
  have hcutCoeff (k : Fin 2 → ℤ) :
      AVenhance.Infra.Torus.smoothFourierCoeff
          (fun x =>
            (AVenhance.Infra.Section5.testFourierCutoff f N x : ℂ)) k =
        if k ∈ AVenhance.Infra.Ergodic.frequencyBall N then coeff k else 0 := by
    simpa [AVenhance.Infra.Section5.testFourierCutoff,
      AVenhance.Infra.Ergodic.lowProjection] using
      (AVenhance.Infra.Ergodic.smoothFourierCoeff_euclideanCutoff N
        (fun k => AVenhance.Infra.Torus.smoothFourierCoeff
          (fun x => (f x : ℂ)) k) hcoeffReal k)
  have hsource := AVenhance.Infra.Torus.hasSum_sq_realToComplexFourierCoeff hf
  have hcut := AVenhance.Infra.Torus.hasSum_sq_realToComplexFourierCoeff
    ((AVenhance.Infra.Section5.testFourierCutoff_analytic f N).of_le (by simp))
  rw [← hcut.tsum_eq, ← hsource.tsum_eq]
  apply Summable.tsum_le_tsum _ hcut.summable hsource.summable
  intro k
  have hcutCoeff' :
      AVenhance.Infra.Torus.smoothFourierCoeff
          (AVenhance.Infra.Torus.realToComplex
            (AVenhance.Infra.Section5.testFourierCutoff f N)) k =
        if k ∈ AVenhance.Infra.Ergodic.frequencyBall N then coeff k else 0 := by
    change AVenhance.Infra.Torus.smoothFourierCoeff
        (fun x => (AVenhance.Infra.Section5.testFourierCutoff f N x : ℂ)) k = _
    exact hcutCoeff k
  rw [hcutCoeff']
  by_cases hk : k ∈ AVenhance.Infra.Ergodic.frequencyBall N
  · simp [hk, coeff, AVenhance.Infra.Torus.realToComplex, Function.comp_def]
  · simp [hk]

theorem TestDensityBridge.bridge_unitCube_measurable : MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem TestDensityBridge.bridge_gradientCoord_energy_le {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    AVenhance.l2NormSq (fun x => AVenhance.spaceGrad f x i) ≤
      AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  have hleft : IntegrableOn (fun x =>
      (AVenhance.spaceGrad f x i) ^ 2) AVenhance.unitCube :=
    bridge_continuous_integrable_cube ((TestDensityBridge.bridge_gradientCoord_continuous hf
        i).pow 2)
  have hright : IntegrableOn (fun x =>
      Homogenization.vecNormSq (AVenhance.spaceGrad f x)) AVenhance.unitCube := by
    have hgrad : Continuous (AVenhance.spaceGrad f) :=
      continuous_pi (fun j => TestDensityBridge.bridge_gradientCoord_continuous hf j)
    have hc : Continuous (fun x =>
        Homogenization.vecNormSq (AVenhance.spaceGrad f x)) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      fun_prop
    exact bridge_continuous_integrable_cube hc
  unfold AVenhance.l2NormSq AVenhance.gradNormSq
  apply setIntegral_mono_on hleft hright (by
    unfold AVenhance.unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo))
  intro x hx
  simp only [Homogenization.vecNormSq, Homogenization.vecDot]
  simpa [pow_two] using (Finset.single_le_sum (s := Finset.univ)
    (fun j hj => sq_nonneg (AVenhance.spaceGrad f x j)) (Finset.mem_univ i))

/-- The derivative part of the Fourier cutoff converges in every cell pairing against an
arbitrary `L²` function. -/
theorem testFourierCutoff_gradient_pairing_tendsto
    {g ψ : Vec 2 → ℝ} (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ)
    (i : Fin 2) :
    Tendsto
      (fun N => ∫ x in AVenhance.unitCube,
        g x * AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i)
      atTop
      (𝓝 (∫ x in AVenhance.unitCube, g x * AVenhance.spaceGrad ψ x i)) := by
  let hψ₁ : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  let cutoff (N : ℕ) : Vec 2 → ℝ :=
    AVenhance.Infra.Section5.testFourierCutoff ψ N
  let err (N : ℕ) : Vec 2 → ℝ :=
    fun x => AVenhance.spaceGrad (fun y => ψ y - cutoff N y) x i
  have hcut (N : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (cutoff N) := by
    exact (AVenhance.Infra.Section5.testFourierCutoff_analytic ψ N).of_le le_top
  have hcut₁ (N : ℕ) : ContDiff ℝ 1 (cutoff N) :=
    (hcut N).of_le (by simp)
  have herrSmooth (N : ℕ) : ContDiff ℝ 1 (fun x => ψ x - cutoff N x) :=
    hψ₁.sub (hcut₁ N)
  have herrContinuous (N : ℕ) (x : Vec 2) :
      err N x = AVenhance.spaceGrad ψ x i -
        AVenhance.spaceGrad (cutoff N) x i := by
    simp only [err, AVenhance.spaceGrad]
    rw [fderiv_fun_sub
      ((hψ₁.differentiable (by norm_num)).differentiableAt)
      ((hcut₁ N).differentiable (by norm_num)).differentiableAt]
    simp
  have htotal : Tendsto
      (fun N => AVenhance.gradNormSq
        (AVenhance.spaceGrad (fun x => ψ x - cutoff N x)))
      atTop (𝓝 0) := by
    simpa [cutoff] using
      AVenhance.Infra.Section5.testFourierCutoff_gradient_error_tendsto
        hψ₁ hperiodic
  have hcoordLe (N : ℕ) :
      AVenhance.l2NormSq (err N) ≤
        AVenhance.gradNormSq
          (AVenhance.spaceGrad (fun x => ψ x - cutoff N x)) := by
    exact TestDensityBridge.bridge_gradientCoord_energy_le (herrSmooth N) i
  have hcoordNonneg (N : ℕ) : 0 ≤ AVenhance.l2NormSq (err N) := by
    unfold AVenhance.l2NormSq
    exact setIntegral_nonneg TestDensityBridge.bridge_unitCube_measurable
      (by intro x hx; exact sq_nonneg _)
  have hcoord : Tendsto (fun N => AVenhance.l2NormSq (err N)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall hcoordNonneg)
      (Eventually.of_forall hcoordLe) htotal
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hcoord
  have hupper : Tendsto
      (fun N => Real.sqrt (AVenhance.l2NormSq g) *
        Real.sqrt (AVenhance.l2NormSq (err N))) atTop (𝓝 0) := by
    simpa using hroot.const_mul (Real.sqrt (AVenhance.l2NormSq g))
  have habs : Tendsto
      (fun N => |∫ x in AVenhance.unitCube, g x * err N x|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) _ hupper
    filter_upwards with N
    exact TestDensityBridge.bridge_pairing_error_bound hg
      (TestDensityBridge.bridge_gradientCoord_continuous (herrSmooth N) i)
  have herror : Tendsto
      (fun N => ∫ x in AVenhance.unitCube, g x * err N x)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have htargetCont : Continuous (fun x => AVenhance.spaceGrad ψ x i) :=
    TestDensityBridge.bridge_gradientCoord_continuous hψ₁ i
  have htargetInt : Integrable (fun x => g x * AVenhance.spaceGrad ψ x i)
      (volume.restrict AVenhance.unitCube) :=
    ((hg.mul (TestDensityBridge.bridge_continuous_memL2 htargetCont)) :
      MemLp (fun x => g x * AVenhance.spaceGrad ψ x i) 1
        (volume.restrict AVenhance.unitCube)).integrable le_rfl
  have herrInt (N : ℕ) : Integrable (fun x => g x * err N x)
      (volume.restrict AVenhance.unitCube) :=
    ((hg.mul (TestDensityBridge.bridge_continuous_memL2
      (TestDensityBridge.bridge_gradientCoord_continuous (herrSmooth N) i))) :
        MemLp (fun x => g x * err N x) 1
          (volume.restrict AVenhance.unitCube)).integrable le_rfl
  have heq (N : ℕ) :
      (∫ x in AVenhance.unitCube,
        g x * AVenhance.spaceGrad (cutoff N) x i) =
      (∫ x in AVenhance.unitCube, g x * AVenhance.spaceGrad ψ x i) -
        (∫ x in AVenhance.unitCube, g x * err N x) := by
    calc
      _ = ∫ x in AVenhance.unitCube,
          g x * (AVenhance.spaceGrad ψ x i - err N x) := by
            apply setIntegral_congr_fun TestDensityBridge.bridge_unitCube_measurable
            intro x hx
            change g x * AVenhance.spaceGrad (cutoff N) x i = _
            calc
              _ = g x * (AVenhance.spaceGrad ψ x i - err N x) := by
                rw [show AVenhance.spaceGrad (cutoff N) x i =
                    AVenhance.spaceGrad ψ x i - err N x by
                      linarith [herrContinuous N x]]
              _ = _ := by ring
      _ = _ := by
        rw [show (fun x => g x *
            (AVenhance.spaceGrad ψ x i - err N x)) =
          fun x => g x * AVenhance.spaceGrad ψ x i - g x * err N x by
            funext x
            ring]
        exact integral_sub htargetInt (herrInt N)
  have hseq :
      (fun N => ∫ x in AVenhance.unitCube,
        g x * AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i) =
      fun N => (∫ x in AVenhance.unitCube,
        g x * AVenhance.spaceGrad ψ x i) -
          (∫ x in AVenhance.unitCube, g x * err N x) := by
    funext N
    simpa [cutoff] using heq N
  rw [hseq]
  simpa using tendsto_const_nhds.sub herror

theorem TestDensityBridge.frequencyBall_pairFrequency_iff (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ AVenhance.Infra.Ergodic.frequencyBall N ↔
      frequencyPair k ∈ symmetricFrequencyBox N := by
  rw [AVenhance.Infra.Ergodic.mem_frequencyBall]
  simp only [frequencyPair, symmetricFrequencyBox, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · intro hk
    have h0 : ‖(k 0 : ℝ)‖ ≤ ‖k‖ := norm_le_pi_norm k 0
    have h1 : ‖(k 1 : ℝ)‖ ≤ ‖k‖ := norm_le_pi_norm k 1
    have hcast0 : |k 0| ≤ (N : ℤ) := by
      have hreal : |(k 0 : ℝ)| ≤ (N : ℝ) := by
        simpa only [Real.norm_eq_abs] using h0.trans hk
      exact_mod_cast hreal
    have hcast1 : |k 1| ≤ (N : ℤ) := by
      have hreal : |(k 1 : ℝ)| ≤ (N : ℝ) := by
        simpa only [Real.norm_eq_abs] using h1.trans hk
      exact_mod_cast hreal
    exact ⟨abs_le.mp hcast0, abs_le.mp hcast1⟩
  · intro hk
    have hcoord : ∀ i : Fin 2, ‖(k i : ℝ)‖ ≤ (N : ℝ) := by
      intro i
      have habs : |k i| ≤ (N : ℤ) := by
        fin_cases i
        · exact abs_le.mpr hk.1
        · exact abs_le.mpr hk.2
      have hcast : |(k i : ℝ)| ≤ (N : ℝ) := by exact_mod_cast habs
      simpa only [Real.norm_eq_abs] using hcast
    exact (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (N : ℝ))).2 hcoord

theorem TestDensityBridge.frequencyPair_pairFrequency (p : ℤ × ℤ) :
    frequencyPair (pairFrequency p) = p := by
  rcases p with ⟨p₀, p₁⟩
  rfl

theorem TestDensityBridge.frequencyPair_injective {p q : Fin 2 → ℤ}
    (h : frequencyPair p = frequencyPair q) : p = q := by
  change (p 0, p 1) = (q 0, q 1) at h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem TestDensityBridge.testFourierCutoff_eq_realFourierProjection_ambient
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) (N : ℕ) (x : Vec 2) :
    AVenhance.Infra.Section5.testFourierCutoff ψ N x =
      realFourierProjection N
        (AVenhance.Infra.Torus.periodicToTorus ψ)
        (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
  let a : (Fin 2 → ℤ) → ℂ :=
    fun k => AVenhance.Infra.Torus.smoothFourierCoeff
      (fun y => (ψ y : ℂ)) k
  have ha : ∀ k, a (-k) = star (a k) := by
    intro k
    dsimp [a]
    exact AVenhance.Infra.Ergodic.smoothFourierCoeff_real_neg k
  have hperiodicC : AVenhance.Infra.Torus.IsZdPeriodic
      (fun y => (ψ y : ℂ)) := by
    intro k y
    exact congrArg Complex.ofReal (hperiodic k y)
  have hcoeff (k : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff
          (fun y : Torus =>
            (AVenhance.Infra.Torus.periodicToTorus (α := ℝ) ψ y : ℂ)) k = a k := by
    have h := AVenhance.Infra.Ergodic.mFourierCoeff_periodicToTorus_eq_smooth
      hperiodicC (Complex.continuous_ofReal.comp hψ.continuous) k
    have h' : UnitAddTorus.mFourierCoeff
        (AVenhance.Infra.Torus.periodicToTorus
          (fun y => (ψ y : ℂ))) k = a k := by
      simpa [a] using h
    have hfun : AVenhance.Infra.Torus.periodicToTorus
        (fun y => (ψ y : ℂ)) =
          fun y => (AVenhance.Infra.Torus.periodicToTorus (α := ℝ) ψ y : ℂ) := by
      rfl
    rw [← hfun]
    exact h'
  have hsum :
      ∑ k ∈ AVenhance.Infra.Ergodic.frequencyBall N,
        a k * AVenhance.Infra.Torus.torusCharacter (-k) x =
      ∑ p ∈ symmetricFrequencyBox N,
        UnitAddTorus.mFourierCoeff
            (fun y : Torus =>
              (AVenhance.Infra.Torus.periodicToTorus (α := ℝ) ψ y : ℂ))
            (pairFrequency p) *
          UnitAddTorus.mFourier (pairFrequency p)
            (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
    classical
    apply Finset.sum_bij (fun k _ => frequencyPair k)
    · intro k hk
      exact (TestDensityBridge.frequencyBall_pairFrequency_iff N k).mp hk
    · intro k hk l hl hkl
      exact TestDensityBridge.frequencyPair_injective hkl
    · intro p hp
      refine ⟨pairFrequency p, ?_, TestDensityBridge.frequencyPair_pairFrequency p⟩
      rw [TestDensityBridge.frequencyBall_pairFrequency_iff,
          TestDensityBridge.frequencyPair_pairFrequency]
      exact hp
    · intro k hk
      rw [pairFrequency_frequencyPair, hcoeff]
      simp [AVenhance.Infra.Torus.torusCharacter]
  change (∑ k ∈ AVenhance.Infra.Ergodic.frequencyBall N,
      a k * AVenhance.Infra.Torus.torusCharacter (-k) x).re = _
  rw [hsum]
  rfl

theorem TestDensityBridge.realFourierModeFin_ambient_at (N : ℕ)
    (i : Fin (RealFourierDimension N)) (x : Vec 2) :
    realFourierModeFin N i (AVenhance.Infra.Torus.toUnitTorus 2 x) =
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x := by
  rw [realFourierModeFin_eq_periodicToTorus]
  have hper := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).2
    (realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i))
  have h := congrFun
    (AVenhance.Infra.Torus.fromUnitTorus_periodicToTorus hper) x
  simpa [AVenhance.Infra.Torus.fromUnitTorus,
    AVenhance.Infra.Torus.periodicToTorus] using h

/-- The spatial Fourier cutoff is exactly a finite real Fourier expansion, including its
ambient periodic representative. -/
theorem testFourierCutoff_ambientExpansion
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) (N : ℕ) :
    ∃ c : Coefficients (RealFourierDimension N),
      ∀ x : Vec 2,
        AVenhance.Infra.Section5.testFourierCutoff ψ N x =
          ∑ i : Fin (RealFourierDimension N),
            c i * realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm i) x := by
  let f : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus ψ
  let fC : Torus → ℂ := AVenhance.Infra.Torus.periodicToTorus
    (fun x => (ψ x : ℂ))
  have hfC : Continuous fC :=
    AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.continuous_ofReal.comp hψ.continuous)
      (fun k x => congrArg Complex.ofReal (hperiodic k x))
  have hf : Continuous f := by
    have heq : f = fun y => (fC y).re := by
      funext y
      rfl
    rw [heq]
    exact Complex.continuous_re.comp hfC
  have hint : Integrable f (volume : Measure Torus) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let c : Coefficients (RealFourierDimension N) :=
    modeProjectionCoefficients (RealFourierDimension N)
      (realFourierModeFin N) f
  have hproj := realFourierModeFin_projectionExpansion_eq_projection N hint
  have hproj' : modeExpansion (RealFourierDimension N)
      (realFourierModeFin N) c = realFourierProjection N f := by
    simpa [c] using hproj
  refine ⟨c, ?_⟩
  intro x
  calc
    AVenhance.Infra.Section5.testFourierCutoff ψ N x =
        realFourierProjection N f
          (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
            exact TestDensityBridge.testFourierCutoff_eq_realFourierProjection_ambient
              (hψ.of_le (by norm_num)) hperiodic N x
    _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) c
          (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
            exact (congrFun hproj'.symm
              (AVenhance.Infra.Torus.toUnitTorus 2 x))
    _ = ∑ i : Fin (RealFourierDimension N),
          c i * realFourierModeAmbient N
            ((realFourierIndexEquivFin N).symm i) x := by
            unfold modeExpansion
            apply Finset.sum_congr rfl
            intro i hi
            rw [TestDensityBridge.realFourierModeFin_ambient_at]

/-- The ambient finite expansion uses the canonical torus projection coefficients. This makes its
time-dependent coefficients explicit when the cutoff is applied to a spacetime test. -/
theorem testFourierCutoff_ambientExpansion_coeff
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) (N : ℕ) :
    ∀ x : Vec 2,
      AVenhance.Infra.Section5.testFourierCutoff ψ N x =
        ∑ i : Fin (RealFourierDimension N),
          (modeProjectionCoefficients (RealFourierDimension N)
            (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus ψ)) i *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm i) x := by
  let f : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus ψ
  let fC : Torus → ℂ := AVenhance.Infra.Torus.periodicToTorus
    (fun x => (ψ x : ℂ))
  have hfC : Continuous fC := by
    exact AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.continuous_ofReal.comp hψ.continuous)
      (fun k x => congrArg Complex.ofReal (hperiodic k x))
  have hf : Continuous f := by
    have heq : f = fun y => (fC y).re := by
      funext y
      rfl
    rw [heq]
    exact Complex.continuous_re.comp hfC
  have hint : Integrable f (volume : Measure Torus) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let c : Coefficients (RealFourierDimension N) :=
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
  have hprojection := realFourierModeFin_projectionExpansion_eq_projection N hint
  intro x
  calc
    AVenhance.Infra.Section5.testFourierCutoff ψ N x =
        realFourierProjection N f
          (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
            exact TestDensityBridge.testFourierCutoff_eq_realFourierProjection_ambient
              (hψ.of_le (by norm_num)) hperiodic N x
    _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) c
          (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
            exact congrFun hprojection.symm
              (AVenhance.Infra.Torus.toUnitTorus 2 x)
    _ = ∑ i : Fin (RealFourierDimension N),
          c i * realFourierModeAmbient N
            ((realFourierIndexEquivFin N).symm i) x := by
            unfold modeExpansion
            apply Finset.sum_congr rfl
            intro i hi
            rw [TestDensityBridge.realFourierModeFin_ambient_at]

/-- A common Fourier-mode weak-derivative identity extends to every smooth periodic spatial test.
The cutoff is the actual finite Fourier polynomial, and convergence is in the exact value
and derivative cell pairings needed for integration by parts. -/
theorem cellWeakDerivative_of_realFourierModes
    {u Du : Vec 2 → ℝ} (hu : MemLp u 2 (volume.restrict AVenhance.unitCube))
    (hDu : MemLp Du 2 (volume.restrict AVenhance.unitCube))
    (i : Fin 2)
    (hmode : ∀ N : ℕ, ∀ j : Fin (RealFourierDimension N),
      ∫ x in AVenhance.unitCube,
        u x * AVenhance.spaceGrad
          (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)) x i =
      -∫ x in AVenhance.unitCube,
        Du x * realFourierModeAmbient N
          ((realFourierIndexEquivFin N).symm j) x)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube, u x * AVenhance.spaceGrad ψ x i =
      -∫ x in AVenhance.unitCube, Du x * ψ x := by
  have hvalue := AVenhance.Infra.Section5.testFourierCutoff_pairing_tendsto
    hDu (hψ.of_le (by norm_num))
  have hgradient := testFourierCutoff_gradient_pairing_tendsto hu hψ hperiodic i
  have hcutIdentity (N : ℕ) :
      ∫ x in AVenhance.unitCube,
        u x * AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i =
      -∫ x in AVenhance.unitCube,
        Du x * AVenhance.Infra.Section5.testFourierCutoff ψ N x := by
    obtain ⟨c, hc⟩ := testFourierCutoff_ambientExpansion hψ hperiodic N
    let mode : Fin (RealFourierDimension N) → Vec 2 → ℝ := fun j x =>
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x
    have hmodeSmooth (j : Fin (RealFourierDimension N)) :
        ContDiff ℝ (↑(⊤ : ℕ∞)) (mode j) := by
      exact (realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm j)).of_le le_top
    have hgradExpansion (x : Vec 2) :
        AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i =
        ∑ j : Fin (RealFourierDimension N),
          c j * AVenhance.spaceGrad (mode j) x i := by
      have hfun : AVenhance.Infra.Section5.testFourierCutoff ψ N =
          fun y => ∑ j : Fin (RealFourierDimension N), c j * mode j y := by
        funext y
        simpa [mode] using hc y
      change fderiv ℝ (AVenhance.Infra.Section5.testFourierCutoff ψ N) x
        (Homogenization.basisVec i) = _
      rw [hfun]
      have hdiff (j : Fin (RealFourierDimension N)) (_hj :
          j ∈ (Finset.univ : Finset (Fin (RealFourierDimension N)))) :
          DifferentiableAt ℝ (fun y => c j * mode j y) x := by
        exact (((hmodeSmooth j).contDiffAt (x := x)).differentiableAt (by norm_num)).const_mul (c j)
      rw [fderiv_fun_sum hdiff]
      simp_rw [fderiv_const_mul
        (((hmodeSmooth _).contDiffAt (x := x)).differentiableAt (by norm_num)) (c _)]
      simp [AVenhance.spaceGrad, mode, smul_eq_mul]
    have hleftInt (j : Fin (RealFourierDimension N)) :
        Integrable (fun x : Vec 2 =>
          c j * (u x * AVenhance.spaceGrad (mode j) x i))
          (volume.restrict AVenhance.unitCube) := by
      have htest : Continuous (fun x : Vec 2 =>
          c j * AVenhance.spaceGrad (mode j) x i) := by
        exact continuous_const.mul
          (TestDensityBridge.bridge_gradientCoord_continuous ((hmodeSmooth j).of_le (by norm_num))
              i)
      have hprod : MemLp (fun x : Vec 2 =>
          u x * (c j * AVenhance.spaceGrad (mode j) x i)) 1
          (volume.restrict AVenhance.unitCube) :=
        hu.mul (TestDensityBridge.bridge_continuous_memL2 htest)
      have hEq : (fun x : Vec 2 =>
          c j * (u x * AVenhance.spaceGrad (mode j) x i)) =
          fun x => u x * (c j * AVenhance.spaceGrad (mode j) x i) := by
        funext x
        ring
      rw [hEq]
      exact hprod.integrable le_rfl
    have hrightInt (j : Fin (RealFourierDimension N)) :
        Integrable (fun x : Vec 2 =>
          c j * (Du x * mode j x)) (volume.restrict AVenhance.unitCube) := by
      have htest : Continuous (fun x : Vec 2 => c j * mode j x) :=
        continuous_const.mul (hmodeSmooth j).continuous
      have hprod : MemLp (fun x : Vec 2 => Du x * (c j * mode j x)) 1
          (volume.restrict AVenhance.unitCube) :=
        hDu.mul (TestDensityBridge.bridge_continuous_memL2 htest)
      have hEq : (fun x : Vec 2 => c j * (Du x * mode j x)) =
          fun x => Du x * (c j * mode j x) := by
        funext x
        ring
      rw [hEq]
      exact hprod.integrable le_rfl
    have hleft :
        (∫ x in AVenhance.unitCube,
          u x * AVenhance.spaceGrad
            (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i) =
        ∑ j : Fin (RealFourierDimension N), c j *
          (∫ x in AVenhance.unitCube,
            u x * AVenhance.spaceGrad (mode j) x i) := by
      calc
        _ = ∫ x in AVenhance.unitCube,
            ∑ j : Fin (RealFourierDimension N),
              c j * (u x * AVenhance.spaceGrad (mode j) x i) := by
                apply setIntegral_congr_fun TestDensityBridge.bridge_unitCube_measurable
                intro x hx
                change u x * AVenhance.spaceGrad
                    (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i = _
                rw [hgradExpansion x, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = ∑ j : Fin (RealFourierDimension N),
            ∫ x in AVenhance.unitCube,
              c j * (u x * AVenhance.spaceGrad (mode j) x i) := by
                have hsum := integral_finsetSum (s := Finset.univ)
                  (f := fun j x => c j *
                    (u x * AVenhance.spaceGrad (mode j) x i))
                  (fun j _hj => hleftInt j)
                rw [hsum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
    have hright :
        (∫ x in AVenhance.unitCube,
          Du x * AVenhance.Infra.Section5.testFourierCutoff ψ N x) =
        ∑ j : Fin (RealFourierDimension N), c j *
          (∫ x in AVenhance.unitCube, Du x * mode j x) := by
      calc
        _ = ∫ x in AVenhance.unitCube,
            ∑ j : Fin (RealFourierDimension N), c j * (Du x * mode j x) := by
                apply setIntegral_congr_fun TestDensityBridge.bridge_unitCube_measurable
                intro x hx
                change Du x * AVenhance.Infra.Section5.testFourierCutoff ψ N x = _
                rw [show AVenhance.Infra.Section5.testFourierCutoff ψ N x =
                    ∑ j : Fin (RealFourierDimension N), c j * mode j x by
                      simpa [mode] using hc x, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = ∑ j : Fin (RealFourierDimension N),
            ∫ x in AVenhance.unitCube, c j * (Du x * mode j x) := by
                have hsum := integral_finsetSum (s := Finset.univ)
                  (f := fun j x => c j * (Du x * mode j x))
                  (fun j _hj => hrightInt j)
                rw [hsum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
    calc
      _ = ∑ j : Fin (RealFourierDimension N), c j *
          (∫ x in AVenhance.unitCube,
            u x * AVenhance.spaceGrad (mode j) x i) := hleft
      _ = -∑ j : Fin (RealFourierDimension N), c j *
          (∫ x in AVenhance.unitCube, Du x * mode j x) := by
            rw [show (∑ j : Fin (RealFourierDimension N), c j *
                (∫ x in AVenhance.unitCube,
                  u x * AVenhance.spaceGrad (mode j) x i)) =
              ∑ j : Fin (RealFourierDimension N), c j *
                (-∫ x in AVenhance.unitCube, Du x * mode j x) by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hmode N j]]
            simp [Finset.sum_neg_distrib]
      _ = -∫ x in AVenhance.unitCube,
          Du x * AVenhance.Infra.Section5.testFourierCutoff ψ N x := by
            rw [hright]
  have hlimits := hgradient.add hvalue
  have hzero : Tendsto (fun N =>
      (∫ x in AVenhance.unitCube,
        u x * AVenhance.spaceGrad
          (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i) +
      (∫ x in AVenhance.unitCube,
        Du x * AVenhance.Infra.Section5.testFourierCutoff ψ N x))
      atTop (𝓝 0) := by
    have hsequence : (fun N =>
        (∫ x in AVenhance.unitCube,
          u x * AVenhance.spaceGrad
            (AVenhance.Infra.Section5.testFourierCutoff ψ N) x i) +
        (∫ x in AVenhance.unitCube,
          Du x * AVenhance.Infra.Section5.testFourierCutoff ψ N x)) =
        fun _ : ℕ => 0 := by
      funext N
      rw [hcutIdentity N]
      ring
    rw [hsequence]
    exact tendsto_const_nhds
  have hEq : (∫ x in AVenhance.unitCube,
      u x * AVenhance.spaceGrad ψ x i) +
      (∫ x in AVenhance.unitCube, Du x * ψ x) = 0 := by
    have := tendsto_nhds_unique hlimits hzero
    exact this
  linarith

end AVenhance.Infra.Parabolic.FourierGalerkin

end
