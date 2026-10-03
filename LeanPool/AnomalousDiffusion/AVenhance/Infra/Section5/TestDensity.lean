/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicFlow
public import Mathlib.Analysis.Normed.Group.Tannery

/-! Fourier test density connecting the analytic App C dual tests to the
smooth-test norm. All approximants are actual finite real trig sums. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Ergodic
namespace AVenhance.Infra.Section5

theorem TestDensity.avg_cube (f : Vec 2 → ℝ) : cellAverage f = ∫ x in unitCube, f x := by
  rw [cellAverage_eq_unitCellIntegral, unitCellSet_eq_torusUnitCell]
  exact Infra.Torus.integral_unitCell_eq_unitCube f

theorem TestDensity.gradient_avg (f : Vec 2 → ℝ) :
    gradientL2SquaredAverage f = gradNormSq (spaceGrad f) := by
  rw [gradientL2SquaredAverage, TestDensity.avg_cube]
  simp [gradNormSq, spaceGrad, vecNormSq, vecDot, basisVec, pow_two]

theorem TestDensity.continuous_L2 {f : Vec 2 → ℝ} (hf : Continuous f) : MemL2On unitCube f := by
  have h := continuous_unitCell_memLp_two hf
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  simpa using h

local instance avInfraSection5TestDensityIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict
    unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The actual real Fourier truncation on the supremum-norm lattice ball. -/
def testFourierCutoff (f : Vec 2 → ℝ) (N : ℕ) : Vec 2 → ℝ := lowProjection f N

theorem testFourierCutoff_analytic (f : Vec 2 → ℝ) (N : ℕ) :
    ContDiff ℝ ⊤ (testFourierCutoff f N) := lowProjection_contDiff N

theorem testFourierCutoff_periodic (f : Vec 2 → ℝ) (N : ℕ) :
    IsZ2Periodic (testFourierCutoff f N) := fun k x => lowProjection_periodic N x k

theorem TestDensity.cutoff_coeff {f : Vec 2 → ℝ} (_hf : Continuous f) (N : ℕ) (k : Fin 2 → ℤ) :
    Infra.Torus.smoothFourierCoeff (fun x => (testFourierCutoff f N x : ℂ)) k =
      if k ∈ frequencyBall N then Infra.Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k else 0 :=
  smoothFourierCoeff_euclideanCutoff N _ (fun k => smoothFourierCoeff_real_neg k) k

theorem TestDensity.tail_coeff {f : Vec 2 → ℝ} (hf : Continuous f) (N : ℕ) (k : Fin 2 → ℤ) :
    Infra.Torus.smoothFourierCoeff (fun x => ((f x - testFourierCutoff f N x : ℝ) : ℂ)) k =
      if k ∈ frequencyBall N then 0 else Infra.Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k := by
  have h := smoothFourierCoeff_sub (f := fun x => (f x : ℂ)) (g := fun x => (testFourierCutoff f N
      x : ℂ)) (Complex.continuous_ofReal.comp hf)
    (Complex.continuous_ofReal.comp (testFourierCutoff_analytic f N).continuous) k
  simp only [Complex.ofReal_sub]
  rw [h, TestDensity.cutoff_coeff hf]
  split_ifs <;> simp

theorem TestDensity.eventually_frequency_mem (k : Fin 2 → ℤ) :
    ∀ᶠ N : ℕ in atTop, k ∈ frequencyBall N := by
  obtain ⟨n, hn⟩ := exists_nat_ge ‖k‖
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [mem_frequencyBall]
  exact hn.trans (by exact_mod_cast hN)

theorem TestDensity.tail_tsum_tendsto {a : (Fin 2 → ℤ) → ℝ} (ha : Summable a)
    (hpos : ∀ k, 0 ≤ a k) :
    Tendsto (fun N => ∑' k, if k ∈ frequencyBall N then 0 else a k) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence ha
    (g := fun _ => (0 : ℝ))
    (f := fun N k => if k ∈ frequencyBall N then 0 else a k)
    (fun k => tendsto_const_nhds.congr' ((TestDensity.eventually_frequency_mem k).mono (fun N hn
        => by simp [hn])))
    (Eventually.of_forall (fun N k => by split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hpos
        k), hpos k]))
  simpa using h

/-- Real Parseval gives convergence of the value error to zero in L2. -/
theorem testFourierCutoff_L2_error_tendsto {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) :
    Tendsto (fun N => l2NormSq (fun x => f x - testFourierCutoff f N x)) atTop (𝓝 0) := by
  let a := fun k => ‖Infra.Torus.smoothFourierCoeff (Infra.Torus.realToComplex f) k‖ ^ 2
  have hsum := Infra.Torus.hasSum_sq_realToComplexFourierCoeff hf
  have heq (N : ℕ) : l2NormSq (fun x => f x - testFourierCutoff f N x) =
      ∑' k, if k ∈ frequencyBall N then 0 else a k := by
    have hp := Infra.Torus.hasSum_sq_realToComplexFourierCoeff
      (hf.sub ((testFourierCutoff_analytic f N).of_le (by simp)))
    rw [← hp.tsum_eq]
    apply tsum_congr
    intro k
    simp only [Infra.Torus.realToComplex, Function.comp_def, Complex.ofRealCLM_apply]
    change ‖Infra.Torus.smoothFourierCoeff (fun x => ((f x - testFourierCutoff f N x : ℝ) : ℂ)) k‖
        ^ 2 = _
    rw [TestDensity.tail_coeff hf.continuous]
    split_ifs <;> simp [a, Infra.Torus.realToComplex, Function.comp_def, Complex.ofRealCLM_apply]
  simp_rw [heq]
  exact TestDensity.tail_tsum_tendsto hsum.summable (fun k => sq_nonneg _)

theorem TestDensity.gradient_coeff_cutoff {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : IsZ2Periodic f) (N : ℕ) (i : Fin 2) (k : Fin 2 → ℤ) :
    Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad (testFourierCutoff f N) x i : ℂ)) k =
      if k ∈ frequencyBall N then Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ))
          k else 0 := by
  rw [Infra.Torus.smoothFourierCoeff_spaceGrad ((testFourierCutoff_analytic f N).of_le (by simp))
    (testFourierCutoff_periodic f N), Infra.Torus.smoothFourierCoeff_spaceGrad hf hp]
  change (2 * Real.pi * Complex.I * (k i : ℂ)) *
    Infra.Torus.smoothFourierCoeff (fun x => (testFourierCutoff f N x : ℂ)) k = _
  rw [TestDensity.cutoff_coeff hf.continuous]
  split_ifs <;> simp [Infra.Torus.realToComplex, Function.comp_def, Complex.ofRealCLM_apply]

theorem TestDensity.grad_component_cont {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => spaceGrad f x i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem TestDensity.gradient_energy_parseval {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) :
    HasSum (fun k : Fin 2 → ℤ => ∑ i : Fin 2,
      ‖Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ)) k‖ ^ 2)
      (gradNormSq (spaceGrad f)) := by
  have h := Infra.Torus.hasSum_sq_realToComplexGradientFourierCoeff hf
  convert h using 1
  funext k
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  congr 1
  funext x
  exact (Infra.Torus.coordDeriv_realToComplex hf i x).symm

/-- Orthogonal truncation never increases gradient energy. Thus normalized
tests stay normalized without an artificial rescaling. -/
theorem testFourierCutoff_gradient_le {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : IsZ2Periodic f) (N : ℕ) :
    gradNormSq (spaceGrad (testFourierCutoff f N)) ≤ gradNormSq (spaceGrad f) := by
  have h1 := TestDensity.gradient_energy_parseval hf
  have h2 := TestDensity.gradient_energy_parseval ((testFourierCutoff_analytic f N).of_le (by simp))
  rw [← h1.tsum_eq, ← h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h2.summable h1.summable
  intro k
  apply Finset.sum_le_sum
  intro i _
  rw [TestDensity.gradient_coeff_cutoff hf hp]
  split_ifs <;> simp

/-- The Fourier derivative multiplier and Parseval give gradient-error
convergence, not merely convergence of values. -/
theorem testFourierCutoff_gradient_error_tendsto {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : IsZ2Periodic f) :
    Tendsto (fun N => gradNormSq (spaceGrad (fun x => f x - testFourierCutoff f N x))) atTop (𝓝 0)
        := by
  let a := fun k => ∑ i : Fin 2,
    ‖Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x i : ℂ)) k‖ ^ 2
  have hsum := TestDensity.gradient_energy_parseval hf
  have heq (N : ℕ) : gradNormSq (spaceGrad (fun x => f x - testFourierCutoff f N x)) =
      ∑' k, if k ∈ frequencyBall N then 0 else a k := by
    have hc := (testFourierCutoff_analytic f N).of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rw [← (TestDensity.gradient_energy_parseval (hf.sub hc)).tsum_eq]
    apply tsum_congr
    intro k
    have hcoord (i : Fin 2) :
        Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad (fun x => f x - testFourierCutoff f N
            x) x i : ℂ)) k =
        if k ∈ frequencyBall N then 0 else Infra.Torus.smoothFourierCoeff (fun x => (spaceGrad f x
            i : ℂ)) k := by
      have he : (fun x => (spaceGrad (fun x => f x - testFourierCutoff f N x) x i : ℂ)) =
          fun x => (spaceGrad f x i : ℂ) - (spaceGrad (testFourierCutoff f N) x i : ℂ) := by
        funext x
        simp [spaceGrad, fderiv_fun_sub ((hf.differentiable (by norm_num)).differentiableAt)
            ((hc.differentiable (by norm_num)).differentiableAt)]
      rw [he, smoothFourierCoeff_sub (f := fun x => (spaceGrad f x i : ℂ)) (g := fun x =>
          (spaceGrad (testFourierCutoff f N) x i : ℂ)) (Complex.continuous_ofReal.comp
          (TestDensity.grad_component_cont hf i))
        (Complex.continuous_ofReal.comp (TestDensity.grad_component_cont hc i)),
            TestDensity.gradient_coeff_cutoff hf hp]
      split_ifs <;> simp
    simp_rw [hcoord]
    split_ifs <;> simp [a]
  simp_rw [heq]
  exact TestDensity.tail_tsum_tendsto hsum.summable (fun k => Finset.sum_nonneg (fun i _ =>
      sq_nonneg _))

theorem TestDensity.coeff_zero (f : Vec 2 → ℝ) (hf : Continuous f) :
    Infra.Torus.smoothFourierCoeff (fun x => (f x : ℂ)) (0 : Fin 2 → ℤ) =
      ((∫ x in unitCube, f x : ℝ) : ℂ) := by
  have h := Complex.ofRealCLM.integral_comp_comm
    (μ := volume.restrict (Infra.Torus.unitCell 2)) (continuous_unitCell_integrable hf)
  rw [← Infra.Torus.integral_unitCell_eq_unitCube f]
  simpa [Infra.Torus.smoothFourierCoeff, Infra.Torus.torusCharacter, UnitAddTorus.mFourier_zero,
      Complex.ofRealCLM_apply] using h

/-- The zero coefficient is retained, so the actual cell mean is preserved. -/
theorem testFourierCutoff_mean (f : Vec 2 → ℝ) (hf : Continuous f) (N : ℕ) :
    (∫ x in unitCube, testFourierCutoff f N x) = ∫ x in unitCube, f x := by
  have h := TestDensity.cutoff_coeff hf N (0 : Fin 2 → ℤ)
  have hz : (0 : Fin 2 → ℤ) ∈ frequencyBall N := by rw [mem_frequencyBall]; simp
  simp only [hz, ite_true] at h
  rw [TestDensity.coeff_zero _ (testFourierCutoff_analytic f N).continuous, TestDensity.coeff_zero
      f hf] at h
  exact_mod_cast h

/-- L2 Cauchy–Schwarz in value carriers. -/
theorem TestDensity.pairing_error_bound {g u : Vec 2 → ℝ} (hg : MemL2On unitCube g)
    (hu : Continuous u) :
    |∫ x in unitCube, g x * u x| ≤ Real.sqrt (l2NormSq g) * Real.sqrt (l2NormSq u) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (f := fun x => |g x|) (g := fun x => |u x|)
    (μ := volume.restrict unitCube) Real.HolderConjugate.two_two
    (ae_of_all _ (fun x => abs_nonneg _)) (ae_of_all _ (fun x => abs_nonneg _))
    (by simpa [Real.norm_eq_abs] using hg.norm)
    (by simpa [Real.norm_eq_abs] using (TestDensity.continuous_L2 hu).norm)
  have h1 : |∫ x in unitCube, g x * u x| ≤ ∫ x in unitCube, |g x| * |u x| := by
    simpa [Real.norm_eq_abs, abs_mul] using norm_integral_le_integral_norm (fun x => g x * u x)
  exact h1.trans (by simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div, l2NormSq]
      using h)

/-- Every L2 datum pairs continuously with the actual Fourier truncations. -/
theorem testFourierCutoff_pairing_tendsto {g f : Vec 2 → ℝ}
    (hg : MemL2On unitCube g) (hf : ContDiff ℝ 1 f) :
    Tendsto (fun N => ∫ x in unitCube, g x * testFourierCutoff f N x) atTop
      (𝓝 (∫ x in unitCube, g x * f x)) := by
  have hroot := (Real.continuous_sqrt.tendsto 0).comp (testFourierCutoff_L2_error_tendsto hf)
  have hz : Tendsto (fun N => Real.sqrt (l2NormSq g) *
      Real.sqrt (l2NormSq (fun x => f x - testFourierCutoff f N x))) atTop (𝓝 0) := by
    simpa using hroot.const_mul (Real.sqrt (l2NormSq g))
  have habs : Tendsto (fun N => |∫ x in unitCube, g x * (f x - testFourierCutoff f N x)|) atTop (𝓝
      0) :=
    squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _))
      (Eventually.of_forall (fun N => TestDensity.pairing_error_bound hg (hf.continuous.sub
          (testFourierCutoff_analytic f N).continuous))) hz
  have herror : Tendsto (fun N => ∫ x in unitCube, g x * (f x - testFourierCutoff f N x)) atTop (𝓝
      0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have heq (N : ℕ) : (∫ x in unitCube, g x * testFourierCutoff f N x) =
      (∫ x in unitCube, g x * f x) - (∫ x in unitCube, g x * (f x - testFourierCutoff f N x)) := by
    have h1 := (hg.mul (TestDensity.continuous_L2 hf.continuous) : MemLp (fun x => g x * f x) 1
        (volume.restrict unitCube)).integrable le_rfl
    have h2 := (hg.mul (TestDensity.continuous_L2 (testFourierCutoff_analytic f N).continuous) :
      MemLp (fun x => g x * testFourierCutoff f N x) 1 (volume.restrict unitCube)).integrable le_rfl
    simp only [mul_sub]
    rw [integral_sub (f := fun x => g x * f x) (g := fun x => g x * testFourierCutoff f N x) h1 h2]
    ring
  simp_rw [heq]
  simpa using tendsto_const_nhds.sub herror

/-- Centred Fourier approximants retain analytic regularity, periodicity,
zero mean and the gradient normalization. -/
theorem testFourierCutoff_admissible {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hp : IsZ2Periodic f) (hm : MeanZeroOn unitCube f)
    (hn : gradNormSq (spaceGrad f) ≤ 1) (N : ℕ) :
    ContDiff ℝ ⊤ (testFourierCutoff f N) ∧ IsZPeriodic (testFourierCutoff f N) ∧
      cellAverage (testFourierCutoff f N) = 0 ∧ gradientL2SquaredAverage (testFourierCutoff f N) ≤
          1 := by
  refine ⟨testFourierCutoff_analytic f N, fun x k => testFourierCutoff_periodic f N k x, ?_, ?_⟩
  · rw [TestDensity.avg_cube, testFourierCutoff_mean f hf.continuous]
    exact hm
  · rw [TestDensity.gradient_avg]
    exact (testFourierCutoff_gradient_le hf hp N).trans hn

/-- Density closes the formerly missing upper-bound direction. No periodicity
of the L2 datum is needed for equality of these cell dual suprema. -/
theorem hMinusOneNorm_eq_ergodic {g : Vec 2 → ℝ}
    (hg : MemL2On unitCube g) (hm : MeanZeroOn unitCube g) :
    hMinusOneNorm g = homogeneousHMinusOneNorm g := by
  apply le_antisymm
  · apply iSup_le
    intro φ
    let c := cellAverage φ.val
    let ψ : Vec 2 → ℝ := fun x => φ.val x - c
    have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := φ.property.1.sub contDiff_const
    have hs1 : ContDiff ℝ 1 ψ := hs.of_le (by simp)
    have hp : IsZ2Periodic ψ := by
      intro k x
      exact congrArg (fun y => y - c) (φ.property.2.1 k x)
    have hgrad : spaceGrad ψ = spaceGrad φ.val := by
      funext x i
      simp [spaceGrad, ψ, fderiv_sub_const]
    have hn : gradNormSq (spaceGrad ψ) ≤ 1 := by rw [hgrad]; exact φ.property.2.2
    have hmean : MeanZeroOn unitCube ψ := by
      have h1 := (TestDensity.continuous_L2 φ.property.1.continuous).integrable (by norm_num : (1
          : ENNReal) ≤ 2)
      have h2 := (TestDensity.continuous_L2 (continuous_const : Continuous (fun _ : Vec 2 =>
          c))).integrable (by norm_num : (1 : ENNReal) ≤ 2)
      change (∫ x in unitCube, φ.val x - c) = 0
      rw [integral_sub h1 h2, ← TestDensity.avg_cube, ← TestDensity.avg_cube]
      simp [c]
    have hpair : (∫ x in unitCube, g x * ψ x) = ∫ x in unitCube, g x * φ.val x := by
      have hi := (hg.mul (TestDensity.continuous_L2 φ.property.1.continuous) :
        MemLp (fun x => g x * φ.val x) 1 (volume.restrict unitCube)).integrable le_rfl
      have hc := (hg.mul_const c).integrable (by norm_num : (1 : ENNReal) ≤ 2)
      simp only [ψ, mul_sub]
      rw [integral_sub (f := fun x => g x * φ.val x) (g := fun x => g x * c) hi hc,
        integral_mul_const, hm, zero_mul, sub_zero]
    have hlim := (ENNReal.continuous_ofReal.tendsto _).comp
      ((testFourierCutoff_pairing_tendsto hg hs1).abs)
    rw [hpair] at hlim
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro N
    obtain ⟨hsm, hper', hmean', hgrad'⟩ := testFourierCutoff_admissible hs1 hp hmean hn N
    let test : HMinusOneTest 2 :=
      ⟨testFourierCutoff ψ N, hsm.of_le le_top, hper', hmean', hgrad'⟩
    change ENNReal.ofReal |∫ x in unitCube, g x * testFourierCutoff ψ N x| ≤ _
    rw [← TestDensity.avg_cube]
    exact dualPairing_le_homogeneousHMinusOneNorm g test
  · exact ergodic_hMinusOneNorm_le_frozen g

theorem TestDensity.product_L2 {f g : Vec 2 → ℝ} (hf : Continuous f)
    (hg : LocallyIntegrable g (volume : Measure (Vec 2)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec 2))) :
    MemL2On unitCube (fun x => f x * g x) := by
  have hs : LocallyIntegrable (fun x => |f x * g x| ^ 2) (volume : Measure (Vec 2)) := by
    simpa only [abs_mul, mul_pow, Pi.pow_apply] using hg2.continuous_mul (hf.abs.pow 2)
  have hm := hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have h := (cellMemLp_two_of_localSquare hm hs).1
  rw [Measure.restrict_congr_set Infra.Torus.unitCell_ae_eq_unitCube] at h
  exact h

/-- Homeomorphism underlying a periodic volume-preserving flow for test-function density. -/
def TestDensity.densityFlowHomeomorph (X : PeriodicVolumePreservingDiffeomorphism 2) :
    Vec 2 ≃ₜ Vec 2 where
  toEquiv := ⟨X.toFun, X.invFun, X.left_inv, X.right_inv⟩
  continuous_toFun := X.contDiff_toFun.continuous
  continuous_invFun := X.contDiff_invFun.continuous

theorem TestDensity.flow_local_integrable (X : PeriodicVolumePreservingDiffeomorphism 2)
    {g : Vec 2 → ℝ} (hg : LocallyIntegrable g (volume : Measure (Vec 2))) :
    LocallyIntegrable (fun x => g (X.invFun x)) (volume : Measure (Vec 2)) := by
  let e := TestDensity.densityFlowHomeomorph X
  have hmp : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm e.toMeasurableEquiv X.measurePreserving
  have h := (locallyIntegrable_map_homeomorph e.symm).1
    (by rw [hmp.map_eq]; exact hg)
  exact h

end AVenhance.Infra.Section5
