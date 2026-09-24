/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondOperator
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Convolution

/-!
# Riesz Second L2 Input

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology Distributions Convolution
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- Smooth compactly supported real test functions on the whole spatial domain. -/
abbrev testFunction := 𝓓((⊤ : TopologicalSpace.Opens Vec3), ℝ)

private lemma pressure_neg_kernel_locallyIntegrable' :
    LocallyIntegrable (fun z : Vec3 => -Foundation.Heat.newtonianKernel z) volume := by
  exact _root_.CKN.pressure_neg_kernel_locallyIntegrable

private lemma test_potential_conv (f : testFunction) :
    pressureNewtonianPotential (f : Vec3 → ℝ) =
      MeasureTheory.convolution (f : Vec3 → ℝ)
        (fun z : Vec3 => -Foundation.Heat.newtonianKernel z)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [pressureNewtonianPotential, MeasureTheory.convolution_def]
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]

private lemma test_potential_add (f g : testFunction) :
    pressureNewtonianPotential ((f + g : testFunction) : Vec3 → ℝ) =
      pressureNewtonianPotential (f : Vec3 → ℝ) +
        pressureNewtonianPotential (g : Vec3 → ℝ) := by
  have hf := f.hasCompactSupport.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) f.continuous pressure_neg_kernel_locallyIntegrable'
  have hg := g.hasCompactSupport.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) g.continuous pressure_neg_kernel_locallyIntegrable'
  rw [test_potential_conv, test_potential_conv, test_potential_conv]
  exact hf.add_distrib hg

private lemma test_potential_smul (c : ℝ) (f : testFunction) :
    pressureNewtonianPotential ((c • f : testFunction) : Vec3 → ℝ) =
      c • pressureNewtonianPotential (f : Vec3 → ℝ) := by
  have hf := f.hasCompactSupport.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) f.continuous pressure_neg_kernel_locallyIntegrable'
  rw [test_potential_conv, test_potential_conv]
  exact MeasureTheory.smul_convolution

private lemma mixedSecond_add_smooth {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i j : Fin 3) :
    mixedSecond (fun x => f x + g x) i j =
      fun x => mixedSecond f i j x + mixedSecond g i j x := by
  have hinner : spatialDeriv (fun y => f y + g y) j =
      fun y => spatialDeriv f j y + spatialDeriv g j y := by
    funext y
    exact spatialDeriv_add (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y) j
  funext x
  simp only [mixedSecond]
  rw [hinner]
  exact spatialDeriv_add
    ((contDiff_spatialDeriv_smooth hf j).differentiable (by norm_num) x)
    ((contDiff_spatialDeriv_smooth hg j).differentiable (by norm_num) x) i

private lemma mixedSecond_smul_smooth {f : Vec3 → ℝ} (c : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 3) :
    mixedSecond (fun x => c • f x) i j =
      fun x => c • mixedSecond f i j x := by
  have hinner : spatialDeriv (fun y => c • f y) j =
      fun y => c • spatialDeriv f j y := by
    funext y
    simp only [spatialDeriv]
    change (fderiv ℝ (c • f) y) (basisVec j) = _
    rw [fderiv_const_smul (hf.differentiable (by norm_num) y)]
    simp only [_root_.smul_apply, smul_eq_mul]
  funext x
  simp only [mixedSecond, spatialDeriv]
  rw [hinner]
  change (fderiv ℝ (c • spatialDeriv f j) x) (basisVec i) = _
  rw [fderiv_const_smul
    ((contDiff_spatialDeriv_smooth hf j).differentiable (by norm_num) x)]
  simp only [_root_.smul_apply, smul_eq_mul]

/-- Linear inclusion of compactly supported smooth test functions into L². -/
def testSource : testFunction →ₗ[ℝ] rieszSecondL2 where
  toFun f := MemLp.toLp (p := (2 : ℝ≥0∞)) (f : Vec3 → ℝ)
    (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure Vec3)) f.hasCompactSupport)
  map_add' f g := by
    change MemLp.toLp (p := (2 : ℝ≥0∞))
        ((f : Vec3 → ℝ) + (g : Vec3 → ℝ)) _ = _
    exact MemLp.toLp_add
      (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
        (μ := (volume : Measure Vec3)) f.hasCompactSupport)
      (g.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
        (μ := (volume : Measure Vec3)) g.hasCompactSupport)
  map_smul' c f := by
    change MemLp.toLp (p := (2 : ℝ≥0∞))
        (c • (f : Vec3 → ℝ)) _ = _
    exact MemLp.toLp_const_smul c
      (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
        (μ := (volume : Measure Vec3)) f.hasCompactSupport)

private lemma test_dense : DenseRange (fun f : testFunction =>
    MemLp.toLp (f : Vec3 → ℝ) (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport) :
    testFunction → rieszSecondL2) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 ?_
  intro ε hε
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le
    (p := (2 : ℝ≥0∞)) (μ := (volume : Measure Vec3)) (by norm_num)
    (by norm_num) (Lp.memLp f) hε
  let hmem : MemLp g (2 : ℝ≥0∞) volume :=
    hg₂.continuous.memLp_of_hasCompactSupport hg₁
  let φ : testFunction := TestFunction.mk g hg₂ hg₁ (by simp)
  refine ⟨MemLp.toLp g hmem, ?_⟩
  constructor
  · exact ⟨φ, rfl⟩
  · rw [Metric.mem_closedBall, dist_comm, Lp.dist_def]
    rw [← ENNReal.le_ofReal_iff_toReal_le (by
      exact ((Lp.memLp f).sub (Lp.memLp (MemLp.toLp g hmem))).eLpNorm_ne_top) hε.le]
    convert hg₃ using 1
    apply eLpNorm_congr_ae
    filter_upwards [hmem.coeFn_toLp] with x hx
    simp [hx]

lemma test_hessian_mem (i j : Fin 3) (f : testFunction) :
    MemLp (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j)
      (2 : ℝ≥0∞) volume := by
  have hP : ContDiff ℝ (⊤ : ℕ∞)
      (pressureNewtonianPotential (f : Vec3 → ℝ)) :=
    pressureNewtonianPotential_smooth f.contDiff f.hasCompactSupport
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j) :=
    contDiff_mixedSecond_smooth hP i j
  have hmeas : AEStronglyMeasurable
      (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j) volume :=
    hH.continuous.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num)
    (by norm_num) hmeas]
  have hbound := riesz_second_l2_bound_global f.contDiff f.hasCompactSupport i j
  have hsource : MemLp (f : Vec3 → ℝ) (2 : ℝ≥0∞) volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hsource_int : ∫⁻ x, absE (f : Vec3 → ℝ) x ^ (2 : ℝ) < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hsource
    norm_num at h ⊢
    simpa [absE, Real.enorm_eq_ofReal_abs] using h
  have hsource_nat : ∫⁻ x, absE (f : Vec3 → ℝ) x ^ (2 : ℕ) < ∞ := by
    convert hsource_int using 1
    norm_num [absE, Real.enorm_eq_ofReal_abs]
  have htarget_nat : ∫⁻ x,
      absE (fun y => mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j y) x ^ (2 : ℕ) <
        ∞ := by
    refine lt_of_le_of_lt hbound ?_
    simpa only [one_pow, ENNReal.ofReal_one, one_mul] using hsource_nat
  have htarget_real : ∫⁻ x,
      absE (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j) x ^ (2 : ℝ) < ∞ := by
    convert htarget_nat using 1
    norm_num [absE, Real.enorm_eq_ofReal_abs]
  have hsqrt : (∫⁻ x,
      absE (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j) x ^ (2 : ℝ)) ^
        (1 / (2 : ℝ)) < ∞ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) htarget_real.ne
  norm_num at hsqrt ⊢
  simpa [absE, Real.enorm_eq_ofReal_abs] using hsqrt

/-- L² class of a second derivative of the Newtonian potential of a test function. -/
def testHessian (i j : Fin 3) : testFunction →ₗ[ℝ] rieszSecondL2 where
  toFun f := MemLp.toLp (p := (2 : ℝ≥0∞))
    (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j)
    (test_hessian_mem i j f)
  map_add' f g := by
    have hmix := mixedSecond_add_smooth
      (pressureNewtonianPotential_smooth f.contDiff f.hasCompactSupport)
      (pressureNewtonianPotential_smooth g.contDiff g.hasCompactSupport) i j
    have hpot := test_potential_add f g
    have hraw : mixedSecond (pressureNewtonianPotential
        ((f + g : testFunction) : Vec3 → ℝ)) i j =
        mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j +
          mixedSecond (pressureNewtonianPotential (g : Vec3 → ℝ)) i j := by
      rw [hpot]
      change mixedSecond (fun x => pressureNewtonianPotential (f : Vec3 → ℝ) x +
        pressureNewtonianPotential (g : Vec3 → ℝ) x) i j = _
      exact hmix
    simpa only [hraw] using
      (MemLp.toLp_add (test_hessian_mem i j f) (test_hessian_mem i j g))
  map_smul' c f := by
    have hmix := mixedSecond_smul_smooth c
      (pressureNewtonianPotential_smooth f.contDiff f.hasCompactSupport) i j
    have hpot := test_potential_smul c f
    have hraw : mixedSecond (pressureNewtonianPotential
        ((c • f : testFunction) : Vec3 → ℝ)) i j =
        c • mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j := by
      rw [hpot]
      change mixedSecond (fun x => c • pressureNewtonianPotential
        (f : Vec3 → ℝ) x) i j = _
      exact hmix
    simpa only [hraw, RingHom.id_apply] using
      (MemLp.toLp_const_smul c (test_hessian_mem i j f))

private lemma test_hessian_norm_le (i j : Fin 3) (f : testFunction) :
    ‖MemLp.toLp (p := (2 : ℝ≥0∞))
        (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j)
        (test_hessian_mem i j f)‖ ≤
      ‖MemLp.toLp (p := (2 : ℝ≥0∞)) (f : Vec3 → ℝ)
        (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
          (μ := (volume : Measure Vec3))
          f.hasCompactSupport)‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono
  · exact (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).eLpNorm_ne_top
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      · apply ENNReal.rpow_le_rpow
        · have hbound := riesz_second_l2_bound_global f.contDiff f.hasCompactSupport i j
          have hbound' :
              (∫⁻ x, absE (fun y => mixedSecond
                (pressureNewtonianPotential (f : Vec3 → ℝ)) i j y) x ^ (2 : ℕ)) ≤
                ∫⁻ x, absE (f : Vec3 → ℝ) x ^ (2 : ℕ) := by
            simpa only [one_pow, ENNReal.ofReal_one, one_mul] using hbound
          convert hbound' using 1
          · simp only [absE, Real.enorm_eq_ofReal_abs]
            norm_num only [ENNReal.toReal_ofNat]
            simp only [ENNReal.rpow_two]
          · simp only [absE, Real.enorm_eq_ofReal_abs]
            norm_num only [ENNReal.toReal_ofNat]
            simp only [ENNReal.rpow_two]
        · positivity
      · exact f.continuous.aestronglyMeasurable
    · exact (contDiff_mixedSecond_smooth
        (pressureNewtonianPotential_smooth f.contDiff f.hasCompactSupport) i
          j).continuous.aestronglyMeasurable

private lemma test_hessian_norm_bound (i j : Fin 3) (f : testFunction) :
    ‖testHessian i j f‖ ≤ 1 * ‖testSource f‖ := by
  change ‖MemLp.toLp (p := (2 : ℝ≥0∞))
      (mixedSecond (pressureNewtonianPotential (f : Vec3 → ℝ)) i j)
      (test_hessian_mem i j f)‖ ≤ 1 * ‖MemLp.toLp (p := (2 : ℝ≥0∞))
        (f : Vec3 → ℝ)
        (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
          (μ := (volume : Measure Vec3)) f.hasCompactSupport)‖
  simpa only [one_mul] using test_hessian_norm_le i j f

/-- Continuous L² extension of the test-function Hessian operator. -/
def testHessianExtension (i j : Fin 3) :
    rieszSecondL2 →L[ℝ] rieszSecondL2 :=
  LinearMap.mkContinuous
    ((testHessian i j).extendOfNorm testSource) 1 (by
      intro f
      exact LinearMap.norm_extendOfNorm_apply_le
        (by
          change DenseRange (fun f : testFunction =>
            MemLp.toLp (p := (2 : ℝ≥0∞)) (f : Vec3 → ℝ)
              (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
                (μ := (volume : Measure Vec3)) f.hasCompactSupport))
          exact test_dense) 1
        (fun φ => test_hessian_norm_bound i j φ) f)

/-- Second-Riesz map on Schwartz functions obtained from the continuous L² extension. -/
def rieszSecondSmoothMap (i j : Fin 3) :
    SchwartzMap Vec3 ℝ →L[ℝ] rieszSecondL2 :=
  (testHessianExtension i j).comp
    (SchwartzMap.toLpCLM ℝ ℝ 2 volume)

lemma rieszSecondSmoothMap_bound (i j : Fin 3)
    (φ : SchwartzMap Vec3 ℝ) :
    ‖rieszSecondSmoothMap i j φ‖ ≤
      ‖SchwartzMap.toLpCLM ℝ ℝ 2 volume φ‖ := by
  change ‖testHessianExtension i j
      (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)‖ ≤ _
  have hdense : DenseRange testSource := by
    change DenseRange (fun f : testFunction =>
      MemLp.toLp (p := (2 : ℝ≥0∞)) (f : Vec3 → ℝ)
        (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
          (μ := (volume : Measure Vec3)) f.hasCompactSupport))
    exact test_dense
  have h := LinearMap.norm_extendOfNorm_apply_le hdense 1
    (fun ψ => test_hessian_norm_bound i j ψ)
      (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)
  change ‖((testHessian i j).extendOfNorm testSource)
      (SchwartzMap.toLpCLM ℝ ℝ 2 volume φ)‖ ≤
    ‖SchwartzMap.toLpCLM ℝ ℝ 2 volume φ‖
  simpa only [one_mul] using h

private lemma rieszSecondSmoothMap_hessian (i j : Fin 3)
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) :
    ∃ hmem : MemLp (mixedSecond (pressureNewtonianPotential F) i j)
        (2 : ℝ≥0∞) volume,
      rieszSecondSmoothMap i j (hFc.toSchwartzMap hF) = MemLp.toLp _ hmem := by
  let f : testFunction := TestFunction.mk F hF hFc (by simp)
  let hmem := test_hessian_mem i j f
  refine ⟨hmem, ?_⟩
  have hdense : DenseRange testSource := by
    change DenseRange (fun f : testFunction =>
      MemLp.toLp (p := (2 : ℝ≥0∞)) (f : Vec3 → ℝ)
        (f.continuous.memLp_of_hasCompactSupport (p := (2 : ℝ≥0∞))
          (μ := (volume : Measure Vec3)) f.hasCompactSupport))
    exact test_dense
  have hext := LinearMap.extendOfNorm_eq hdense (by
    refine ⟨1, ?_⟩
    intro ψ
    exact test_hessian_norm_bound i j ψ) f
  have hemb : SchwartzMap.toLpCLM ℝ ℝ 2 volume (hFc.toSchwartzMap hF) =
      testSource f := by
    let hFmem : MemLp F (2 : ℝ≥0∞) volume :=
      hF.continuous.memLp_of_hasCompactSupport hFc
    change MemLp.toLp (p := (2 : ℝ≥0∞)) F hFmem =
      MemLp.toLp F hFmem
    rfl
  change testHessianExtension i j
      (SchwartzMap.toLpCLM ℝ ℝ 2 volume (hFc.toSchwartzMap hF)) = _
  rw [hemb]
  change ((testHessian i j).extendOfNorm testSource) (testSource f) = _
  rw [hext]
  rfl

/-- The indexed smooth Hessian map obtained from the global endpoint estimate. -/
def rieszSecondL2Input (i j : Fin 3) : RieszSecondL2Input i j where
  smoothMap := rieszSecondSmoothMap i j
  smooth_bound := rieszSecondSmoothMap_bound i j
  smooth_hessian := by
    intro F hF hFc
    exact rieszSecondSmoothMap_hessian i j hF hFc

/-- The completed endpoint extension agrees with the smooth Hessian on compact data. -/
theorem rieszSecondL2Input_extension_smooth_hessian (i j : Fin 3)
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) :
    ∃ hmem : MemLp (mixedSecond (pressureNewtonianPotential F) i j)
        (2 : ℝ≥0∞) volume,
      rieszSecondL2Extension (rieszSecondL2Input i j)
          (MemLp.toLp F (hF.continuous.memLp_of_hasCompactSupport hFc)) =
        MemLp.toLp (mixedSecond (pressureNewtonianPotential F) i j) hmem := by
  exact rieszSecondL2Extension_smooth_hessian (rieszSecondL2Input i j) hF hFc

end CKN.Foundation.Euclidean
