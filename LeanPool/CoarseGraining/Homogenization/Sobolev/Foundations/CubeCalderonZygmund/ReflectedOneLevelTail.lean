/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedGlobalEnergy
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GlobalStoppingFamily
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaTailControl
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaVitaliAssembly
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionWeightedTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionDivergenceRhs

/-!
# The reflected one-level cube good-`λ` inequality

This is the unconditional Caffarelli--Peral one-level estimate on a centered
cube.  Odd reflection, extension by zero, stopping radii, local harmonic
comparison, and Vitali selection are all constructed internally.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

/-- The centered-cube one-level good-`λ` bound obtained from the reflected
parent problem.  The stopping energy is the corrected square root of the sum
of the two squared normalized energies. -/
theorem sqWeightedMeasure_reflected_oneLevel_tail_originCube
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth)
    (hq : 2 < q.exponent.toReal) {m : ℤ} {sigma0 eps M level : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M) (u : H10Function (openCubeSet (originCube d m)))
    (H : Vec d → Vec d)
    (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hweak : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (H x) (psi.toH1Function.grad x) ∂volume)
    (hlevel : reflectedGoodLambdaCutoff m depth eps sigma0 u H < level) :
    sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad) volume
        ({x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ∩
          openCubeSet (originCube d m)) ≤
      ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad) volume
            ({x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} ∩
              openCubeSet (originCube d m)) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField H) volume
              ({x | eps * level / 2 < ‖(sigma0⁻¹ • hilbertifyVecField H) x‖} ∩
                openCubeSet (originCube d m))) := by
  let Q : Set (Vec d) := openCubeSet (originCube d m)
  let P : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let fu : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField H
  obtain ⟨uP, _huP_fun, huP_grad, hweakP⟩ :=
    exists_h1Function_cubeDirichletOddReflectionParent_divergence_rhs_originCube hH hweak
  let HP : Vec d → Vec d :=
    cubeDirichletOddReflectionVectorField (originCube d m) H
  have hHP : MemVectorL2 P HP := by
    simpa only [P, HP] using
      memVectorL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField hH
  have hweakP' : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi → tsupport phi ⊆ P →
      sigma0 * ∫ y in P, vecDot (uP.grad y) (euclideanGradient phi y) ∂volume =
        -∫ y in P, vecDot (HP y) (euclideanGradient phi y) ∂volume := by
    simpa only [P, HP] using hweakP
  let F : Vec d → HilbertVec d := reflectedParentGradientExtension m uP
  let Hext : Vec d → Vec d := reflectedParentDatumExtension m HP
  let gext : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField Hext
  have hF : MemLp F 2 volume := by
    simpa only [F] using memLp_reflectedParentGradientExtension_two m uP
  have hHext : MemLp (hilbertifyVecField Hext) 2 volume := by
    simpa only [Hext] using
      memLp_hilbertify_reflectedParentDatumExtension_two m HP hHP
  have hgext : MemLp gext 2 volume := by
    exact hHext.const_smul sigma0⁻¹
  have hcutoff :
      Real.sqrt (((2 * (cubeRadius (originCube d m) /
        (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
        ((∫ y, ‖F y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y, ‖gext y‖ ^ (2 : ℕ) ∂volume)) < level := by
    have hglobal := reflectedGoodLambdaCutoff_eq_globalEnergy
      (depth := depth) (eps := eps) hsigma0 u uP H HP hH huP_grad (by rfl)
    rw [hglobal] at hlevel
    simpa only [reflectedStoppingRadius, reflectedGlobalSquaredEnergy, F, Hext, gext] using! hlevel
  have hlevel_pos : 0 < level :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  let T : Set (Vec d) := {x | M * level < ‖F x‖} ∩ Q
  obtain ⟨D, radius, hDnull, hradius⟩ :=
    exists_globalStoppingFamily depth F gext eps M level hF hgext heps hM
      hcutoff T (by intro x hx; exact hx.1)
  have hQP : Q ⊆ P := by
    intro x hx
    exact cubeFaceReflectionBlockSet_originCube_subset_openCubeSet_succ d m
      (openCubeSet_subset_cubeFaceReflectionBlockSet (originCube d m) hx)
  have hQmeas : MeasurableSet Q := by
    simpa only [Q] using measurableSet_openCubeSet (originCube d m)
  have hPmeas : MeasurableSet P := by
    simpa only [P] using measurableSet_openCubeSet (originCube d (m + 1))
  have hFQ : F =ᵐ[volume.restrict Q] fu := by
    filter_upwards [ae_restrict_mem hQmeas] with x hx
    change (P.indicator (hilbertifyVecField uP.grad)) x = fu x
    rw [Set.indicator_of_mem (hQP hx)]
    change HilbertVec.ofVec (uP.grad x) = HilbertVec.ofVec (u.toH1Function.grad x)
    rw [huP_grad, cubeDirichletOddReflectionVectorField_eq_self_of_mem_openCubeSet
      (originCube d m) _ hx]
  let K : ℝ≥0∞ := oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  have hvitali : sqWeightedMeasure F volume (T ∩ D) ≤
      K * oneStoppingBallTailControl F gext eps level P := by
    apply measure_le_mul_measure_of_vitali_stopping_family
      (sqWeightedMeasure F volume) (oneStoppingBallTailControl F gext eps level)
      (T ∩ D) P radius
      (cubeRadius (originCube d m) / (10 * (3 : ℝ) ^ depth)) 5 K
    · intro x hx
      exact (hradius x hx).2.1
    · intro x hx
      exact (hradius x hx).1
    · norm_num
    · intro x hx
      obtain ⟨hr, hcutoffx, hstop, hlast⟩ := hradius x hx
      obtain ⟨_hF, _hHext, hlocalF, hlocalweak⟩ :=
        reflectedParent_oneStoppingBall_inputs (depth := depth) (sigma0 := sigma0)
          (by exact hx.1.2) hr hcutoffx uP HP hHP hweakP'
      have hball := sqWeightedMeasure_oneStoppingBall_le G hq x hr hsigma0 heps heps_one
        (lt_of_lt_of_le zero_lt_one hM) hlevel_pos hcutoffx F Hext hF hHext
        (reflectedParentLocalSolution (depth := depth) m x (radius x) uP
          (stoppingComparisonParent_axisCube_subset_openCubeSet_originCube_succ
            depth hx.1.2 hr hcutoffx)) hlocalF hlocalweak hstop hlast
      have hmono :
          sqWeightedMeasure F volume ((T ∩ D) ∩ Metric.closedBall x (5 * radius x)) ≤
            sqWeightedMeasure F volume
              ({y | M * level < ‖F y‖} ∩ Metric.closedBall x (5 * radius x)) := by
        apply measure_mono
        intro y hy
        exact ⟨hy.1.1.1, hy.2⟩
      calc
        sqWeightedMeasure F volume ((T ∩ D) ∩ Metric.closedBall x (5 * radius x)) ≤
            sqWeightedMeasure F volume
              ({y | M * level < ‖F y‖} ∩ Metric.closedBall x (5 * radius x)) := hmono
        _ ≤ K *
            (sqWeightedMeasure F volume
                ({y | level / 2 < ‖F y‖} ∩ Metric.closedBall x (radius x)) +
              ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
                sqWeightedMeasure gext volume
                  ({y | eps * level / 2 < ‖gext y‖} ∩
                    Metric.closedBall x (radius x))) := by
              simpa only [K, gext] using hball
        _ = K * oneStoppingBallTailControl F gext eps level
            (Metric.closedBall x (radius x)) := by
              rw [oneStoppingBallTailControl_apply F gext eps level measurableSet_closedBall]
    · intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
      obtain ⟨hr, hcutoffx, _hstop, _hlast⟩ := hradius x hx
      exact closedBall_subset_openCubeSet_originCube_succ_of_mem hx.1.2 hr.le
        (by
          have hdenom : 2 ≤ 10 * (3 : ℝ) ^ depth := by
            have hpow : 1 ≤ (3 : ℝ) ^ depth := one_le_pow₀ (by norm_num)
            nlinarith
          exact hcutoffx.trans (div_le_div_of_nonneg_left (cubeRadius_pos _).le
            (by norm_num) hdenom)) hyx
  have hnuD : sqWeightedMeasure F volume Dᶜ = 0 :=
    MeasureTheory.withDensity_absolutelyContinuous volume _ hDnull
  have hTD : sqWeightedMeasure F volume (T ∩ D) =
      sqWeightedMeasure F volume T :=
    MeasureTheory.measure_inter_conull hnuD
  have hfu_meas : AEStronglyMeasurable fu (volume.restrict Q) := by
    simpa only [fu, Q, volumeMeasureOn] using
      (memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2).aestronglyMeasurable
  have hF_tail (a : ℝ) :
      sqWeightedMeasure F volume ({x | a < ‖F x‖} ∩ P) =
        sqWeightedMeasure fu volume ({x | a < ‖fu x‖} ∩ Q) * ((3 : ℝ≥0∞) ^ d) := by
    have hindicator := sqWeightedMeasure_indicator_tail_inter_eq_of_subset
      (μ := volume) (f := hilbertifyVecField uP.grad) (a := a)
      hPmeas hPmeas (by rintro x hx; exact hx)
    have hreflect :
        sqWeightedMeasure F volume ({x | a < ‖F x‖} ∩ P) =
          sqWeightedMeasure
            (fun x => HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (fun y => u.toH1Function.grad y) x)) volume
            ({x | a < ‖HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (fun y => u.toH1Function.grad y) x)‖} ∩ P) := by
      simpa only [F, P, reflectedParentGradientExtension, huP_grad] using! hindicator
    calc
      sqWeightedMeasure F volume ({x | a < ‖F x‖} ∩ P) =
          sqWeightedMeasure
            (fun x => HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (fun y => u.toH1Function.grad y) x)) volume
            ({x | a < ‖HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (fun y => u.toH1Function.grad y) x)‖} ∩ P) := hreflect
      _ = ((3 : ℝ≥0∞) ^ d) *
          sqWeightedMeasure fu volume ({x | a < ‖fu x‖} ∩ Q) := by
            simpa only [fu, Q, mul_comm] using!
              sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_tail
                (fun y => u.toH1Function.grad y) hfu_meas
      _ = sqWeightedMeasure fu volume ({x | a < ‖fu x‖} ∩ Q) *
          ((3 : ℝ≥0∞) ^ d) := by ring
  have hFQpoint : ∀ x ∈ Q, F x = fu x := by
    intro x hx
    change (P.indicator (hilbertifyVecField uP.grad)) x = fu x
    rw [Set.indicator_of_mem (hQP hx)]
    change HilbertVec.ofVec (uP.grad x) = HilbertVec.ofVec (u.toH1Function.grad x)
    rw [huP_grad, cubeDirichletOddReflectionVectorField_eq_self_of_mem_openCubeSet
      (originCube d m) _ hx]
  have hT_eq : T = {x | M * level < ‖fu x‖} ∩ Q := by
    ext x
    simp only [T, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨by rw [hFQpoint x hx.2] at hx; exact hx.1, hx.2⟩
    · intro hx
      exact ⟨by rw [hFQpoint x hx.2]; exact hx.1, hx.2⟩
  have hT_source : sqWeightedMeasure F volume T =
      sqWeightedMeasure fu volume ({x | M * level < ‖fu x‖} ∩ Q) := by
    rw [hT_eq]
    exact sqWeightedMeasure_apply_inter_eq_of_ae_eq_restrict hQmeas hFQ
  have hHP_scalar :
      (fun x => HilbertVec.ofVec
        (cubeDirichletOddReflectionVectorField (originCube d m)
          (sigma0⁻¹ • H) x)) =
        sigma0⁻¹ • hilbertifyVecField HP := by
    funext x
    change (HilbertVec.ofVecL d)
        (cubeDirichletOddReflectionVectorField (originCube d m) (sigma0⁻¹ • H) x) =
      sigma0⁻¹ • (HilbertVec.ofVecL d) (HP x)
    rw [← (HilbertVec.ofVecL d).map_smul]
    congr 1
    funext i
    simp only [HP, cubeDirichletOddReflectionVectorField,
      cubeCoordinateFoldReflectedVectorField, Pi.smul_apply, smul_eq_mul]
    ring
  have hgext_indicator : gext = P.indicator (sigma0⁻¹ • hilbertifyVecField HP) := by
    change sigma0⁻¹ • hilbertifyVecField Hext = P.indicator (sigma0⁻¹ • hilbertifyVecField HP)
    rw [show hilbertifyVecField Hext = P.indicator (hilbertifyVecField HP) by
      simpa only [Hext] using hilbertifyVecField_reflectedParentDatumExtension m HP]
    funext x
    change sigma0⁻¹ • (P.indicator (hilbertifyVecField HP)) x =
      P.indicator (sigma0⁻¹ • hilbertifyVecField HP) x
    by_cases hx : x ∈ P
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      exact smul_zero _
  have hH_source_meas : AEStronglyMeasurable (sigma0⁻¹ • hilbertifyVecField H)
      (volume.restrict Q) :=
    (memHilbertVectorL2_hilbertifyVecField hH).const_smul sigma0⁻¹ |>.aestronglyMeasurable
  have hgext_tail (a : ℝ) :
      sqWeightedMeasure gext volume ({x | a < ‖gext x‖} ∩ P) =
        sqWeightedMeasure g volume ({x | a < ‖g x‖} ∩ Q) * ((3 : ℝ≥0∞) ^ d) := by
    have hindicator := sqWeightedMeasure_indicator_tail_inter_eq_of_subset
      (μ := volume) (f := sigma0⁻¹ • hilbertifyVecField HP) (a := a)
      hPmeas hPmeas (by rintro x hx; exact hx)
    have hreflect :
        sqWeightedMeasure gext volume ({x | a < ‖gext x‖} ∩ P) =
          sqWeightedMeasure
            (fun x => HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (sigma0⁻¹ • H) x)) volume
            ({x | a < ‖HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (sigma0⁻¹ • H) x)‖} ∩ P) := by
      rw [hgext_indicator, hindicator]
      rw [← hHP_scalar]
    calc
      sqWeightedMeasure gext volume ({x | a < ‖gext x‖} ∩ P) =
          sqWeightedMeasure
            (fun x => HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (sigma0⁻¹ • H) x)) volume
            ({x | a < ‖HilbertVec.ofVec
              (cubeDirichletOddReflectionVectorField (originCube d m)
                (sigma0⁻¹ • H) x)‖} ∩ P) := hreflect
      _ = ((3 : ℝ≥0∞) ^ d) *
          sqWeightedMeasure g volume ({x | a < ‖g x‖} ∩ Q) := by
            simpa only [g, Q, mul_comm] using!
              sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_tail
                (sigma0⁻¹ • H) hH_source_meas
      _ = sqWeightedMeasure g volume ({x | a < ‖g x‖} ∩ Q) *
          ((3 : ℝ≥0∞) ^ d) := by ring
  have hkappa : oneStoppingBallTailControl F gext eps level P =
      sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ P) +
        ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
          sqWeightedMeasure gext volume
            ({x | eps * level / 2 < ‖gext x‖} ∩ P) :=
    oneStoppingBallTailControl_apply_ambient F gext eps level hPmeas
  calc
    sqWeightedMeasure fu volume ({x | M * level < ‖fu x‖} ∩ Q) =
        sqWeightedMeasure F volume T := hT_source.symm
    _ = sqWeightedMeasure F volume (T ∩ D) := hTD.symm
    _ ≤ K * oneStoppingBallTailControl F gext eps level P := hvitali
    _ = K *
        (sqWeightedMeasure F volume ({x | level / 2 < ‖F x‖} ∩ P) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure gext volume
              ({x | eps * level / 2 < ‖gext x‖} ∩ P)) := by rw [hkappa]
    _ = ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure fu volume
            ({x | level / 2 < ‖fu x‖} ∩ Q) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure g volume
              ({x | eps * level / 2 < ‖g x‖} ∩ Q)) := by
          rw [hF_tail (level / 2), hgext_tail (eps * level / 2)]
          dsimp only [K]
          ring

end CubeCalderonZygmund

end

end Homogenization
