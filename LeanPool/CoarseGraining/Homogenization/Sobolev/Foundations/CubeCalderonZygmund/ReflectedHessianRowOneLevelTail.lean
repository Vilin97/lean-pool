/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorHessianRowTailTransfer
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorOneLevelTail
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorParentGeometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedParentHessianRowIdentification
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionScalarWeightedTail
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakHessianRowL2Energy
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakPoissonDerivative
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.Regularity
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentApprox

/-!
# One-level tails for Hessian rows of scalar Dirichlet solutions

This file crosses the global good-`lambda` seam for one weak-Hessian row. It
constructs both the source Hessian and the canonical half-parent Hessian,
identifies their rows by mixed-parity reflection, and transfers the interior
one-level estimate back to the source cube. No regularity, comparison, or
reflection premise is exposed to the caller.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

/-- A source-facing large-scale cutoff for one reflected Hessian row. The
first energy is bounded by the source weak-`H²` coordinate sum; the second is
the exact raw source scalar `L²` energy. -/
noncomputable def reflectedHessianRowGoodLambdaCutoff
    {d : ℕ} {m : ℤ} (depth : ℕ) (eps : ℝ)
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (F : Vec d → ℝ) : ℝ :=
  Real.sqrt
    (((2 * (cubeRadius (originCube d m) /
      (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
      ((3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) +
        (eps⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
          ∫ x in openCubeSet (originCube d m), F x * F x
            ∂MeasureTheory.volume))

theorem reflectedHessianRowGoodLambdaCutoff_nonneg
    {d : ℕ} {m : ℤ} (depth : ℕ) (eps : ℝ)
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (F : Vec d → ℝ) :
    0 ≤ reflectedHessianRowGoodLambdaCutoff depth eps H F :=
  Real.sqrt_nonneg _

private theorem integral_sqNorm_reflectedHessianRow_parent_le
    {d : ℕ} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i (fun y j ↦ H.hess i j y) x)‖ ^ (2 : ℕ)
          ∂volume ≤
      (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) := by
  let R : Vec d → Vec d := fun y j ↦ H.hess i j y
  have hR : MemVectorL2 (openCubeSet (originCube d m)) R := by
    change MemLp R 2 (volumeMeasureOn (openCubeSet (originCube d m)))
    rw [MeasureTheory.memLp_pi_iff]
    intro j
    exact H.hess_memL2 i j
  have hrowMem : MemLp (hilbertifyVecField R) 2
      (volumeMeasureOn (openCubeSet (originCube d m))) := by
    simpa only [R] using H.hessianHilbertRow_memLp_two i
  have hrowNorm :
      (eLpNorm (hilbertifyVecField R) 2
        (volumeMeasureOn (openCubeSet (originCube d m)))).toReal ≤
          H.hessianCoordL2NormSum := by
    simpa only [R] using H.toReal_eLpNorm_hessianHilbertRow_two_le i
  have hrowIntegral :
      ∫ x in openCubeSet (originCube d m),
          ‖HilbertVec.ofVec (R x)‖ ^ (2 : ℕ) ∂volume ≤
        H.hessianCoordL2NormSum ^ (2 : ℕ) := by
    have heq := toReal_eLpNorm_two_sq_eq_integral_norm_sq hrowMem
    have heq' :
        (eLpNorm (hilbertifyVecField R) 2
          (volumeMeasureOn (openCubeSet (originCube d m)))).toReal ^ 2 =
            ∫ x in openCubeSet (originCube d m),
              ‖HilbertVec.ofVec (R x)‖ ^ (2 : ℕ) ∂volume := by
      simpa only [volumeMeasureOn, hilbertifyVecField] using heq
    have hnorm_nonneg :
        0 ≤ (eLpNorm (hilbertifyVecField R) 2
          (volumeMeasureOn (openCubeSet (originCube d m)))).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [heq', H.hessianCoordL2NormSum_nonneg, sq_nonneg
      (H.hessianCoordL2NormSum -
        (eLpNorm (hilbertifyVecField R) 2
          (volumeMeasureOn (openCubeSet (originCube d m)))).toReal)]
  calc
    ∫ x in openCubeSet (originCube d (m + 1)),
        ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x)‖ ^ (2 : ℕ) ∂volume =
      ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot
          (cubeDirichletOddReflectionVectorField (originCube d m) R x)
          (cubeDirichletOddReflectionVectorField (originCube d m) R x)
          ∂volume := by
        refine MeasureTheory.setIntegral_congr_fun
          (measurableSet_openCubeSet (originCube d (m + 1))) ?_
        intro x _hx
        calc
          ‖HilbertVec.ofVec
              (cubeDirichletOddReflectionHessianRowVectorField
                (originCube d m) i R x)‖ ^ (2 : ℕ) =
              ‖HilbertVec.ofVec
                (cubeDirichletOddReflectionVectorField
                  (originCube d m) R x)‖ ^ (2 : ℕ) :=
            congrArg (fun t : ℝ ↦ t ^ (2 : ℕ))
              (norm_hilbertVec_cubeDirichletOddReflectionHessianRowVectorField_eq_oddReflection
                (originCube d m) i R x)
          _ = vecDot
              (cubeDirichletOddReflectionVectorField (originCube d m) R x)
              (cubeDirichletOddReflectionVectorField (originCube d m) R x) :=
            HilbertVec.norm_sq_ofVec _
    _ = (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m), vecDot (R x) (R x)
          ∂volume :=
      setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_self_pairing_of_memVectorL2_three_pow
        hR
    _ = (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m),
          ‖HilbertVec.ofVec (R x)‖ ^ (2 : ℕ) ∂volume := by
      congr 1
      refine MeasureTheory.setIntegral_congr_fun
        (measurableSet_openCubeSet (originCube d m)) ?_
      intro x _hx
      exact (HilbertVec.norm_sq_ofVec (R x)).symm
    _ ≤ (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hrowIntegral (by positivity)

private theorem integral_sqNorm_openParentGradientExtension_hessianRow_le
    {d : ℕ} {m : ℤ}
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (i : Fin d)
    (uU : H1Function
      (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
    (hrow : hilbertifyVecField uU.grad =ᵐ[
      volume.restrict
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))]
      fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i (fun y j ↦ H.hess i j y) x)) :
    ∫ x, ‖openParentGradientExtension
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) uU x‖ ^
          (2 : ℕ) ∂volume ≤
      (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) := by
  let U : Set (Vec d) :=
    scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
  let P : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let row : Vec d → HilbertVec d := fun x ↦ HilbertVec.ofVec
    (cubeDirichletOddReflectionHessianRowVectorField
      (originCube d m) i (fun y j ↦ H.hess i j y) x)
  have hUmeas : MeasurableSet U :=
    (isOpen_scaledOpenCubeSet
      (originCube d (m + 1)) (1 / 2 : ℝ)).measurableSet
  have hUP : U ⊆ P := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
      (originCube d (m + 1)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)
    intro j
    exact le_of_lt (hx j)
  have hrowMem : MemLp row 2 (volume.restrict P) := by
    exact memLp_openCubeSet_succ_originCube_hessianRowVectorField
      i FiniteLpExponent.two (H.hessianHilbertRow_memLp_two i)
  have hrowInt : IntegrableOn (fun x ↦ ‖row x‖ ^ (2 : ℕ)) P volume :=
    hrowMem.integrable_norm_pow (by norm_num)
  have hzero :
      (fun x ↦ ‖openParentGradientExtension U uU x‖ ^ (2 : ℕ)) =
        U.indicator (fun x ↦ ‖hilbertifyVecField uU.grad x‖ ^ (2 : ℕ)) := by
    funext x
    by_cases hx : x ∈ U
    · simp [openParentGradientExtension, hx]
    · simp [openParentGradientExtension, hx]
  calc
    ∫ x, ‖openParentGradientExtension U uU x‖ ^ (2 : ℕ) ∂volume =
        ∫ x in U, ‖hilbertifyVecField uU.grad x‖ ^ (2 : ℕ) ∂volume := by
      rw [hzero, integral_indicator_eq_integral_restrict hUmeas]
    _ = ∫ x in U, ‖row x‖ ^ (2 : ℕ) ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hrow] with x hx
      rw [hx]
    _ ≤ ∫ x in P, ‖row x‖ ^ (2 : ℕ) ∂volume := by
      apply MeasureTheory.setIntegral_mono_set hrowInt
      · exact Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖row x‖
      · exact Filter.Eventually.of_forall hUP
    _ ≤ (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) := by
      simpa only [row, P] using
        integral_sqNorm_reflectedHessianRow_parent_le H i

private theorem integral_sqNorm_openParentDatumExtension_single_le
    {d : ℕ} {m : ℤ} (i : Fin d) (F : Vec d → ℝ)
    (hF : MemScalarL2 (openCubeSet (originCube d m)) F) :
    ∫ x, ‖hilbertifyVecField
        (openParentDatumExtension
          (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))
          (fun y j ↦ if j = i then
            cubeDirichletOddReflectionScalar (originCube d m) F y else 0)) x‖ ^
          (2 : ℕ) ∂volume ≤
      (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m), F x * F x ∂volume := by
  let U : Set (Vec d) :=
    scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
  let P : Set (Vec d) := openCubeSet (originCube d (m + 1))
  let FR : Vec d → ℝ :=
    cubeDirichletOddReflectionScalar (originCube d m) F
  let datum : Vec d → Vec d := fun y j ↦ if j = i then FR y else 0
  have hUmeas : MeasurableSet U :=
    (isOpen_scaledOpenCubeSet
      (originCube d (m + 1)) (1 / 2 : ℝ)).measurableSet
  have hUP : U ⊆ P := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
      (originCube d (m + 1)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)
    intro j
    exact le_of_lt (hx j)
  have hFR : MemScalarL2 P FR := by
    simpa only [P, FR] using
      memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
        (m := m) hF
  have hFRint : IntegrableOn (fun x ↦ FR x * FR x) P volume :=
    hFR.integrable_mul hFR
  have hdatumPoint (x : Vec d) : datum x = Pi.single i (FR x) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [datum]
    · simp [datum, hji]
  have hdatumSq : ∀ x, ‖(hilbertifyVecField datum) x‖ ^ (2 : ℕ) =
      FR x * FR x := by
    intro x
    change ‖HilbertVec.ofVec (datum x)‖ ^ (2 : ℕ) = FR x * FR x
    rw [hdatumPoint]
    have hkey : ‖HilbertVec.ofVec (Pi.single i (FR x))‖ = ‖FR x‖ :=
      PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin d => ℝ) i (FR x)
    rw [hkey, Real.norm_eq_abs, sq_abs]
    ring
  have hzero :
      (fun x ↦ ‖hilbertifyVecField (openParentDatumExtension U datum) x‖ ^
          (2 : ℕ)) = U.indicator (fun x ↦ FR x * FR x) := by
    funext x
    by_cases hx : x ∈ U
    · rw [hilbertifyVecField_openParentDatumExtension,
        Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact hdatumSq x
    · rw [hilbertifyVecField_openParentDatumExtension,
        Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  calc
    ∫ x, ‖hilbertifyVecField (openParentDatumExtension U datum) x‖ ^
          (2 : ℕ) ∂volume =
        ∫ x in U, FR x * FR x ∂volume := by
      rw [hzero, integral_indicator_eq_integral_restrict hUmeas]
    _ ≤ ∫ x in P, FR x * FR x ∂volume := by
      apply MeasureTheory.setIntegral_mono_set hFRint
      · exact Filter.Eventually.of_forall fun x ↦ mul_self_nonneg (FR x)
      · exact Filter.Eventually.of_forall hUP
    _ = (3 : ℝ) ^ d *
        ∫ x in openCubeSet (originCube d m), F x * F x ∂volume := by
      simpa only [P, FR] using
        setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_sq_of_memScalarL2_three_pow
          hF

/-- The global source-cube one-level good-`lambda` estimate for every Hessian
row of a scalar Dirichlet Poisson solution. All weak Hessians, reflected
representatives, local equations, and tail transfers are constructed inside
the theorem. -/
theorem exists_hasWeakHessianOn_sqWeightedMeasure_oneLevel_tail_originCube
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth)
    (hq : 2 < q.exponent.toReal) {m : ℤ} {eps M : ℝ}
    (heps : 0 < eps) (heps_one : eps ≤ 1) (hM : 1 ≤ M)
    (F : Vec d → ℝ)
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)))
    (u : H10Function (openCubeSet (originCube d m)))
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F) :
    ∃ H : HasWeakHessianOn
        (openCubeSet (originCube d m)) u.toH1Function,
      H.hessianCoordL2NormSum ≤
          CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact
              (originCube d m) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞) F ∧
        ∀ (i : Fin d) (level : ℝ),
          reflectedHessianRowGoodLambdaCutoff depth eps H F < level →
          sqWeightedMeasure
              (hilbertifyVecField (fun x j ↦ H.hess i j x)) volume
              ({x | M * level <
                ‖hilbertifyVecField (fun y j ↦ H.hess i j y) x‖} ∩
                openCubeSet (originCube d m)) ≤
            ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
              (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
                ENNReal.ofReal (eps ^ (2 : ℕ))) *
              (sqWeightedMeasure
                  (hilbertifyVecField (fun x j ↦ H.hess i j x)) volume
                  ({x | level / 2 <
                    ‖hilbertifyVecField (fun y j ↦ H.hess i j y) x‖} ∩
                    openCubeSet (originCube d m)) +
                ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
                  sqWeightedMeasure F volume
                    ({x | eps * level / 2 < ‖F x‖} ∩
                      openCubeSet (originCube d m))) := by
  obtain ⟨H, hH⟩ :=
    (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityExact
      (originCube d m)).2 u F hF hweak
  refine ⟨H, hH, ?_⟩
  obtain ⟨uP, _huPfun, huPgrad, hweakP, uU, _huUfun, huUgrad, HU, _hHU⟩ :=
    hweak.exists_cubeDirichletOddReflectionParent_innerHalf_hasWeakHessianOn hF
  intro i level hlevel
  let Q : Set (Vec d) := openCubeSet (originCube d m)
  let U : Set (Vec d) :=
    scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
  let FR : Vec d → ℝ :=
    cubeDirichletOddReflectionScalar (originCube d m) F
  let datum : Vec d → Vec d := fun x j ↦ if j = i then FR x else 0
  let rowU : H1Function U := HU.gradCoordH1Function i
  let R : Vec d → Vec d := fun x j ↦ H.hess i j x
  let row : Vec d → HilbertVec d := hilbertifyVecField R
  have hUopen : IsOpen U :=
    (isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos
      (originCube d (m + 1)) (by norm_num : 0 < (1 / 2 : ℝ))).isOpen
  have hUparent : U ⊆ openCubeSet (originCube d (m + 1)) := by
    intro x hx
    apply scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
      (originCube d (m + 1)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)
    intro j
    exact le_of_lt (hx j)
  have hQU : Q ⊆ U := by
    change openCubeSet (originCube d m) ⊆
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
    rw [← scaledOpenCubeSet_originCube_succ_one_div_three]
    intro x hx j
    have hxj := hx j
    change |x j - cubeCenter (originCube d (m + 1)) j| <
      (1 / 2 : ℝ) * cubeRadius (originCube d (m + 1))
    change |x j - cubeCenter (originCube d (m + 1)) j| <
      (1 / 3 : ℝ) * cubeRadius (originCube d (m + 1)) at hxj
    nlinarith [cubeRadius_pos (originCube d (m + 1))]
  have hFopen : MemScalarL2 Q F := by
    simpa only [Q] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure
        (originCube d m) hF
  have hFRparent : MemScalarL2
      (openCubeSet (originCube d (m + 1))) FR := by
    simpa only [FR] using
      memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
        (m := m) hFopen
  have hFRU : MemScalarL2 U FR := memL2On_mono hUparent hFRparent
  have hweakU : WeakPoissonEquationOn U uU FR := by
    have hres := hweakP.restrict hUopen hUparent
    intro φ hφ hφs hφsub
    have ht := hres.test φ hφ hφs hφsub
    simpa only [H1Function.restrict, huUgrad] using ht
  have hweakRow : ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (1 : ℝ) * ∫ y in U,
          vecDot (rowU.grad y) (euclideanGradient φ y) ∂volume =
        -∫ y in U, vecDot (datum y) (euclideanGradient φ y) ∂volume := by
    simpa only [rowU, datum, FR, one_mul] using
      hweakU.gradCoordH1Function_weakDivergence hUopen hFRU HU i
  have hdatum : MemVectorL2 U datum := by
    simpa only [datum] using memVectorL2_singleCoordinate hFRU i
  have hidentified :=
    H.cubeDirichletOddReflectionParent_innerHalf_hessianRow_ae_eq
      huPgrad huUgrad HU i
  have hUrow : hilbertifyVecField rowU.grad =ᵐ[volume.restrict U]
      fun x ↦ HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i R x) := by
    simpa only [rowU, R, U, hilbertifyVecField,
      HasWeakHessianOn.gradCoordH1Function_grad] using! hidentified
  have hQsource : openParentGradientExtension U rowU =ᵐ[volume.restrict Q] row := by
    have hrestricted := hUrow.filter_mono
      (ae_mono (Measure.restrict_mono hQU le_rfl))
    filter_upwards [hrestricted, ae_restrict_mem
      (measurableSet_openCubeSet (originCube d m))] with x hx hxQ
    change U.indicator (hilbertifyVecField rowU.grad) x = row x
    rw [Set.indicator_of_mem (hQU hxQ), hx]
    change HilbertVec.ofVec
        (cubeDirichletOddReflectionHessianRowVectorField
          (originCube d m) i R x) = HilbertVec.ofVec (R x)
    rw [cubeDirichletOddReflectionHessianRowVectorField_eq_self_of_mem_openCubeSet
      (originCube d m) i R hxQ]
  have hRmeas : AEStronglyMeasurable row (volume.restrict Q) := by
    simpa only [row, R, Q] using
      (H.hessianHilbertRow_memLp_two i).aestronglyMeasurable
  have htransfer :=
    openParentGradientExtension_reflectedHessianRow_tail_transfer
      i R hRmeas rowU hUrow hQsource
  have hgradientEnergy :
      ∫ x, ‖openParentGradientExtension U rowU x‖ ^ (2 : ℕ) ∂volume ≤
        (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) := by
    simpa only [U, rowU, R] using
      integral_sqNorm_openParentGradientExtension_hessianRow_le H i rowU hUrow
  have hdatumEnergy :
      ∫ x, ‖hilbertifyVecField (openParentDatumExtension U datum) x‖ ^
          (2 : ℕ) ∂volume ≤
        (3 : ℝ) ^ d * ∫ x in Q, F x * F x ∂volume := by
    simpa only [U, datum, FR, Q] using
      integral_sqNorm_openParentDatumExtension_single_le i F hFopen
  have hcutoff :
      Real.sqrt (((2 * (cubeRadius (originCube d m) /
        (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹ *
        ((∫ y, ‖openParentGradientExtension U rowU y‖ ^ (2 : ℕ) ∂volume) +
          (eps⁻¹) ^ (2 : ℕ) * ∫ y,
            ‖((1 : ℝ)⁻¹ • hilbertifyVecField
              (openParentDatumExtension U datum)) y‖ ^ (2 : ℕ) ∂volume)) < level := by
    have henergy :
        (∫ y, ‖openParentGradientExtension U rowU y‖ ^ (2 : ℕ) ∂volume) +
            (eps⁻¹) ^ (2 : ℕ) * ∫ y,
              ‖((1 : ℝ)⁻¹ • hilbertifyVecField
                (openParentDatumExtension U datum)) y‖ ^ (2 : ℕ) ∂volume ≤
          (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) +
            (eps⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
              ∫ x in Q, F x * F x ∂volume := by
      simp only [inv_one, one_smul]
      calc
        (∫ y, ‖openParentGradientExtension U rowU y‖ ^ (2 : ℕ) ∂volume) +
              (eps⁻¹) ^ (2 : ℕ) * ∫ y,
                ‖hilbertifyVecField
                  (openParentDatumExtension U datum) y‖ ^ (2 : ℕ) ∂volume ≤
            (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) +
              (eps⁻¹) ^ (2 : ℕ) *
                ((3 : ℝ) ^ d * ∫ x in Q, F x * F x ∂volume) :=
          add_le_add hgradientEnergy
            (mul_le_mul_of_nonneg_left hdatumEnergy (sq_nonneg eps⁻¹))
        _ = (3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) +
              (eps⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
                ∫ x in Q, F x * F x ∂volume := by ring
    have hfactor :
        0 ≤ (((2 * (cubeRadius (originCube d m) /
          (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹) := by
      apply inv_nonneg.mpr
      apply pow_nonneg
      exact mul_nonneg (by norm_num)
        (div_nonneg (cubeRadius_pos _).le (by positivity))
    apply lt_of_le_of_lt (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left henergy hfactor))
    simpa only [reflectedHessianRowGoodLambdaCutoff, Q] using hlevel
  have hinterior := sqWeightedMeasure_openParent_oneLevel_tail_originCube
    G hq hUopen (m := m) (sigma0 := (1 : ℝ)) (eps := eps)
    (M := M) (level := level) (by norm_num) heps heps_one hM
    rowU datum hdatum hweakRow
    (by
      intro x hx r hr hrcut
      exact
        stoppingComparisonParent_axisCube_subset_scaledOpenCubeSet_originCube_succ_one_div_two
          depth hx hr hrcut)
    hcutoff
  have hself := (htransfer (level / 2)).2
  have hleft := (htransfer (M * level)).1
  have hFmeas : AEStronglyMeasurable F (volume.restrict Q) := hFopen.aestronglyMeasurable
  have hdatumTail :
      sqWeightedMeasure
          ((1 : ℝ)⁻¹ • hilbertifyVecField
            (openParentDatumExtension U datum)) volume
          ({x | eps * level / 2 <
            ‖((1 : ℝ)⁻¹ • hilbertifyVecField
              (openParentDatumExtension U datum)) x‖} ∩ U) ≤
        ((3 : ℝ≥0∞) ^ d) * sqWeightedMeasure F volume
          ({x | eps * level / 2 < ‖F x‖} ∩ Q) := by
    have hindicator := sqWeightedMeasure_indicator_tail_inter_eq_of_subset
      (μ := volume) (U := U) (B := U) (f := hilbertifyVecField datum)
      (a := eps * level / 2) hUopen.measurableSet hUopen.measurableSet
      (fun _ hx ↦ hx)
    have hdatumPoint (x : Vec d) : datum x = Pi.single i (FR x) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [datum]
      · simp [datum, hji]
    have hnorm : ∀ x, ‖(hilbertifyVecField datum) x‖ = ‖FR x‖ := by
      intro x
      change ‖HilbertVec.ofVec (datum x)‖ = ‖FR x‖
      rw [hdatumPoint]
      exact PiLp.norm_single (2 : ℝ≥0∞) (fun _ : Fin d => ℝ) i (FR x)
    have hmeasure : sqWeightedMeasure (hilbertifyVecField datum) volume =
        sqWeightedMeasure FR volume := by
      apply MeasureTheory.withDensity_congr_ae
      filter_upwards with x
      rw [hnorm x]
    have htail : {x | eps * level / 2 < ‖(hilbertifyVecField datum) x‖} =
        {x | eps * level / 2 < ‖FR x‖} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [hnorm x]
    have hindicator' :
        sqWeightedMeasure
            (hilbertifyVecField (openParentDatumExtension U datum)) volume
            ({x | eps * level / 2 <
              ‖hilbertifyVecField (openParentDatumExtension U datum) x‖} ∩ U) =
          sqWeightedMeasure (hilbertifyVecField datum) volume
            ({x | eps * level / 2 < ‖hilbertifyVecField datum x‖} ∩ U) := by
      rw [hilbertifyVecField_openParentDatumExtension]
      exact hindicator
    simp only [inv_one, one_smul]
    calc
      sqWeightedMeasure
          (hilbertifyVecField (openParentDatumExtension U datum)) volume
          ({x | eps * level / 2 <
            ‖hilbertifyVecField (openParentDatumExtension U datum) x‖} ∩ U) =
        sqWeightedMeasure (hilbertifyVecField datum) volume
          ({x | eps * level / 2 < ‖hilbertifyVecField datum x‖} ∩ U) :=
        hindicator'
      _ = sqWeightedMeasure FR volume
          ({x | eps * level / 2 < ‖FR x‖} ∩ U) := by
        rw [hmeasure, htail]
      _ ≤ ((3 : ℝ≥0∞) ^ d) * sqWeightedMeasure F volume
          ({x | eps * level / 2 < ‖F x‖} ∩ Q) := by
        simpa only [U, Q, FR] using
          (sqWeightedMeasure_innerHalf_succ_originCube_cubeDirichletOddReflectionScalar_tail_le
            F hFmeas (a := eps * level / 2))
  calc
    sqWeightedMeasure row volume
        ({x | M * level < ‖row x‖} ∩ Q) =
      sqWeightedMeasure (openParentGradientExtension U rowU) volume
        ({x | M * level < ‖openParentGradientExtension U rowU x‖} ∩ Q) :=
      hleft.symm
    _ ≤
      oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure (openParentGradientExtension U rowU) volume
            ({x | level / 2 < ‖openParentGradientExtension U rowU x‖} ∩ U) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure
              ((1 : ℝ)⁻¹ • hilbertifyVecField
                (openParentDatumExtension U datum)) volume
              ({x | eps * level / 2 <
                ‖((1 : ℝ)⁻¹ • hilbertifyVecField
                  (openParentDatumExtension U datum)) x‖} ∩ U)) := hinterior
    _ ≤ oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        ((((3 : ℝ≥0∞) ^ d) * sqWeightedMeasure row volume
            ({x | level / 2 < ‖row x‖} ∩ Q)) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            (((3 : ℝ≥0∞) ^ d) * sqWeightedMeasure F volume
              ({x | eps * level / 2 < ‖F x‖} ∩ Q))) := by
      apply mul_le_mul_right
      apply add_le_add
      · simpa only [U, Q, row, hilbertifyVecField] using! hself
      · exact mul_le_mul_right hdatumTail _
    _ = ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure row volume
            ({x | level / 2 < ‖row x‖} ∩ Q) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure F volume
              ({x | eps * level / 2 < ‖F x‖} ∩ Q)) := by
      ring

end CubeCalderonZygmund

end

end Homogenization
