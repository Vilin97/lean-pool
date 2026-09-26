/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.OriginCubeEndpoint
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothTestBoundEstimate

/-! # Energy Bound -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeDirichletWeakPoissonProblem

variable {d : ℕ} {m : ℤ} {u : H10Function (openCubeSet (originCube d m))}
  {F : Vec d → ℝ}

/-- Original-cube energy bound obtained after reading the fixed-radii
odd-reflected parent reduced smooth-test constant through the all-face
reflection identities. -/
noncomputable def originCubeParentReducedOriginalEnergyBound
    (u : H10Function (openCubeSet (originCube d m))) (F : Vec d → ℝ)
    (_i : Fin d) : ℝ :=
  ((4 : ℝ) *
    ((2 : ℝ) *
        ((3 : ℝ) ^ d *
          ∫ y in openCubeSet (originCube d m), F y ^ 2 ∂MeasureTheory.volume) +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            (((1 / 2 : ℝ) - (1 / 3 : ℝ)) *
              cubeRadius (originCube d (m + 1)))) ^ 2)) *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d *
              ∫ y in openCubeSet (originCube d m),
                vecDot (u.toH1Function.grad y) (u.toH1Function.grad y)
                ∂MeasureTheory.volume) +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                (((7 / 8 : ℝ) - (3 / 4 : ℝ)) *
                  cubeRadius (originCube d (m + 1)))) ^ 2) *
              ((3 : ℝ) ^ d *
                ∫ y in openCubeSet (originCube d m),
                u.toH1Function.toFun y ^ 2 ∂MeasureTheory.volume))))) ^
    (1 / (2 : ℝ))

/-- The same reflected-parent reduced energy bound, but with the original-cube
forcing, gradient, and value integrals rewritten as normalized/`L²`
realizations. -/
noncomputable def originCubeParentReducedNormEnergyBound
    (u : H10Function (openCubeSet (originCube d m))) (F : Vec d → ℝ)
    (_i : Fin d) : ℝ :=
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  ((4 : ℝ) *
    ((2 : ℝ) *
        ((3 : ℝ) ^ d *
          (cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℝ))) +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)) *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d * ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2) +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2) *
              ((3 : ℝ) ^ d * ‖u.toH1Function.toScalarL2‖ ^ 2))))) ^
    (1 / (2 : ℝ))

/-- The raw original-cube Dirichlet reflected-parent energy expression is
exactly the same as its norm-realized form. -/
theorem originCubeParentReducedOriginalEnergyBound_eq_normEnergyBound
    (u : H10Function (openCubeSet (originCube d m))) {F : Vec d → ℝ}
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (i : Fin d) :
    originCubeParentReducedOriginalEnergyBound u F i =
      originCubeParentReducedNormEnergyBound u F i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  have hforce :
      ∫ y in openCubeSet Q, F y ^ 2 ∂MeasureTheory.volume =
        cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) F) ^ (2 : ℝ) := by
    simpa [Q, pow_two] using
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow Q F hF
  have hgrad :
      ∫ y in openCubeSet Q,
          vecDot (u.toH1Function.grad y) (u.toH1Function.grad y)
          ∂MeasureTheory.volume =
        ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
    have hinner :
        ∫ y in openCubeSet Q,
            vecDot (u.toH1Function.grad y) (u.toH1Function.grad y)
            ∂MeasureTheory.volume =
          inner ℝ u.toH1Function.gradToHilbertVectorL2
            u.toH1Function.gradToHilbertVectorL2 := by
      simpa [H1Function.gradToHilbertVectorL2] using
        (inner_toHilbertVectorL2OfVecField_eq_integral
          (U := openCubeSet Q)
          u.toH1Function.grad_memVectorL2
          u.toH1Function.grad_memVectorL2).symm
    rw [hinner]
    exact real_inner_self_eq_norm_sq u.toH1Function.gradToHilbertVectorL2
  have hvalue :
      ∫ y in openCubeSet Q, u.toH1Function.toFun y ^ 2
          ∂MeasureTheory.volume =
        ‖u.toH1Function.toScalarL2‖ ^ 2 := by
    simpa [H1Function.toScalarL2, Homogenization.toScalarL2] using
      (toReal_eLpNorm_two_sq_eq_integral_sq u.toH1Function.memL2).symm
  simp [originCubeParentReducedOriginalEnergyBound,
    originCubeParentReducedNormEnergyBound, Q, hforce, hgrad, hvalue]

/-- A fixed-radii reduced smooth-test constant on the odd-reflected parent is
bounded by the corresponding original-cube energy expression. -/
theorem openCubeInnerQuotientHessianSmoothTestReducedBound_le_originCubeParentReducedOriginalEnergyBound
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    {uP : H1Function (openCubeSet (originCube d (m + 1)))}
    (huP_toFun :
      uP.toFun =
        cubeDirichletOddReflectionScalar (originCube d m)
          u.toH1Function.toFun)
    (huP_grad :
      uP.grad =
        cubeDirichletOddReflectionVectorField (originCube d m)
          (fun y => u.toH1Function.grad y))
    (i : Fin d) :
    @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
        d (originCube d (m + 1)) uP
        (cubeDirichletOddReflectionScalar (originCube d m) F)
        i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
        (originCubeParentThreeQuarterSevenEighthCutoff d m) ≤
      originCubeParentReducedOriginalEnergyBound u F i := by
  let Q : TriadicCube d := originCube d m
  let Qp : TriadicCube d := originCube d (m + 1)
  let fP : Vec d → ℝ := cubeDirichletOddReflectionScalar Q F
  let G : Vec d → Vec d := fun y => u.toH1Function.grad y
  let GP : Vec d → Vec d := cubeDirichletOddReflectionVectorField Q G
  let uPfun : Vec d → ℝ :=
    cubeDirichletOddReflectionScalar Q u.toH1Function.toFun
  let Kinner : ℝ :=
    (3 : ℝ) *
      ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          (((1 / 2 : ℝ) - (1 / 3 : ℝ)) * cubeRadius Qp)) ^ 2)
  let Kouter : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        (((7 / 8 : ℝ) - (3 / 4 : ℝ)) * cubeRadius Qp)) ^ 2
  let A : ℝ :=
    (2 : ℝ) * ∫ x in openCubeSet Qp, fP x ^ 2 ∂MeasureTheory.volume +
      Kinner *
        ((2 : ℝ) * ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2
            ∂MeasureTheory.volume +
          (2 : ℝ) *
            (Kouter *
              ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume))
  let B : ℝ :=
    (2 : ℝ) *
        ((3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y ^ 2 ∂MeasureTheory.volume) +
      Kinner *
        ((2 : ℝ) *
            ((3 : ℝ) ^ d *
              ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume) +
          (2 : ℝ) *
            (Kouter *
              ((3 : ℝ) ^ d *
                ∫ y in openCubeSet Q, u.toH1Function.toFun y ^ 2
                  ∂MeasureTheory.volume)))
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [Q, MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure (originCube d m) hF
  have hforce_eq :
      ∫ x in openCubeSet Qp, fP x ^ 2 ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, F y ^ 2 ∂MeasureTheory.volume := by
    simpa [Q, Qp, fP, pow_two] using
      setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_sq_of_memScalarL2_three_pow
        (m := m) hFopen
  have hvalue_eq :
      ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume =
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, u.toH1Function.toFun y ^ 2
            ∂MeasureTheory.volume := by
    have hu : MemScalarL2 (openCubeSet Q) u.toH1Function.toFun := by
      simpa [Q, MemScalarL2, volumeMeasureOn] using u.toH1Function.memL2
    calc
      ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume =
          ∫ x in openCubeSet Qp, uPfun x ^ 2 ∂MeasureTheory.volume := by
            rw [huP_toFun]
      _ =
          (3 : ℝ) ^ d *
            ∫ y in openCubeSet Q, u.toH1Function.toFun y ^ 2
              ∂MeasureTheory.volume := by
            simpa [Q, Qp, uPfun, pow_two] using
              setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar_sq_of_memScalarL2_three_pow
                (m := m) hu
  have hgrad_coord_le :
      ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2 ∂MeasureTheory.volume ≤
        (3 : ℝ) ^ d *
          ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume := by
    have hcoord :
        ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2 ∂MeasureTheory.volume ≤
          ∫ x in openCubeSet Qp, vecNormSq (uP.grad x) ∂MeasureTheory.volume := by
      simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        WeakPoissonEquationOn.integral_coord_norm_rpow_two_le_integral_vecNormSq_of_memVectorL2
          (U := openCubeSet Qp) uP.grad_memVectorL2 i
    have hG : MemVectorL2 (openCubeSet Q) G := by
      simpa [Q, G, MemVectorL2, volumeMeasureOn] using
        u.toH1Function.grad_memVectorL2
    have hvec_eq :
        ∫ x in openCubeSet Qp, vecNormSq (uP.grad x) ∂MeasureTheory.volume =
          (3 : ℝ) ^ d *
            ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume := by
      calc
        ∫ x in openCubeSet Qp, vecNormSq (uP.grad x) ∂MeasureTheory.volume =
            ∫ x in openCubeSet Qp, vecDot (GP x) (GP x)
              ∂MeasureTheory.volume := by
              rw [huP_grad]
              rfl
        _ =
            (3 : ℝ) ^ d *
              ∫ y in openCubeSet Q, vecDot (G y) (G y)
                ∂MeasureTheory.volume := by
              simpa [Q, Qp, G, GP] using
                setIntegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_self_pairing_of_memVectorL2_three_pow
                  (m := m) hG
    exact hcoord.trans_eq hvec_eq
  have hlower :
      (2 : ℝ) * ∫ x in openCubeSet Qp, (uP.grad x i) ^ 2
          ∂MeasureTheory.volume +
        (2 : ℝ) *
          (Kouter *
            ∫ x in openCubeSet Qp, uP.toFun x ^ 2 ∂MeasureTheory.volume) ≤
      (2 : ℝ) *
          ((3 : ℝ) ^ d *
            ∫ y in openCubeSet Q, vecDot (G y) (G y) ∂MeasureTheory.volume) +
        (2 : ℝ) *
          (Kouter *
            ((3 : ℝ) ^ d *
              ∫ y in openCubeSet Q, u.toH1Function.toFun y ^ 2
                ∂MeasureTheory.volume)) := by
    rw [hvalue_eq]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hgrad_coord_le (by norm_num))
      (le_refl _)
  have hKinner_nonneg : 0 ≤ Kinner := by
    dsimp [Kinner]
    positivity
  have hAB : A ≤ B := by
    dsimp [A, B]
    rw [hforce_eq]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hlower hKinner_nonneg) _
  have h4AB : (4 : ℝ) * A ≤ (4 : ℝ) * B :=
    mul_le_mul_of_nonneg_left hAB (by norm_num)
  have h4A_nonneg : 0 ≤ (4 : ℝ) * A := by
    dsimp [A, Kinner, Kouter]
    positivity
  simpa [WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound,
    originCubeParentReducedOriginalEnergyBound, Q, Qp, fP, G, GP, uPfun,
    Kinner, Kouter, A, B] using
    Real.rpow_le_rpow h4A_nonneg h4AB (by norm_num : 0 ≤ (1 / (2 : ℝ)))

/-- The fixed-radii reflected-parent Hessian estimate with the raw smooth-test
constant replaced by the reduced unweighted `H¹` bound. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_reducedBound
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
                  d (originCube d (m + 1)) uP
                  (cubeDirichletOddReflectionScalar (originCube d m) F)
                  i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                  (originCubeParentThreeQuarterSevenEighthCutoff d m) := by
  rcases
    hweak.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le
      hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound_le_reducedBound
        (Q := originCube d (m + 1)) uP
        (cubeDirichletOddReflectionScalar (originCube d m) F) i
        (ρ₁ := (1 / 3 : ℝ)) (ρ₂ := (1 / 2 : ℝ))
        (σ₁ := (3 / 4 : ℝ)) (σ₂ := (7 / 8 : ℝ))
        (originCubeParentThreeQuarterSevenEighthCutoff d m)

/-- The fixed-radii reflected-parent Hessian estimate, with the right-hand
side expressed entirely in original-cube energy terms. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_originalEnergyBound
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                originCubeParentReducedOriginalEnergyBound u F i := by
  rcases
    hweak.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_reducedBound
      hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      openCubeInnerQuotientHessianSmoothTestReducedBound_le_originCubeParentReducedOriginalEnergyBound
        hF huP_toFun huP_grad i

/-- The fixed-radii reflected-parent Hessian estimate with the right-hand side
expressed through `L²` norm realizations of the solution and forcing. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                originCubeParentReducedNormEnergyBound u F i := by
  rcases
    hweak.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_originalEnergyBound
      hF with
    ⟨uP, huP_toFun, huP_grad, H, hH⟩
  refine ⟨uP, huP_toFun, huP_grad, H, hH.trans ?_⟩
  exact Finset.sum_le_sum fun i _hi =>
    Finset.sum_le_sum fun _j _hj =>
      le_of_eq (originCubeParentReducedOriginalEnergyBound_eq_normEnergyBound u hF i)

end CubeDirichletWeakPoissonProblem

end

end Homogenization
