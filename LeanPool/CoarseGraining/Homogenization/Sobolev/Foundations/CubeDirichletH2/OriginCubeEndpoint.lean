/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.ReflectionParentH1Graph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessianPointwise
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ScaledCubeGeometry

/-! # Origin Cube Endpoint -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

private theorem hasWeakPartialDerivOn_congr_of_eqOn {d : ℕ} {U : Set (Vec d)}
    (hU_meas : MeasurableSet U) {i : Fin d}
    {u v gi hi : Vec d → ℝ} (huv : Set.EqOn u v U)
    (hgi : Set.EqOn gi hi U)
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn U i v hi := by
  intro φ hφ hφs hφ_sub
  have hleft :
      ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU_meas ?_
    intro x hx
    change v x * (fderiv ℝ φ x) (basisVec i) =
      u x * (fderiv ℝ φ x) (basisVec i)
    rw [← huv hx]
  have hright :
      ∫ x in U, gi x * φ x ∂MeasureTheory.volume =
        ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU_meas ?_
    intro x hx
    change gi x * φ x = hi x * φ x
    rw [hgi hx]
  calc
    ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := hleft
    _ = -∫ x in U, gi x * φ x ∂MeasureTheory.volume :=
      h φ hφ hφs hφ_sub
    _ = -∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
      rw [hright]

namespace CubeDirichletWeakPoissonProblem

/-- Canonical cutoff from the original cube, viewed as the one-third inner
cube of its centered parent, to a half-radius parent cube. -/
noncomputable def originCubeParentOneThirdHalfCutoff (d : ℕ) (m : ℤ) :
    QuantitativeCubeCutoff (originCube d (m + 1)) (1 / 3 : ℝ) (1 / 2 : ℝ) :=
  QuantitativeCubeCutoff.canonical (originCube d (m + 1)) (1 / 3 : ℝ) (1 / 2 : ℝ)
    (by norm_num) (by norm_num)

/-- Canonical outer cutoff used by the parent-cube interior estimate. -/
noncomputable def originCubeParentThreeQuarterSevenEighthCutoff (d : ℕ) (m : ℤ) :
    QuantitativeCubeCutoff (originCube d (m + 1)) (3 / 4 : ℝ) (7 / 8 : ℝ) :=
  QuantitativeCubeCutoff.canonical (originCube d (m + 1)) (3 / 4 : ℝ) (7 / 8 : ℝ)
    (by norm_num) (by norm_num)

variable {d : ℕ} {m : ℤ} {V : Set (Vec d)} {u : H10Function (openCubeSet (originCube d m))}
  {F : Vec d → ℝ}

/-- Apply the interior weak-Hessian estimate on the centered parent cube after
all-face odd reflection of an origin-cube Dirichlet solution. -/
theorem exists_cubeDirichletOddReflectionParent_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (hV : IsOpenBoundedConvexDomain V)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff (originCube d (m + 1)) ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet (originCube d (m + 1)) ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff (originCube d (m + 1)) σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet (originCube d (m + 1)) ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν < σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
          ∃ uS : H1Function (scaledOpenCubeSet (originCube d (m + 1)) ρ₁),
            uS.toFun = uP.toFun ∧
              uS.grad = uP.grad ∧
                ∃ H :
                  HasWeakHessianOn
                    (scaledOpenCubeSet (originCube d (m + 1)) ρ₁) uS,
                  H.hessianCoordL2NormSum ≤
                    ∑ i : Fin d, ∑ _j : Fin d,
                      @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                        d (originCube d (m + 1)) uP
                        (cubeDirichletOddReflectionScalar (originCube d m) F)
                        i ρ₁ ρ₂ σ₁ σ₂ θ := by
  rcases hweak.exists_cubeDirichletOddReflectionParent_weakPoissonEquationOn_originCube
      hF with
    ⟨uP, huP_toFun, huP_grad, hweakParent⟩
  have hFopen : MemScalarL2 (openCubeSet (originCube d m)) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure (originCube d m) hF
  have hFparent :
      MemScalarL2 (openCubeSet (originCube d (m + 1)))
        (cubeDirichletOddReflectionScalar (originCube d m) F) :=
    memScalarL2_openCubeSet_succ_originCube_cubeDirichletOddReflectionScalar
      (m := m) hFopen
  rcases
    hweakParent.exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
      hFparent hV η hη_sub hinnerV θ hVν hν_nonneg hνσ
      hσ₁_lt_one hσ₂_nonneg hσ₂_lt_one hρ₁_nonneg with
    ⟨uS, huS_toFun, huS_grad, H, hH⟩
  exact ⟨uP, huP_toFun, huP_grad, uS, huS_toFun, huS_grad, H, hH⟩

/-- The parent reflected Hessian estimate specialized to the one-third inner
cube, read back as an estimate on the original centered cube. -/
theorem exists_cubeDirichletOddReflectionParent_hasWeakHessianOn_originCube_hessianCoordL2NormSum_le
    (hweak : CubeDirichletWeakPoissonProblem (originCube d m) u F)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m)))
    (hV : IsOpenBoundedConvexDomain V)
    {ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff (originCube d (m + 1)) (1 / 3 : ℝ) ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet (originCube d (m + 1)) (1 / 3 : ℝ) ⊆ V)
    (θ : QuantitativeCubeCutoff (originCube d (m + 1)) σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet (originCube d (m + 1)) ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν < σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d m)
            u.toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d m)
            (fun y => u.toH1Function.grad y) ∧
          ∃ uS : H1Function (openCubeSet (originCube d m)),
            uS.toFun = uP.toFun ∧
              uS.grad = uP.grad ∧
                ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) uS,
                  H.hessianCoordL2NormSum ≤
                    ∑ i : Fin d, ∑ _j : Fin d,
                      @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                        d (originCube d (m + 1)) uP
                        (cubeDirichletOddReflectionScalar (originCube d m) F)
                        i (1 / 3 : ℝ) ρ₂ σ₁ σ₂ θ := by
  have hparent :=
    hweak.exists_cubeDirichletOddReflectionParent_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le
      hF hV η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one (by norm_num : 0 ≤ (1 / 3 : ℝ))
  have hgeom :
      scaledOpenCubeSet (originCube d (m + 1)) (1 / 3 : ℝ) =
        openCubeSet (originCube d m) :=
    scaledOpenCubeSet_originCube_succ_one_div_three d m
  rw [hgeom] at hparent
  exact hparent

/-- The one-third reflected-parent Hessian estimate with fixed numerical
cutoffs. -/
theorem exists_cubeDirichletOddReflectionParent_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le
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
          ∃ uS : H1Function (openCubeSet (originCube d m)),
            uS.toFun = uP.toFun ∧
              uS.grad = uP.grad ∧
                ∃ H : HasWeakHessianOn (openCubeSet (originCube d m)) uS,
                  H.hessianCoordL2NormSum ≤
                    ∑ i : Fin d, ∑ _j : Fin d,
                      @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                        d (originCube d (m + 1)) uP
                        (cubeDirichletOddReflectionScalar (originCube d m) F)
                        i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                        (originCubeParentThreeQuarterSevenEighthCutoff d m) := by
  let Qp : TriadicCube d := originCube d (m + 1)
  let Vp : Set (Vec d) := scaledOpenCubeSet Qp (2 / 3 : ℝ)
  have hV : IsOpenBoundedConvexDomain Vp :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Qp
      (by norm_num : 0 < (2 / 3 : ℝ))
  have hη_sub :
      tsupport (originCubeParentOneThirdHalfCutoff d m : Vec d → ℝ) ⊆ Vp := by
    have hclosed :
        tsupport (originCubeParentOneThirdHalfCutoff d m : Vec d → ℝ) ⊆
          scaledClosedCubeSet Qp (1 / 2 : ℝ) :=
      (originCubeParentOneThirdHalfCutoff d m).tsupport_subset_scaledClosedCubeSet_of_support_subset
    exact hclosed.trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Qp
        (by norm_num : (1 / 2 : ℝ) < 2 / 3))
  have hinnerV :
      scaledClosedCubeSet Qp (1 / 3 : ℝ) ⊆ Vp :=
    scaledClosedCubeSet_subset_scaledOpenCubeSet_of_lt Qp
      (by norm_num : (1 / 3 : ℝ) < 2 / 3)
  have hVν :
      Vp ⊆ scaledClosedCubeSet Qp (2 / 3 : ℝ) :=
    scaledOpenCubeSet_subset_scaledClosedCubeSet Qp (2 / 3 : ℝ)
  simpa [Qp, Vp, originCubeParentOneThirdHalfCutoff,
    originCubeParentThreeQuarterSevenEighthCutoff] using
    hweak.exists_cubeDirichletOddReflectionParent_hasWeakHessianOn_originCube_hessianCoordL2NormSum_le
      hF hV (originCubeParentOneThirdHalfCutoff d m) hη_sub hinnerV
      (originCubeParentThreeQuarterSevenEighthCutoff d m) hVν
      (by norm_num : 0 ≤ (2 / 3 : ℝ)) (by norm_num : (2 / 3 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : 0 ≤ (7 / 8 : ℝ))
      (by norm_num : (7 / 8 : ℝ) < 1)

/-- Read the reflected-parent fixed-radii Hessian witness as a weak Hessian
of the original Dirichlet solution on the original cube. -/
theorem exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le
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
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                  d (originCube d (m + 1)) uP
                  (cubeDirichletOddReflectionScalar (originCube d m) F)
                  i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                  (originCubeParentThreeQuarterSevenEighthCutoff d m) := by
  rcases
    hweak.exists_cubeDirichletOddReflectionParent_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le
      hF with
    ⟨uP, huP_toFun, huP_grad, uS, _huS_toFun, huS_grad, H, hH⟩
  let HW : HasWeakHessianOn (openCubeSet (originCube d m)) u.toH1Function :=
    { hess := H.hess
      hess_memL2 := H.hess_memL2
      weak_second := by
        intro i j
        have hgrad_eq :
            Set.EqOn (fun x => uS.grad x i)
              (fun x => u.toH1Function.grad x i) (openCubeSet (originCube d m)) := by
          intro x hx
          calc
            uS.grad x i = uP.grad x i := by rw [huS_grad]
            _ =
                cubeDirichletOddReflectionVectorField (originCube d m)
                  (fun y => u.toH1Function.grad y) x i := by
                  rw [huP_grad]
            _ = u.toH1Function.grad x i := by
              exact congrFun
                (cubeDirichletOddReflectionVectorField_eq_self_of_mem_openCubeSet
                  (originCube d m) (fun y => u.toH1Function.grad y) hx) i
        exact
          hasWeakPartialDerivOn_congr_of_eqOn
            (measurableSet_openCubeSet (originCube d m)) hgrad_eq
            (fun _x _hx => rfl) (H.weak_second i j) }
  refine ⟨uP, huP_toFun, huP_grad, HW, ?_⟩
  simpa [HW, HasWeakHessianOn.hessianCoordL2NormSum,
    HasWeakHessianOn.hessCoordToScalarL2] using hH

end CubeDirichletWeakPoissonProblem

end

end Homogenization
