/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.OriginCubeEndpoint
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.EnergyBound
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.SolverEnergy
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.PoissonTranslation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianTranslation

/-! # Arbitrary Cube Endpoint -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeDirichletWeakPoissonProblem

variable {d : ℕ} {Q : TriadicCube d} {u : H10Function (openCubeSet Q)}
  {F : Vec d → ℝ}

/-- Transport the centered-cube reflected-parent Hessian estimate back to an
arbitrary cube of the same scale.  The right-hand side is still the canonical
origin-cube smooth-test bound for the translated forcing; a later quantitative
lemma collapses it to a dimension-only multiple of the cube `L²` norm. -/
theorem exists_hasWeakHessianOn_cube_canonicalRadii_hessianCoordL2NormSum_le_smoothTestBound
    (hweak : CubeDirichletWeakPoissonProblem Q u F)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∃ uP : H1Function (openCubeSet (originCube d (Q.scale + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d Q.scale)
            (untranslateToOriginFunction Q u).toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d Q.scale)
            (fun y => (untranslateToOriginFunction Q u).toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet Q) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                  d (originCube d (Q.scale + 1)) uP
                  (cubeDirichletOddReflectionScalar (originCube d Q.scale)
                    (fun x => F (x + triadicCubeShift Q)))
                  i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                  (originCubeParentThreeQuarterSevenEighthCutoff d Q.scale) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let z : Vec d := triadicCubeShift Q
  let F₀ : Vec d → ℝ := fun x => F (x + z)
  let u₀ : H10Function (openCubeSet Q₀) := untranslateToOriginFunction Q u
  have hweak₀ : CubeDirichletWeakPoissonProblem Q₀ u₀ F₀ := by
    simpa [Q₀, F₀, z, u₀] using hweak.untranslateToOrigin
  have hF₀ : MeasureTheory.MemLp F₀ (2 : ℝ≥0∞) (normalizedCubeMeasure Q₀) := by
    simpa [Q₀, F₀, z] using memLp_originCube_comp_addRight_of_memLp Q hF
  rcases
    hweak₀.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le
      hF₀ with
    ⟨uP, huP_toFun, huP_grad, H₀, hH₀⟩
  have hU : openCubeSet Q = translateSet z (openCubeSet Q₀) := by
    simpa [Q₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let HT : HasWeakHessianOn (translateSet z (openCubeSet Q₀))
      (u₀.toH1Function.translate z) := H₀.translate z
  let H : HasWeakHessianOn (openCubeSet Q) u.toH1Function :=
    { hess := HT.hess
      hess_memL2 := by
        intro i j
        simpa [hU] using HT.hess_memL2 i j
      weak_second := by
        intro i j
        have hweakT :
            HasWeakPartialDerivOn (openCubeSet Q) j
              (fun x => (u₀.toH1Function.translate z).grad x i)
              (HT.hess i j) := by
          simpa [hU] using HT.weak_second i j
        refine
          HasWeakPartialDerivOn.congr_of_eqOn
            (measurableSet_openCubeSet Q) ?_ ?_ hweakT
        · intro x _hx
          exact congrArg (fun v : Vec d => v i)
            (untranslateToOriginFunction_translate_grad Q u x)
        · intro x _hx
          rfl }
  refine ⟨uP, ?_, ?_, H, ?_⟩
  · simpa [Q₀, u₀] using huP_toFun
  · simpa [Q₀, u₀] using huP_grad
  · have hH_HT : H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := by
      simp [H, hU, HasWeakHessianOn.hessianCoordL2NormSum,
        HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2]
    have hHT_H₀ : HT.hessianCoordL2NormSum = H₀.hessianCoordL2NormSum := by
      simpa [HT] using H₀.hessianCoordL2NormSum_translate_eq z
    calc
      H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := hH_HT
      _ = H₀.hessianCoordL2NormSum := hHT_H₀
      _ ≤
          ∑ i : Fin d, ∑ _j : Fin d,
            @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
              d (originCube d (Q.scale + 1)) uP
              (cubeDirichletOddReflectionScalar (originCube d Q.scale)
                (fun x => F (x + triadicCubeShift Q)))
              i (1 / 3 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
              (originCubeParentThreeQuarterSevenEighthCutoff d Q.scale) := by
            simpa [Q₀, F₀, z] using hH₀

/-- Transport the centered-cube norm-energy reflected-parent Hessian estimate
back to an arbitrary cube of the same scale. -/
theorem exists_hasWeakHessianOn_cube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
    (hweak : CubeDirichletWeakPoissonProblem Q u F)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∃ uP : H1Function (openCubeSet (originCube d (Q.scale + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d Q.scale)
            (untranslateToOriginFunction Q u).toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d Q.scale)
            (fun y => (untranslateToOriginFunction Q u).toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet Q) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                originCubeParentReducedNormEnergyBound
                  (untranslateToOriginFunction Q u)
                  (fun x => F (x + triadicCubeShift Q)) i := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let z : Vec d := triadicCubeShift Q
  let F₀ : Vec d → ℝ := fun x => F (x + z)
  let u₀ : H10Function (openCubeSet Q₀) := untranslateToOriginFunction Q u
  have hweak₀ : CubeDirichletWeakPoissonProblem Q₀ u₀ F₀ := by
    simpa [Q₀, F₀, z, u₀] using hweak.untranslateToOrigin
  have hF₀ : MeasureTheory.MemLp F₀ (2 : ℝ≥0∞) (normalizedCubeMeasure Q₀) := by
    simpa [Q₀, F₀, z] using memLp_originCube_comp_addRight_of_memLp Q hF
  rcases
    hweak₀.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_normEnergyBound
      hF₀ with
    ⟨uP, huP_toFun, huP_grad, H₀, hH₀⟩
  have hU : openCubeSet Q = translateSet z (openCubeSet Q₀) := by
    simpa [Q₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let HT : HasWeakHessianOn (translateSet z (openCubeSet Q₀))
      (u₀.toH1Function.translate z) := H₀.translate z
  let H : HasWeakHessianOn (openCubeSet Q) u.toH1Function :=
    { hess := HT.hess
      hess_memL2 := by
        intro i j
        simpa [hU] using HT.hess_memL2 i j
      weak_second := by
        intro i j
        have hweakT :
            HasWeakPartialDerivOn (openCubeSet Q) j
              (fun x => (u₀.toH1Function.translate z).grad x i)
              (HT.hess i j) := by
          simpa [hU] using HT.weak_second i j
        refine
          HasWeakPartialDerivOn.congr_of_eqOn
            (measurableSet_openCubeSet Q) ?_ ?_ hweakT
        · intro x _hx
          exact congrArg (fun v : Vec d => v i)
            (untranslateToOriginFunction_translate_grad Q u x)
        · intro x _hx
          rfl }
  refine ⟨uP, ?_, ?_, H, ?_⟩
  · simpa [Q₀, u₀] using huP_toFun
  · simpa [Q₀, u₀] using huP_grad
  · have hH_HT : H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := by
      simp [H, hU, HasWeakHessianOn.hessianCoordL2NormSum,
        HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2]
    have hHT_H₀ : HT.hessianCoordL2NormSum = H₀.hessianCoordL2NormSum := by
      simpa [HT] using H₀.hessianCoordL2NormSum_translate_eq z
    calc
      H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := hH_HT
      _ = H₀.hessianCoordL2NormSum := hHT_H₀
      _ ≤
          ∑ i : Fin d, ∑ _j : Fin d,
            originCubeParentReducedNormEnergyBound
              (untranslateToOriginFunction Q u)
              (fun x => F (x + triadicCubeShift Q)) i := by
            simpa [Q₀, F₀, z, u₀] using hH₀

/-- Transport the forcing-facing centered-cube Dirichlet solver-energy Hessian
estimate back to an arbitrary cube of the same scale. -/
theorem exists_hasWeakHessianOn_cube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
    [NeZero d]
    (hweak : CubeDirichletWeakPoissonProblem Q u F)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∃ uP : H1Function (openCubeSet (originCube d (Q.scale + 1))),
      uP.toFun =
          cubeDirichletOddReflectionScalar (originCube d Q.scale)
            (untranslateToOriginFunction Q u).toH1Function.toFun ∧
        uP.grad =
          cubeDirichletOddReflectionVectorField (originCube d Q.scale)
            (fun y => (untranslateToOriginFunction Q u).toH1Function.grad y) ∧
          ∃ H : HasWeakHessianOn (openCubeSet Q) u.toH1Function,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                originCubeParentReducedSolverEnergyBoundExact d Q.scale
                  (fun x => F (x + triadicCubeShift Q)) i := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let z : Vec d := triadicCubeShift Q
  let F₀ : Vec d → ℝ := fun x => F (x + z)
  let u₀ : H10Function (openCubeSet Q₀) := untranslateToOriginFunction Q u
  have hweak₀ : CubeDirichletWeakPoissonProblem Q₀ u₀ F₀ := by
    simpa [Q₀, F₀, z, u₀] using hweak.untranslateToOrigin
  have hF₀ : MeasureTheory.MemLp F₀ (2 : ℝ≥0∞) (normalizedCubeMeasure Q₀) := by
    simpa [Q₀, F₀, z] using memLp_originCube_comp_addRight_of_memLp Q hF
  rcases
    hweak₀.exists_hasWeakHessianOn_originCube_canonicalRadii_hessianCoordL2NormSum_le_solverEnergyBoundExact
      hF₀ with
    ⟨uP, huP_toFun, huP_grad, H₀, hH₀⟩
  have hU : openCubeSet Q = translateSet z (openCubeSet Q₀) := by
    simpa [Q₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let HT : HasWeakHessianOn (translateSet z (openCubeSet Q₀))
      (u₀.toH1Function.translate z) := H₀.translate z
  let H : HasWeakHessianOn (openCubeSet Q) u.toH1Function :=
    { hess := HT.hess
      hess_memL2 := by
        intro i j
        simpa [hU] using HT.hess_memL2 i j
      weak_second := by
        intro i j
        have hweakT :
            HasWeakPartialDerivOn (openCubeSet Q) j
              (fun x => (u₀.toH1Function.translate z).grad x i)
              (HT.hess i j) := by
          simpa [hU] using HT.weak_second i j
        refine
          HasWeakPartialDerivOn.congr_of_eqOn
            (measurableSet_openCubeSet Q) ?_ ?_ hweakT
        · intro x _hx
          exact congrArg (fun v : Vec d => v i)
            (untranslateToOriginFunction_translate_grad Q u x)
        · intro x _hx
          rfl }
  refine ⟨uP, ?_, ?_, H, ?_⟩
  · simpa [Q₀, u₀] using huP_toFun
  · simpa [Q₀, u₀] using huP_grad
  · have hH_HT : H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := by
      simp [H, hU, HasWeakHessianOn.hessianCoordL2NormSum,
        HasWeakHessianOn.hessCoordToScalarL2, Homogenization.toScalarL2]
    have hHT_H₀ : HT.hessianCoordL2NormSum = H₀.hessianCoordL2NormSum := by
      simpa [HT] using H₀.hessianCoordL2NormSum_translate_eq z
    calc
      H.hessianCoordL2NormSum = HT.hessianCoordL2NormSum := hH_HT
      _ = H₀.hessianCoordL2NormSum := hHT_H₀
      _ ≤
          ∑ i : Fin d, ∑ _j : Fin d,
            originCubeParentReducedSolverEnergyBoundExact d Q.scale
              (fun x => F (x + triadicCubeShift Q)) i := by
            simpa [Q₀, F₀, z] using hH₀

end CubeDirichletWeakPoissonProblem

end

end Homogenization
