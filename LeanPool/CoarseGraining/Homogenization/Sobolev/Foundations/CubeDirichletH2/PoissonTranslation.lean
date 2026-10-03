/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.Definitions
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CubeTranslationTransport

/-! # Poisson Translation -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeDirichletWeakPoissonProblem

variable {d : ℕ}

/-- Pull an arbitrary-cube zero-trace function back to the centered cube of
the same scale. -/
noncomputable def untranslateToOriginFunction (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) :
    H10Function (openCubeSet (originCube d Q.scale)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uT : H10Function (translateSet z U₀) :=
    { toH1Function :=
        { toFun := u.toH1Function.toFun
          grad := u.toH1Function.grad
          memL2 := by
            simpa [← hU] using u.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [← hU] using u.toH1Function.gradMemL2 i
          hasWeakGradient := by
            simpa [← hU] using u.toH1Function.hasWeakGradient }
      approx := u.approx
      approx_smooth := u.approx_smooth
      approx_hasCompactSupport := u.approx_hasCompactSupport
      approx_support_subset := by
        intro n
        simpa [← hU] using u.approx_support_subset n
      tendsto_approx := by
        simpa [← hU] using u.tendsto_approx
      tendsto_approx_grad := by
        intro i
        simpa [← hU] using u.tendsto_approx_grad i }
  exact H10Function.untranslate z uT

@[simp] theorem untranslateToOriginFunction_toFun (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (x : Vec d) :
    (untranslateToOriginFunction Q u).toH1Function.toFun x =
      u.toH1Function.toFun (x + triadicCubeShift Q) := by
  simp [untranslateToOriginFunction, H10Function.untranslate, H1Function.untranslate]

@[simp] theorem untranslateToOriginFunction_grad (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (x : Vec d) :
    (untranslateToOriginFunction Q u).toH1Function.grad x =
      u.toH1Function.grad (x + triadicCubeShift Q) := by
  simp [untranslateToOriginFunction, H10Function.untranslate, H1Function.untranslate]

/-- Pull a cube Dirichlet weak Poisson equation back to the centered cube of
the same scale. -/
theorem untranslateToOrigin {Q : TriadicCube d}
    {u : H10Function (openCubeSet Q)} {F : Vec d → ℝ}
    (hweak : CubeDirichletWeakPoissonProblem Q u F) :
    CubeDirichletWeakPoissonProblem (originCube d Q.scale)
      (untranslateToOriginFunction Q u)
      (fun x => F (x + triadicCubeShift Q)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  intro φ
  let φT : H10Function (translateSet z U₀) := φ.translate z
  let φQ : H10Function (openCubeSet Q) :=
    { toH1Function :=
        { toFun := φT.toH1Function.toFun
          grad := φT.toH1Function.grad
          memL2 := by
            simpa [hU] using φT.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [hU] using φT.toH1Function.gradMemL2 i
          hasWeakGradient := by
            simpa [hU] using φT.toH1Function.hasWeakGradient }
      approx := φT.approx
      approx_smooth := φT.approx_smooth
      approx_hasCompactSupport := φT.approx_hasCompactSupport
      approx_support_subset := by
        intro n
        simpa [hU] using φT.approx_support_subset n
      tendsto_approx := by
        simpa [hU] using φT.tendsto_approx
      tendsto_approx_grad := by
        intro i
        simpa [hU] using φT.tendsto_approx_grad i }
  have hEqT :
      ∫ x in translateSet z U₀,
          vecDot (u.toH1Function.grad x) (φT.toH1Function.grad x)
            ∂MeasureTheory.volume =
        ∫ x in translateSet z U₀, F x * φT.toH1Function x
            ∂MeasureTheory.volume := by
    simpa [φQ, hU] using hweak φQ
  have hleft :
      ∫ x in U₀,
          vecDot ((untranslateToOriginFunction Q u).toH1Function.grad x)
            (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in translateSet z U₀,
          vecDot (u.toH1Function.grad x) (φT.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa [Q₀, U₀, z, φT, H10Function.translate, H1Function.translate,
      sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
        (fun x => vecDot (u.toH1Function.grad x) (φT.toH1Function.grad x)))
  have hright :
      ∫ x in translateSet z U₀, F x * φT.toH1Function x
          ∂MeasureTheory.volume =
        ∫ x in U₀, F (x + z) * φ.toH1Function x
          ∂MeasureTheory.volume := by
    symm
    simpa [φT, H10Function.translate, H1Function.translate,
      sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
        (fun x => F x * φT.toH1Function x))
  calc
    ∫ x in openCubeSet Q₀,
        vecDot ((untranslateToOriginFunction Q u).toH1Function.grad x)
          (φ.toH1Function.grad x) ∂MeasureTheory.volume
        = ∫ x in translateSet z U₀,
            vecDot (u.toH1Function.grad x) (φT.toH1Function.grad x)
              ∂MeasureTheory.volume := by
          simpa [U₀] using hleft
    _ = ∫ x in translateSet z U₀, F x * φT.toH1Function x
          ∂MeasureTheory.volume := hEqT
    _ = ∫ x in U₀, F (x + z) * φ.toH1Function x
          ∂MeasureTheory.volume := hright
    _ = ∫ x in openCubeSet Q₀, F (x + triadicCubeShift Q) * φ.toH1Function x
          ∂MeasureTheory.volume := by
          simp [Q₀, U₀, z]

/-- Translating the centered pullback recovers the original arbitrary-cube
gradient. -/
theorem untranslateToOriginFunction_translate_grad (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (x : Vec d) :
    ((untranslateToOriginFunction Q u).toH1Function.translate
        (triadicCubeShift Q)).grad x =
      u.toH1Function.grad x := by
  simp [H1Function.translate, sub_eq_add_neg, add_assoc]

end CubeDirichletWeakPoissonProblem

end

end Homogenization
