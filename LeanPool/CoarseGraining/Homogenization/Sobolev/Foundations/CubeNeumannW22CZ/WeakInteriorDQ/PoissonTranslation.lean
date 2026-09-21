/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CubeTranslationTransport

/-! # Poisson Translation -/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ}

/-- Pull a cube Neumann solution back to the centered cube of the same scale. -/
noncomputable def untranslateToOrigin (Q : TriadicCube d) {F : Vec d → ℝ}
    (W : MeanZeroNeumannPoissonSolution Q F) :
    MeanZeroNeumannPoissonSolution (originCube d Q.scale)
      (fun x => F (x + triadicCubeShift Q)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let wT : H1MeanZeroFunction (translateSet z U₀) :=
    { toH1Function :=
        { toFun := W.w.toH1Function.toFun
          grad := W.w.toH1Function.grad
          memL2 := by
            simpa [← hU] using W.w.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [← hU] using W.w.toH1Function.gradMemL2 i
          hasWeakGradient := by
            simpa [← hU] using W.w.toH1Function.hasWeakGradient }
      meanZero := by
        simpa [MeanZeroOn, ← hU] using W.w.meanZero }
  refine
    { w := wT.untranslate z
      equation := ?_ }
  intro φ
  let φT : H1MeanZeroFunction (translateSet z U₀) := φ.translate z
  let φQ : H1MeanZeroFunction (openCubeSet Q) :=
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
      meanZero := by
        simpa [MeanZeroOn, hU] using φT.meanZero }
  have hEqT :
      ∫ x in translateSet z U₀,
          vecDot (wT.toH1Function.grad x) (φT.toH1Function.grad x)
            ∂MeasureTheory.volume =
        ∫ x in translateSet z U₀, F x * φT.toH1Function x
            ∂MeasureTheory.volume := by
    simpa [wT, φQ, hU] using W.equation φQ
  have hleft :
      ∫ x in U₀,
          vecDot ((wT.untranslate z).toH1Function.grad x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume =
        ∫ x in translateSet z U₀,
          vecDot (wT.toH1Function.grad x) (φT.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    simpa [φT, H1MeanZeroFunction.translate, H1Function.translate,
      H1MeanZeroFunction.untranslate, H1Function.untranslate, U₀, z,
      sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
        (fun x => vecDot (wT.toH1Function.grad x) (φT.toH1Function.grad x)))
  have hright :
      ∫ x in translateSet z U₀, F x * φT.toH1Function x
          ∂MeasureTheory.volume =
        ∫ x in U₀, F (x + z) * φ.toH1Function x
          ∂MeasureTheory.volume := by
    symm
    simpa [φT, H1MeanZeroFunction.translate, H1Function.translate,
      sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
        (fun x => F x * φT.toH1Function x))
  calc
    ∫ x in openCubeSet Q₀,
        vecDot ((wT.untranslate z).toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
        = ∫ x in translateSet z U₀,
            vecDot (wT.toH1Function.grad x) (φT.toH1Function.grad x)
              ∂MeasureTheory.volume := by
          simpa [U₀] using hleft
    _ = ∫ x in translateSet z U₀, F x * φT.toH1Function x
          ∂MeasureTheory.volume := hEqT
    _ = ∫ x in U₀, F (x + z) * φ.toH1Function x
          ∂MeasureTheory.volume := hright
    _ = ∫ x in openCubeSet Q₀, F (x + triadicCubeShift Q) * φ.toH1Function x
          ∂MeasureTheory.volume := by
          simp [Q₀, U₀, z]

theorem untranslateToOrigin_translate_grad (Q : TriadicCube d) {F : Vec d → ℝ}
    (W : MeanZeroNeumannPoissonSolution Q F) (x : Vec d) :
    (((W.untranslateToOrigin Q).w.toH1Function).translate (triadicCubeShift Q)).grad x =
      W.w.toH1Function.grad x := by
  simp [untranslateToOrigin, H1MeanZeroFunction.untranslate, H1Function.untranslate,
    H1Function.translate, sub_eq_add_neg, add_assoc]

end MeanZeroNeumannPoissonSolution

end

end Homogenization
