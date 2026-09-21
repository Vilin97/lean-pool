/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Core
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.Translation

/-! # Translation -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

/-- Translation preserves the scalar `L^p` seminorm of a `W^{1,p}` witness. -/
theorem valueLpSeminorm_translate_eq (u : W1pFunction U p) (z : Vec d) :
    (u.translate z).valueLpSeminorm = u.valueLpSeminorm := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  have hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  unfold valueLpSeminorm
  exact congrArg ENNReal.toReal (by
    simpa [V, T, Function.comp, volumeMeasureOn] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := u.toFun) (p := p) u.memLp.aestronglyMeasurable hμ))

/-- Translation commutes with the integral average. -/
theorem integralAverage_translate_eq (u : W1pFunction U p) (z : Vec d) :
    integralAverage (translateSet z U) (u.translate z).toFun = integralAverage U u.toFun := by
  change
    (MeasureTheory.volume (translateSet z U)).toReal⁻¹ *
        ∫ x in translateSet z U, u.toFun (x - z) ∂MeasureTheory.volume =
      (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, u.toFun x ∂MeasureTheory.volume
  rw [volume_translateSet_eq, setIntegral_comp_subRight_translateSet]

/-- Translation preserves the scalar `L^p` seminorm after subtracting the average. -/
theorem subAverageLpSeminorm_translate_eq (u : W1pFunction U p) (z : Vec d) :
    (u.translate z).subAverageLpSeminorm = u.subAverageLpSeminorm := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  have hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  unfold subAverageLpSeminorm
  rw [u.integralAverage_translate_eq z]
  exact congrArg ENNReal.toReal (by
    simpa [V, T, Function.comp, volumeMeasureOn] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := fun x => u.toFun x - integralAverage U u.toFun) (p := p)
        (u.memLp.aestronglyMeasurable.sub continuous_const.aestronglyMeasurable) hμ))

/-- Translation preserves every coordinate gradient `L^p` seminorm. -/
theorem gradCoordLpSeminorm_translate_eq (u : W1pFunction U p) (z : Vec d) (i : Fin d) :
    (u.translate z).gradCoordLpSeminorm i = u.gradCoordLpSeminorm i := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  have hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  unfold gradCoordLpSeminorm
  exact congrArg ENNReal.toReal (by
    simpa [V, T, Function.comp, volumeMeasureOn] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := fun x => u.grad x i) (p := p) (u.gradMemLp i).aestronglyMeasurable hμ))

/-- Translation preserves the coordinate-sum gradient `L^p` seminorm. -/
theorem gradientCoordLpSeminormSum_translate_eq (u : W1pFunction U p) (z : Vec d) :
    (u.translate z).gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum := by
  unfold gradientCoordLpSeminormSum
  exact Finset.sum_congr rfl fun i _ => u.gradCoordLpSeminorm_translate_eq z i

private noncomputable def castDomain {V : Set (Vec d)}
    (hUV : U = V) (u : W1pFunction U p) : W1pFunction V p :=
  hUV ▸ u

@[simp] private theorem castDomain_toFun {V : Set (Vec d)}
    (hUV : U = V) (u : W1pFunction U p) :
    (castDomain hUV u).toFun = u.toFun := by
  subst V
  rfl

@[simp] private theorem castDomain_grad {V : Set (Vec d)}
    (hUV : U = V) (u : W1pFunction U p) :
    (castDomain hUV u).grad = u.grad := by
  subst V
  rfl

private noncomputable def untranslateForPoincare (z : Vec d)
    (u : W1pFunction (translateSet z U) p) : W1pFunction U p := by
  have hset : translateSet (-z) (translateSet z U) = U := by
    rw [translateSet_translateSet]
    simp
  exact castDomain hset (u.translate (-z))

@[simp] private theorem untranslateForPoincare_toFun (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (x : Vec d) :
    (untranslateForPoincare z u).toFun x = u.toFun (x + z) := by
  simp [untranslateForPoincare, W1pFunction.translate, sub_eq_add_neg]

@[simp] private theorem untranslateForPoincare_grad (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (x : Vec d) :
    (untranslateForPoincare z u).grad x = u.grad (x + z) := by
  simp [untranslateForPoincare, W1pFunction.translate, sub_eq_add_neg]

private theorem valueLpSeminorm_untranslateForPoincare_eq (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    (untranslateForPoincare z u).valueLpSeminorm = u.valueLpSeminorm := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  have hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  unfold valueLpSeminorm
  have hfun : (untranslateForPoincare z u).toFun = u.toFun ∘ T := by
    funext x
    simp [T, Function.comp]
  rw [hfun]
  exact congrArg ENNReal.toReal (by
    simpa [V, T, Function.comp, volumeMeasureOn] using
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := u.toFun) (p := p) u.memLp.aestronglyMeasurable hμ))

private theorem gradientCoordLpSeminormSum_untranslateForPoincare_eq (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    (untranslateForPoincare z u).gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum := by
  unfold gradientCoordLpSeminormSum gradCoordLpSeminorm
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  have hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg ENNReal.toReal
  have hfun : (fun x => (untranslateForPoincare z u).grad x i) =
      (fun x => u.grad x i) ∘ T := by
    funext x
    simp [T, Function.comp]
  rw [hfun]
  simpa [V, T, Function.comp, volumeMeasureOn] using
    (MeasureTheory.eLpNorm_comp_measurePreserving
      (g := fun x => u.grad x i) (p := p) (u.gradMemLp i).aestronglyMeasurable hμ)

end W1pFunction

namespace W1pMeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

/-- Translate a mean-zero `W^{1,p}(U)` witness to `W^{1,p}(U + z)`. -/
noncomputable def translate (u : W1pMeanZeroFunction U p) (z : Vec d) :
    W1pMeanZeroFunction (translateSet z U) p where
  toW1pFunction := u.toW1pFunction.translate z
  meanZero := by
    change ∫ x in translateSet z U, u.toW1pFunction.toFun (x - z) ∂MeasureTheory.volume = 0
    rw [setIntegral_comp_subRight_translateSet]
    exact u.meanZero

@[simp] theorem translate_toW1pFunction (u : W1pMeanZeroFunction U p) (z : Vec d) :
    (u.translate z).toW1pFunction = u.toW1pFunction.translate z :=
  rfl

private noncomputable def untranslateForPoincare (z : Vec d)
    (u : W1pMeanZeroFunction (translateSet z U) p) : W1pMeanZeroFunction U p where
  toW1pFunction := W1pFunction.untranslateForPoincare z u.toW1pFunction
  meanZero := by
    change ∫ x in U, W1pFunction.untranslateForPoincare z u.toW1pFunction x
      ∂MeasureTheory.volume = 0
    simp only [W1pFunction.untranslateForPoincare_toFun]
    rw [setIntegral_comp_addRight_translateSet]
    exact u.meanZero

end W1pMeanZeroFunction

namespace W1pPoincareEstimate

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

/-- Translate a finite-`p` Poincare estimate from `U` to `U + z` unchanged. -/
noncomputable def translate (hC : W1pPoincareEstimate U p) (z : Vec d) :
    W1pPoincareEstimate (translateSet z U) p where
  fixedValue := hC.constant
  constant_nonneg := hC.constant_nonneg
  bound := by
    intro u
    let v : W1pMeanZeroFunction U p := W1pMeanZeroFunction.untranslateForPoincare z u
    calc
      u.valueLpSeminorm = v.valueLpSeminorm := by
        simpa [v, W1pMeanZeroFunction.valueLpSeminorm] using!
          (W1pFunction.valueLpSeminorm_untranslateForPoincare_eq (U := U) z
            u.toW1pFunction).symm
      _ ≤ hC.constant * v.gradientCoordLpSeminormSum := hC.bound v
      _ = hC.constant * u.gradientCoordLpSeminormSum := by
        rw [show v.gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum by
          simpa [v, W1pMeanZeroFunction.gradientCoordLpSeminormSum] using!
            W1pFunction.gradientCoordLpSeminormSum_untranslateForPoincare_eq (U := U) z
              u.toW1pFunction]

@[simp] theorem translate_constant (hC : W1pPoincareEstimate U p) (z : Vec d) :
    (hC.translate z).constant = hC.constant :=
  rfl

end W1pPoincareEstimate

end

end Homogenization
