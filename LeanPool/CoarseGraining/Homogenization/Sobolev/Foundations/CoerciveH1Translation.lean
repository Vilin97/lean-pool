/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Translation

/-! # Coercive H1Translation -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- Translate a mean-zero `H¹(U)` witness to `H¹(U + z)`. -/
noncomputable def translate (u : H1MeanZeroFunction U) (z : Vec d) :
    H1MeanZeroFunction (translateSet z U) where
  toH1Function := u.toH1Function.translate z
  meanZero := by
    change ∫ x in translateSet z U, u.toH1Function.toFun (x - z) ∂MeasureTheory.volume = 0
    rw [setIntegral_comp_subRight_translateSet]
    exact u.meanZero

@[simp] theorem translate_toH1Function (u : H1MeanZeroFunction U) (z : Vec d) :
    (u.translate z).toH1Function = u.toH1Function.translate z :=
  rfl

@[simp] theorem translate_apply (u : H1MeanZeroFunction U) (z : Vec d) (x : Vec d) :
    u.translate z x = u (x - z) :=
  rfl

@[simp] theorem translate_grad (u : H1MeanZeroFunction U) (z : Vec d) (x : Vec d) :
    (u.translate z).toH1Function.grad x = u.toH1Function.grad (x - z) :=
  rfl

/-- Pull a mean-zero `H¹(U + z)` witness back to `H¹(U)`. -/
noncomputable def untranslate (z : Vec d)
    (u : H1MeanZeroFunction (translateSet z U)) : H1MeanZeroFunction U where
  toH1Function := H1Function.untranslate z u.toH1Function
  meanZero := by
    change ∫ x in U, u.toH1Function.toFun (x + z) ∂MeasureTheory.volume = 0
    rw [setIntegral_comp_addRight_translateSet]
    exact u.meanZero

@[simp] theorem untranslate_toH1Function (z : Vec d)
    (u : H1MeanZeroFunction (translateSet z U)) :
    (u.untranslate z).toH1Function = H1Function.untranslate z u.toH1Function :=
  rfl

@[simp] theorem untranslate_apply (z : Vec d)
    (u : H1MeanZeroFunction (translateSet z U)) (x : Vec d) :
    u.untranslate z x = u (x + z) :=
  rfl

@[simp] theorem untranslate_grad (z : Vec d)
    (u : H1MeanZeroFunction (translateSet z U)) (x : Vec d) :
    (u.untranslate z).toH1Function.grad x = u.toH1Function.grad (x + z) :=
  rfl

/-- Translation preserves the scalar `L²` norm of a mean-zero `H¹` witness. -/
theorem valueL2Norm_untranslate_eq (z : Vec d)
    (u : H1MeanZeroFunction (translateSet z U)) :
    (u.untranslate z).valueL2Norm = u.valueL2Norm := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  have hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  unfold H1MeanZeroFunction.valueL2Norm H1MeanZeroFunction.toScalarL2
    H1Function.toScalarL2 Homogenization.toScalarL2
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  exact congrArg ENNReal.toReal (by
    simpa [H1MeanZeroFunction.untranslate, H1Function.untranslate, V, T, Function.comp,
      volumeMeasureOn] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := u.toH1Function.toFun) (p := (2 : ℝ≥0∞))
        u.toH1Function.memL2.aestronglyMeasurable hμ))

/-- Translation preserves the gradient `L²` norm of a mean-zero `H¹` witness. -/
theorem gradientL2Norm_untranslate_eq (z : Vec d)
    (u : H1MeanZeroFunction (translateSet z U)) :
    (u.untranslate z).gradientL2Norm = u.gradientL2Norm := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  have hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  unfold H1MeanZeroFunction.gradientL2Norm H1MeanZeroFunction.gradToVectorL2
    H1Function.gradToVectorL2 Homogenization.toVectorL2
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  exact congrArg ENNReal.toReal (by
    simpa [H1MeanZeroFunction.untranslate, H1Function.untranslate, V, T, Function.comp,
      volumeMeasureOn] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := u.toH1Function.grad) (p := (2 : ℝ≥0∞))
        u.toH1Function.grad_memVectorL2.aestronglyMeasurable hμ))

end H1MeanZeroFunction

namespace H1CoerciveEstimate

variable {d : ℕ} {U : Set (Vec d)}

/-- Translate a coercive `H¹` estimate from `U` to `U + z` without changing its
constant. -/
noncomputable def translate [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hC : H1CoerciveEstimate U) (z : Vec d) :
    H1CoerciveEstimate (translateSet z U) where
  fixedValue := hC.fixedValue
  constant_nonneg := hC.constant_nonneg
  bound := by
    intro u
    let v : H1MeanZeroFunction U := u.untranslate z
    calc
      u.valueL2Norm = v.valueL2Norm := by
        simpa [v] using (H1MeanZeroFunction.valueL2Norm_untranslate_eq (U := U) z u).symm
      _ ≤ hC.fixedValue * v.gradientL2Norm := hC.bound v
      _ = hC.fixedValue * u.gradientL2Norm := by
        rw [H1MeanZeroFunction.gradientL2Norm_untranslate_eq (U := U) z u]

@[simp] theorem translate_constant [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hC : H1CoerciveEstimate U) (z : Vec d) :
    (hC.translate z).fixedValue = hC.fixedValue :=
  rfl

end H1CoerciveEstimate

end

end Homogenization
