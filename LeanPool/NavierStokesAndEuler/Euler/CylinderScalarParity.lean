/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarClassical
public import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveParity

@[expose] public section

/-! The normalized scalar angular primitive converts joint odd parity to even parity. -/

noncomputable section

namespace EulerCylinderScalarPrimitive

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerAngleMeanZeroPrimitive

variable (P : ℝ) [Fact (0 < P)] (f : LiftDomain P → ℝ) (hf : Continuous f)
  (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) = 0)

theorem classicalPrimitive_joint_even
    (hodd : ∀ y θ, f (-y,((-θ : ℝ) : AddCircle P)) = -f (y,(θ : AddCircle P)))
    (y : Space) (θ : ℝ) :
    classicalPrimitive P f hf hmean (-y,((-θ : ℝ) : AddCircle P)) =
      classicalPrimitive P f hf hmean (y,(θ : AddCircle P)) := by
  rw [classicalPrimitive_cover,classicalPrimitive_cover]
  have he : (fun s : ℝ => f (-y,(s : AddCircle P))) = fun s => -f (y,((-s : ℝ) : AddCircle P)) := by
    funext s
    simpa only [neg_neg] using hodd y (-s)
  rw [he,primitive_reflection P (Fact.out : 0 < P).ne'
    (fun s : ℝ => f (y,(s : AddCircle P)))
    (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P)))
    (scalarAngle_periodic P f y) (hmean y)]
  simp only [neg_neg]

end EulerCylinderScalarPrimitive
