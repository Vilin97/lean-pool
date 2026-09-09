/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveSpatialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity

@[expose] public section

/-! The literal periodic scalar pressure primitive, with actual smoothness and normalization. -/

noncomputable section

namespace EulerCylinderScalarPrimitive

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] (f : LiftDomain P → ℝ) (hf : Continuous f)
  (hmean : ∀ y, (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) = 0)

omit [Fact (0 < P)] in
theorem scalarAngle_periodic (y : Space) : Function.Periodic (fun s : ℝ => f (y,(s : AddCircle P)))
  P := by
  intro s
  change f (y,((s+P : ℝ) : AddCircle P)) = f (y,(s : AddCircle P))
  rw [AddCircle.coe_add_period]

/-- The normalized integral descended to the actual periodic cylinder. -/
def classicalPrimitive (x : LiftDomain P) : ℝ :=
  (EulerAngleMeanZeroPrimitive.primitive_periodic P (fun s => f (x.1,(s : AddCircle P)))
    (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P)))
    (scalarAngle_periodic P f x.1) (hmean x.1)).lift x.2

omit [Fact (0 < P)] in
theorem classicalPrimitive_cover (y : Space) (θ : ℝ) :
    classicalPrimitive P f hf hmean (y,(θ : AddCircle P)) =
      EulerAngleMeanZeroPrimitive.primitive P (fun s => f (y,(s : AddCircle P))) θ :=
  Function.Periodic.lift_coe _ θ

omit [Fact (0 < P)] in
/-- The literal angular derivative is the original scalar field. -/
theorem classicalPrimitive_angle (y : Space) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => classicalPrimitive P f hf hmean (y,(s : AddCircle P)))
      (f (y,(θ : AddCircle P))) θ := by
  have he : (fun s : ℝ => classicalPrimitive P f hf hmean (y,(s : AddCircle P))) =
      EulerAngleMeanZeroPrimitive.primitive P (fun s => f (y,(s : AddCircle P))) :=
    funext (classicalPrimitive_cover P f hf hmean y)
  rw [he]
  exact EulerAngleMeanZeroPrimitive.primitive_hasDerivAt P _
    (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P))) θ

theorem classicalPrimitive_mean_zero (y : Space) :
    (∫ θ in (0 : ℝ)..P, classicalPrimitive P f hf hmean (y,(θ : AddCircle P))) = 0 := by
  simp_rw [classicalPrimitive_cover]
  exact EulerAngleMeanZeroPrimitive.primitive_mean_zero P (ne_of_gt (Fact.out : 0 < P)) _
    (hf.comp (continuous_const.prodMk (AddCircle.continuous_mk' P)))

/-- The actual normalized integral is smooth in all cylinder variables. -/
theorem classicalPrimitive_smooth
    (hfs : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (x : LiftDomain P) :
    ContDiff ℝ ∞ (localFieldLift P (classicalPrimitive P f hf hmean) x) := by
  let F : Space × ℝ → ℝ := localFieldLift P f 0
  have hF : ContDiff ℝ ∞ F := hfs 0
  have hq := EulerAngleMeanZeroPrimitive.primitive_joint_contDiff P (le_of_lt (Fact.out : 0 < P)) F
    hF
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have hx : x = coveringMap P (x.1,θ) := by
    apply Prod.ext
    · rfl
    · exact hθ.symm
  rw [hx,localFieldLift_cover]
  have he : localFieldLift P (classicalPrimitive P f hf hmean) 0 =
      fun z : LiftTangent => EulerAngleMeanZeroPrimitive.primitive P (fun s => F (z.1,s)) z.2 := by
    funext z
    simp only [localFieldLift,Prod.fst_zero,Prod.snd_zero,zero_add,classicalPrimitive_cover,F]
  rw [he]
  exact hq.comp (contDiff_const.add contDiff_id)

theorem classicalPrimitive_continuous
    (hfs : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) :
    Continuous (classicalPrimitive P f hf hmean) :=
  smoothField_continuous P _ (classicalPrimitive_smooth P f hf hmean hfs)

omit [Fact (0 < P)] in
/-- Angular integration does not spread spatial support. -/
theorem classicalPrimitive_zero (y : Space) (hy : ∀ θ : AddCircle P, f (y,θ) = 0) (θ : AddCircle P)
  :
    classicalPrimitive P f hf hmean (y,θ) = 0 := by
  obtain ⟨s,rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [classicalPrimitive_cover]
  have he : (fun r : ℝ => f (y,(r : AddCircle P))) = fun _ => 0 := funext (fun r => hy r)
  simp only [he,EulerAngleMeanZeroPrimitive.primitive,EulerAngleMeanZeroPrimitive.rawPrimitive,
    intervalIntegral.integral_zero,smul_zero,sub_zero]

end EulerCylinderScalarPrimitive
