/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalForcing

/-! The actual time derivative and normalized pressure also match at the history/forward junction.
-/

section

/-!
# The history trace matches the actual forward transverse solve

The forward datum is the constructed history coordinate velocity. Both
physical velocities therefore agree at the source time τ, with the same
deformation frame on the two intervals.
-/

section

/-!
The joined inverse uses coercivity only on the actual history interval.
Its source Hessian need not satisfy a smallness condition on the full
history-plus-forward time interval.
-/

@[expose] public section

noncomputable section

namespace EulerTransversePacketJoin

open Set EulerSmoothLimit EulerLpCylinderTranslation EulerTransversePacketProvider
  EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

/-- The terminal coordinate of the actual local history, used as forward data. -/
def forwardInitial : InitialData P (D.tail τ hτ.le hτT) where
  value := (B.terminalInitial (G.initial τ hτ hτT.le)).value
  orbit := (B.terminalInitial (G.initial τ hτ hτT.le)).orbit
  mean_zero := (B.terminalInitial (G.initial τ hτ hτT.le)).mean_zero

theorem forwardInitial_eq :
    ((forwardInitial τ hτ hτT B G).value : CylinderL2 P U) =
      B.coordinatePath (G.initial τ hτ hτT.le) ⟨τ,hτ.le,le_rfl⟩ :=
  congrArg₂ (fun (c : C(Icc (0 : ℝ) τ, CylinderL2 P U)) t => c t) rfl rfl

end EulerTransversePacketJoin

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTimeIntervalRestriction
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderRectangular
  EulerCylinderSmoothOrbit EulerPacketProfileRecursion EulerCylinderAngleAverage
  EulerTransversePacketProvider
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

/-- Past velocity, given by `B.velocityPath (G.initial τ hτ hτT.le)`. -/
def pastVelocity : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  B.velocityPath (G.initial τ hτ hτT.le)

/-- Future velocity, given by `includePath P D.support D.support_measurable ((G.tail τ hτ.le
hτT).velocityPath (forwardInitial τ hτ hτT B G))`. -/
def futureVelocity : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P D.support D.support_measurable
    ((G.tail τ hτ.le hτT).velocityPath (forwardInitial τ hτ hτT B G))

/-- Past derivative, given by `B.derivativePath (G.initial τ hτ hτT.le)`. -/
def pastDerivative : C(Icc (0 : ℝ) τ,LiftL2 P) :=
  B.derivativePath (G.initial τ hτ hτT.le)

/-- Future derivative, given by `includePath P D.support D.support_measurable ((G.tail τ hτ.le
hτT).derivativePath (forwardInitial τ hτ hτT B G))`. -/
def futureDerivative : C(Icc (0 : ℝ) (D.T-τ),LiftL2 P) :=
  includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P D.support D.support_measurable
    ((G.tail τ hτ.le hτT).derivativePath (forwardInitial τ hτ hτT B G))

/-- Past pressure, given by `B.pressurePath (G.initial τ hτ hτT.le)`. -/
def pastPressure : C(Icc (0 : ℝ) τ,CylinderL2 P ℝ) :=
  B.pressurePath (G.initial τ hτ hτT.le)

/-- Future pressure, given by `(G.tail τ hτ.le hτT).pressurePath (forwardInitial τ hτ hτT B G)`. -/
def futurePressure : C(Icc (0 : ℝ) (D.T-τ),CylinderL2 P ℝ) :=
  (G.tail τ hτ.le hτT).pressurePath (forwardInitial τ hτ hτT B G)

theorem pastVelocity_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) τ) (V := Vector3) P a
      (pastVelocity τ hτ hτT B G)) :=
  B.velocityPath_orbit (G.initial τ hτ hτT.le)

theorem futureVelocity_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P a
      (futureVelocity τ hτ hτT B G)) :=
  (G.tail τ hτ.le hτT).velocityPath_orbit (forwardInitial τ hτ hτT B G)

theorem pastDerivative_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) τ) (V := Vector3) P a
      (pastDerivative τ hτ hτT B G)) :=
  B.derivativePath_orbit (G.initial τ hτ hτT.le)

theorem futureDerivative_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) (D.T-τ)) (V := Vector3) P a
      (futureDerivative τ hτ hτT B G)) :=
  (G.tail τ hτ.le hτT).derivativePath_orbit (forwardInitial τ hτ hτT B G)

theorem pastPressure_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) τ) (V := ℝ) P a
      (pastPressure τ hτ hτT B G)) :=
  B.pressurePath_orbit (G.initial τ hτ hτT.le)

theorem futurePressure_orbit :
    ContDiff ℝ ∞ (fun a => pathTranslate (K := Icc (0 : ℝ) (D.T-τ)) (V := ℝ) P a
      (futurePressure τ hτ hτT B G)) :=
  (G.tail τ hτ.le hτT).pressurePath_orbit (forwardInitial τ hτ hτT B G)

theorem history_velocityPath_apply {D' : Data U} (B' : HistoryData D') {raw' : VectorField}
    (G' : Forcing P D' raw') (t : Icc (0 : ℝ) D'.T) :
    B'.velocityPath G' t =
      fullOperatorMap (E := U) (F := Space) P (D'.frame.field t) (B'.coordinatePath G' t) := rfl

theorem forward_velocityPath_apply {D' : Data U} {raw' : VectorField} (G' : Forcing P D' raw')
    (I : InitialData P D') (t : Icc (0 : ℝ) D'.T) :
    (G'.velocityPath I t : CylinderL2 P Space) =
      fullOperatorMap (E := U) (F := Space) P (D'.frame.field t)
        (G'.coordinatePath I t : CylinderL2 P U) := rfl

/-- The actual forward velocity starts from the actual history velocity. -/
theorem velocity_match : pastVelocity τ hτ hτT B G ⟨τ,hτ.le,le_rfl⟩ =
    futureVelocity τ hτ hτT B G ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  have hQ : (D.initial τ hτ hτT.le).frame.field (⟨τ,hτ.le,le_rfl⟩ : Icc (0 : ℝ) τ) =
      (D.tail τ hτ.le hτT).frame.field
        (⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : Icc (0 : ℝ) (D.T-τ)) := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    rw [Data.initial_frame_apply, Data.tail_frame_apply]
    exact congrArg (fun s => D.frame.field s x v) (Subtype.ext (add_zero τ).symm)
  rw [show pastVelocity τ hτ hτT B G = B.velocityPath (G.initial τ hτ hτT.le) from rfl,
    show futureVelocity τ hτ hτT B G =
      includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Space) P D.support D.support_measurable
        ((G.tail τ hτ.le hτT).velocityPath (forwardInitial τ hτ hτT B G)) from rfl]
  refine (history_velocityPath_apply B (G.initial τ hτ hτT.le)
    (⟨τ,hτ.le,le_rfl⟩ : Icc (0 : ℝ) τ)).trans (Eq.trans ?_
      (forward_velocityPath_apply (G.tail τ hτ.le hτT) (forwardInitial τ hτ hτT B G)
        (⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : Icc (0 : ℝ) (D.T-τ))).symm)
  simp only [hQ]
  refine congrArg _ ?_
  erw [EulerSourceCylinderEquation.coordinates_initial]
  rfl

end EulerTransversePacketJoin

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketJoin

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerTimeIntervalRestriction EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerLpCylinderRectangular EulerCylinderScalarPrimitive
      EulerSourceNormalCoefficient
  EulerPacketProfileRecursion EulerTransversePacketProvider
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

omit [Fact (0 < P)] [CompleteSpace U] in
theorem source_coefficient_match {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothCoefficientPath (Icc (0 : ℝ) D.T) V) :
    (A.comp (initialInclusion D.T τ hτT.le)).field ⟨τ,hτ.le,le_rfl⟩ =
      (A.comp (tailInclusion D.T τ hτ.le)).field ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  change A.field ⟨τ,hτ.le,hτT.le⟩ = A.field ⟨τ+0,by linarith,by linarith⟩
  simp only [add_zero]

omit [Fact (0 < P)] [CompleteSpace U] in
theorem normal_match :
    (D.initial τ hτ hτT.le).normal.field ⟨τ,hτ.le,le_rfl⟩ =
      (D.tail τ hτ.le hτT).normal.field ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ :=
  source_coefficient_match τ hτ hτT D.normal

omit [CompleteSpace U] in
theorem forcing_match :
    ((G.initial τ hτ hτT.le).path ⟨τ,hτ.le,le_rfl⟩ : CylinderL2 P Space) =
      ((G.tail τ hτ.le hτT).path ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : CylinderL2 P Space) := by
  change (G.path ⟨τ,hτ.le,hτT.le⟩ : CylinderL2 P Space) =
    (G.path ⟨τ+0,by linarith,by linarith⟩ : CylinderL2 P Space)
  simp only [add_zero]

theorem balance_cancel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a b v w m n f g : E} {M N : E →L[ℝ] E}
    (hx : a + M v + ((⟪m, f⟫_ℝ - 2 * ⟪m, M v⟫_ℝ) / ‖m‖ ^ 2) • m = f)
    (hy : b + N w + ((⟪n, g⟫_ℝ - 2 * ⟪n, N w⟫_ℝ) / ‖n‖ ^ 2) • n = g)
    (hM : M = N) (hm : m = n) (hf : f = g) (hv : v = w) : a = b := by
  subst hM hm hf hv
  exact add_right_cancel (add_right_cancel (hx.trans hy.symm))

theorem forward_balance_ae {D' : Data U} {raw' : VectorField} (G' : Forcing P D' raw')
    (I : InitialData P D') (t : Icc (0 : ℝ) D'.T) :
    ∀ᵐ x ∂liftMeasure P,
      (G'.derivativePath I t : CylinderL2 P Space) x +
        D'.M.field t x.1 ((G'.velocityPath I t : CylinderL2 P Space) x) +
        ((⟪D'.normal.field t x.1, (G'.path t : CylinderL2 P Space) x⟫_ℝ -
          2 * ⟪D'.normal.field t x.1,
            D'.M.field t x.1 ((G'.velocityPath I t : CylinderL2 P Space) x)⟫_ℝ) /
          ‖D'.normal.field t x.1‖ ^ 2) • D'.normal.field t x.1 =
      (G'.path t : CylinderL2 P Space) x := by
  unfold Forcing.derivativePath Forcing.velocityPath
  exact EulerSourceCylinderEquation.velocity_balance_ae P D'.support D'.support_measurable
    D'.T D'.T_pos.le D'.frame D'.frameDerivative D'.frameLower D'.frameLower_pos D'.frame_lower
    G'.path I.value (fun t x => D'.M.field t x) (fun t x => D'.normal.field t x)
    (HistoryData.normal_ne_zero (D := D')) D'.frame_tangent D'.frame_range D'.frame_strain t

/-- The same physical first-order equation determines the same derivative
from the matching velocity and forcing. -/
theorem derivative_match : pastDerivative τ hτ hτT B G ⟨τ,hτ.le,le_rfl⟩ =
    futureDerivative τ hτ hτT B G ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  -- The trace paths are unfolded as bundled paths (cheap `rfl`s between applications), so the
  -- two balance laws below are compared syntactically rather than by unfolding their values.
  have hpd : pastDerivative τ hτ hτT B G = B.derivativePath (G.initial τ hτ hτT.le) := rfl
  have hfd : futureDerivative τ hτ hτT B G =
      includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Space) P D.support D.support_measurable
        ((G.tail τ hτ.le hτT).derivativePath (forwardInitial τ hτ hτT B G)) := rfl
  have hv := velocity_match τ hτ hτT B G
  rw [show pastVelocity τ hτ hτT B G = B.velocityPath (G.initial τ hτ hτT.le) from rfl,
    show futureVelocity τ hτ hτT B G =
      includePath (K := Icc (0 : ℝ) (D.T-τ)) (V := Space) P D.support D.support_measurable
        ((G.tail τ hτ.le hτT).velocityPath (forwardInitial τ hτ hτT B G)) from rfl] at hv
  rw [hpd, hfd]
  apply Lp.ext
  filter_upwards [B.balance_ae (G.initial τ hτ hτT.le) (⟨τ,hτ.le,le_rfl⟩ : Icc (0 : ℝ) τ),
    forward_balance_ae (G.tail τ hτ.le hτT) (forwardInitial τ hτ hτT B G)
      (⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ : Icc (0 : ℝ) (D.T-τ))] with x hx hy
  exact balance_cancel hx hy
    (DFunLike.congr_fun (source_coefficient_match τ hτ hτT D.M) x.1)
    (DFunLike.congr_fun (normal_match τ hτ hτT) x.1)
    (congrArg (fun f : CylinderL2 P Space => f x) (forcing_match τ hτ hτT G))
    (congrArg (fun f : LiftL2 P => f x) hv)

/-- The normalized pressure integral has the same input scalar L² class on
both sides of the junction. -/
theorem pressure_match : pastPressure τ hτ hτT B G ⟨τ,hτ.le,le_rfl⟩ =
    futurePressure τ hτ hτT B G ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩ := by
  let Dh := D.initial τ hτ hτT.le
  let Df := D.tail τ hτ.le hτT
  let th : Icc (0 : ℝ) τ := ⟨τ,hτ.le,le_rfl⟩
  let tf : Icc (0 : ℝ) (D.T-τ) := ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  have hM : Dh.M.field th = Df.M.field tf := source_coefficient_match τ hτ hτT D.M
  have hm : Dh.normal.field th = Df.normal.field tf := normal_match τ hτ hτT
  have hN : normalFunctional Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower th =
      normalFunctional Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower tf := by
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    exact (normalFunctional_apply Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower
      th x v).trans ((congrArg (fun m : Space →ᵇ Space => ⟪m x,v⟫_ℝ / ‖m x‖^2) hm).trans
        (normalFunctional_apply Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower
          tf x v).symm)
  change primitive P (fullOperatorMap (E := Space) (F := ℝ) P
      (normalFunctional Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower th)
      (((G.initial τ hτ hτT.le).path th : CylinderL2 P Space)-(2 : ℝ) •
        fullOperatorMap (E := Space) (F := Space) P (Dh.M.field th)
          (pastVelocity τ hτ hτT B G th))) =
    primitive P (fullOperatorMap (E := Space) (F := ℝ) P
      (normalFunctional Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower tf)
      (((G.tail τ hτ.le hτT).path tf : CylinderL2 P Space)-(2 : ℝ) •
        fullOperatorMap (E := Space) (F := Space) P (Df.M.field tf)
          (futureVelocity τ hτ hτT B G tf)))
  have hforce : ((G.initial τ hτ hτT.le).path th : CylinderL2 P Space) =
      ((G.tail τ hτ.le hτT).path tf : CylinderL2 P Space) := forcing_match τ hτ hτT G
  have hv : pastVelocity τ hτ hτT B G th = futureVelocity τ hτ hτT B G tf :=
    velocity_match τ hτ hτT B G
  exact congrArg (fun x => primitive P x)
    (congrArg₂ (fun N w => fullOperatorMap (E := Space) (F := ℝ) P N w) hN
      (congrArg₂ (fun (f w : CylinderL2 P Space) => f - (2 : ℝ) • w) hforce
        (congrArg₂ (fun M w => fullOperatorMap (E := Space) (F := Space) P M w) hM hv)))

end EulerTransversePacketJoin
