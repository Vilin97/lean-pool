/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedField
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderPressureWeight
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientWeight
public import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight

@[expose] public section

/-!
# The joined pressure is the actual global normal-residual primitive

The two local coercivity constants may differ. Both normal functionals are
nevertheless the literal quotient by the same squared normal, so the joined
pressure equals one global bounded cylinder operator applied to the actual
forcing and velocity. This gives its estimates without any further solve.
-/

noncomputable section

namespace EulerTransversePacketJoin

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
    EulerLpCylinderRectangular
  EulerPacketProfileRecursion EulerTransversePacketProvider EulerTimeIntervalRestriction
  EulerSourceNormalCoefficient EulerSourceNormalResidualBounds EulerCylinderScalarPrimitive
  EulerContinuousTimeWeight EulerParameterWordGevrey EulerGevrey EulerTimeLpGramGevrey
  EulerPacketCylinderField EulerCylinderSobolev
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

/-- Actual equality of the whole pressure path, including the junction. -/
theorem pressurePath_eq_source : pressurePath τ hτ hτT B G =
    sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
      (HistoryData.forcingPath G) (velocityPath τ hτ hτT B G) := by
  apply ContinuousMap.ext
  intro t
  by_cases ht : (t : ℝ) ≤ τ
  · let th : Icc (0 : ℝ) τ := ⟨t,t.property.1,ht⟩
    let Dh := D.initial τ hτ hτT.le
    have hN : normalFunctional Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower th =
        normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t := by
      apply BoundedContinuousFunction.ext
      intro x
      apply ContinuousLinearMap.ext
      intro v
      erw [normalFunctional_apply]
    rw [pressurePath_left τ hτ hτT B G th]
    change primitive P (fullOperatorMap P
      (normalFunctional Dh.normal Dh.normalLower Dh.normalLower_pos Dh.normal_lower th)
      ((HistoryData.forcingPath (G.initial τ hτ hτT.le)) th-(2 : ℝ) •
        fullOperatorMap P (Dh.M.field th) (pastVelocity τ hτ hτT B G th))) =
      primitive P (fullOperatorMap P
        (normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t)
        ((HistoryData.forcingPath G) t-(2 : ℝ) • fullOperatorMap P (D.M.field t)
          (velocityPath τ hτ hτT B G t)))
    rw [hN,velocityPath_left τ hτ hτT B G th]
    rfl
  · let tr : Icc τ D.T := ⟨t,(not_le.mp ht).le,t.property.2⟩
    let tf : Icc (0 : ℝ) (D.T-τ) :=
      ⟨(t : ℝ)-τ,sub_nonneg.mpr tr.property.1,sub_le_sub_right t.property.2 τ⟩
    let Df := D.tail τ hτ.le hτT
    have he : tailInclusion D.T τ hτ.le tf = t := by
      apply Subtype.ext
      change τ+((t : ℝ)-τ) = t
      ring
    have hN : normalFunctional Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower tf =
        normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t := by
      apply BoundedContinuousFunction.ext
      intro x
      apply ContinuousLinearMap.ext
      intro v
      erw [normalFunctional_apply,normalFunctional_apply]
      change ⟪D.normal.field (tailInclusion D.T τ hτ.le tf) x,v⟫_ℝ/
        ‖D.normal.field (tailInclusion D.T τ hτ.le tf) x‖^2 = _
      rw [he]
    have hM : Df.M.field tf = D.M.field t := by
      change D.M.field (tailInclusion D.T τ hτ.le tf) = _
      rw [he]
    have hf : (HistoryData.forcingPath (G.tail τ hτ.le hτT)) tf = (HistoryData.forcingPath G) t :=
      by
      change (HistoryData.forcingPath G) (tailInclusion D.T τ hτ.le tf) = _
      rw [he]
    rw [pressurePath_right τ hτ hτT B G tr]
    change primitive P (fullOperatorMap P
      (normalFunctional Df.normal Df.normalLower Df.normalLower_pos Df.normal_lower tf)
      ((HistoryData.forcingPath (G.tail τ hτ.le hτT)) tf-(2 : ℝ) •
        fullOperatorMap P (Df.M.field tf) (futureVelocity τ hτ hτT B G tf))) =
      primitive P (fullOperatorMap P
        (normalFunctional D.normal D.normalLower D.normalLower_pos D.normal_lower t)
        ((HistoryData.forcingPath G) t-(2 : ℝ) • fullOperatorMap P (D.M.field t)
          (velocityPath τ hτ hτT B G t)))
    rw [hN,hM,hf,velocityPath_right τ hτ hτT B G tr]

theorem pressurePath_normalized_eq_source
    (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t) :
    normalize g hg (pressurePath τ hτ hτT B G) =
      sourcePressure P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
        (normalize g hg (HistoryData.forcingPath G))
        (normalize g hg (velocityPath τ hτ hτT B G)) := by
  rw [pressurePath_eq_source]
  exact (sourcePressure_weight P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    (reciprocal g hg) (HistoryData.forcingPath G) (velocityPath τ hτ hτT B G)).symm

/-- Literal pressure bound from the actual normalized forcing and velocity. -/
theorem source_pressure_bound
    (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
    {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc Cm CM Ri R Af Av : ℝ) (hRc : 0 ≤ Rc) (hCm : 0 ≤ Cm) (hCM : 0 ≤ CM)
    (hAf : 0 ≤ Af) (hAv : 0 ≤ Av) (hRi : 2*gramCost D.normalLower Cm 1*(Rc+1) ≤ Ri)
    (hR : sobolevCoefficientRadius ι (4*Ri) ≤ R)
    (hm : ∀ n t x, ‖iteratedFDeriv ℝ n (D.normal.field t : Space → Space) x‖ ≤ Cm*majorant Rc 0 n)
    (hM : ∀ n t x, ‖iteratedFDeriv ℝ n (D.M.field t : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant
      Rc 0 n)
    (d : ℕ)
    (hf : ∀ n, block directions q (fun a => pathTranslate P a
      (normalize g hg (HistoryData.forcingPath G))) n 0 ≤ Af*majorant R d n)
    (hv : ∀ n, block directions q (fun a => pathTranslate P a
      (normalize g hg (velocityPath τ hτ hτT B G))) n 0 ≤ Av*majorant R d n) (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize g hg (pressurePath τ hτ hτT B G))) n 0 ≤
        (P*pressureCost ι q Ri Cm CM Af Av)*majorant R d n := by
  rw [pressurePath_normalized_eq_source]
  exact sourcePressure_block_bound P D.M D.normal D.normalLower D.normalLower_pos D.normal_lower
    _ _ directions hdir q
    (normalize_orbit_contDiff P g hg _ G.path_orbit)
    (normalize_orbit_contDiff P g hg _ (velocityPath_orbit τ hτ hτT B G))
    Rc Cm CM Ri R Af Av hRc hCm hCM hAf hAv hRi hR hm hM d hf hv n

theorem scalarGradientField_normalized_bound
    (g : C(Icc (0 : ℝ) D.T,ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q (fun a => pathTranslate P a
      (normalize g hg (pressurePath τ hτ hτT B G))) n 0 ≤ A*majorant R d n) (n : ℕ) :
    block standardDirection q (fun a => pathTranslate P a
      (normalize g hg (scalarGradientField τ hτ hτT B G).path)) n 0 ≤
        (3*A)*majorant R (d+1) n :=
  scalarGradientPath_normalized_majorant (pressurePath τ hτ hτT B G)
    (pressurePath_orbit τ hτ hτT B G) g hg q R A d hb n

end EulerTransversePacketJoin
