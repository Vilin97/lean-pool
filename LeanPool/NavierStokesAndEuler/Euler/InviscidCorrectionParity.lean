/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionParity
public import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionUniqueness

@[expose] public section

/-! Odd parity of actual inviscid correction solutions, proved by genuine PDE uniqueness. -/

noncomputable section

namespace EulerInviscidCorrectionParity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionStabilityBudget EulerInviscidCorrectionUniqueness
  EulerVolterraConvolution EulerCylinderReflection EulerSobolevReflection EulerCorrectionParity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The inherited finite Sobolev normed-group instance. -/
local instance inviscidParityGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
  inferInstance
/-- The inherited real finite Sobolev module instance. -/
local instance inviscidParitySpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- Every actual zero-initial inviscid correction is odd under the
source's genuine parity hypotheses on the prescribed fields and coefficients.
The reflected path solves the literal same equation; uniqueness is proved
by the existing metric-energy theorem, not assumed. -/
theorem inviscid_correction_odd {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period q (Icc (0 : ℝ) T)) (B : StabilityBudget period hT D)
    (hG : ∀ t x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ t x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ t i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
      t).coefficient x)
    (hzOdd : ∀ t, oddReflection period (q+1) (D.approximation t) = D.approximation t)
    (hrOdd : ∀ t, oddReflection period q (D.residual t) = D.residual t)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)))
    (hi : u ⟨0,le_rfl,hT⟩ = 0)
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period hq).apply ⟨t,ht.1.le,ht.2.le⟩ (u
          ⟨t,ht.1.le,ht.2.le⟩))) t)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∀ t, oddReflection period (q+1) (u t) = u t := by
  let v := (oddReflection period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  have hv0 : v ⟨0,le_rfl,hT⟩ = 0 := by
    change oddReflection period (q+1) (u ⟨0,le_rfl,hT⟩) = 0
    rw [hi, map_zero]
  have hv : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT v r))
        (value period ((D.coefficients period hq).apply ⟨t,ht.1.le,ht.2.le⟩ (v
          ⟨t,ht.1.le,ht.2.le⟩))) t := by
    intro t ht
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
    have hd := ((reflection period).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hu t
      ht)).neg
    have he := congrArg (value period (q := q))
      (correction_source_oddReflection period hq D τ (hG τ) (hL τ) (hQ τ) (hzOdd τ) (hrOdd τ) (u τ))
    rw [value_oddReflection] at he
    convert! hd using 1
    · funext r
      change value period (oddReflection period (q+1) (u (projIcc 0 T hT r))) =
        -reflection period (value period (u (projIcc 0 T hT r)))
      exact value_oddReflection period _
    · exact he.symm
  have hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction := by
    intro t
    exact oddReflection_divergenceFree period D.κ D.direction (u t) (hud t)
  have he := inviscid_correction_unique period hq T hT D B u v (hi.trans hv0.symm) hu hv hz hud hvd
  intro t
  exact (congrArg (fun f => f t) he).symm

/-- The actual signed coercive correction pressure has odd gradient parity
at every time once the correction parity has been established. -/
theorem inviscid_correction_pressure_odd {q : ℕ} (hq : 6 ≤ q) {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (t : T)
    (hG : ∀ x, (D.metric.coefficient t).coefficient (-x) = (D.metric.coefficient t).coefficient x)
    (hL : ∀ x, (D.linear.coefficient t).coefficient (-x) = (D.linear.coefficient t).coefficient x)
    (hQ : ∀ i x, ((D.quadratic i).coefficient t).coefficient (-x) = -((D.quadratic i).coefficient
      t).coefficient x)
    (hz : oddReflection period (q+1) (D.approximation t) = D.approximation t)
    (hr : oddReflection period q (D.residual t) = D.residual t)
    (u : SobolevSpace period (q+1)) (hu : oddReflection period (q+1) u = u) :
    oddReflection period q (D.pressure period hq t u) = D.pressure period hq t u := by
  have hh := correction_pressure_oddReflection period hq D t hG hL hQ hz hr u
  rwa [hu] at hh

end EulerInviscidCorrectionParity
