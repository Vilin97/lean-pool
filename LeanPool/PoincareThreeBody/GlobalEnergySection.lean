/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.ParameterDomainTopology
import LeanPool.PoincareThreeBody.Analytic
import LeanPool.PoincareThreeBody.ParameterizedAnalyticDivision
import LeanPool.PoincareThreeBody.DelaunaySection

/-!
# A global analytic section of the mass-zero energy map

The rotating Kepler Hamiltonian admits a collision-free analytic phase-space section over every
real energy.  This supplies a canonical globally analytic one-variable representative for the
mass-zero coefficient of any jointly analytic family.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- A small positive radius chosen so that the remaining kinetic radicand is positive for every
real energy. -/
noncomputable def globalEnergyRadius (energy : ℝ) : ℝ :=
  1 / (energy ^ 2 + 2)

theorem globalEnergyRadius_pos (energy : ℝ) : 0 < globalEnergyRadius energy := by
  unfold globalEnergyRadius
  positivity

theorem one_div_globalEnergyRadius (energy : ℝ) :
    1 / globalEnergyRadius energy = energy ^ 2 + 2 := by
  unfold globalEnergyRadius
  field_simp

/-- The squared shifted momentum needed to realize the prescribed energy. -/
noncomputable def globalEnergyRadicand (energy : ℝ) : ℝ :=
  2 * (energy + globalEnergyRadius energy ^ 2 / 2 +
    1 / globalEnergyRadius energy)

theorem globalEnergyRadicand_pos (energy : ℝ) :
    0 < globalEnergyRadicand energy := by
  rw [globalEnergyRadicand, one_div_globalEnergyRadius]
  have hsquare : 0 ≤ (energy + 1 / 2 : ℝ) ^ 2 := sq_nonneg _
  have hradius : 0 ≤ globalEnergyRadius energy ^ 2 := sq_nonneg _
  nlinarith

/-- Positive shifted momentum along the global section. -/
noncomputable def globalEnergySpeed (energy : ℝ) : ℝ :=
  Real.sqrt (globalEnergyRadicand energy)

theorem globalEnergySpeed_sq (energy : ℝ) :
    globalEnergySpeed energy ^ 2 = globalEnergyRadicand energy := by
  exact Real.sq_sqrt (globalEnergyRadicand_pos energy).le

/-- An explicit collision-free phase point with mass-zero Hamiltonian equal to `energy`. -/
noncomputable def globalEnergySection (energy : ℝ) : PhaseSpace :=
  ![0, globalEnergyRadius energy,
    -globalEnergySpeed energy - globalEnergyRadius energy, 0]

theorem globalEnergySection_collisionFree (energy : ℝ) :
    (0, globalEnergySection energy) ∈ collisionFree := by
  constructor
  · simp only [firstPrimaryDistanceSq, globalEnergySection,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    positivity
  · simp only [secondPrimaryDistanceSq, globalEnergySection,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    intro hzero
    norm_num at hzero
    exact (globalEnergyRadius_pos energy).ne' hzero

/-- The explicit section is a right inverse of the mass-zero Hamiltonian. -/
theorem hamiltonian_zero_globalEnergySection (energy : ℝ) :
    hamiltonian 0 (globalEnergySection energy) = energy := by
  let radius := globalEnergyRadius energy
  let speed := globalEnergySpeed energy
  have hradius : 0 < radius := globalEnergyRadius_pos energy
  have hinverse : 1 / radius = energy ^ 2 + 2 :=
    one_div_globalEnergyRadius energy
  have hspeed : speed ^ 2 =
      2 * (energy + radius ^ 2 / 2 + 1 / radius) := by
    exact globalEnergySpeed_sq energy
  have hsqrtRadius : Real.sqrt (radius ^ 2) = radius := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hradius]
  unfold hamiltonian potential globalEnergySection
  change ((-speed - radius) ^ 2 + 0 ^ 2) / 2 +
      (-speed - radius) * radius - 0 * 0 -
        (0 / Real.sqrt ((0 - 1 + 0) ^ 2 + radius ^ 2) +
          (1 - 0) / Real.sqrt ((0 + 0) ^ 2 + radius ^ 2)) = energy
  norm_num only [zero_pow, zero_add, zero_mul, one_mul, sub_zero, zero_div]
  rw [hsqrtRadius]
  rw [hinverse] at hspeed ⊢
  nlinarith

@[simp] theorem globalEnergyRadius_neg_two :
    globalEnergyRadius (-2) = (1 / 6 : ℝ) := by
  norm_num [globalEnergyRadius]

@[simp] theorem globalEnergyRadicand_neg_two :
    globalEnergyRadicand (-2) = (289 / 36 : ℝ) := by
  norm_num [globalEnergyRadicand, globalEnergyRadius]

@[simp] theorem globalEnergySpeed_neg_two :
    globalEnergySpeed (-2) = (17 / 6 : ℝ) := by
  rw [globalEnergySpeed, globalEnergyRadicand_neg_two]
  have hnonneg : (0 : ℝ) ≤ 17 / 6 := by norm_num
  rw [show (289 / 36 : ℝ) = (17 / 6) ^ 2 by norm_num,
    Real.sqrt_sq hnonneg]

/-- A rational phase-space anchor for the global section. -/
theorem globalEnergySection_neg_two :
    globalEnergySection (-2) = ![(0 : ℝ), 1 / 6, -3, 0] := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [globalEnergySection]

theorem cartesianKeplerEnergy_globalEnergySection_neg_two :
    cartesianKeplerEnergy (globalEnergySection (-2)) = (-3 / 2 : ℝ) := by
  rw [globalEnergySection_neg_two]
  simp only [cartesianKeplerEnergy, Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num
  rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem cartesianAngularAction_globalEnergySection_neg_two :
    cartesianAngularAction (globalEnergySection (-2)) = (1 / 2 : ℝ) := by
  rw [globalEnergySection_neg_two]
  simp only [cartesianAngularAction, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num

theorem cartesianDelaunayActions_globalEnergySection_neg_two :
    cartesianDelaunayActions (globalEnergySection (-2)) =
      ![1 / Real.sqrt 3, (1 / 2 : ℝ)] := by
  funext coordinate
  fin_cases coordinate
  · simp only [cartesianDelaunayActions, cartesianFirstAction,
      cartesianKeplerEnergy_globalEnergySection_neg_two]
    norm_num
  · change cartesianAngularAction (globalEnergySection (-2)) = (1 / 2 : ℝ)
    exact cartesianAngularAction_globalEnergySection_neg_two

theorem globalEnergySection_neg_two_action_prograde :
    cartesianDelaunayActions (globalEnergySection (-2)) ∈
      ProgradeEllipticActions := by
  rw [cartesianDelaunayActions_globalEnergySection_neg_two]
  constructor
  · norm_num
  · have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [show (![1 / Real.sqrt 3, (1 / 2 : ℝ)] : ActionSpace) 1 = 1 / 2 by rfl,
      show (![1 / Real.sqrt 3, (1 / 2 : ℝ)] : ActionSpace) 0 =
        1 / Real.sqrt 3 by rfl]
    apply (lt_div_iff₀ hsqrtPos).2
    nlinarith

theorem eccentricityFromActions_globalEnergySection_neg_two :
    eccentricityFromActions
      (cartesianDelaunayActions (globalEnergySection (-2))) = (1 / 2 : ℝ) := by
  rw [cartesianDelaunayActions_globalEnergySection_neg_two]
  unfold eccentricityFromActions
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hratio :
      ((![1 / Real.sqrt 3, (1 / 2 : ℝ)] : ActionSpace) 1 /
        (![1 / Real.sqrt 3, (1 / 2 : ℝ)] : ActionSpace) 0) ^ 2 = 3 / 4 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsqrtPos.ne']
    nlinarith
  rw [hratio]
  norm_num
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem globalEnergySection_neg_two_action_apoapsis :
    let action := cartesianDelaunayActions (globalEnergySection (-2))
    action 0 ^ 2 * (1 + eccentricityFromActions action) < 1 := by
  dsimp only
  rw [eccentricityFromActions_globalEnergySection_neg_two,
    cartesianDelaunayActions_globalEnergySection_neg_two]
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [Matrix.cons_val_zero]
  field_simp [hsqrtPos.ne']
  nlinarith

/-- The rational anchor is the periapsis point of the explicit interior Delaunay ellipse with
`L = 1 / √3`, eccentricity `1/2`, and apsidal angle `π/2`. -/
theorem globalEnergySection_neg_two_eq_liftedDelaunayPhasePoint :
    globalEnergySection (-2) =
      liftedDelaunayPhasePoint (1 / Real.sqrt 3) (1 / 2) 0 (Real.pi / 2) := by
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hanomaly : eccentricAnomaly (1 / 2 : ℝ) 0 = 0 :=
    eccentricAnomaly_zero (by norm_num) (by norm_num)
  rw [globalEnergySection_neg_two]
  unfold liftedDelaunayPhasePoint liftedDelaunayPosition liftedDelaunayMomentum
    liftedDelaunayEccentricAnomaly positionMomentumPhasePoint
  rw [hanomaly]
  funext coordinate
  fin_cases coordinate <;>
    simp [positionInRotatingFrame, inertialEllipsePosition,
      inertialEllipseVelocity]
  all_goals norm_num
  rw [show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  field_simp [hsqrtPos.ne']
  nlinarith

theorem analyticAt_globalEnergyRadius (energy : ℝ) :
    AnalyticAt ℝ globalEnergyRadius energy := by
  unfold globalEnergyRadius
  exact analyticAt_const.div ((analyticAt_id.pow 2).add analyticAt_const)
    (by positivity)

theorem analyticAt_globalEnergyRadicand (energy : ℝ) :
    AnalyticAt ℝ globalEnergyRadicand energy := by
  unfold globalEnergyRadicand
  have hradius := analyticAt_globalEnergyRadius energy
  have hone : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) energy := analyticAt_const
  have htwo : AnalyticAt ℝ (fun _ : ℝ ↦ (2 : ℝ)) energy := analyticAt_const
  apply (htwo.mul
    (analyticAt_id.add (((hradius.pow 2).div_const (c := (2 : ℝ))).add
      (hone.div hradius (globalEnergyRadius_pos energy).ne')))).congr
  filter_upwards [] with candidate
  simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
  ring

theorem analyticAt_globalEnergySpeed (energy : ℝ) :
    AnalyticAt ℝ globalEnergySpeed energy := by
  unfold globalEnergySpeed
  exact (analyticAt_sqrt_of_pos (globalEnergyRadicand_pos energy)).comp
    (analyticAt_globalEnergyRadicand energy)

theorem analyticAt_globalEnergySection (energy : ℝ) :
    AnalyticAt ℝ globalEnergySection energy := by
  apply AnalyticAt.pi
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_const
  · exact analyticAt_globalEnergyRadius energy
  · exact (analyticAt_globalEnergySpeed energy).neg.sub
      (analyticAt_globalEnergyRadius energy)
  · exact analyticAt_const

/-- Evaluate the mass-zero coefficient along the global energy section. -/
noncomputable def globalEnergyCoefficient
    (F : ℝ → PhaseSpace → ℝ) (energy : ℝ) : ℝ :=
  F 0 (globalEnergySection energy)

/-- At the rational anchor, the global energy representative agrees with the Delaunay action
representative used by the classical Poincaré-set obstruction. -/
theorem IsFirstIntegralFamily.globalEnergyCoefficient_neg_two_eq_leadingActionCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F) :
    globalEnergyCoefficient F (-2) =
      leadingActionCoefficient F
        ![1 / Real.sqrt 3,
          angularActionFromEccentricity (1 / Real.sqrt 3) (1 / 2)] := by
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hfirstAction : 0 < (1 / Real.sqrt 3 : ℝ) := one_div_pos.mpr hsqrtPos
  have hapoapsis :
      (1 / Real.sqrt 3 : ℝ) ^ 2 * (1 + (1 / 2 : ℝ)) < 1 := by
    field_simp [hsqrtPos.ne']
    nlinarith
  have hvalue :=
    IsFirstIntegralFamily.leadingActionCoefficient_eq_liftedDelaunayPhasePoint
      hδ hanalytic hfirstIntegral hfirstAction (by norm_num) (by norm_num)
      hapoapsis ((0 : ℝ), Real.pi / 2)
  unfold globalEnergyCoefficient
  rw [globalEnergySection_neg_two_eq_liftedDelaunayPhasePoint]
  exact hvalue.symm

/-- Energies near the rational anchor remain in the same interior prograde Delaunay chart. -/
theorem eventually_globalEnergySection_interiorPrograde :
    ∀ᶠ energy in nhds (-2 : ℝ),
      let action := cartesianDelaunayActions (globalEnergySection energy)
      action ∈ ProgradeEllipticActions ∧
        action 0 ^ 2 * (1 + eccentricityFromActions action) < 1 := by
  let actionCurve : ℝ → ActionSpace := fun energy ↦
    cartesianDelaunayActions (globalEnergySection energy)
  have hposition :
      (globalEnergySection (-2)) 0 ^ 2 + (globalEnergySection (-2)) 1 ^ 2 ≠ 0 := by
    rw [globalEnergySection_neg_two]
    norm_num
  have henergy : cartesianKeplerEnergy (globalEnergySection (-2)) < 0 := by
    rw [cartesianKeplerEnergy_globalEnergySection_neg_two]
    norm_num
  have hactionAnalytic : AnalyticAt ℝ actionCurve (-2) := by
    exact (analyticAt_cartesianDelaunayActions hposition henergy).comp
      (f := globalEnergySection) (analyticAt_globalEnergySection (-2))
  have hbaseAction : actionCurve (-2) ∈ ProgradeEllipticActions := by
    exact globalEnergySection_neg_two_action_prograde
  have hprograde : ∀ᶠ energy in nhds (-2 : ℝ),
      actionCurve energy ∈ ProgradeEllipticActions :=
    hactionAnalytic.continuousAt.eventually
      (isOpen_progradeEllipticActions.mem_nhds hbaseAction)
  have hcoordinate : AnalyticAt ℝ
      (fun action : ActionSpace ↦ action 0) (actionCurve (-2)) :=
    (ContinuousLinearMap.proj 0 : ActionSpace →L[ℝ] ℝ).analyticAt _
  have heccentricity : AnalyticAt ℝ eccentricityFromActions (actionCurve (-2)) :=
    analyticAt_eccentricityFromActions hbaseAction
  have hapoapsisContinuous : ContinuousAt
      (fun energy ↦ (actionCurve energy) 0 ^ 2 *
        (1 + eccentricityFromActions (actionCurve energy))) (-2) := by
    exact (((hcoordinate.pow 2).mul
      (analyticAt_const.add heccentricity)).comp hactionAnalytic).continuousAt
  have hbaseApoapsis :
      (actionCurve (-2)) 0 ^ 2 *
        (1 + eccentricityFromActions (actionCurve (-2))) < 1 := by
    exact globalEnergySection_neg_two_action_apoapsis
  have hapoapsis : ∀ᶠ energy in nhds (-2 : ℝ),
      (actionCurve energy) 0 ^ 2 *
        (1 + eccentricityFromActions (actionCurve energy)) < 1 :=
    hapoapsisContinuous.eventually_lt continuousAt_const hbaseApoapsis
  filter_upwards [hprograde, hapoapsis] with energy haction hapo
  exact ⟨haction, hapo⟩

/-- Joint analyticity makes the global energy representative analytic at every real energy. -/
theorem IsJointlyAnalytic.analyticAt_globalEnergyCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F) (energy : ℝ) :
    AnalyticAt ℝ (globalEnergyCoefficient F) energy := by
  have hdomain : (0, globalEnergySection energy) ∈ parameterDomain δ :=
    ⟨by simpa using hδ, globalEnergySection_collisionFree energy⟩
  have hcurve : AnalyticAt ℝ
      (fun candidateEnergy ↦ ((0 : ℝ), globalEnergySection candidateEnergy)) energy :=
    analyticAt_const.prod (analyticAt_globalEnergySection energy)
  exact (hanalytic (0, globalEnergySection energy) hdomain).comp
    (f := fun candidateEnergy ↦ ((0 : ℝ), globalEnergySection candidateEnergy)) hcurve

/-- Intrinsic form of the classical zeroth-coefficient conclusion: the coefficient at a phase
point equals its value on the canonical section at the same Kepler energy. -/
def GlobalZerothCoefficientFactorization : Prop :=
  ∀ {δ : ℝ} {F : ℝ → PhaseSpace → ℝ},
    0 < δ → IsJointlyAnalytic δ F → IsFirstIntegralFamily δ F →
      ∀ state, (0, state) ∈ collisionFree →
        F 0 state = globalEnergyCoefficient F (hamiltonian 0 state)

/-- The canonical-section formulation is exactly equivalent to the energy-function formulation
used by the normalization induction. -/
theorem globalZerothCoefficientFactorization_iff_classicalPrinciple :
    GlobalZerothCoefficientFactorization ↔ ClassicalZerothCoefficientPrinciple := by
  constructor
  · intro hfactor δ F hδ hanalytic hfirstIntegral
    refine ⟨globalEnergyCoefficient F,
      IsJointlyAnalytic.analyticAt_globalEnergyCoefficient hδ hanalytic,
      hfactor hδ hanalytic hfirstIntegral⟩
  · intro hprinciple δ F hδ hanalytic hfirstIntegral state hcollision
    obtain ⟨energyFunction, _henergy, hcancel⟩ :=
      hprinciple hδ hanalytic hfirstIntegral
    have hsection (energy : ℝ) :
        globalEnergyCoefficient F energy = energyFunction energy := by
      unfold globalEnergyCoefficient
      rw [hcancel (globalEnergySection energy)
        (globalEnergySection_collisionFree energy),
        hamiltonian_zero_globalEnergySection]
    rw [hcancel state hcollision, hsection]

/-- With analytic mass division now proved, the exact challenge is reduced to the intrinsic
classical factorization statement alone. -/
theorem nonintegrability_of_globalZerothCoefficientFactorization
    (hfactor : GlobalZerothCoefficientFactorization) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F := by
  apply nonintegrability_of_zerothCoefficient_of_massDivision
  · exact globalZerothCoefficientFactorization_iff_classicalPrinciple.mp hfactor
  · exact jointAnalyticMassDivisionPrinciple

end LeanPool.PoincareThreeBody
