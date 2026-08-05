/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanPool.PoincareThreeBody.DenseResonantObstruction
import LeanPool.PoincareThreeBody.PoincareSet

/-!
# The classical obstruction for the leading coefficient

This file packages the density argument on the full prograde elliptic action region and pulls
the resulting dependence back to physical phase space.  The remaining celestial-mechanics input
is isolated as `ClassicalDisturbingNondegeneracy`: the resonant disturbing average must be
nonconstant at every rational resonance under consideration.
-/

namespace LeanPool.PoincareThreeBody

open Challenge.PoincareThreeBody

/-- The classical nondegeneracy input for Poincaré's set: every interior positive rational
resonance has a nonconstant disturbing average as the relative apsidal orientation varies. -/
def ClassicalDisturbingNondegeneracy : Prop :=
  ∀ {eccentricity : ℝ}, 0 < eccentricity → eccentricity < 1 →
    ∀ {p q : ℕ}, 0 < p → 0 < q →
      resonantFirstAction p q ^ 2 * (1 + eccentricity) < 1 →
      ∃ orientation,
        deriv (resonantDisturbingAverage p q eccentricity) orientation ≠ 0

/-- Pulling two dependent Euclidean action covectors back along any linear map cannot make them
linearly independent. -/
theorem not_linearIndependent_actionCovector_comp_of_wedge_eq_zero
    {u v : ActionSpace} (actionDerivative : PhaseSpace →L[ℝ] ActionSpace)
    (hwedge : wedge u v = 0) :
    ¬LinearIndependent ℝ
      ![(actionCovector u).comp actionDerivative,
        (actionCovector v).comp actionDerivative] := by
  let pullback : ActionSpace →ₗ[ℝ] (PhaseSpace →L[ℝ] ℝ) :=
    { toFun := fun vector ↦ (actionCovector vector).comp actionDerivative
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro direction
        simp only [add_apply, ContinuousLinearMap.comp_apply,
          actionCovector_apply, dot_eq, Pi.add_apply]
        ring
      map_smul' := by
        intro scalar vector
        apply ContinuousLinearMap.ext
        intro direction
        simp only [smul_apply, ContinuousLinearMap.comp_apply,
          actionCovector_apply, dot_eq, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  intro hpulled
  have horiginal : LinearIndependent ℝ ![u, v] := by
    apply LinearIndependent.of_comp pullback
    convert hpulled using 1
    funext coordinate
    fin_cases coordinate <;> rfl
  exact not_linearIndependent_of_wedge_eq_zero hwedge horiginal

/-- Poincaré's dense resonant set forces the leading candidate differential to be dependent on
the Kepler frequency throughout the full interior prograde elliptic action region. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hnondegenerate : ClassicalDisturbingNondegeneracy)
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1) :
    wedge (delaunayFrequency (action 0))
      (leadingActionDifferential F action) = 0 := by
  let eccentricity := eccentricityFromActions action
  let interiorAction : InteriorPositiveAction eccentricity :=
    ⟨⟨action 0, haction.1.trans haction.2⟩, hapoapsis⟩
  have heccentricity : 0 < eccentricity := eccentricityFromActions_pos haction
  have heccentricityOne : eccentricity < 1 := eccentricityFromActions_lt_one haction
  have hfixed :=
    IsFirstIntegralFamily.wedge_leadingActionDifferentialAtEccentricity_eq_zero
      hδ hanalytic hfirstIntegral heccentricity heccentricityOne
      (fun hp hq hinside ↦
        hnondegenerate heccentricity heccentricityOne hp hq hinside)
      interiorAction
  have hrecover : fixedEccentricityAction eccentricity (action 0) = action := by
    exact actions_from_eccentricityFromActions haction
  change wedge (delaunayFrequency (action 0))
    (leadingActionDifferential F
      (fixedEccentricityAction eccentricity (action 0))) = 0 at hfixed
  rwa [hrecover] at hfixed

/-- Natural classical form of the full action obstruction, assuming only density of the
Poincaré set rather than nonvanishing at every rational resonance. -/
theorem IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_poincareSet
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet)
    {action : ActionSpace} (haction : action ∈ ProgradeEllipticActions)
    (hapoapsis : action 0 ^ 2 * (1 + eccentricityFromActions action) < 1) :
    wedge (delaunayFrequency (action 0))
      (leadingActionDifferential F action) = 0 := by
  exact IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_densePoincareSet
    hδ hanalytic hfirstIntegral hdense ⟨action, haction, hapoapsis⟩

/-- Physical form of the leading-coefficient obstruction on every noncircular lifted ellipse:
the phase differentials of the zero-mass Hamiltonian and leading candidate are dependent. -/
theorem IsFirstIntegralFamily.mass_zero_differentials_dependent_on_liftedEllipse
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    (hdense : HasDenseClassicalPoincareSet)
    {firstAction eccentricity meanAnomaly periapsisAngle : ℝ}
    (hfirstAction : 0 < firstAction)
    (heccentricity : 0 < eccentricity) (heccentricityOne : eccentricity < 1)
    (hapoapsis : firstAction ^ 2 * (1 + eccentricity) < 1) :
    let state := liftedDelaunayPhasePoint
      firstAction eccentricity meanAnomaly periapsisAngle
    ¬LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian 0) state, fderiv ℝ (F 0) state] := by
  let state := liftedDelaunayPhasePoint
    firstAction eccentricity meanAnomaly periapsisAngle
  let action : ActionSpace :=
    ![firstAction, angularActionFromEccentricity firstAction eccentricity]
  have haction : action ∈ ProgradeEllipticActions :=
    ⟨angularActionFromEccentricity_pos hfirstAction heccentricity heccentricityOne,
      angularActionFromEccentricity_lt_firstAction hfirstAction heccentricity⟩
  have heRecover : eccentricityFromActions action = eccentricity :=
    eccentricityFromActions_angularActionFromEccentricity hfirstAction
      heccentricity.le heccentricityOne
  have hactionApoapsis :
      action 0 ^ 2 * (1 + eccentricityFromActions action) < 1 := by
    simpa only [action, Matrix.cons_val_zero, heRecover] using hapoapsis
  have hwedge : wedge (delaunayFrequency (action 0))
      (leadingActionDifferential F action) = 0 :=
    IsFirstIntegralFamily.wedge_leadingActionDifferential_eq_zero_of_poincareSet
      hδ hanalytic hfirstIntegral hdense haction hactionApoapsis
  have hpulled := not_linearIndependent_actionCovector_comp_of_wedge_eq_zero
    (fderiv ℝ cartesianDelaunayActions state) hwedge
  have hcollision : (0, state) ∈ collisionFree :=
    liftedDelaunayPhasePoint_collisionFree_mass_zero hfirstAction.ne'
      heccentricity.le heccentricityOne hapoapsis
  have hposition : state 0 ^ 2 + state 1 ^ 2 ≠ 0 := by
    simpa [secondPrimaryDistanceSq] using hcollision.2
  have henergyIdentity : cartesianKeplerEnergy state =
      -1 / (2 * firstAction ^ 2) :=
    cartesianKeplerEnergy_liftedDelaunayPhasePoint hfirstAction.ne'
      heccentricity.le heccentricityOne
  have henergy : cartesianKeplerEnergy state < 0 := by
    rw [henergyIdentity]
    exact div_neg_of_neg_of_pos (by norm_num)
      (mul_pos (by norm_num) (sq_pos_of_pos hfirstAction))
  have hactions : cartesianDelaunayActions state = action :=
    cartesianDelaunayActions_liftedDelaunayPhasePoint hfirstAction
      heccentricity.le heccentricityOne
  have hhamiltonian := fderiv_hamiltonian_zero_eq_frequencyCovector_comp_actions
    hposition henergy
  have hcandidate :=
    IsFirstIntegralFamily.fderiv_mass_zero_eq_actionDifferential_comp_actions
      (meanAnomaly := meanAnomaly) (periapsisAngle := periapsisAngle)
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
  dsimp only [state, action] at hactions hhamiltonian hcandidate hpulled ⊢
  rw [hactions] at hhamiltonian
  rw [hhamiltonian, hcandidate]
  exact hpulled

end LeanPool.PoincareThreeBody
