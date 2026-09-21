/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage8EuclideanWeights
import LeanPool.ParameterFreeGradient.O3.Stage8EuclideanMinimizer
import LeanPool.ParameterFreeGradient.O3.Stage3Anchor
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
# Stage 8: the actual guarded Euclidean estimate sequence

The state stores only recursively computed vector data.  The estimate
minimizer, query, two oracle observations, literal potential, and guard are
deterministic definitions, while their correctness properties are theorems.
-/

namespace O3

noncomputable def euclideanBarycenter {d : ℕ} (A a : ℝ)
    (x z : Vec d) : Vec d :=
  (A + a)⁻¹ • (A • x + a • z)

structure EuclideanEstimateState (d : ℕ) where
  accelerated : Vec d
  cumulativeGradient : Vec d

mutual
  noncomputable def euclideanEstimateState {d : ℕ}
      (P : AdmissibleInstance d 2) (M : ℝ) : ℕ → EuclideanEstimateState d
    | 0 => ⟨P.x0, 0⟩
    | k + 1 =>
        let A := euclideanA k
        let a := euclideanWeight A
        let state := euclideanEstimateState P M k
        let z := Stage8EuclideanMinimizer.euclideanPsiMinimizer M P.x0
          state.cumulativeGradient
        let y := euclideanBarycenter A a state.accelerated z
        let observation := P.oracle.observe y
        let sNext := state.cumulativeGradient + a • observation.gradient
        let zNext := Stage8EuclideanMinimizer.euclideanPsiMinimizer M P.x0 sNext
        ⟨euclideanBarycenter A a state.accelerated zNext, sNext⟩
end

noncomputable def euclideanEstimateMinimizer {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) : Vec d :=
  Stage8EuclideanMinimizer.euclideanPsiMinimizer M P.x0
    (euclideanEstimateState P M k).cumulativeGradient

noncomputable def euclideanEstimateQuery {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) : Vec d :=
  euclideanBarycenter (euclideanA k) (euclideanWeight (euclideanA k))
    (euclideanEstimateState P M k).accelerated
    (euclideanEstimateMinimizer P M k)

noncomputable def euclideanEstimateObservation {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) : Observation d :=
  P.oracle.observe (euclideanEstimateQuery P M k)

noncomputable def euclideanEstimateConstant {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      let a := euclideanWeight (euclideanA k)
      let observation := euclideanEstimateObservation P M k
      euclideanEstimateConstant P M k +
        a * (observation.value +
          pairing observation.gradient (P.x0 - observation.point))

/-- The literal recursively accumulated source potential. -/
noncomputable def euclideanEstimateFunction {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) : ℕ → Vec d → ℝ
  | 0 => fun x => M / 2 * (lpNorm 2 (x - P.x0)) ^ (2 : ℕ)
  | k + 1 => fun x =>
      let a := euclideanWeight (euclideanA k)
      let observation := euclideanEstimateObservation P M k
      euclideanEstimateFunction P M k x +
        a * (observation.value +
          pairing observation.gradient (x - observation.point))

noncomputable def euclideanEstimateMinimum {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) : ℝ :=
  euclideanEstimateFunction P M k (euclideanEstimateMinimizer P M k)

noncomputable def euclideanEstimateGuard {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) : GuardCheck :=
  let atY := euclideanEstimateObservation P M k
  let xNext := (euclideanEstimateState P M (k + 1)).accelerated
  let atX := P.oracle.observe xNext
  upperModelGuard atY.value atX.value
    (pairing atY.gradient (xNext - atY.point))
    ((lpNorm 2 (xNext - atY.point)) ^ (2 : ℕ)) M

def EuclideanEstimateAccepted {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (m : ℕ) : Prop :=
  ∀ k, k < m → (euclideanEstimateGuard P M k).Holds

@[simp] theorem euclideanEstimateState_zero {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) :
    euclideanEstimateState P M 0 = ⟨P.x0, 0⟩ := rfl

theorem euclideanEstimateState_succ_cumulative {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) :
    (euclideanEstimateState P M (k + 1)).cumulativeGradient =
      (euclideanEstimateState P M k).cumulativeGradient +
        euclideanWeight (euclideanA k) •
          (euclideanEstimateObservation P M k).gradient := by
  rfl

theorem euclideanEstimateState_succ_accelerated {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) :
    (euclideanEstimateState P M (k + 1)).accelerated =
      euclideanBarycenter (euclideanA k) (euclideanWeight (euclideanA k))
        (euclideanEstimateState P M k).accelerated
        (euclideanEstimateMinimizer P M (k + 1)) := by
  rfl

/-- Exact canonical form of the literal recursive `Psi_k`. -/
theorem euclideanEstimateFunction_eq_canonical {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) : ∀ k x,
    euclideanEstimateFunction P M k x =
      Stage8EuclideanMinimizer.euclideanPsi M P.x0
        (euclideanEstimateState P M k).cumulativeGradient
        (euclideanEstimateConstant P M k) x := by
  intro k
  induction k with
  | zero =>
      intro x
      simp [euclideanEstimateFunction, euclideanEstimateConstant,
        Stage8EuclideanMinimizer.euclideanPsi, pairing]
  | succ k ih =>
      intro x
      simp only [euclideanEstimateFunction]
      rw [ih x]
      rw [Stage8EuclideanMinimizer.euclideanPsi_add_linearization]
      simp only [euclideanEstimateConstant,
        euclideanEstimateState_succ_cumulative]

theorem euclideanEstimateFunction_strongLower {d : ℕ}
    (P : AdmissibleInstance d 2) {M : ℝ} (hM : 0 < M)
    (k : ℕ) (x : Vec d) :
    euclideanEstimateFunction P M k x ≥
      euclideanEstimateMinimum P M k + M / 2 *
        (lpNorm 2 (x - euclideanEstimateMinimizer P M k)) ^ (2 : ℕ) := by
  rw [euclideanEstimateFunction_eq_canonical P M k x]
  change _ ≥ euclideanEstimateFunction P M k
      (euclideanEstimateMinimizer P M k) + _
  rw [euclideanEstimateFunction_eq_canonical P M k
    (euclideanEstimateMinimizer P M k)]
  exact Stage8EuclideanMinimizer.euclideanPsi_strongLower_at_minimizer
    hM _ _ _ x

theorem euclideanEstimateMinimum_le_function {d : ℕ}
    (P : AdmissibleInstance d 2) {M : ℝ} (hM : 0 < M)
    (k : ℕ) (x : Vec d) :
    euclideanEstimateMinimum P M k ≤ euclideanEstimateFunction P M k x := by
  have h := euclideanEstimateFunction_strongLower P hM k x
  have hterm : 0 ≤ M / 2 *
      (lpNorm 2 (x - euclideanEstimateMinimizer P M k)) ^ (2 : ℕ) :=
    mul_nonneg (div_nonneg hM.le (by norm_num)) (sq_nonneg _)
  linarith

/-- The actual two barycenters have the source displacement. -/
theorem euclideanBarycenter_sub {d : ℕ} {A a : ℝ}
    (hAa : A + a ≠ 0) (x z zNext : Vec d) :
    euclideanBarycenter A a x zNext - euclideanBarycenter A a x z =
      (a / (A + a)) • (zNext - z) := by
  funext i
  simp only [euclideanBarycenter, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul, div_eq_mul_inv]
  field_simp [hAa]
  ring

/-- The old barycenter identity needed to combine convexity and the model. -/
theorem euclideanBarycenter_balance {d : ℕ} {A a : ℝ}
    (hAa : A + a ≠ 0) (x z : Vec d) :
    A • (x - euclideanBarycenter A a x z) +
      a • (z - euclideanBarycenter A a x z) = 0 := by
  funext i
  simp only [euclideanBarycenter, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply]
  field_simp [hAa]
  ring

end O3
