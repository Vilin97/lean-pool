/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Stage8EuclideanPhase
public import LeanPool.ParameterFreeGradient.O3.Stage8EuclideanRadius

/-!
# Stage 8: the guarded Euclidean gap

This module proves the vector estimate-sequence invariant for the actual
recursive Phase-A execution and evaluates it at the internally constructed
closest optimizer.
-/

@[expose] public section

namespace O3

/-- The literal recursive potential is bounded by the quadratic prox plus
`A_k f(x)`, using convexity at every actual query. -/
theorem euclideanEstimateFunction_le_model {d : ℕ}
    (P : AdmissibleInstance d 2) {M : ℝ} (_hM : 0 < M) : ∀ k x,
    euclideanEstimateFunction P M k x ≤
      M / 2 * (lpNorm 2 (x - P.x0)) ^ (2 : ℕ) + euclideanA k * P.f x := by
  intro k
  induction k with
  | zero =>
      intro x
      simp [euclideanEstimateFunction]
  | succ k ih =>
      intro x
      let a := euclideanWeight (euclideanA k)
      let observation := euclideanEstimateObservation P M k
      have hfirst := Stage3Anchor.firstOrderConvex_of_coordinateGradient
        P.convex P.gradient_spec observation.point x
      have hlinear : observation.value +
          pairing observation.gradient (x - observation.point) ≤ P.f x := by
        simpa only [observation, euclideanEstimateObservation,
          PairOracle.observe, AdmissibleInstance.oracle] using hfirst
      have ha : 0 ≤ a := (euclideanA_increment_pos k).le
      have hprev := ih x
      rw [euclideanA_succ]
      change euclideanEstimateFunction P M k x + a *
          (observation.value + pairing observation.gradient
            (x - observation.point)) ≤
        M / 2 * lpNorm 2 (x - P.x0) ^ (2 : ℕ) +
          (euclideanA k + a) * P.f x
      nlinarith

/-- One accepted actual step closes with exact cancellation
`a_(k+1)^2=A_(k+1)`. -/
theorem euclideanEstimate_oneStep {d : ℕ}
    (P : AdmissibleInstance d 2) {M : ℝ} (hM : 0 < M) (k : ℕ)
    (hprev : euclideanA k *
        P.f (euclideanEstimateState P M k).accelerated ≤
      euclideanEstimateMinimum P M k)
    (hguard : (euclideanEstimateGuard P M k).Holds) :
    euclideanA (k + 1) *
        P.f (euclideanEstimateState P M (k + 1)).accelerated ≤
      euclideanEstimateMinimum P M (k + 1) := by
  let A := euclideanA k
  let a := euclideanWeight A
  let Aplus := euclideanA (k + 1)
  let xA := (euclideanEstimateState P M k).accelerated
  let z := euclideanEstimateMinimizer P M k
  let y := euclideanEstimateQuery P M k
  let observation := euclideanEstimateObservation P M k
  let g := observation.gradient
  let zNext := euclideanEstimateMinimizer P M (k + 1)
  let xNext := (euclideanEstimateState P M (k + 1)).accelerated
  have hA : 0 ≤ A := euclideanA_nonneg k
  have ha : 0 < a := euclideanA_increment_pos k
  have hAplus : Aplus = A + a := by rfl
  have hAplusPos : 0 < Aplus := by rw [hAplus]; positivity
  have haSq : a ^ 2 = Aplus := by
    exact euclideanWeight_sq_eq_next k
  have hy : y = euclideanBarycenter A a xA z := rfl
  have hxNext : xNext = euclideanBarycenter A a xA zNext := rfl
  have hdisp : xNext - y = (a / Aplus) • (zNext - z) := by
    rw [hy, hxNext, hAplus]
    exact euclideanBarycenter_sub (ne_of_gt hAplusPos) xA z zNext
  have hratio : 0 ≤ a / Aplus := div_nonneg ha.le hAplusPos.le
  have hnorm : lpNorm 2 (xNext - y) =
      (a / Aplus) * lpNorm 2 (zNext - z) := by
    rw [hdisp, Stage2RouteC.lpNorm_smul (by norm_num)]
    rw [abs_of_nonneg hratio]
  have hquad : Aplus * (M / 2 * (lpNorm 2 (xNext - y)) ^ (2 : ℕ)) =
      M / 2 * (lpNorm 2 (zNext - z)) ^ (2 : ℕ) := by
    rw [hnorm]
    field_simp [ne_of_gt hAplusPos]
    nlinarith
  have hlinstep : Aplus * pairing g (xNext - y) =
      a * pairing g (zNext - z) := by
    rw [hdisp, Stage2RouteD.pairing_smul_right]
    field_simp [ne_of_gt hAplusPos]
  have hfirst : P.f y + pairing g (xA - y) ≤ P.f xA := by
    have hf := Stage3Anchor.firstOrderConvex_of_coordinateGradient
      P.convex P.gradient_spec y xA
    simpa only [g, observation, euclideanEstimateObservation,
      PairOracle.observe, AdmissibleInstance.oracle] using hf
  have hbalanceVec : A • (xA - y) + a • (z - y) = 0 := by
    rw [hy]
    apply euclideanBarycenter_balance
    rw [← hAplus]
    exact ne_of_gt hAplusPos
  have hbalance : A * pairing g (xA - y) +
      a * pairing g (z - y) = 0 := by
    have hp := congrArg (fun v : Vec d => pairing g v) hbalanceVec
    simp only [pairing, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hp ⊢
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsplit : pairing g (zNext - z) =
      pairing g (zNext - y) + pairing g (y - z) := by
    unfold pairing
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hantisym : pairing g (y - z) = -pairing g (z - y) := by
    unfold pairing
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hmodel : Aplus * P.f y + a * pairing g (zNext - z) ≤
      A * P.f xA + a * (P.f y + pairing g (zNext - y)) := by
    rw [hAplus]
    rw [hsplit, hantisym]
    nlinarith
  have hguardRaw : P.f xNext ≤ P.f y + pairing g (xNext - y) +
      M / 2 * (lpNorm 2 (xNext - y)) ^ (2 : ℕ) := by
    simpa [euclideanEstimateGuard, GuardCheck.Holds, upperModelGuard,
      xNext, y, observation, g, euclideanEstimateObservation,
      PairOracle.observe, AdmissibleInstance.oracle] using hguard
  have hguardScaled := mul_le_mul_of_nonneg_left hguardRaw hAplusPos.le
  have hupper : Aplus * P.f xNext ≤
      A * P.f xA + a * (P.f y + pairing g (zNext - y)) +
        M / 2 * (lpNorm 2 (zNext - z)) ^ (2 : ℕ) := by
    nlinarith [hmodel, hlinstep, hquad]
  have hstrong : euclideanEstimateFunction P M k z +
      M / 2 * (lpNorm 2 (zNext - z)) ^ (2 : ℕ) ≤
      euclideanEstimateFunction P M k zNext := by
    have hs := euclideanEstimateFunction_strongLower P hM k zNext
    simpa only [z, zNext, euclideanEstimateMinimum] using hs
  have hupdate : euclideanEstimateFunction P M (k + 1) zNext =
      euclideanEstimateFunction P M k zNext +
        a * (P.f y + pairing g (zNext - y)) := by
    rfl
  have hprev' : A * P.f xA ≤ euclideanEstimateFunction P M k z := by
    simpa only [A, xA, z, euclideanEstimateMinimum] using hprev
  change Aplus * P.f xNext ≤ euclideanEstimateFunction P M (k + 1) zNext
  rw [hupdate]
  nlinarith [hprev']

/-- The source vector estimate-sequence invariant on the actual accepted
prefix. -/
theorem euclideanEstimate_potential {d : ℕ}
    (P : AdmissibleInstance d 2) {M : ℝ} (hM : 0 < M) : ∀ m,
    EuclideanEstimateAccepted P M m →
      euclideanA m * P.f (euclideanEstimateState P M m).accelerated ≤
        euclideanEstimateMinimum P M m := by
  intro m
  induction m with
  | zero =>
      intro _
      simp [euclideanEstimateMinimum, euclideanEstimateFunction,
        euclideanEstimateMinimizer,
        Stage8EuclideanMinimizer.euclideanPsiMinimizer]
  | succ k ih =>
      intro haccepted
      have hprev := ih (fun j hj => haccepted j (by omega))
      exact euclideanEstimate_oneStep P hM k hprev (haccepted k (by omega))

/-- Exact frozen carrier for TeX Lemma `lem:euclideangap`.  The optimizer is
proof-side and universally quantified in the conclusion; it is not supplied
to the algorithm or used by its recursion. -/
def EuclideanGapStatement : Prop :=
  ∀ (d : ℕ) (P : AdmissibleInstance d 2) (M D : ℝ) (m : ℕ),
    0 < M → 1 ≤ m → EuclideanEstimateAccepted P M m → P.radius ≤ D →
      euclideanA m * P.f (euclideanEstimateState P M m).accelerated ≤
          euclideanEstimateMinimum P M m ∧
      ∀ xstar, xstar ∈ MinimizerSet P.f →
        P.f (euclideanEstimateState P M m).accelerated - P.f xstar ≤
            M * D ^ 2 / (2 * euclideanA m) ∧
        P.f (euclideanEstimateState P M m).accelerated - P.f xstar ≤
            2 * M * D ^ 2 / ((m : ℝ) + 1) ^ 2

/-- Native closure of the guarded Euclidean gap. -/
theorem euclideanGap : EuclideanGapStatement := by
  intro d P M D m hM hm haccepted hDR
  have hinvariant := euclideanEstimate_potential P hM m haccepted
  refine ⟨hinvariant, ?_⟩
  obtain ⟨xclose, hxclose, hcloseD⟩ :=
    Stage8EuclideanRadius.exists_minimizer_within P hDR
  have hD : 0 ≤ D := le_trans (lpNorm_nonneg 2 (xclose - P.x0)) hcloseD
  have hA : 0 < euclideanA m := euclideanA_pos_of_one_le hm
  have hmodel := euclideanEstimateFunction_le_model P hM m xclose
  have hmin := euclideanEstimateMinimum_le_function P hM m xclose
  have heval : euclideanEstimateMinimum P M m ≤
      M / 2 * D ^ 2 + euclideanA m * P.f xclose := by
    have hsq : (lpNorm 2 (xclose - P.x0)) ^ (2 : ℕ) ≤ D ^ 2 := by
      nlinarith [lpNorm_nonneg 2 (xclose - P.x0)]
    exact hmin.trans (hmodel.trans (by nlinarith))
  have hgapClose :
      P.f (euclideanEstimateState P M m).accelerated - P.f xclose ≤
        M * D ^ 2 / (2 * euclideanA m) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hA)]
    nlinarith
  intro xstar hxstar
  have hopt : P.f xstar = P.f xclose := by
    exact le_antisymm (hxstar xclose) (hxclose xstar)
  have hfirst :
      P.f (euclideanEstimateState P M m).accelerated - P.f xstar ≤
        M * D ^ 2 / (2 * euclideanA m) := by
    simpa only [hopt] using hgapClose
  refine ⟨hfirst, ?_⟩
  exact euclideanGap_scalar M D
    (P.f (euclideanEstimateState P M m).accelerated - P.f xstar)
    (euclideanA m) m hM hD hm (euclideanA_quadratic_lower hm) hfirst

end O3
