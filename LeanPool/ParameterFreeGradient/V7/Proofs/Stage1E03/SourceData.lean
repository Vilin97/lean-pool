/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Ledger

/-!
The literal Euclidean trajectories packaged with their dynamics and exact traces.
-/

open scoped BigOperators

namespace V7
namespace Stage1E03

/-- The literal recursive estimate state driven by an arbitrary value-gradient oracle. -/
noncomputable def sourceEstimateState (oracle : PairOracle d) (M : ℝ)
    (x0 : Point d) : ℕ → O3.EuclideanEstimateState d
  | 0 => ⟨x0, 0⟩
  | k + 1 =>
      nextEstimateState M x0 k (sourceEstimateState oracle M x0 k)
        (oracle.observe (estimateQuery M x0 k (sourceEstimateState oracle M x0 k)))

/-- The quadratic potential minimizer associated with the source estimate state. -/
noncomputable def sourceEstimateMinimizer (oracle : PairOracle d) (M : ℝ)
    (x0 : Point d) (k : ℕ) : Point d :=
  O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer M x0
    (sourceEstimateState oracle M x0 k).cumulativeGradient

/-- The source estimate-weight increment, extended by zero at index zero. -/
noncomputable def sourcePhaseAWeight : ℕ → ℝ
  | 0 => 0
  | k + 1 => O3.euclideanWeight (O3.euclideanA k)

/-- The literal source estimate execution packaged as Euclidean gap-phase data. -/
noncomputable def sourcePhaseAData (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (m : ℕ) : EuclideanGapData d m where
  x0 := x0
  inst := inst
  M := M
  D := D
  A := O3.euclideanA
  a := sourcePhaseAWeight
  x := fun k => (sourceEstimateState inst.oracle M x0 k).accelerated
  w := fun k => sourceEstimateMinimizer inst.oracle M x0 k
  y := fun k => estimateQuery M x0 k (sourceEstimateState inst.oracle M x0 k)
  trace := (List.range m).flatMap fun k =>
    [inst.oracle.observe (estimateQuery M x0 k
      (sourceEstimateState inst.oracle M x0 k)),
     inst.oracle.observe (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated]

/-- The literal source OGM-G execution packaged as finite phase data. -/
noncomputable def sourcePhaseBData (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) (U : Point d) : OGMGData d n :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M U
  { oracle := inst.oracle
    M := M
    fstar := inst.fstar
    U := U
    theta := O3.stage9Theta n
    u := fun i => (O3.ogmgState cfg i).current
    v := O3.ogmgV cfg
    vMinusOne := U
    trace := ((List.range (n + 1)).map fun i =>
      inst.oracle.observe (O3.ogmgState cfg i).current) ++
      [inst.oracle.observe (O3.ogmgV cfg n)] }

@[simp] theorem sourceEstimateState_zero (oracle : PairOracle d) (M : ℝ)
    (x0 : Point d) : sourceEstimateState oracle M x0 0 = ⟨x0, 0⟩ := rfl

@[simp] theorem sourceEstimateState_succ (oracle : PairOracle d) (M : ℝ)
    (x0 : Point d) (k : ℕ) :
    sourceEstimateState oracle M x0 (k + 1) =
      nextEstimateState M x0 k (sourceEstimateState oracle M x0 k)
        (oracle.observe (estimateQuery M x0 k
          (sourceEstimateState oracle M x0 k))) := rfl

theorem sourceEstimate_cumulative (oracle : PairOracle d) (M : ℝ)
    (x0 : Point d) : ∀ k,
    (sourceEstimateState oracle M x0 k).cumulativeGradient =
      fun j => ∑ i ∈ Finset.range k,
        O3.euclideanWeight (O3.euclideanA i) *
          oracle.gradient (estimateQuery M x0 i
            (sourceEstimateState oracle M x0 i)) j := by
  intro k
  induction k with
  | zero =>
      funext j
      simp
  | succ k ih =>
      rw [sourceEstimateState_succ]
      simp only [nextEstimateState, O3.PairOracle.observe]
      rw [ih]
      funext j
      simp [Finset.sum_range_succ]

theorem sourcePhaseA_dynamics (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (m : ℕ) (hM : 0 < M) :
    EuclideanGapDynamics (sourcePhaseAData inst M D m) := by
  refine ⟨hM, rfl, rfl, ?_, ?_⟩
  · simp [sourcePhaseAData, sourceEstimateMinimizer,
      O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer]
  intro k hk
  have ha : 0 < O3.euclideanWeight (O3.euclideanA k) :=
    O3.euclideanA_increment_pos k
  have hApos : 0 < O3.euclideanA (k + 1) :=
    O3.euclideanA_pos_of_one_le (by omega)
  have hden : 0 < O3.euclideanA k + O3.euclideanWeight (O3.euclideanA k) :=
    add_pos_of_nonneg_of_pos (O3.euclideanA_nonneg k) ha
  refine ⟨ha, ?_, rfl, ?_, ?_, ?_⟩
  · change (O3.euclideanWeight (O3.euclideanA k)) ^ (2 : ℕ) =
      O3.euclideanA k + O3.euclideanWeight (O3.euclideanA k)
    exact O3.euclideanWeight_equation (O3.euclideanA_nonneg k)
  · change estimateQuery M x0 k (sourceEstimateState inst.oracle M x0 k) =
      (O3.euclideanA k /
          (O3.euclideanA k + O3.euclideanWeight (O3.euclideanA k))) •
        (sourceEstimateState inst.oracle M x0 k).accelerated +
      (O3.euclideanWeight (O3.euclideanA k) /
          (O3.euclideanA k + O3.euclideanWeight (O3.euclideanA k))) •
        sourceEstimateMinimizer inst.oracle M x0 k
    unfold estimateQuery sourceEstimateMinimizer
    funext j
    simp only [O3.euclideanBarycenter, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp [hden.ne']
  · change sourceEstimateMinimizer inst.oracle M x0 (k + 1) =
      x0 - (1 / M) •
        (fun j => ∑ i ∈ Finset.range (k + 1),
          O3.euclideanWeight (O3.euclideanA i) *
            inst.oracle.gradient (estimateQuery M x0 i
              (sourceEstimateState inst.oracle M x0 i)) j)
    unfold sourceEstimateMinimizer
    rw [sourceEstimate_cumulative]
    rw [one_div]
    rfl
  · change (sourceEstimateState inst.oracle M x0 (k + 1)).accelerated =
      (O3.euclideanA k /
          (O3.euclideanA k + O3.euclideanWeight (O3.euclideanA k))) •
        (sourceEstimateState inst.oracle M x0 k).accelerated +
      (O3.euclideanWeight (O3.euclideanA k) /
          (O3.euclideanA k + O3.euclideanWeight (O3.euclideanA k))) •
        sourceEstimateMinimizer inst.oracle M x0 (k + 1)
    simp only [sourceEstimateMinimizer, sourceEstimateState_succ,
      nextEstimateState]
    unfold O3.euclideanBarycenter
    funext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp [hden.ne']

theorem sourcePhaseB_dynamics (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) (U : Point d) (hM : 0 < M) (hn : 1 ≤ n) :
    OGMGDynamics (sourcePhaseBData inst M n U) := by
  let cfg := O3.stage9ExecutionConfig n inst.oracle M U
  refine ⟨hn, hM, O3.stage9Theta_endpoint hn, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro i hi hin
    dsimp [sourcePhaseBData]
    rw [O3.stage9Theta_of_pos (by omega)]
    rw [O3.stage9Theta_of_pos (by omega : 0 < i + 1)]
    have hsub : n - i = (n - (i + 1)) + 1 := by
      omega
    rw [hsub, O3.ogmgThetaTail]
    rfl
  · dsimp [sourcePhaseBData]
    rw [O3.stage9Theta_zero, O3.ogmgThetaZero]
    rw [O3.stage9Theta_of_pos (by omega : 0 < (1 : ℕ))]
    rfl
  · intro i hin
    constructor
    · change O3.ogmgV (O3.stage9ExecutionConfig n inst.oracle M U) i =
        (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).current -
          (1 / M) • inst.oracle.gradient
            (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).current
      rw [O3.ogmgV_eq, O3.ogmgGradient_eq]
      rw [one_div]
      rfl
    · have hprev :
          (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) i).previousV =
            (if i = 0 then U else
              O3.ogmgV (O3.stage9ExecutionConfig n inst.oracle M U) (i - 1)) := by
        cases i with
        | zero => rfl
        | succ k =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            exact O3.ogmgState_succ_previousV
              (O3.stage9ExecutionConfig n inst.oracle M U) k
      dsimp [sourcePhaseBData, cfg]
      rw [O3.ogmgState_succ_current]
      rw [hprev]
      rfl
  · change O3.ogmgV (O3.stage9ExecutionConfig n inst.oracle M U) n =
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current -
        (1 / M) • inst.oracle.gradient
          (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M U) n).current
    rw [O3.ogmgV_eq, O3.ogmgGradient_eq]
    rw [one_div]
    rfl

theorem sourcePhaseA_trace_exact (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (m : ℕ) :
    TraceExact inst.oracle (sourcePhaseAData inst M D m).trace := by
  intro obs hobs
  simp only [sourcePhaseAData, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hobs
  rcases hobs with ⟨k, hk, rfl | rfl⟩ <;> rfl

theorem sourcePhaseB_trace_exact (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) (U : Point d) :
    TraceExact inst.oracle (sourcePhaseBData inst M n U).trace := by
  intro obs hobs
  simp only [sourcePhaseBData, List.mem_append, List.mem_map,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hobs
  rcases hobs with ⟨i, hi, rfl⟩ | rfl <;> rfl

@[simp] theorem phaseABudget_eq (n fuel : ℕ) :
    phaseABudget n fuel = 2 * fuel + n + 1 := by
  induction fuel with
  | zero => simp [phaseABudget]
  | succ fuel ih =>
      simp only [phaseABudget, ih]
      omega

end Stage1E03
end V7
