/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Stage9Theta
import LeanPool.ParameterFreeGradient.O3.Stage9Telescoping
import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
# Stage 9: actual finite-data OGM-G execution

This module implements the literal deterministic recursion from TeX Lemma
`lem:ogmg`.  It contains no convergence conclusion and no algebraic
certificate: its only job is to expose the actual queried data, the complete
ordered-pair interpolation checks, and the final descent query.

The phase-B trace deliberately omits `u₀ = U`, which is reused from Phase A,
and contains exactly the newly queried points `u₁, …, uₙ, vₙ`.
-/

open scoped BigOperators

namespace O3

/-- Data fixed before running the finite OGM-G phase.  The coefficient
function is kept explicit here so the execution algebra can also be reused by
the coefficient auditor; the source run below instantiates it by the frozen
backward theta sequence. -/
structure OGMGExecutionConfig (d : ℕ) where
  horizon : ℕ
  oracle : PairOracle d
  M : ℝ
  U : Vec d
  theta : ℕ → ℝ

/-- The source-exact configuration: no theta sequence is supplied by the
caller; it is the frozen special-zero/backward-tail sequence for horizon `n`. -/
noncomputable def stage9ExecutionConfig {d : ℕ} (n : ℕ)
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) : OGMGExecutionConfig d :=
  { horizon := n
    oracle := oracle
    M := M
    U := U
    theta := stage9Theta n }

@[simp] theorem stage9ExecutionConfig_horizon {d : ℕ} (n : ℕ)
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) :
    (stage9ExecutionConfig n oracle M U).horizon = n := rfl

@[simp] theorem stage9ExecutionConfig_theta {d : ℕ} (n i : ℕ)
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) :
    (stage9ExecutionConfig n oracle M U).theta i = stage9Theta n i := rfl

/-- At the beginning of iteration `i`, `current` is `u_i` and `previousV` is
`v_(i-1)`.  Thus the initial previous point is literally `v_(-1)=U`. -/
structure OGMGExecutionState (d : ℕ) where
  current : Vec d
  previousV : Vec d

/-- One literal source step. -/
noncomputable def ogmgExecutionStep (cfg : OGMGExecutionConfig d) (i : ℕ)
    (state : OGMGExecutionState d) : OGMGExecutionState d :=
  let v := state.current - cfg.M⁻¹ • (cfg.oracle.observe state.current).gradient
  let momentum :=
    ((cfg.theta i - 1) * (2 * cfg.theta (i + 1) - 1)) /
      (cfg.theta i * (2 * cfg.theta i - 1))
  let correction := (2 * cfg.theta (i + 1) - 1) / (2 * cfg.theta i - 1)
  { current := v + momentum • (v - state.previousV) +
      correction • (v - state.current)
    previousV := v }

/-- Primitive-recursive actual execution, beginning from
`u_0=U, v_(-1)=U`. -/
noncomputable def ogmgState (cfg : OGMGExecutionConfig d) : ℕ → OGMGExecutionState d
  | 0 => ⟨cfg.U, cfg.U⟩
  | i + 1 => ogmgExecutionStep cfg i (ogmgState cfg i)

/-- The actual observation at `u_i`. -/
noncomputable def ogmgObservation (cfg : OGMGExecutionConfig d) (i : ℕ) : Observation d :=
  cfg.oracle.observe (ogmgState cfg i).current

/-- The actual queried gradient `g_i`. -/
noncomputable def ogmgGradient (cfg : OGMGExecutionConfig d) (i : ℕ) : Vec d :=
  (ogmgObservation cfg i).gradient

/-- The literal gradient point `v_i=u_i-g_i/M`. -/
noncomputable def ogmgV (cfg : OGMGExecutionConfig d) (i : ℕ) : Vec d :=
  (ogmgState cfg i).current - cfg.M⁻¹ • ogmgGradient cfg i

@[simp] theorem ogmgState_zero_current (cfg : OGMGExecutionConfig d) :
    (ogmgState cfg 0).current = cfg.U := rfl

@[simp] theorem ogmgState_zero_previousV (cfg : OGMGExecutionConfig d) :
    (ogmgState cfg 0).previousV = cfg.U := rfl

@[simp] theorem ogmgObservation_point (cfg : OGMGExecutionConfig d) (i : ℕ) :
    (ogmgObservation cfg i).point = (ogmgState cfg i).current := rfl

@[simp] theorem ogmgObservation_value (cfg : OGMGExecutionConfig d) (i : ℕ) :
    (ogmgObservation cfg i).value = cfg.oracle.value (ogmgState cfg i).current := rfl

@[simp] theorem ogmgObservation_gradient (cfg : OGMGExecutionConfig d) (i : ℕ) :
    (ogmgObservation cfg i).gradient = cfg.oracle.gradient (ogmgState cfg i).current := rfl

@[simp] theorem ogmgGradient_eq (cfg : OGMGExecutionConfig d) (i : ℕ) :
    ogmgGradient cfg i = cfg.oracle.gradient (ogmgState cfg i).current := rfl

theorem ogmgV_eq (cfg : OGMGExecutionConfig d) (i : ℕ) :
    ogmgV cfg i = (ogmgState cfg i).current - cfg.M⁻¹ • ogmgGradient cfg i := rfl

@[simp] theorem ogmgState_succ_previousV (cfg : OGMGExecutionConfig d) (i : ℕ) :
    (ogmgState cfg (i + 1)).previousV = ogmgV cfg i := by
  rfl

/-- The actual source recurrence with its coefficients unchanged. -/
theorem ogmgState_succ_current (cfg : OGMGExecutionConfig d) (i : ℕ) :
    (ogmgState cfg (i + 1)).current =
      ogmgV cfg i +
        (((cfg.theta i - 1) * (2 * cfg.theta (i + 1) - 1)) /
          (cfg.theta i * (2 * cfg.theta i - 1))) •
            (ogmgV cfg i - (ogmgState cfg i).previousV) +
        ((2 * cfg.theta (i + 1) - 1) / (2 * cfg.theta i - 1)) •
          (ogmgV cfg i - (ogmgState cfg i).current) := by
  rfl

/-- The recurrence specialized to the non-user-supplied, source-exact theta
coefficients. -/
theorem stage9Execution_succ_current {d : ℕ} (n : ℕ)
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) (i : ℕ) :
    (ogmgState (stage9ExecutionConfig n oracle M U) (i + 1)).current =
      ogmgV (stage9ExecutionConfig n oracle M U) i +
        (((stage9Theta n i - 1) * (2 * stage9Theta n (i + 1) - 1)) /
          (stage9Theta n i * (2 * stage9Theta n i - 1))) •
            (ogmgV (stage9ExecutionConfig n oracle M U) i -
              (ogmgState (stage9ExecutionConfig n oracle M U) i).previousV) +
        ((2 * stage9Theta n (i + 1) - 1) /
          (2 * stage9Theta n i - 1)) •
            (ogmgV (stage9ExecutionConfig n oracle M U) i -
              (ogmgState (stage9ExecutionConfig n oracle M U) i).current) := by
  exact ogmgState_succ_current (stage9ExecutionConfig n oracle M U) i

theorem stage9Execution_theta_denominators_pos {d : ℕ} (n i : ℕ)
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) :
    0 < (stage9ExecutionConfig n oracle M U).theta i ∧
      0 < 2 * (stage9ExecutionConfig n oracle M U).theta i - 1 := by
  exact ⟨stage9Theta_pos n i, stage9_two_mul_theta_sub_one_pos n i⟩

/-- The actual iterate recursion produces the precise velocity identity used
by the frozen quadratic telescoping proof.  This is proved for every natural
index, hence in particular at the terminal endpoint `i=n`; no extrapolated
iterate hypothesis is introduced. -/
theorem ogmg_velocity_p_relation (cfg : OGMGExecutionConfig d)
    (hM : cfg.M ≠ 0)
    (hθ : ∀ i, cfg.theta i ≠ 0)
    (hden : ∀ i, 2 * cfg.theta i - 1 ≠ 0) :
    ∀ i,
      cfg.M • (ogmgV cfg i - (ogmgState cfg i).previousV) =
        (-cfg.theta i) •
          (stage9P cfg.theta (ogmgGradient cfg) i +
            stage9P cfg.theta (ogmgGradient cfg) (i + 1)) := by
  intro i
  induction i with
  | zero =>
      funext j
      simp only [ogmgV, ogmgState, ogmgGradient, ogmgObservation,
        PairOracle.observe, stage9P, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add]
      field_simp [hM, hθ 0]
      ring
  | succ i ih =>
      have hgi := stage9P_gradient_eq
        (theta := cfg.theta) (g := ogmgGradient cfg) (hθ i)
      have hgis := stage9P_gradient_eq
        (theta := cfg.theta) (g := ogmgGradient cfg) (hθ (i + 1))
      rw [ogmgState_succ_previousV, ogmgV_eq, ogmgState_succ_current]
      funext j
      have ihj := congrFun ih j
      have hgij := congrFun hgi j
      have hgisj := congrFun hgis j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ihj
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hgij
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hgisj
      have hvuj :
          cfg.M * (ogmgV cfg i j - (ogmgState cfg i).current j) =
            -ogmgGradient cfg i j := by
        rw [ogmgV_eq]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp [hM]
        ring
      have ihdiv :
          ogmgV cfg i j - (ogmgState cfg i).previousV j =
            (-(cfg.theta i *
              (stage9P cfg.theta (ogmgGradient cfg) i j +
                stage9P cfg.theta (ogmgGradient cfg) (i + 1) j))) / cfg.M := by
        apply (eq_div_iff hM).2
        calc
          (ogmgV cfg i j - (ogmgState cfg i).previousV j) * cfg.M =
              cfg.M * (ogmgV cfg i j - (ogmgState cfg i).previousV j) := by ring
          _ = _ := by rw [ihj]; ring
      have hvudiv :
          ogmgV cfg i j - (ogmgState cfg i).current j =
            (-ogmgGradient cfg i j) / cfg.M := by
        apply (eq_div_iff hM).2
        calc
          (ogmgV cfg i j - (ogmgState cfg i).current j) * cfg.M =
              cfg.M * (ogmgV cfg i j - (ogmgState cfg i).current j) := by ring
          _ = _ := hvuj
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ihdiv, hvudiv, hgij, hgisj]
      have hden' : cfg.theta i * 2 - 1 ≠ 0 := by
        intro h
        apply hden i
        linarith
      field_simp [hM, hθ i, hθ (i + 1), hden i, hden']
      ring

/-- Source-exact specialization of the velocity identity. -/
theorem stage9Execution_velocity_p_relation {d : ℕ} (n : ℕ)
    (oracle : PairOracle d) (M : ℝ) (U : Vec d) (hM : M ≠ 0) (i : ℕ) :
    let cfg := stage9ExecutionConfig n oracle M U
    M • (ogmgV cfg i - (ogmgState cfg i).previousV) =
      (-stage9Theta n i) •
        (stage9P (stage9Theta n) (ogmgGradient cfg) i +
          stage9P (stage9Theta n) (ogmgGradient cfg) (i + 1)) := by
  dsimp only
  exact ogmg_velocity_p_relation (stage9ExecutionConfig n oracle M U) hM
    (stage9Theta_ne_zero n)
    (stage9_two_mul_theta_sub_one_ne_zero n) i

/-- For every positive index the stored predecessor is the actual preceding
gradient point. -/
theorem ogmgState_previousV (cfg : OGMGExecutionConfig d) (i : ℕ) :
    (ogmgState cfg (i + 1)).previousV = ogmgV cfg i :=
  ogmgState_succ_previousV cfg i

/-- The `n` new iterate queries `u_1,…,u_n`, indexed without a phantom query. -/
noncomputable def ogmgNewIterates (cfg : OGMGExecutionConfig d) : Fin cfg.horizon → Vec d :=
  fun i => (ogmgState cfg (i.val + 1)).current

/-- The final extra query is at exactly `v_n`. -/
noncomputable def ogmgTerminalObservation (cfg : OGMGExecutionConfig d) : Observation d :=
  cfg.oracle.observe (ogmgV cfg cfg.horizon)

/-- Phase-B calls only: `u_1,…,u_n,v_n`. -/
noncomputable def ogmgExecutionTrace (cfg : OGMGExecutionConfig d) : OracleTrace d :=
  finiteDataOGMGTrace cfg.oracle (ogmgNewIterates cfg) (ogmgV cfg cfg.horizon)

theorem ogmgExecutionTrace_exact (cfg : OGMGExecutionConfig d) :
    TraceExact cfg.oracle (ogmgExecutionTrace cfg) := by
  exact finiteDataOGMGTrace_exact cfg.oracle (ogmgNewIterates cfg)
    (ogmgV cfg cfg.horizon)

@[simp] theorem ogmgExecutionTrace_length (cfg : OGMGExecutionConfig d) :
    (ogmgExecutionTrace cfg).length = cfg.horizon + 1 := by
  exact finiteDataOGMGTrace_length cfg.oracle (ogmgNewIterates cfg)
    (ogmgV cfg cfg.horizon)

/-- The additional terminal point `v_n` is genuinely queried. -/
theorem ogmgExecutionTrace_terminal_queried (cfg : OGMGExecutionConfig d) :
    WasQueried (ogmgExecutionTrace cfg) (ogmgV cfg cfg.horizon) := by
  refine ⟨cfg.oracle.observe (ogmgV cfg cfg.horizon), ?_, rfl⟩
  simp [ogmgExecutionTrace, finiteDataOGMGTrace]

/-- For a nonzero horizon, `u_n` is one of the newly queried iterates. -/
theorem ogmgExecutionTrace_final_iterate_queried (cfg : OGMGExecutionConfig d)
    (hn : 1 ≤ cfg.horizon) :
    WasQueried (ogmgExecutionTrace cfg) (ogmgState cfg cfg.horizon).current := by
  let last : Fin cfg.horizon :=
    ⟨cfg.horizon - 1, Nat.sub_lt (by omega) (by omega)⟩
  refine ⟨cfg.oracle.observe ((ogmgState cfg cfg.horizon).current), ?_, rfl⟩
  rw [ogmgExecutionTrace, finiteDataOGMGTrace, List.mem_append]
  left
  apply List.mem_map.mpr
  refine ⟨last, List.mem_finRange last, ?_⟩
  have hidx : cfg.horizon - 1 + 1 = cfg.horizon := Nat.sub_add_cancel hn
  simp only [ogmgNewIterates, last, hidx]

/-- The reused point `u₀=U` and every subsequently queried `u_i`, including
`u_n`, as an actual oracle observation. -/
noncomputable def ogmgDataObservation (cfg : OGMGExecutionConfig d)
    (i : Fin (cfg.horizon + 1)) : Observation d :=
  ogmgObservation cfg i.val

/-- Scalar/vector projections of the actual finite data, ready for the
algebraic certificate.  These are definitions, not freely supplied arrays. -/
noncomputable def ogmgFunctionValue (cfg : OGMGExecutionConfig d) (i : ℕ) : ℝ :=
  (ogmgObservation cfg i).value

noncomputable def ogmgGradientSq (cfg : OGMGExecutionConfig d) (i : ℕ) : ℝ :=
  (lpNorm 2 (ogmgGradient cfg i)) ^ (2 : ℕ)

noncomputable def ogmgPairTerm (cfg : OGMGExecutionConfig d)
    (i j : ℕ) : ℝ :=
  pairing (ogmgGradient cfg j) (ogmgV cfg i - ogmgV cfg j)

@[simp] theorem ogmgFunctionValue_zero (cfg : OGMGExecutionConfig d) :
    ogmgFunctionValue cfg 0 = cfg.oracle.value cfg.U := rfl

@[simp] theorem ogmgPairTerm_self (cfg : OGMGExecutionConfig d) (i : ℕ) :
    ogmgPairTerm cfg i i = 0 := by
  simp [ogmgPairTerm, pairing]

/-- The observable ordered interpolation check for `(i,j)`. -/
noncomputable def ogmgInterpolationCheck (cfg : OGMGExecutionConfig d)
    (i j : Fin (cfg.horizon + 1)) : GuardCheck :=
  let oi := ogmgDataObservation cfg i
  let oj := ogmgDataObservation cfg j
  interpolationGuard oi.value oj.value
    (pairing oj.gradient (oi.point - oj.point))
    ((lpNorm 2 (oi.gradient - oj.gradient)) ^ (2 : ℕ)) cfg.M

/-- A concrete list containing all `(n+1)^2` ordered interpolation checks. -/
noncomputable def ogmgAllInterpolationChecks
    (cfg : OGMGExecutionConfig d) : List GuardCheck :=
  (List.finRange (cfg.horizon + 1)).flatMap fun i =>
    (List.finRange (cfg.horizon + 1)).map fun j =>
      ogmgInterpolationCheck cfg i j

@[simp] theorem ogmgAllInterpolationChecks_length
    (cfg : OGMGExecutionConfig d) :
    (ogmgAllInterpolationChecks cfg).length =
      (cfg.horizon + 1) * (cfg.horizon + 1) := by
  simp [ogmgAllInterpolationChecks]

@[simp] theorem ogmgInterpolationCheck_kind
    (cfg : OGMGExecutionConfig d) (i j : Fin (cfg.horizon + 1)) :
    (ogmgInterpolationCheck cfg i j).kind = .interpolation := rfl

/-- All ordered-pair finite-data interpolation guards pass. -/
def OGMGAllInterpolationGuardsHold (cfg : OGMGExecutionConfig d) : Prop :=
  allGuardsPass (ogmgAllInterpolationChecks cfg)

theorem ogmgAllInterpolationGuardsHold_iff
    (cfg : OGMGExecutionConfig d) :
    OGMGAllInterpolationGuardsHold cfg ↔
      ∀ i j : Fin (cfg.horizon + 1),
        (ogmgInterpolationCheck cfg i j).Holds := by
  constructor
  · intro h i j
    apply h (ogmgInterpolationCheck cfg i j)
    simp [ogmgAllInterpolationChecks]
  · intro h check hcheck
    simp only [ogmgAllInterpolationChecks, List.mem_flatMap, List.mem_map] at hcheck
    obtain ⟨i, _, j, _, rfl⟩ := hcheck
    exact h i j

/-- The source terminal guard is the actual upper-model check at the extra
query `v_n`. -/
noncomputable def ogmgTerminalDescentCheck
    (cfg : OGMGExecutionConfig d) : GuardCheck :=
  let on := ogmgObservation cfg cfg.horizon
  let ov := ogmgTerminalObservation cfg
  upperModelGuard on.value ov.value
    (pairing on.gradient (ov.point - on.point))
    ((lpNorm 2 (ov.point - on.point)) ^ (2 : ℕ)) cfg.M

theorem ogmgTerminalDescentCheck_holds_iff
    (cfg : OGMGExecutionConfig d) :
    (ogmgTerminalDescentCheck cfg).Holds ↔
      (ogmgTerminalObservation cfg).value ≤
        (ogmgObservation cfg cfg.horizon).value +
          pairing (ogmgGradient cfg cfg.horizon)
            (ogmgV cfg cfg.horizon - (ogmgState cfg cfg.horizon).current) +
          (cfg.M / 2) *
            (lpNorm 2
              (ogmgV cfg cfg.horizon - (ogmgState cfg cfg.horizon).current)) ^
              (2 : ℕ) := by
  rw [ogmgTerminalDescentCheck, upperModelGuard_holds_iff]
  rfl

/-- Exact displacement of the queried terminal gradient point. -/
theorem ogmgTerminal_displacement (cfg : OGMGExecutionConfig d) :
    ogmgV cfg cfg.horizon - (ogmgState cfg cfg.horizon).current =
      (-cfg.M⁻¹) • ogmgGradient cfg cfg.horizon := by
  rw [ogmgV_eq]
  ext i
  simp

theorem pairing_self_eq_lpNorm_two_sq {d : ℕ} (g : Vec d) :
    pairing g g = (lpNorm 2 g) ^ (2 : ℕ) := by
  rw [Stage2RouteC.lpNorm_two_sq]
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- With `M>0`, the actual queried upper-model check at `v_n=u_n-g_n/M`
is exactly the terminal descent inequality printed in the source. -/
theorem ogmgTerminalDescentCheck_source_iff
    (cfg : OGMGExecutionConfig d) (hM : 0 < cfg.M) :
    (ogmgTerminalDescentCheck cfg).Holds ↔
      (ogmgTerminalObservation cfg).value ≤
        (ogmgObservation cfg cfg.horizon).value -
          (lpNorm 2 (ogmgGradient cfg cfg.horizon)) ^ (2 : ℕ) /
            (2 * cfg.M) := by
  rw [ogmgTerminalDescentCheck_holds_iff]
  let g := ogmgGradient cfg cfg.horizon
  let n2 := (lpNorm 2 g) ^ (2 : ℕ)
  have hMne : cfg.M ≠ 0 := ne_of_gt hM
  have hdisp := ogmgTerminal_displacement cfg
  have hpair :
      pairing g
        (ogmgV cfg cfg.horizon - (ogmgState cfg cfg.horizon).current) =
        -cfg.M⁻¹ * n2 := by
    rw [hdisp, Stage2RouteD.pairing_smul_right]
    rw [pairing_self_eq_lpNorm_two_sq]
  have habs : |(-cfg.M⁻¹ : ℝ)| = cfg.M⁻¹ := by
    rw [abs_neg, abs_of_pos (inv_pos.mpr hM)]
  have hnorm :
      (lpNorm 2
        (ogmgV cfg cfg.horizon - (ogmgState cfg cfg.horizon).current)) ^
          (2 : ℕ) = cfg.M⁻¹ ^ (2 : ℕ) * n2 := by
    rw [hdisp, Stage2RouteC.lpNorm_smul (by norm_num), habs]
    dsimp only [n2, g]
    ring
  have hcombine :
      -cfg.M⁻¹ * n2 +
          cfg.M / 2 * (cfg.M⁻¹ ^ (2 : ℕ) * n2) =
        -n2 / (2 * cfg.M) := by
    field_simp [hMne]
    ring
  have hfull :
      (ogmgObservation cfg cfg.horizon).value + (-cfg.M⁻¹ * n2) +
          cfg.M / 2 * (cfg.M⁻¹ ^ (2 : ℕ) * n2) =
        (ogmgObservation cfg cfg.horizon).value -
          (lpNorm 2 (ogmgGradient cfg cfg.horizon)) ^ (2 : ℕ) /
            (2 * cfg.M) := by
    calc
      _ = (ogmgObservation cfg cfg.horizon).value +
          (-cfg.M⁻¹ * n2 +
            cfg.M / 2 * (cfg.M⁻¹ ^ (2 : ℕ) * n2)) := by ring
      _ = (ogmgObservation cfg cfg.horizon).value +
          (-n2 / (2 * cfg.M)) := by rw [hcombine]
      _ = _ := by dsimp only [n2, g]; ring
  rw [hpair, hnorm]
  rw [hfull]

/-- All Stage-9 observable guards, without any algebraic certificate field. -/
noncomputable def ogmgExecutionGuards
    (cfg : OGMGExecutionConfig d) : List GuardCheck :=
  ogmgAllInterpolationChecks cfg ++ [ogmgTerminalDescentCheck cfg]

theorem ogmgExecutionGuards_interpolation
    (cfg : OGMGExecutionConfig d)
    (h : allGuardsPass (ogmgExecutionGuards cfg))
    (i j : Fin (cfg.horizon + 1)) :
    (ogmgInterpolationCheck cfg i j).Holds := by
  apply h (ogmgInterpolationCheck cfg i j)
  simp [ogmgExecutionGuards, ogmgAllInterpolationChecks]

theorem ogmgExecutionGuards_terminal
    (cfg : OGMGExecutionConfig d)
    (h : allGuardsPass (ogmgExecutionGuards cfg)) :
    (ogmgTerminalDescentCheck cfg).Holds := by
  apply h (ogmgTerminalDescentCheck cfg)
  simp [ogmgExecutionGuards]

end O3
