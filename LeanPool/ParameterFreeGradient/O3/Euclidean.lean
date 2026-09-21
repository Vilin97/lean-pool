/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Oracle

/-!
# Euclidean-chain arithmetic and oracle accounting

This module closes scalar recurrences and exact finite-query accounting that
are independent of the guarded estimate-sequence and finite-data OGM-G vector
identities.  It deliberately does not turn either load-bearing identity into
a certificate field.
-/

namespace O3

noncomputable def euclideanWeight (A : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * A)) / 2

theorem euclideanWeight_pos {A : ℝ} (hA : 0 ≤ A) : 0 < euclideanWeight A := by
  unfold euclideanWeight
  positivity

theorem euclideanWeight_equation {A : ℝ} (hA : 0 ≤ A) :
    (euclideanWeight A) ^ 2 = A + euclideanWeight A := by
  have hrad : 0 ≤ 1 + 4 * A := by linarith
  have hsqrt := Real.sq_sqrt hrad
  unfold euclideanWeight
  nlinarith

noncomputable def thetaStep (t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * t ^ 2)) / 2

noncomputable def thetaZeroStep (t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 8 * t ^ 2)) / 2

theorem thetaStep_pos (t : ℝ) : 0 < thetaStep t := by
  unfold thetaStep
  positivity

theorem thetaStep_equation (t : ℝ) :
    (thetaStep t) ^ 2 - thetaStep t = t ^ 2 := by
  have hrad : 0 ≤ 1 + 4 * t ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hrad
  unfold thetaStep
  nlinarith

theorem thetaZeroStep_equation (t : ℝ) :
    (thetaZeroStep t) ^ 2 - thetaZeroStep t = 2 * t ^ 2 := by
  have hrad : 0 ≤ 1 + 8 * t ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hrad
  unfold thetaZeroStep
  nlinarith

theorem thetaStep_ge_add_half {t : ℝ} (ht : 0 ≤ t) :
    t + 1 / 2 ≤ thetaStep t := by
  have hrad : 0 ≤ 1 + 4 * t ^ 2 := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * t ^ 2) := Real.sqrt_nonneg _
  have hsqrt_sq := Real.sq_sqrt hrad
  have hsqrt_ge : 2 * t ≤ Real.sqrt (1 + 4 * t ^ 2) := by nlinarith
  unfold thetaStep
  linarith

/-- Backward OGM-G coefficients with the special doubled first equation. -/
noncomputable def ogmgTheta (n : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if _hlast : i.val = n then 1
  else if _hzero : i.val = 0 then
    thetaZeroStep (Nat.rec (motive := fun _ => ℝ) 1 (fun _ t => thetaStep t) (n - 1))
  else Nat.rec (motive := fun _ => ℝ) 1 (fun _ t => thetaStep t) (n - i.val)

/-- The ordinary backward tail `theta_n=1`, iterated away from the endpoint. -/
noncomputable def ogmgThetaTail : ℕ → ℝ
  | 0 => 1
  | k + 1 => thetaStep (ogmgThetaTail k)

theorem ogmgThetaTail_pos : ∀ k, 0 < ogmgThetaTail k := by
  intro k
  induction k with
  | zero => simp [ogmgThetaTail]
  | succ k _ => exact thetaStep_pos _

theorem ogmgThetaTail_ge (k : ℕ) :
    1 + (k : ℝ) / 2 ≤ ogmgThetaTail k := by
  induction k with
  | zero => simp [ogmgThetaTail]
  | succ k ih =>
      rw [ogmgThetaTail]
      have hstep := thetaStep_ge_add_half (le_of_lt (ogmgThetaTail_pos k))
      push_cast
      linarith

/-- The special doubled first coefficient of the OGM-G certificate. -/
noncomputable def ogmgThetaZero (n : ℕ) : ℝ :=
  thetaZeroStep (ogmgThetaTail (n - 1))

theorem thetaZeroStep_ge_sqrtTwo_mul {t : ℝ} (_ht : 0 ≤ t) :
    Real.sqrt 2 * t ≤ thetaZeroStep t := by
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrad : 0 ≤ 1 + 8 * t ^ 2 := by positivity
  have hr : 0 ≤ Real.sqrt (1 + 8 * t ^ 2) := Real.sqrt_nonneg _
  have hrsq : (Real.sqrt (1 + 8 * t ^ 2)) ^ 2 = 1 + 8 * t ^ 2 :=
    Real.sq_sqrt hrad
  have hcompare : 2 * Real.sqrt 2 * t ≤ Real.sqrt (1 + 8 * t ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt (1 + 8 * t ^ 2) - 2 * Real.sqrt 2 * t)]
  unfold thetaZeroStep
  linarith

/-- The exact lower bound `theta_0 >= (n+1)/sqrt 2`. -/
theorem ogmgThetaZero_ge {n : ℕ} (hn : 1 ≤ n) :
    (n + 1 : ℝ) / Real.sqrt 2 ≤ ogmgThetaZero n := by
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htail := ogmgThetaTail_ge (n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have htail' : (n + 1 : ℝ) / 2 ≤ ogmgThetaTail (n - 1) := by
    rw [hcast] at htail
    linarith
  have hzero := thetaZeroStep_ge_sqrtTwo_mul (le_of_lt (ogmgThetaTail_pos (n - 1)))
  rw [ogmgThetaZero]
  calc
    (n + 1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 * ((n + 1 : ℝ) / 2) := by
      field_simp [ne_of_gt hs2pos]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ Real.sqrt 2 * ogmgThetaTail (n - 1) :=
      mul_le_mul_of_nonneg_left htail' (Real.sqrt_nonneg _)
    _ ≤ thetaZeroStep (ogmgThetaTail (n - 1)) := hzero

/-- Exact number of pair calls in the source's Euclidean trial: Phase A makes
at most two calls per iteration, Phase B reuses `U`, makes `n` further iterate
queries, and makes one terminal descent query. -/
def euclideanTrialCallBudget (m n : ℕ) : ℕ := 2 * m + n + 1

theorem euclideanTrialCallBudget_diagonal (n : ℕ) :
    euclideanTrialCallBudget n n = 3 * n + 1 := by
  simp [euclideanTrialCallBudget]
  omega

/-- The source horizon `ceil (2 sqrt (M D / eps))`. -/
noncomputable def euclideanHorizon (kappa : ℝ) : ℕ :=
  Nat.ceil (2 * Real.sqrt kappa)

theorem euclideanHorizon_real_le {kappa : ℝ} :
    (euclideanHorizon kappa : ℝ) ≤ 2 * Real.sqrt kappa + 1 := by
  exact (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).le

/-- Universal concrete call constant for the diagonal Euclidean horizon. -/
theorem euclideanTrialCallBudget_horizon {kappa : ℝ} (hkappa : 1 ≤ kappa) :
    (euclideanTrialCallBudget (euclideanHorizon kappa)
      (euclideanHorizon kappa) : ℝ) ≤ 10 * Real.sqrt kappa := by
  have hkappa0 : 0 ≤ kappa := le_trans (by norm_num) hkappa
  have hh := euclideanHorizon_real_le (kappa := kappa)
  have hsqrt : 1 ≤ Real.sqrt kappa := by
    exact (Real.le_sqrt (by norm_num) hkappa0).2 (by simpa using hkappa)
  rw [euclideanTrialCallBudget_diagonal]
  push_cast
  nlinarith

/-- The two Phase-A oracle calls at each iteration, in chronological order. -/
def euclideanPhaseTrace {d m : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin m → Vec d) : OracleTrace d :=
  (List.finRange m).flatMap fun i =>
    [oracle.observe (y i), oracle.observe (accelerated i)]

theorem euclideanPhaseTrace_exact {d m : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin m → Vec d) :
    TraceExact oracle (euclideanPhaseTrace oracle y accelerated) := by
  intro observation hobservation
  rw [euclideanPhaseTrace, List.mem_flatMap] at hobservation
  obtain ⟨i, _, hi⟩ := hobservation
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem euclideanPhaseTrace_length {d m : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin m → Vec d) :
    (euclideanPhaseTrace oracle y accelerated).length = 2 * m := by
  simp [euclideanPhaseTrace]
  omega

/--
Phase B reuses `U`; this trace therefore contains only the `n` newly queried
iterates `u_1,...,u_n` and the additional terminal query at `v_n`.
-/
def finiteDataOGMGTrace {d n : ℕ} (oracle : PairOracle d)
    (newIterates : Fin n → Vec d) (terminalDescent : Vec d) : OracleTrace d :=
  (List.finRange n).map (fun i => oracle.observe (newIterates i)) ++
    [oracle.observe terminalDescent]

theorem finiteDataOGMGTrace_exact {d n : ℕ} (oracle : PairOracle d)
    (newIterates : Fin n → Vec d) (terminalDescent : Vec d) :
    TraceExact oracle (finiteDataOGMGTrace oracle newIterates terminalDescent) := by
  intro observation hobservation
  rw [finiteDataOGMGTrace, List.mem_append] at hobservation
  rcases hobservation with hiter | hterminal
  · rw [List.mem_map] at hiter
    obtain ⟨i, _, rfl⟩ := hiter
    rfl
  · simp only [List.mem_singleton] at hterminal
    subst observation
    rfl

@[simp] theorem finiteDataOGMGTrace_length {d n : ℕ} (oracle : PairOracle d)
    (newIterates : Fin n → Vec d) (terminalDescent : Vec d) :
    (finiteDataOGMGTrace oracle newIterates terminalDescent).length = n + 1 := by
  simp [finiteDataOGMGTrace]

/-- Full Euclidean local-trial trace with no double-counting of the reused `U`. -/
def euclideanTrialTrace {d m n : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin m → Vec d) (newIterates : Fin n → Vec d)
    (terminalDescent : Vec d) : OracleTrace d :=
  euclideanPhaseTrace oracle y accelerated ++
    finiteDataOGMGTrace oracle newIterates terminalDescent

theorem euclideanTrialTrace_exact {d m n : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin m → Vec d) (newIterates : Fin n → Vec d)
    (terminalDescent : Vec d) :
    TraceExact oracle
      (euclideanTrialTrace oracle y accelerated newIterates terminalDescent) := by
  exact traceExact_append (euclideanPhaseTrace_exact oracle y accelerated)
    (finiteDataOGMGTrace_exact oracle newIterates terminalDescent)

@[simp] theorem euclideanTrialTrace_length {d m n : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin m → Vec d) (newIterates : Fin n → Vec d)
    (terminalDescent : Vec d) :
    (euclideanTrialTrace oracle y accelerated newIterates terminalDescent).length =
      euclideanTrialCallBudget m n := by
  simp [euclideanTrialTrace, euclideanTrialCallBudget]
  omega

theorem finiteDataOGMGTrace_final_iterate_queried {d n : ℕ}
    (hn : 1 ≤ n) (oracle : PairOracle d) (newIterates : Fin n → Vec d)
    (terminalDescent : Vec d) :
    WasQueried (finiteDataOGMGTrace oracle newIterates terminalDescent)
      (newIterates ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩) := by
  let last : Fin n := ⟨n - 1, Nat.sub_lt (by omega) (by omega)⟩
  refine ⟨oracle.observe (newIterates last), ?_, rfl⟩
  rw [finiteDataOGMGTrace, List.mem_append]
  left
  apply List.mem_map.mpr
  exact ⟨last, List.mem_finRange last, rfl⟩

/-- Scalar denominator step used at the end of the guarded Euclidean-gap proof. -/
noncomputable def EuclideanGapScalarStatement : Prop :=
  ∀ (M D fGap A : ℝ) (m : ℕ),
    0 < M → 0 ≤ D → 1 ≤ m →
    A ≥ ((m : ℝ) + 1) ^ 2 / 4 →
    fGap ≤ M * D ^ 2 / (2 * A) →
    fGap ≤ 2 * M * D ^ 2 / ((m : ℝ) + 1) ^ 2

theorem euclideanGap_scalar : EuclideanGapScalarStatement := by
  intro M D fGap A m hM hD hm hA hgap
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have hApos : 0 < A := lt_of_lt_of_le (by positivity : 0 < ((m : ℝ) + 1) ^ 2 / 4) hA
  calc
    fGap ≤ M * D ^ 2 / (2 * A) := hgap
    _ ≤ 2 * M * D ^ 2 / ((m : ℝ) + 1) ^ 2 := by
      have hnum : 0 ≤ M * D ^ 2 := mul_nonneg hM.le (sq_nonneg D)
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * A)
        (by positivity : 0 < ((m : ℝ) + 1) ^ 2)).2
      nlinarith

end O3
