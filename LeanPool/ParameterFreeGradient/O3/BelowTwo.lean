/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Foundation

/-!
# The `1 < p < 2` branch: exact numerical recurrences and call ledger

This module contains the parts of the frozen below-two chain that do not rely
on the still-open real-exponent squared-`ell_p` strong-convexity bridge.  It
uses the exact real exponent range, the source weights, and a chronological
pair-oracle trace with two calls per accelerated iteration and one extraction
call.

The public declarations `O3.belowEstimate` and `O3.belowTrial` are intentionally
not asserted while `O3.belowGeometry` is unavailable: their TeX proofs use that
result load-bearingly.  No conditional replacement taking the desired
strong-convexity conclusion as an extra hypothesis is introduced.
-/

@[expose] public section

namespace O3

/-- The genuine-real regime from TeX Section 4. -/
def BelowTwoRegime (p : ℝ) : Prop := 1 < p ∧ p < 2

/-- The source parameter `sigma = p - 1`. -/
def belowSigma (p : ℝ) : ℝ := p - 1

theorem belowSigma_pos {p : ℝ} (hp : BelowTwoRegime p) :
    0 < belowSigma p := by
  exact sub_pos.mpr hp.1

theorem belowSigma_lt_one {p : ℝ} (hp : BelowTwoRegime p) :
    belowSigma p < 1 := by
  unfold belowSigma
  linarith [hp.2]

/-- The exact regularization parameter `lambda = eps / (4 D)`. -/
noncomputable def belowLambda (eps D : ℝ) : ℝ := eps / (4 * D)

/-- The exact residual target `rho = sigma eps / 32`. -/
noncomputable def belowRho (sigma eps : ℝ) : ℝ := sigma * eps / 32

/-- The exact source amplification factor `Q = 4096 kappa^2 / sigma^4`. -/
noncomputable def belowQ (kappa sigma : ℝ) : ℝ :=
  4096 * kappa ^ 2 / sigma ^ 4

theorem belowLambda_pos {eps D : ℝ} (heps : 0 < eps) (hD : 0 < D) :
    0 < belowLambda eps D := by
  exact div_pos heps (mul_pos (by norm_num) hD)

theorem belowRho_pos {sigma eps : ℝ} (hsigma : 0 < sigma) (heps : 0 < eps) :
    0 < belowRho sigma eps := by
  exact div_pos (mul_pos hsigma heps) (by norm_num)

theorem one_lt_belowQ {kappa sigma : ℝ}
    (hkappa : 1 < kappa) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    1 < belowQ kappa sigma := by
  have hsigma_sq : sigma ^ 2 < 1 := by nlinarith [sq_nonneg sigma]
  have hsigma_four : sigma ^ 4 < 1 := by
    nlinarith [sq_nonneg (sigma ^ 2)]
  have hkappa_sq : 1 < kappa ^ 2 := by nlinarith [sq_nonneg kappa]
  have hsigma_four_pos : 0 < sigma ^ 4 := pow_pos hsigma 4
  rw [belowQ, lt_div_iff₀ hsigma_four_pos]
  nlinarith

/-- The source contraction parameter, with no discretization of `p`. -/
noncomputable def belowTau (M lambda sigma : ℝ) : ℝ :=
  2 / (1 + Real.sqrt (1 + 4 * M / (lambda * sigma)))

theorem belowTau_pos {M lambda sigma : ℝ}
    (hM : 0 < M) (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    0 < belowTau M lambda sigma := by
  have hls : 0 < lambda * sigma := mul_pos hlambda hsigma
  have hrad : 0 < 1 + 4 * M / (lambda * sigma) := by
    have : 0 < 4 * M / (lambda * sigma) :=
      div_pos (mul_pos (by norm_num) hM) hls
    linarith
  have hsqrt : 0 ≤ Real.sqrt (1 + 4 * M / (lambda * sigma)) :=
    Real.sqrt_nonneg _
  exact div_pos (by norm_num) (by linarith)

theorem belowTau_lt_one {M lambda sigma : ℝ}
    (hM : 0 < M) (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    belowTau M lambda sigma < 1 := by
  have hls : 0 < lambda * sigma := mul_pos hlambda hsigma
  have hfrac : 0 < 4 * M / (lambda * sigma) :=
    div_pos (mul_pos (by norm_num) hM) hls
  have hone : 1 < Real.sqrt (1 + 4 * M / (lambda * sigma)) := by
    have hsqrt := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)
      (show (1 : ℝ) < 1 + 4 * M / (lambda * sigma) by linarith)
    simpa using hsqrt
  have hden : 0 < 1 + Real.sqrt (1 + 4 * M / (lambda * sigma)) := by
    linarith
  rw [belowTau, div_lt_one hden]
  linarith

/-- The exact source identity `M * tau^2 = lambda * sigma * (1 - tau)`. -/
theorem belowTau_equation {M lambda sigma : ℝ}
    (hM : 0 < M) (hlambda : 0 < lambda) (hsigma : 0 < sigma) :
    M * (belowTau M lambda sigma) ^ 2 =
      lambda * sigma * (1 - belowTau M lambda sigma) := by
  have hls : 0 < lambda * sigma := mul_pos hlambda hsigma
  have hfrac : 0 < 4 * M / (lambda * sigma) :=
    div_pos (mul_pos (by norm_num) hM) hls
  have hrad : 0 ≤ 1 + 4 * M / (lambda * sigma) := by linarith
  set s := Real.sqrt (1 + 4 * M / (lambda * sigma)) with hsdef
  have hsqrt : s ^ 2 = 1 + 4 * M / (lambda * sigma) := by
    rw [hsdef]
    exact Real.sq_sqrt hrad
  have hden : 1 + s ≠ 0 := by
    have := Real.sqrt_nonneg (1 + 4 * M / (lambda * sigma))
    rw [← hsdef] at this
    linarith
  have hlsne : lambda * sigma ≠ 0 := ne_of_gt hls
  have hcore :
      4 * M = lambda * sigma * (s ^ 2 - 1) := by
    rw [hsqrt]
    field_simp [hlsne]
    ring
  rw [belowTau, ← hsdef]
  field_simp [hden]
  nlinarith [hcore]

/--
The accepted estimate-sequence weight `A_N`.  This recursive definition is
exactly `A_0 = 0`, `A_1 = 1/M`, and
`A_(k+1) = A_k/(1-tau)` for `k >= 1`.
-/
noncomputable def belowWeight (M tau : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if n = 0 then 1 / M else belowWeight M tau n / (1 - tau)

@[simp] theorem belowWeight_zero (M tau : ℝ) :
    belowWeight M tau 0 = 0 := rfl

@[simp] theorem belowWeight_one (M tau : ℝ) :
    belowWeight M tau 1 = 1 / M := by
  simp [belowWeight]

theorem belowWeight_succ {M tau : ℝ} {k : ℕ} (hk : 1 ≤ k) :
    belowWeight M tau (k + 1) = belowWeight M tau k / (1 - tau) := by
  cases k with
  | zero => omega
  | succ k =>
      simp only [belowWeight]
      split
      next h =>
        have : k + 1 ≠ 0 := Nat.succ_ne_zero k
        contradiction
      next => rfl

theorem belowWeight_pos {M tau : ℝ}
    (hM : 0 < M) (htau : tau < 1) :
    ∀ {N : ℕ}, 1 ≤ N → 0 < belowWeight M tau N := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp [belowWeight, hM]
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        rw [belowWeight_succ hNpos]
        exact div_pos (ih hNpos) (sub_pos.mpr htau)

/-- Closed form `A_N = M⁻¹ (1-tau)^(-(N-1))`, written as division. -/
theorem belowWeight_eq {M tau : ℝ} (htau : tau ≠ 1) :
    ∀ {N : ℕ}, 1 ≤ N →
      belowWeight M tau N = (1 / M) / (1 - tau) ^ (N - 1) := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
      cases N with
      | zero => simp
      | succ N =>
          have hprev : 1 ≤ N + 1 := by omega
          rw [belowWeight_succ hprev, ih hprev]
          have hden : 1 - tau ≠ 0 := sub_ne_zero.mpr (Ne.symm htau)
          simp only [Nat.add_sub_cancel, pow_succ]
          field_simp [hden]

/-- One below-two accelerated iteration adds exactly its two pair responses. -/
structure BelowPhaseState (d : ℕ) where
  /-- The number of primal iterations recorded in this phase. -/
  iteration : ℕ
  /-- The current accelerated primal point. -/
  accelerated : Vec d
  /-- The current minimizer of the phase's estimate function. -/
  estimateMinimizer : Vec d
  /-- The cumulative acceleration weight at the current iteration. -/
  weight : ℝ
  /-- The chronological oracle responses accumulated by this phase. -/
  queries : List (Observation d)

/-- The number of oracle responses recorded by the phase. -/
def BelowPhaseState.callCount (state : BelowPhaseState d) : ℕ :=
  state.queries.length

/-- Advance the phase state and append the two observations from one primal iteration. -/
def BelowPhaseState.recordIteration
    (state : BelowPhaseState d) (accelerated estimateMinimizer : Vec d)
    (weight : ℝ) (atY atAccelerated : Observation d) : BelowPhaseState d :=
  { iteration := state.iteration + 1
    accelerated := accelerated
    estimateMinimizer := estimateMinimizer
    weight := weight
    queries := state.queries ++ [atY, atAccelerated] }

theorem BelowPhaseState.recordIteration_callCount
    (state : BelowPhaseState d) (accelerated estimateMinimizer : Vec d)
    (weight : ℝ) (atY atAccelerated : Observation d) :
    (state.recordIteration accelerated estimateMinimizer weight
      atY atAccelerated).callCount = state.callCount + 2 := by
  simp [BelowPhaseState.recordIteration, BelowPhaseState.callCount]

/-- Chronological exact trace of `N` two-query phase iterations. -/
def belowPhaseTrace {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) : List (Observation d) :=
  (List.finRange N).flatMap fun i =>
    [oracle.observe (y i), oracle.observe (accelerated i)]

/-- Every entry is the exact oracle response at its recorded query point. -/
def ObservationTraceExact {d : ℕ} (oracle : PairOracle d)
    (trace : List (Observation d)) : Prop :=
  ∀ observation ∈ trace, observation = oracle.observe observation.point

theorem belowPhaseTrace_exact {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    ObservationTraceExact oracle (belowPhaseTrace oracle y accelerated) := by
  intro observation hobservation
  rw [belowPhaseTrace, List.mem_flatMap] at hobservation
  obtain ⟨i, _, hi⟩ := hobservation
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem belowPhaseTrace_length {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    (belowPhaseTrace oracle y accelerated).length = 2 * N := by
  simp [belowPhaseTrace]
  omega

/-- The phase trace followed by the counted residual-extraction query. -/
def belowTrialTrace {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) (extraction : Vec d) :
    List (Observation d) :=
  belowPhaseTrace oracle y accelerated ++ [oracle.observe extraction]

/-- Exact local oracle accounting from TeX lines 751--752. -/
theorem belowTrialTrace_callCount {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) (extraction : Vec d) :
    (belowTrialTrace oracle y accelerated extraction).length = 2 * N + 1 := by
  simp [belowTrialTrace]

theorem belowTrialTrace_exact {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) (extraction : Vec d) :
    ObservationTraceExact oracle (belowTrialTrace oracle y accelerated extraction) := by
  intro observation hobservation
  rw [belowTrialTrace, List.mem_append] at hobservation
  rcases hobservation with hphase | hextraction
  · exact belowPhaseTrace_exact oracle y accelerated observation hphase
  · simp only [List.mem_singleton] at hextraction
    subst observation
    rfl

theorem belowTrialTrace_extraction_queried {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) (extraction : Vec d) :
    extraction ∈
      (belowTrialTrace oracle y accelerated extraction).map Observation.point := by
  apply List.mem_map.mpr
  refine ⟨oracle.observe extraction, ?_, rfl⟩
  simp [belowTrialTrace]

/--
The final scalar budget in TeX lines 729--737.  It is kept independent of the
unavailable vector strong-convexity step: once the three displayed scalar
terms have been derived, their sum is strictly below `eps`.
-/
theorem belowFinalScalarBudget {sigma eps D : ℝ}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (heps : 0 < eps) (hD : 0 < D) :
    belowLambda eps D * D + belowRho sigma eps +
        belowRho sigma eps / sigma < eps := by
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
  have hD_ne : D ≠ 0 := ne_of_gt hD
  rw [belowLambda, belowRho]
  field_simp [hsigma_ne, hD_ne]
  nlinarith

end O3
