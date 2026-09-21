/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import LeanPool.ParameterFreeGradient.O3.Foundation

/-!
# The `2 < p < infinity` branch: exact restart and oracle-count ledger

This module proves the source-exact numerical and finite-trace facts that do
not require the currently unresolved real-exponent `p`-uniform convexity
theorem.  In particular it records the corrected fact that one ceiling per
restart contributes at most the number of restart levels, never
`Delta_0 / delta`.

The public declarations `O3.abovePhase` and `O3.aboveTrial` are not asserted
while `O3.pUniformConvexity` is unavailable.  Their proofs use that theorem to
derive both the estimate-sequence ledger and the restart gap/distance
implication.  This module does not replace it with a target-shaped assumption.
-/

open scoped BigOperators

namespace O3

/-- The genuine-real regime from TeX Section 3. -/
def AboveTwoRegime (p : ℝ) : Prop := 2 < p

/-- The exact trial exponent `2(p-1)/(p+2)`. -/
noncomputable def aboveAlpha (p : ℝ) : ℝ := 2 * (p - 1) / (p + 2)

theorem aboveAlpha_pos {p : ℝ} (hp : AboveTwoRegime p) :
    0 < aboveAlpha p := by
  change 2 < p at hp
  unfold aboveAlpha
  exact div_pos (mul_pos (by norm_num) (by linarith)) (by linarith)

/-- `a_p = 2^(2-p)/p` from the uniform-convexity inequality. -/
noncomputable def aboveAP (p : ℝ) : ℝ := 2 ^ (2 - p) / p

/-- `eta_p = 2^(-p-2)`. -/
noncomputable def aboveEta (p : ℝ) : ℝ := 2 ^ (-p - 2)

/-- `vartheta_p = a_p eta_p`. -/
noncomputable def aboveTheta (p : ℝ) : ℝ := aboveAP p * aboveEta p

theorem aboveAP_pos {p : ℝ} (hp : AboveTwoRegime p) :
    0 < aboveAP p := by
  change 2 < p at hp
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)

theorem aboveEta_pos (p : ℝ) : 0 < aboveEta p := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem aboveTheta_pos {p : ℝ} (hp : AboveTwoRegime p) :
    0 < aboveTheta p := by
  exact mul_pos (aboveAP_pos hp) (aboveEta_pos p)

theorem aboveAP_lt_one {p : ℝ} (hp : AboveTwoRegime p) :
    aboveAP p < 1 := by
  change 2 < p at hp
  have hpow : (2 : ℝ) ^ (2 - p) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [aboveAP, div_lt_one (by linarith)]
  linarith

theorem aboveEta_lt_one {p : ℝ} (hp : AboveTwoRegime p) :
    aboveEta p < 1 := by
  change 2 < p at hp
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem aboveTheta_lt_one {p : ℝ} (hp : AboveTwoRegime p) :
    aboveTheta p < 1 := by
  rw [aboveTheta]
  calc
    aboveAP p * aboveEta p < 1 * aboveEta p :=
      mul_lt_mul_of_pos_right (aboveAP_lt_one hp) (aboveEta_pos p)
    _ < 1 := by simpa using aboveEta_lt_one hp

/-- `gamma = n^((p-2)/p) B^(2-p)`. -/
noncomputable def aboveGamma (p : ℝ) (n : ℕ) (B : ℝ) : ℝ :=
  (n : ℝ) ^ ((p - 2) / p) * B ^ (2 - p)

theorem aboveGamma_pos {p B : ℝ} {n : ℕ}
    (_hp : AboveTwoRegime p) (hn : 1 ≤ n) (hB : 0 < B) :
    0 < aboveGamma p n B := by
  unfold aboveGamma
  exact mul_pos
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)
    (Real.rpow_pos_of_pos hB _)

/-- `a_t=t/M` for a natural iteration index. -/
noncomputable def aboveStepWeight (M : ℝ) (t : ℕ) : ℝ := (t : ℝ) / M

/-- `A_t=t(t+1)/(2M)`. -/
noncomputable def aboveAccumulatedWeight (M : ℝ) (t : ℕ) : ℝ :=
  (t : ℝ) * (t + 1 : ℕ) / (2 * M)

@[simp] theorem aboveAccumulatedWeight_zero (M : ℝ) :
    aboveAccumulatedWeight M 0 = 0 := by
  simp [aboveAccumulatedWeight]

theorem aboveAccumulatedWeight_succ {M : ℝ} (hM : M ≠ 0) (t : ℕ) :
    aboveAccumulatedWeight M (t + 1) =
      aboveAccumulatedWeight M t + aboveStepWeight M (t + 1) := by
  unfold aboveAccumulatedWeight aboveStepWeight
  push_cast
  field_simp [hM]
  ring

theorem aboveAccumulatedWeight_pos {M : ℝ} {t : ℕ}
    (hM : 0 < M) (ht : 1 ≤ t) :
    0 < aboveAccumulatedWeight M t := by
  unfold aboveAccumulatedWeight
  positivity

/-- The source coefficient `c_t=t/(t+1)` and its bound by one. -/
theorem abovePhaseCoefficient_eq {M : ℝ} (hM : M ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    M * (aboveStepWeight M t) ^ 2 /
        (2 * aboveAccumulatedWeight M t) =
      (t : ℝ) / (t + 1 : ℕ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have htsucc0 : (t + 1 : ℝ) ≠ 0 := by positivity
  unfold aboveStepWeight aboveAccumulatedWeight
  push_cast
  field_simp [hM, ht0, htsucc0]

theorem abovePhaseCoefficient_le_one {t : ℕ} :
    (t : ℝ) / (t + 1 : ℕ) ≤ 1 := by
  have hpos : (0 : ℝ) < (t + 1 : ℕ) := by positivity
  rw [div_le_one hpos]
  norm_num

/-- `mu=eta_p eps / D^(p-1)`. -/
noncomputable def aboveMu (p eps D : ℝ) : ℝ :=
  aboveEta p * eps / D ^ (p - 1)

/-- `rho=vartheta_p eps`. -/
noncomputable def aboveRho (p eps : ℝ) : ℝ := aboveTheta p * eps

theorem aboveMu_pos {p eps D : ℝ}
    (_hp : AboveTwoRegime p) (heps : 0 < eps) (hD : 0 < D) :
    0 < aboveMu p eps D := by
  exact div_pos (mul_pos (aboveEta_pos p) heps)
    (Real.rpow_pos_of_pos hD _)

theorem aboveRho_pos {p eps : ℝ}
    (hp : AboveTwoRegime p) (heps : 0 < eps) :
    0 < aboveRho p eps := by
  exact mul_pos (aboveTheta_pos hp) heps

/-- `Delta_0=M D^2`. -/
noncomputable def aboveInitialLevel (M D : ℝ) : ℝ := M * D ^ 2

/-- `Delta_s=2^(-s)Delta_0=Delta_0/2^s`. -/
noncomputable def aboveLevel (Delta0 : ℝ) (s : ℕ) : ℝ :=
  Delta0 / (2 : ℝ) ^ s

/-- `delta=rho^2/(8M)`. -/
noncomputable def aboveTerminalLevel (rho M : ℝ) : ℝ :=
  rho ^ 2 / (8 * M)

theorem aboveInitialLevel_pos {M D : ℝ} (hM : 0 < M) (hD : 0 < D) :
    0 < aboveInitialLevel M D := by
  exact mul_pos hM (sq_pos_of_pos hD)

theorem aboveLevel_pos {Delta0 : ℝ} (hDelta0 : 0 < Delta0) (s : ℕ) :
    0 < aboveLevel Delta0 s := by
  exact div_pos hDelta0 (pow_pos (by norm_num) _)

@[simp] theorem aboveLevel_zero (Delta0 : ℝ) :
    aboveLevel Delta0 0 = Delta0 := by
  simp [aboveLevel]

theorem aboveLevel_succ (Delta0 : ℝ) (s : ℕ) :
    aboveLevel Delta0 (s + 1) = aboveLevel Delta0 s / 2 := by
  unfold aboveLevel
  rw [pow_succ]
  ring

theorem aboveTerminalLevel_pos {rho M : ℝ} (hrho : 0 < rho) (hM : 0 < M) :
    0 < aboveTerminalLevel rho M := by
  exact div_pos (sq_pos_of_pos hrho) (mul_pos (by norm_num) hM)

/-- The source restart count `S = ceil(log_2 (Delta_0/delta))`. -/
noncomputable def aboveRestartCount (Delta0 delta : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (Delta0 / delta))

theorem aboveRestartCount_pos {Delta0 delta : ℝ}
    (hdelta : 0 < delta) (horder : delta < Delta0) :
    0 < aboveRestartCount Delta0 delta := by
  have hratio : 1 < Delta0 / delta := (lt_div_iff₀ hdelta).2 (by simpa)
  have hlog : 0 < Real.logb 2 (Delta0 / delta) :=
    Real.logb_pos (by norm_num) hratio
  exact Nat.ceil_pos.mpr hlog

/-- Exact logarithmic ceiling bound; no `Delta_0/delta` overhead appears. -/
theorem aboveRestartCount_cast_le {Delta0 delta : ℝ}
    (hdelta : 0 < delta) (horder : delta ≤ Delta0) :
    (aboveRestartCount Delta0 delta : ℝ) ≤
      Real.logb 2 (Delta0 / delta) + 1 := by
  have hratio : 1 ≤ Delta0 / delta := (le_div_iff₀ hdelta).2 (by simpa)
  have hlog : 0 ≤ Real.logb 2 (Delta0 / delta) :=
    Real.logb_nonneg (by norm_num) hratio
  exact (Nat.ceil_lt_add_one hlog).le

/-- The ceiling-defined restart count reaches the terminal level. -/
theorem aboveLevel_restartCount_le {Delta0 delta : ℝ}
    (hDelta0 : 0 < Delta0) (hdelta : 0 < delta) :
    aboveLevel Delta0 (aboveRestartCount Delta0 delta) ≤ delta := by
  let ratio := Delta0 / delta
  have hratio : 0 < ratio := div_pos hDelta0 hdelta
  have hlog : Real.logb 2 ratio ≤ (aboveRestartCount Delta0 delta : ℝ) := by
    exact Nat.le_ceil _
  have hratio_pow : ratio ≤ 2 ^ (aboveRestartCount Delta0 delta : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hratio).mp hlog
  rw [Real.rpow_natCast] at hratio_pow
  have hscaled : Delta0 ≤ (2 : ℝ) ^ aboveRestartCount Delta0 delta * delta := by
    calc
      Delta0 = ratio * delta := by
        dsimp [ratio]
        exact (div_mul_cancel₀ Delta0 hdelta.ne').symm
      _ ≤ (2 : ℝ) ^ aboveRestartCount Delta0 delta * delta :=
        mul_le_mul_of_nonneg_right hratio_pow hdelta.le
  unfold aboveLevel
  exact (div_le_iff₀ (pow_pos (by norm_num) _)).2 (by
    simpa [mul_comm] using hscaled)

/--
The restart induction: halving a proved gap at each successful level gives
`gap_s <= Delta_s`.  This is purely the scalar induction after the missing
uniform-convexity and phase-rate steps have produced the halving premise.
-/
theorem aboveRestartGap
    {Delta0 : ℝ} (gap : ℕ → ℝ)
    (hzero : gap 0 ≤ Delta0)
    (hstep : ∀ s, gap (s + 1) ≤ gap s / 2) :
    ∀ s, gap s ≤ aboveLevel Delta0 s := by
  intro s
  induction s with
  | zero => simpa using hzero
  | succ s ih =>
      rw [aboveLevel_succ]
      exact (hstep s).trans (div_le_div_of_nonneg_right ih (by norm_num))

/--
The exact ceiling ledger: one ceiling at each of `S` levels contributes at
most `S` above the corresponding real-valued work.  This is the corrected
overhead in TeX lines 484--492.
-/
theorem aboveCeilingSum_le (S : ℕ) (work : Fin S → ℝ)
    (hwork : ∀ s, 0 ≤ work s) :
    ∑ s, (Nat.ceil (work s) : ℝ) ≤ (∑ s, work s) + S := by
  calc
    ∑ s, (Nat.ceil (work s) : ℝ) ≤ ∑ s, (work s + 1) := by
      apply Finset.sum_le_sum
      intro s _
      exact (Nat.ceil_lt_add_one (hwork s)).le
    _ = (∑ s, work s) + S := by simp [Finset.sum_add_distrib]

/-- Exact finite geometric-sum identity used in the restart count. -/
theorem aboveGeometricSum_eq {c ratio : ℝ} (hratio : ratio ≠ 1) (S : ℕ) :
    ∑ s ∈ Finset.range S, c * ratio ^ s =
      c * ((ratio ^ S - 1) / (ratio - 1)) := by
  rw [← Finset.mul_sum, geom_sum_eq hratio]

/-- For ratio bigger than one, the geometric work is controlled by its end. -/
theorem aboveGeometricSum_le {c ratio : ℝ}
    (hc : 0 ≤ c) (hratio : 1 < ratio) (S : ℕ) :
    ∑ s ∈ Finset.range S, c * ratio ^ s ≤
      c * ratio ^ S / (ratio - 1) := by
  rw [aboveGeometricSum_eq hratio.ne']
  have hden : 0 < ratio - 1 := sub_pos.mpr hratio
  have hpow : 0 ≤ ratio ^ S := pow_nonneg (by linarith) _
  calc
    c * ((ratio ^ S - 1) / (ratio - 1)) =
        c * (ratio ^ S - 1) / (ratio - 1) :=
      (mul_div_assoc c (ratio ^ S - 1) (ratio - 1)).symm
    _ ≤ c * ratio ^ S / (ratio - 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hc) hden.le

/-- `kappa=MD/eps`. -/
noncomputable def aboveKappa (M D eps : ℝ) : ℝ := M * D / eps

/--
The source identity `Delta_0/delta=8 kappa^2/vartheta_p^2`.  It is the exact
input to the logarithmic restart-count statement.
-/
theorem aboveLevelRatio_eq {M D eps theta : ℝ}
    (hM : M ≠ 0) (heps : eps ≠ 0) (htheta : theta ≠ 0) :
    aboveInitialLevel M D /
        aboveTerminalLevel (theta * eps) M =
      8 * (aboveKappa M D eps) ^ 2 / theta ^ 2 := by
  unfold aboveInitialLevel aboveTerminalLevel aboveKappa
  field_simp [hM, heps, htheta]

theorem aboveKappaThetaRatio_gt_one {p kappa : ℝ}
    (hp : AboveTwoRegime p) (hkappa : 1 < kappa) :
    1 < 8 * kappa ^ 2 / (aboveTheta p) ^ 2 := by
  have htheta : 0 < aboveTheta p := aboveTheta_pos hp
  have htheta1 : aboveTheta p < 1 := aboveTheta_lt_one hp
  have htheta_sq : (aboveTheta p) ^ 2 < 1 := by nlinarith [sq_nonneg (aboveTheta p)]
  have hkappa_sq : 1 < kappa ^ 2 := by nlinarith [sq_nonneg kappa]
  rw [lt_div_iff₀ (sq_pos_of_pos htheta)]
  nlinarith

/-- One accelerated iteration contributes its two exact pair observations. -/
def abovePhaseTrace {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) : List (Observation d) :=
  (List.finRange N).flatMap fun i =>
    [oracle.observe (y i), oracle.observe (accelerated i)]

def AboveObservationTraceExact {d : ℕ} (oracle : PairOracle d)
    (trace : List (Observation d)) : Prop :=
  ∀ observation ∈ trace, observation = oracle.observe observation.point

theorem abovePhaseTrace_exact {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    AboveObservationTraceExact oracle (abovePhaseTrace oracle y accelerated) := by
  intro observation hobservation
  rw [abovePhaseTrace, List.mem_flatMap] at hobservation
  obtain ⟨i, _, hi⟩ := hobservation
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

@[simp] theorem abovePhaseTrace_length {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    (abovePhaseTrace oracle y accelerated).length = 2 * N := by
  simp [abovePhaseTrace]
  omega

/--
All restart phases concatenated chronologically.  `horizons s` is the actual
natural iteration count at restart level `s`.
-/
def aboveRestartTrace {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    List (Observation d) :=
  (List.finRange S).flatMap fun s =>
    abovePhaseTrace oracle (y s) (accelerated s)

theorem aboveRestartTrace_exact {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    AboveObservationTraceExact oracle
      (aboveRestartTrace oracle horizons y accelerated) := by
  intro observation hobservation
  rw [aboveRestartTrace, List.mem_flatMap] at hobservation
  obtain ⟨s, _, hs⟩ := hobservation
  exact abovePhaseTrace_exact oracle (y s) (accelerated s) observation hs

@[simp] theorem aboveRestartTrace_length {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    (aboveRestartTrace oracle horizons y accelerated).length =
      ((List.finRange S).map fun s => 2 * horizons s).sum := by
  simp [aboveRestartTrace, abovePhaseTrace, Nat.mul_comm]

/-- Restart phases followed by the single counted extraction query. -/
def aboveTrialTrace {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) : List (Observation d) :=
  aboveRestartTrace oracle horizons y accelerated ++
    [oracle.observe extraction]

theorem aboveTrialTrace_exact {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) :
    AboveObservationTraceExact oracle
      (aboveTrialTrace oracle horizons y accelerated extraction) := by
  intro observation hobservation
  rw [aboveTrialTrace, List.mem_append] at hobservation
  rcases hobservation with hrestart | hextraction
  · exact aboveRestartTrace_exact oracle horizons y accelerated observation hrestart
  · simp only [List.mem_singleton] at hextraction
    subst observation
    rfl

/-- Exact count: two calls per accelerated iteration and one extraction call. -/
theorem aboveTrialTrace_callCount {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) :
    (aboveTrialTrace oracle horizons y accelerated extraction).length =
      ((List.finRange S).map fun s => 2 * horizons s).sum + 1 := by
  simp [aboveTrialTrace, Nat.mul_comm]

theorem aboveTrialTrace_extraction_queried {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d)
    (extraction : Vec d) :
    extraction ∈
      (aboveTrialTrace oracle horizons y accelerated extraction).map
        Observation.point := by
  apply List.mem_map.mpr
  refine ⟨oracle.observe extraction, ?_, rfl⟩
  simp [aboveTrialTrace]

end O3
