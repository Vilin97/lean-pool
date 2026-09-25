/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.ScannedBetheThresholdFeasibility
public import LeanPool.BeyondBethe.BeyondBethe.BetheBisection
public import Mathlib.Tactic

/-!
# Rational bisection for the row-major Bethe oracle

The earlier semantic bisection permits a different choice among violated
floor constraints.  This file follows the implemented row-major oracle
exactly.  Its proof uses only validity and acceptance of that oracle, so the
optimization guarantee is unchanged even though the returned rational point
need not be byte-for-byte equal to the earlier runner's point.
-/

@[expose] public section

namespace BeyondBethe

def scannedBetheBisectionStep {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ)
    (s : BetheBisectionState (m * m + 1)) :
    BetheBisectionState (m * m + 1) :=
  let mid := (s.low + s.high) / 2
  match runExplicitScannedBetheThresholdFeasibility
      tau A p delta (rawRatOfRat mid) r with
  | .accepted q => ⟨s.low, mid, some q⟩
  | .exhausted _ => ⟨mid, s.high, s.witness⟩

def runScannedBetheBisection {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ) :
    ℕ → BetheBisectionState (m * m + 1) →
      BetheBisectionState (m * m + 1)
  | 0, s => s
  | N + 1, s => runScannedBetheBisection tau A p delta r N
      (scannedBetheBisectionStep tau A p delta r s)

def initialScannedBetheBisectionState {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (mix r : ℚ) :
    BetheBisectionState (m * m + 1) :=
  let high := betheBisectionInitialHigh A mix r
  match runExplicitScannedBetheThresholdFeasibility
      tau A p delta (rawRatOfRat high) r with
  | .accepted q => ⟨betheNegativeObjectiveLower m, high, some q⟩
  | .exhausted _ => ⟨betheNegativeObjectiveLower m, high, none⟩

@[simp] theorem initialScannedBetheBisectionState_low {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (mix r : ℚ) :
    (initialScannedBetheBisectionState tau A p delta mix r).low =
      betheNegativeObjectiveLower m := by
  rw [initialScannedBetheBisectionState]
  split <;> rfl

@[simp] theorem initialScannedBetheBisectionState_high {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (mix r : ℚ) :
    (initialScannedBetheBisectionState tau A p delta mix r).high =
      betheBisectionInitialHigh A mix r := by
  rw [initialScannedBetheBisectionState]
  split <;> rfl

def ScannedBetheBisectionWitnessValid {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ)
    (s : BetheBisectionState (m * m + 1)) : Prop :=
  ∀ q, s.witness = some q →
    runExplicitScannedBetheThresholdFeasibility
        tau A p delta (rawRatOfRat s.high) r = .accepted q ∧
      BetheEpigraphOracleAccepted tau A p delta.value s.high q

theorem initialScannedBetheBisectionState_witnessValid {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (mix r : ℚ) :
    ScannedBetheBisectionWitnessValid tau A p delta r
      (initialScannedBetheBisectionState tau A p delta mix r) := by
  intro q hq
  rw [initialScannedBetheBisectionState] at hq ⊢
  split at hq <;> rename_i hrun
  · cases hq
    refine ⟨hrun, ?_⟩
    simpa only [rawRatOfRat_value] using
      runExplicitScannedBetheThresholdFeasibility_acceptsOnly
        tau A p delta _ r hrun
  · contradiction

theorem scannedBetheBisectionStep_witnessValid {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ)
    {s : BetheBisectionState (m * m + 1)}
    (hs : ScannedBetheBisectionWitnessValid tau A p delta r s) :
    ScannedBetheBisectionWitnessValid tau A p delta r
      (scannedBetheBisectionStep tau A p delta r s) := by
  intro q hq
  rw [scannedBetheBisectionStep] at hq ⊢
  split at hq <;> rename_i hrun
  · cases hq
    refine ⟨hrun, ?_⟩
    simpa only [rawRatOfRat_value] using
      runExplicitScannedBetheThresholdFeasibility_acceptsOnly
        tau A p delta _ r hrun
  · exact hs q hq

theorem runScannedBetheBisection_witnessValid {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ)
    {s : BetheBisectionState (m * m + 1)}
    (hs : ScannedBetheBisectionWitnessValid tau A p delta r s) (N : ℕ) :
    ScannedBetheBisectionWitnessValid tau A p delta r
      (runScannedBetheBisection tau A p delta r N s) := by
  induction N generalizing s with
  | zero => simpa [runScannedBetheBisection] using hs
  | succ N ih =>
      rw [runScannedBetheBisection]
      exact ih (scannedBetheBisectionStep_witnessValid tau A p delta r hs)

theorem scannedBetheBisectionStep_width {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ)
    (s : BetheBisectionState (m * m + 1)) :
    (scannedBetheBisectionStep tau A p delta r s).high -
        (scannedBetheBisectionStep tau A p delta r s).low =
      (s.high - s.low) / 2 := by
  rw [scannedBetheBisectionStep]
  split <;> ring

theorem runScannedBetheBisection_width {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ) (N : ℕ)
    (s : BetheBisectionState (m * m + 1)) :
    (runScannedBetheBisection tau A p delta r N s).high -
        (runScannedBetheBisection tau A p delta r N s).low =
      (s.high - s.low) / 2 ^ N := by
  induction N generalizing s with
  | zero => simp [runScannedBetheBisection]
  | succ N ih =>
      rw [runScannedBetheBisection, ih, scannedBetheBisectionStep_width]
      rw [pow_succ]
      ring

theorem scannedBetheBisectionStep_low_le_cutoff {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ) {cutoff : ℝ}
    (hbelow : ∀ (u : ℚ) (E : RationalEllipsoidState (m * m + 1)),
      runExplicitScannedBetheThresholdFeasibility
          tau A p delta (rawRatOfRat u) r = .exhausted E →
        (u : ℝ) < cutoff)
    {s : BetheBisectionState (m * m + 1)}
    (hlow : (s.low : ℝ) ≤ cutoff) :
    ((scannedBetheBisectionStep tau A p delta r s).low : ℚ) ≤
      cutoff := by
  rw [scannedBetheBisectionStep]
  split <;> rename_i hrun
  · exact hlow
  · exact (hbelow _ _ hrun).le

theorem runScannedBetheBisection_low_le_cutoff {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ) {cutoff : ℝ}
    (hbelow : ∀ (u : ℚ) (E : RationalEllipsoidState (m * m + 1)),
      runExplicitScannedBetheThresholdFeasibility
          tau A p delta (rawRatOfRat u) r = .exhausted E →
        (u : ℝ) < cutoff)
    {s : BetheBisectionState (m * m + 1)}
    (hlow : (s.low : ℝ) ≤ cutoff) (N : ℕ) :
    (((runScannedBetheBisection tau A p delta r N s).low : ℚ) : ℝ) ≤
      cutoff := by
  induction N generalizing s with
  | zero => simpa [runScannedBetheBisection] using hlow
  | succ N ih =>
      rw [runScannedBetheBisection]
      exact ih (scannedBetheBisectionStep_low_le_cutoff
        tau A p delta r hbelow hlow)

theorem runScannedBetheBisection_preserves_some {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (delta : RawRat) (r : ℚ)
    {s : BetheBisectionState (m * m + 1)}
    (hsome : ∃ q, s.witness = some q) (N : ℕ) :
    ∃ q, (runScannedBetheBisection tau A p delta r N s).witness = some q := by
  induction N generalizing s with
  | zero => simpa [runScannedBetheBisection] using hsome
  | succ N ih =>
      rw [runScannedBetheBisection]
      apply ih
      rw [scannedBetheBisectionStep]
      split
      · rename_i q hrun
        exact ⟨q, rfl⟩
      · exact hsome

theorem initialScannedBetheBisectionState_has_witness_of_optimizer
    {m : ℕ} (hm : 0 < m) {tau : ℚ} (htau0 : 0 < tau)
    (htau1 : tau ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix r : ℚ} {delta : RawRat}
    (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hdelta : 0 < delta.value) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : delta.value ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) tau)
    (p : ℕ) :
    ∃ q, (initialScannedBetheBisectionState
      tau A p delta mix r).witness = some q := by
  have hupper := (negativeObjective_mem_initial_interval htau0.le htau1
    hApos hAupper hX).2
  have hthreshold :
      -regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤ (betheBisectionInitialHigh A mix r : ℝ) := by
    rw [betheBisectionInitialHigh, betheSmoothingSlack]
    push_cast
    linarith
  have hthreshold' :
      -regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤
        ((rawRatOfRat (betheBisectionInitialHigh A mix r)).value : ℝ) := by
    simpa only [rawRatOfRat_value] using hthreshold
  obtain ⟨q, hrun, _⟩ :=
    runExplicitScannedBetheThresholdFeasibility_accepts_of_slack
      (upper := rawRatOfRat (betheBisectionInitialHigh A mix r))
      hm htau0 htau1 hApos hAupper hX hmax hmix0 hmix1 hdelta hr
        hspike hfloor hthreshold' p
  refine ⟨q, ?_⟩
  rw [initialScannedBetheBisectionState, hrun]

theorem runScannedBetheBisection_objective_gap
    {m : ℕ} (hm : 0 < m) {tau : ℚ} (htau0 : 0 < tau)
    (htau1 : tau ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix r : ℚ} {delta : RawRat}
    (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hdelta : 0 < delta.value) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : delta.value ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) tau)
    (p N : ℕ) :
    let s0 := initialScannedBetheBisectionState tau A p delta mix r
    let sN := runScannedBetheBisection tau A p delta r N s0
    ∃ q : Fin (m * m + 1) → ℚ,
      sN.witness = some q ∧
      BetheEpigraphOracleAccepted tau A p delta.value sN.high q ∧
      IsDoublyStochastic (acceptedBetheMatrix q) ∧
      (∀ i j, (delta.value : ℝ) ≤ acceptedBetheMatrix q i j) ∧
      regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) X -
        regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) (acceptedBetheMatrix q) ≤
        (betheSmoothingSlack A mix r : ℝ) +
          (((betheBisectionInitialHigh A mix r -
              betheNegativeObjectiveLower m) / 2 ^ N : ℚ) : ℝ) +
          (betheObjectiveEvaluationError m p : ℝ) := by
  dsimp only
  let s0 := initialScannedBetheBisectionState tau A p delta mix r
  let sN := runScannedBetheBisection tau A p delta r N s0
  have hsome0 : ∃ q, s0.witness = some q := by
    simpa only [s0] using
      initialScannedBetheBisectionState_has_witness_of_optimizer
        hm htau0 htau1 hApos hAupper hX hmax hmix0 hmix1 hdelta hr
          hspike hfloor p
  obtain ⟨q, hq⟩ := runScannedBetheBisection_preserves_some
    tau A p delta r hsome0 N
  have hqN : sN.witness = some q := by simpa only [sN] using hq
  have hvalid0 := initialScannedBetheBisectionState_witnessValid
    tau A p delta mix r
  have hvalidN := runScannedBetheBisection_witnessValid
    tau A p delta r hvalid0 N
  have hcertificate :
      BetheEpigraphOracleAccepted tau A p delta.value sN.high q :=
    (hvalidN q (by simpa only [sN] using hqN)).2
  have hbounds := negativeObjective_mem_initial_interval htau0.le htau1
    hApos hAupper hX
  let cutoff : ℝ :=
    -regularizedBetheObjective (tau : ℝ)
        (fun i j ↦ (A i j : ℝ)) X +
      (betheSmoothingSlack A mix r : ℝ)
  have hslack0 : 0 ≤ betheSmoothingSlack A mix r := by
    rw [betheSmoothingSlack]
    exact add_nonneg
      (mul_nonneg hmix0.le (rationalRegularizedObjectiveRange_nonneg A))
      (mul_nonneg (by norm_num) hr.le)
  have hlow0 : (s0.low : ℝ) ≤ cutoff := by
    rw [show s0.low = betheNegativeObjectiveLower m by
      simp only [s0, initialScannedBetheBisectionState_low]]
    dsimp only [cutoff]
    have hslack0R : 0 ≤ (betheSmoothingSlack A mix r : ℝ) :=
      Rat.cast_nonneg.mpr hslack0
    linarith [hbounds.1]
  have hbelow : ∀ (u : ℚ) (E : RationalEllipsoidState (m * m + 1)),
      runExplicitScannedBetheThresholdFeasibility
          tau A p delta (rawRatOfRat u) r = .exhausted E →
        (u : ℝ) < cutoff := by
    intro u E hrun
    have h :=
      runExplicitScannedBetheThresholdFeasibility_exhausted_lt_optimum_add_slack
        hm htau0 htau1 hApos hAupper hX hmax hmix0 hmix1 hdelta hr
          hspike hfloor p hrun
    dsimp only [cutoff]
    rw [betheSmoothingSlack]
    push_cast
    simpa [add_assoc] using h
  have hlowN : (sN.low : ℝ) ≤ cutoff := by
    simpa only [sN] using runScannedBetheBisection_low_le_cutoff
      tau A p delta r hbelow hlow0 N
  have hwidthQ := runScannedBetheBisection_width tau A p delta r N s0
  have hwidth : (sN.high : ℝ) - (sN.low : ℝ) =
      (((betheBisectionInitialHigh A mix r -
          betheNegativeObjectiveLower m) / 2 ^ N : ℚ) : ℝ) := by
    have hwidthQ' : sN.high - sN.low =
        (betheBisectionInitialHigh A mix r -
          betheNegativeObjectiveLower m) / 2 ^ N := by
      simpa only [sN, s0, initialScannedBetheBisectionState_high,
        initialScannedBetheBisectionState_low] using hwidthQ
    exact_mod_cast hwidthQ'
  have hhigh : (sN.high : ℝ) ≤ cutoff +
      (((betheBisectionInitialHigh A mix r -
          betheNegativeObjectiveLower m) / 2 ^ N : ℚ) : ℝ) := by
    linarith
  have hobjective :=
    BetheEpigraphOracleAccepted_exact_objective_upper_compact
      hm htau0.le htau1 hApos hdelta hcertificate
  have hheight : ((epigraphHeight q : ℚ) : ℝ) ≤ (sN.high : ℝ) := by
    exact_mod_cast hcertificate.2.1
  have hreturned :
      -regularizedBetheObjective (tau : ℝ)
          (fun i j ↦ (A i j : ℝ)) (acceptedBetheMatrix q) ≤
        (sN.high : ℝ) + (betheObjectiveEvaluationError m p : ℝ) := by
    have hobjective' :
        -regularizedBetheObjective (tau : ℝ)
            (fun i j ↦ (A i j : ℝ)) (acceptedBetheMatrix q) ≤
          ((epigraphHeight q : ℚ) : ℝ) +
            (betheObjectiveEvaluationError m p : ℝ) := by
      simpa only [affineNegativeObjective, acceptedBetheMatrix] using hobjective
    linarith
  refine ⟨q, hqN, hcertificate,
    BetheEpigraphOracleAccepted_doublyStochastic hdelta.le hcertificate,
    BetheEpigraphOracleAccepted_entry_floor hcertificate, ?_⟩
  dsimp only [cutoff] at hhigh
  linarith

end BeyondBethe
