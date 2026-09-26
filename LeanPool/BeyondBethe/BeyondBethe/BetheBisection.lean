/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.BetheThresholdFeasibility
public import Mathlib.Tactic

/-! # Bethe Bisection -/

@[expose] public section

namespace BeyondBethe

/-!
# Rational bisection for the regularized Bethe objective

The bisection uses only the concrete threshold feasibility runner.  An
accepted midpoint becomes the new upper endpoint and carries its rational
witness.  An exhausted midpoint becomes the new lower endpoint.  Correctness
uses the proved implication that exhaustion can occur only below the exact
optimum plus the explicit smoothing slack.
-/

/-- The initial lower threshold `-2 * (m + 1)^2` for the negative Bethe objective. -/
def betheNegativeObjectiveLower (m : ℕ) : ℚ :=
  -(2 * (m + 1) ^ 2)

/-- The negative-objective upper threshold obtained from the dimension and matrix entry bit
bound. -/
def betheNegativeObjectiveUpper {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) : ℚ :=
  (m + 1) * rationalMatrixEntryBitBound A + (m + 1)

/-- The smoothing allowance: the mixing weight times the objective range, plus twice the inner
radius. -/
def betheSmoothingSlack {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (mix r : ℚ) : ℚ :=
  mix * rationalRegularizedObjectiveRange A + 2 * r

/-- The initial upper bisection threshold, including the smoothing allowance. -/
def betheBisectionInitialHigh {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (mix r : ℚ) : ℚ :=
  betheNegativeObjectiveUpper A + betheSmoothingSlack A mix r

theorem negativeObjective_mem_initial_interval
    {m : ℕ} {τ : ℚ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X) :
    (betheNegativeObjectiveLower m : ℝ) ≤
        -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X ∧
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X ≤
        (betheNegativeObjectiveUpper A : ℝ) := by
  have h := negativeRegularizedBetheObjective_rational_bounds
    (n := m + 1) (by omega) hτ0 hτ1 hApos hAupper hX
  norm_num [betheNegativeObjectiveLower, betheNegativeObjectiveUpper] at h ⊢
  exact h

/-- Executable state of the rational bisection. -/
structure BetheBisectionState (d : ℕ) where
  /-- The current lower objective threshold of the bisection interval. -/
  low : ℚ
  /-- The current upper objective threshold of the bisection interval. -/
  high : ℚ
  /-- The stored accepted feasibility point, if one has been found. -/
  witness : Option (Fin d → ℚ)

/-- One bisection step. -/
def betheBisectionStep {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) (s : BetheBisectionState (m * m + 1)) :
    BetheBisectionState (m * m + 1) :=
  let mid := (s.low + s.high) / 2
  match runBetheThresholdFeasibility τ A p δ mid r with
  | .accepted q => ⟨s.low, mid, some q⟩
  | .exhausted _ => ⟨mid, s.high, s.witness⟩

/-- Iterate the bisection a prescribed number of times. -/
def runBetheBisection {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) :
    ℕ → BetheBisectionState (m * m + 1) →
      BetheBisectionState (m * m + 1)
  | 0, s => s
  | N + 1, s => runBetheBisection τ A p δ r N
      (betheBisectionStep τ A p δ r s)

/-- Initialize by querying the explicit global upper endpoint. -/
def initialBetheBisectionState {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ mix r : ℚ) : BetheBisectionState (m * m + 1) :=
  let high := betheBisectionInitialHigh A mix r
  match runBetheThresholdFeasibility τ A p δ high r with
  | .accepted q => ⟨betheNegativeObjectiveLower m, high, some q⟩
  | .exhausted _ => ⟨betheNegativeObjectiveLower m, high, none⟩

@[simp] theorem initialBetheBisectionState_low {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ mix r : ℚ) :
    (initialBetheBisectionState τ A p δ mix r).low =
      betheNegativeObjectiveLower m := by
  rw [initialBetheBisectionState]
  split <;> rfl

@[simp] theorem initialBetheBisectionState_high {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ mix r : ℚ) :
    (initialBetheBisectionState τ A p δ mix r).high =
      betheBisectionInitialHigh A mix r := by
  rw [initialBetheBisectionState]
  split <;> rfl

/-- A stored witness is certified by an actual accepted run at the state's
current upper endpoint. -/
def BetheBisectionWitnessValid {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) (s : BetheBisectionState (m * m + 1)) : Prop :=
  ∀ q, s.witness = some q →
    runBetheThresholdFeasibility τ A p δ s.high r = .accepted q ∧
      BetheEpigraphOracleAccepted τ A p δ s.high q

theorem initialBetheBisectionState_witnessValid {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ mix r : ℚ) :
    BetheBisectionWitnessValid τ A p δ r
      (initialBetheBisectionState τ A p δ mix r) := by
  intro q hq
  rw [initialBetheBisectionState] at hq ⊢
  split at hq <;> rename_i hrun
  · cases hq
    exact ⟨hrun, runBetheThresholdFeasibility_acceptsOnly
      τ A p δ _ r hrun⟩
  · contradiction

theorem betheBisectionStep_witnessValid {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) {s : BetheBisectionState (m * m + 1)}
    (hs : BetheBisectionWitnessValid τ A p δ r s) :
    BetheBisectionWitnessValid τ A p δ r
      (betheBisectionStep τ A p δ r s) := by
  intro q hq
  rw [betheBisectionStep] at hq ⊢
  split at hq <;> rename_i hrun
  · cases hq
    exact ⟨hrun, runBetheThresholdFeasibility_acceptsOnly
      τ A p δ _ r hrun⟩
  · exact hs q hq

theorem runBetheBisection_witnessValid {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) {s : BetheBisectionState (m * m + 1)}
    (hs : BetheBisectionWitnessValid τ A p δ r s) (N : ℕ) :
    BetheBisectionWitnessValid τ A p δ r
      (runBetheBisection τ A p δ r N s) := by
  induction N generalizing s with
  | zero => simpa [runBetheBisection] using hs
  | succ N ih =>
      rw [runBetheBisection]
      exact ih (betheBisectionStep_witnessValid τ A p δ r hs)

/-- Every step halves the rational interval width exactly. -/
theorem betheBisectionStep_width {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) (s : BetheBisectionState (m * m + 1)) :
    (betheBisectionStep τ A p δ r s).high -
        (betheBisectionStep τ A p δ r s).low =
      (s.high - s.low) / 2 := by
  rw [betheBisectionStep]
  split <;> ring

theorem runBetheBisection_width {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) (N : ℕ)
    (s : BetheBisectionState (m * m + 1)) :
    (runBetheBisection τ A p δ r N s).high -
        (runBetheBisection τ A p δ r N s).low =
      (s.high - s.low) / 2 ^ N := by
  induction N generalizing s with
  | zero => simp [runBetheBisection]
  | succ N ih =>
      rw [runBetheBisection, ih, betheBisectionStep_width]
      rw [pow_succ]
      ring

/-- If every exhausted query lies below `cutoff`, a bisection step preserves
the invariant that the lower endpoint is at most `cutoff`. -/
theorem betheBisectionStep_low_le_cutoff {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) {cutoff : ℝ}
    (hbelow : ∀ (u : ℚ) (E : RationalEllipsoidState (m * m + 1)),
      runBetheThresholdFeasibility τ A p δ u r = .exhausted E →
        (u : ℝ) < cutoff)
    {s : BetheBisectionState (m * m + 1)}
    (hlow : (s.low : ℝ) ≤ cutoff) :
    ((betheBisectionStep τ A p δ r s).low : ℚ) ≤ cutoff := by
  rw [betheBisectionStep]
  split <;> rename_i hrun
  · exact hlow
  · exact (hbelow _ _ hrun).le

theorem runBetheBisection_low_le_cutoff {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) {cutoff : ℝ}
    (hbelow : ∀ (u : ℚ) (E : RationalEllipsoidState (m * m + 1)),
      runBetheThresholdFeasibility τ A p δ u r = .exhausted E →
        (u : ℝ) < cutoff)
    {s : BetheBisectionState (m * m + 1)}
    (hlow : (s.low : ℝ) ≤ cutoff) (N : ℕ) :
    (((runBetheBisection τ A p δ r N s).low : ℚ) : ℝ) ≤ cutoff := by
  induction N generalizing s with
  | zero => simpa [runBetheBisection] using hlow
  | succ N ih =>
      rw [runBetheBisection]
      exact ih (betheBisectionStep_low_le_cutoff τ A p δ r hbelow hlow)

/-- Once a witness exists, every later state still carries one. -/
theorem runBetheBisection_preserves_some {m : ℕ}
    (τ : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (p : ℕ) (δ r : ℚ) {s : BetheBisectionState (m * m + 1)}
    (hsome : ∃ q, s.witness = some q) (N : ℕ) :
    ∃ q, (runBetheBisection τ A p δ r N s).witness = some q := by
  induction N generalizing s with
  | zero => simpa [runBetheBisection] using hsome
  | succ N ih =>
      rw [runBetheBisection]
      apply ih
      rw [betheBisectionStep]
      split
      · rename_i q hrun
        exact ⟨q, rfl⟩
      · exact hsome

/-- The explicit global upper endpoint is guaranteed to initialize the
bisection with an accepted witness. -/
theorem initialBetheBisectionState_has_witness_of_optimizer
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix δ r : ℚ} (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hδ : 0 < δ) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : δ ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) τ)
    (p : ℕ) :
    ∃ q, (initialBetheBisectionState τ A p δ mix r).witness = some q := by
  have hupper := (negativeObjective_mem_initial_interval hτ0.le hτ1
    hApos hAupper hX).2
  have hthreshold :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X +
        (mix : ℝ) * (rationalRegularizedObjectiveRange A : ℝ) +
          2 * (r : ℝ) ≤ (betheBisectionInitialHigh A mix r : ℝ) := by
    rw [betheBisectionInitialHigh, betheSmoothingSlack]
    push_cast
    linarith
  obtain ⟨q, hrun, _⟩ := runBetheThresholdFeasibility_accepts_of_slack
    hm hτ0 hτ1 hApos hAupper hX hmax hmix0 hmix1 hδ hr
      hspike hfloor hthreshold p
  refine ⟨q, ?_⟩
  rw [initialBetheBisectionState, hrun]

/-- Complete semantic guarantee of executable bisection: it returns a
rational interior doubly stochastic matrix whose regularized objective gap
is the sum of the smoothing slack, the exact dyadic interval width, and the
directed-evaluation loss. -/
theorem runBetheBisection_objective_gap
    {m : ℕ} (hm : 0 < m) {τ : ℚ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hApos : ∀ i j, 0 < A i j) (hAupper : ∀ i j, A i j ≤ 1)
    {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) Y ≤
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X)
    {mix δ r : ℚ} (hmix0 : 0 < mix) (hmix1 : mix ≤ 1)
    (hδ : 0 < δ) (hr : 0 < r)
    (hspike : r / mix ≤ 1 / (m + 1 : ℚ))
    (hfloor : δ ≤ (1 - mix) *
      numericalInteriorFloor (m + 1) (rationalMatrixEntryBitBound A) τ)
    (p N : ℕ) :
    let s0 := initialBetheBisectionState τ A p δ mix r
    let sN := runBetheBisection τ A p δ r N s0
    ∃ q : Fin (m * m + 1) → ℚ,
      sN.witness = some q ∧
      BetheEpigraphOracleAccepted τ A p δ sN.high q ∧
      IsDoublyStochastic (acceptedBetheMatrix q) ∧
      (∀ i j, (δ : ℝ) ≤ acceptedBetheMatrix q i j) ∧
      regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) X -
        regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) (acceptedBetheMatrix q) ≤
        (betheSmoothingSlack A mix r : ℝ) +
          (((betheBisectionInitialHigh A mix r -
              betheNegativeObjectiveLower m) / 2 ^ N : ℚ) : ℝ) +
          (betheObjectiveEvaluationError m p : ℝ) := by
  dsimp only
  let s0 := initialBetheBisectionState τ A p δ mix r
  let sN := runBetheBisection τ A p δ r N s0
  have hsome0 : ∃ q, s0.witness = some q := by
    simpa only [s0] using initialBetheBisectionState_has_witness_of_optimizer
      hm hτ0 hτ1 hApos hAupper hX hmax hmix0 hmix1 hδ hr
        hspike hfloor p
  obtain ⟨q, hq⟩ := runBetheBisection_preserves_some
    τ A p δ r hsome0 N
  have hqN : sN.witness = some q := by simpa only [sN] using hq
  have hvalid0 := initialBetheBisectionState_witnessValid
    τ A p δ mix r
  have hvalidN := runBetheBisection_witnessValid
    τ A p δ r hvalid0 N
  have hcertificate : BetheEpigraphOracleAccepted τ A p δ sN.high q := by
    exact (hvalidN q (by simpa only [sN] using hqN)).2
  have hbounds := negativeObjective_mem_initial_interval hτ0.le hτ1
    hApos hAupper hX
  let cutoff : ℝ :=
    -regularizedBetheObjective (τ : ℝ)
        (fun i j ↦ (A i j : ℝ)) X +
      (betheSmoothingSlack A mix r : ℝ)
  have hslack0 : 0 ≤ betheSmoothingSlack A mix r := by
    rw [betheSmoothingSlack]
    exact add_nonneg
      (mul_nonneg hmix0.le (rationalRegularizedObjectiveRange_nonneg A))
      (mul_nonneg (by norm_num) hr.le)
  have hlow0 : (s0.low : ℝ) ≤ cutoff := by
    rw [show s0.low = betheNegativeObjectiveLower m by
      simp only [s0, initialBetheBisectionState_low]]
    dsimp only [cutoff]
    have hslack0R : 0 ≤ (betheSmoothingSlack A mix r : ℝ) :=
      Rat.cast_nonneg.mpr hslack0
    linarith [hbounds.1]
  have hbelow : ∀ (u : ℚ) (E : RationalEllipsoidState (m * m + 1)),
      runBetheThresholdFeasibility τ A p δ u r = .exhausted E →
        (u : ℝ) < cutoff := by
    intro u E hrun
    have h := runBetheThresholdFeasibility_exhausted_lt_optimum_add_slack
      hm hτ0 hτ1 hApos hAupper hX hmax hmix0 hmix1 hδ hr
        hspike hfloor p hrun
    dsimp only [cutoff]
    rw [betheSmoothingSlack]
    push_cast
    simpa [add_assoc] using h
  have hlowN : (sN.low : ℝ) ≤ cutoff := by
    simpa only [sN] using runBetheBisection_low_le_cutoff
      τ A p δ r hbelow hlow0 N
  have hwidthQ := runBetheBisection_width τ A p δ r N s0
  have hwidth : (sN.high : ℝ) - (sN.low : ℝ) =
      (((betheBisectionInitialHigh A mix r -
          betheNegativeObjectiveLower m) / 2 ^ N : ℚ) : ℝ) := by
    have hwidthQ' : sN.high - sN.low =
        (betheBisectionInitialHigh A mix r -
          betheNegativeObjectiveLower m) / 2 ^ N := by
      simpa only [sN, s0, initialBetheBisectionState_high,
        initialBetheBisectionState_low] using hwidthQ
    exact_mod_cast hwidthQ'
  have hhigh : (sN.high : ℝ) ≤ cutoff +
      (((betheBisectionInitialHigh A mix r -
          betheNegativeObjectiveLower m) / 2 ^ N : ℚ) : ℝ) := by
    linarith
  have hobjective :=
    BetheEpigraphOracleAccepted_exact_objective_upper_compact
      hm hτ0.le hτ1 hApos hδ hcertificate
  have hheight : ((epigraphHeight q : ℚ) : ℝ) ≤ (sN.high : ℝ) := by
    exact_mod_cast hcertificate.2.1
  have hreturned :
      -regularizedBetheObjective (τ : ℝ)
          (fun i j ↦ (A i j : ℝ)) (acceptedBetheMatrix q) ≤
        (sN.high : ℝ) + (betheObjectiveEvaluationError m p : ℝ) := by
    have hobjective' :
        -regularizedBetheObjective (τ : ℝ)
            (fun i j ↦ (A i j : ℝ)) (acceptedBetheMatrix q) ≤
          ((epigraphHeight q : ℚ) : ℝ) +
            (betheObjectiveEvaluationError m p : ℝ) := by
      simpa only [affineNegativeObjective, acceptedBetheMatrix] using hobjective
    linarith
  refine ⟨q, hqN, hcertificate,
    BetheEpigraphOracleAccepted_doublyStochastic hδ.le hcertificate,
    BetheEpigraphOracleAccepted_entry_floor hcertificate, ?_⟩
  dsimp only [cutoff] at hhigh
  linarith

end BeyondBethe
