/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — counting bad vertices by Markov's inequality (no union bound)

The corrected nibble route (`LeanPool.AsymptoticTrianglePacking.Internal.RoundOracleKernel`) does not need *every* vertex to behave well
after a round — only all but a small FRACTION of them (the exceptional set of
`LeanPool.AsymptoticTrianglePacking.Internal.CeilRoundInv`).  This is essential: the degree scale `d` is not tied to `|V|`, so a union
bound over the `|V|` vertices of a per-vertex failure probability is unavailable.

What replaces it is Markov's inequality applied to the *number* of bad vertices: if every vertex
fails with probability at most `q`, then the expected number of failures is at most `q|V|`, so the
probability that more than a `δ`-fraction of the vertices fail is at most `q/δ` — a bound that is
small as soon as the per-vertex failure probability `q` is small compared to `δ`, with no dependence
on `|V|` whatsoever.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory Finset
open scoped ProbabilityTheory

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

open scoped Classical in
/-- The number of vertices that are "bad" at the outcome `ω`. -/
noncomputable def badCount (Bad : V → Set Ω) (ω : Ω) : ℝ :=
  ((Finset.univ.filter (fun v => ω ∈ Bad v)).card : ℝ)

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem badCount_nonneg (Bad : V → Set Ω) (ω : Ω) : 0 ≤ badCount Bad ω := by
  classical
  simp [badCount]

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem badCount_eq_sum (Bad : V → Set Ω) (ω : Ω) :
    badCount Bad ω = ∑ v : V, (Set.indicator (Bad v) (fun _ => (1 : ℝ)) ω) := by
  classical
  simp only [badCount, Set.indicator_apply, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => by by_cases h : ω ∈ Bad v <;> simp [h])

theorem integrable_badCount (Bad : V → Set Ω) (hmeas : ∀ v, MeasurableSet (Bad v)) :
    Integrable (badCount Bad) (ℙ : Measure Ω) := by
  classical
  have hrw : badCount Bad
      = fun ω => ∑ v : V, (Set.indicator (Bad v) (fun _ => (1 : ℝ)) ω) :=
    funext (badCount_eq_sum Bad)
  rw [hrw]
  refine integrable_finset_sum _ (fun v _ => ?_)
  exact (integrable_const (1 : ℝ)).indicator (hmeas v)

/-- **The expected number of bad vertices is the sum of the failure probabilities.** -/
theorem integral_badCount (Bad : V → Set Ω) (hmeas : ∀ v, MeasurableSet (Bad v)) :
    ∫ ω, badCount Bad ω ∂(ℙ : Measure Ω) = ∑ v : V, ((ℙ : Measure Ω) (Bad v)).toReal := by
  classical
  have hrw : badCount Bad
      = fun ω => ∑ v : V, (Set.indicator (Bad v) (fun _ => (1 : ℝ)) ω) :=
    funext (badCount_eq_sum Bad)
  rw [show (fun ω => badCount Bad ω) = badCount Bad from rfl, hrw,
    integral_finset_sum _ (fun v _ => (integrable_const (1 : ℝ)).indicator (hmeas v))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) (hmeas v)]
  simp [measureReal_def]

/-- **Markov over the vertices.**  If every vertex is bad with probability at most `q`, then more
than a `δ`-fraction of the vertices are bad with probability at most `q/δ`.  No union bound, and no
dependence on `|V|`. -/
theorem measure_badCount_gt_le (Bad : V → Set Ω) (hmeas : ∀ v, MeasurableSet (Bad v))
    {q δ : ℝ} (hq0 : 0 ≤ q) (hq : ∀ v, ((ℙ : Measure Ω) (Bad v)).toReal ≤ q) (hδ : 0 < δ) :
    ((ℙ : Measure Ω) {ω | δ * (Fintype.card V : ℝ) < badCount Bad ω}).toReal ≤ q / δ := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
  · -- no vertices: the event is empty
    have hempty : {ω : Ω | δ * (Fintype.card V : ℝ) < badCount Bad ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : badCount Bad ω = 0 := by
        have : (Finset.univ.filter (fun v => ω ∈ Bad v)).card ≤ Fintype.card V :=
          Finset.card_le_univ _
        rw [hV] at this
        simp only [badCount, Nat.le_zero] at this ⊢
        exact_mod_cast this
      rw [h1, hV]
      simp
    rw [hempty]
    simpa using div_nonneg hq0 hδ.le
  · have hVR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
    set ε : ℝ := δ * (Fintype.card V : ℝ) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    -- Markov
    have hmarkov : ε * ((ℙ : Measure Ω)).real {ω | ε ≤ badCount Bad ω}
        ≤ ∫ ω, badCount Bad ω ∂(ℙ : Measure Ω) :=
      mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall (fun ω => badCount_nonneg Bad ω))
        (integrable_badCount Bad hmeas) ε
    have hmean : ∫ ω, badCount Bad ω ∂(ℙ : Measure Ω) ≤ q * (Fintype.card V : ℝ) := by
      rw [integral_badCount Bad hmeas]
      calc ∑ v : V, ((ℙ : Measure Ω) (Bad v)).toReal ≤ ∑ _v : V, q :=
            Finset.sum_le_sum (fun v _ => hq v)
        _ = q * (Fintype.card V : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            ring
    have hsubset : {ω : Ω | ε < badCount Bad ω} ⊆ {ω : Ω | ε ≤ badCount Bad ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact le_of_lt hω
    have hmono : ((ℙ : Measure Ω) {ω | ε < badCount Bad ω}).toReal
        ≤ ((ℙ : Measure Ω)).real {ω | ε ≤ badCount Bad ω} := by
      simp only [measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    have hfinal : ε * ((ℙ : Measure Ω) {ω | ε < badCount Bad ω}).toReal
        ≤ q * (Fintype.card V : ℝ) := by
      calc ε * ((ℙ : Measure Ω) {ω | ε < badCount Bad ω}).toReal
          ≤ ε * ((ℙ : Measure Ω)).real {ω | ε ≤ badCount Bad ω} :=
            mul_le_mul_of_nonneg_left hmono hεpos.le
        _ ≤ ∫ ω, badCount Bad ω ∂(ℙ : Measure Ω) := hmarkov
        _ ≤ q * (Fintype.card V : ℝ) := hmean
    rw [le_div_iff₀ hδ]
    have hcancel : δ * ((ℙ : Measure Ω) {ω | ε < badCount Bad ω}).toReal
          * (Fintype.card V : ℝ) ≤ q * (Fintype.card V : ℝ) := by
      calc δ * ((ℙ : Measure Ω) {ω | ε < badCount Bad ω}).toReal * (Fintype.card V : ℝ)
          = ε * ((ℙ : Measure Ω) {ω | ε < badCount Bad ω}).toReal := by rw [hεdef]; ring
        _ ≤ q * (Fintype.card V : ℝ) := hfinal
    have hle := le_of_mul_le_mul_right hcancel hVR
    linarith

end LeanPool.AsymptoticTrianglePacking.Internal
