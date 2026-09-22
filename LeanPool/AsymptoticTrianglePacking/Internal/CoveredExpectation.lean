/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Greedy
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Conflict
import LeanPool.AsymptoticTrianglePacking.Internal.RoundConflict
import LeanPool.AsymptoticTrianglePacking.Internal.Survival
import LeanPool.AsymptoticTrianglePacking.Internal.Covered
import LeanPool.AsymptoticTrianglePacking.Internal.Measurable
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — covered-whp : expected covered-vertex count per
round

Standalone, Mathlib-only. Turns the expected-matching-size bound (`matching_expectation_lower`,
C4b-2) into a statement about the actual matching-size random variable, and links it to the covered
set via `|covered| = r · |matching|` (the round matching is a matching of an `r`-uniform
hypergraph).

* `matchingIndicator` / `matchingSize` — the round matching size as a sum of `{0,1}` indicators.
* `matchingSize_expectation_lower` — `E[|matching|] ≥ |H| · p·(1-p)^{rΔ}`.
* `covered_card_eq` — `|covered R| = r · |roundMatching R|`.

Must be placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Indicator that edge `e` is in the round's matching at outcome `ω`. -/
noncomputable def matchingIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (e : Finset V) (ω : Ω) : ℝ :=
  if e ∈ roundMatching (retainedSet H ρ ω) then 1 else 0

/-- **covered = r·matching.** The covered set of a retained set `R` has `r · |roundMatching R|`
vertices, since the round matching is a matching of the `r`-uniform hypergraph `R`... here stated
for `R ⊆ H` with `H` `r`-uniform. -/
theorem covered_card_eq {H R : Finset (Finset V)} {r : ℕ} (hr : IsUniform H r) (hRH : R ⊆ H) :
    (covered R).card = r * (roundMatching R).card := by
  have hRr : IsUniform R r := fun e he => hr e (hRH he)
  exact matching_support_card hRr (roundMatching_isMatching (le_refl R))

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The matching-membership event equals the survival event of `Survival`. -/
theorem matchingEvent_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {e : Finset V} (he : e ∈ H) :
    {ω | e ∈ roundMatching (retainedSet H ρ ω)}
      = ρ.A e ∩ ⋂ g ∈ conflicts H e, (ρ.A g)ᶜ := by
  ext ω
  have hRsub : retainedSet H ρ ω ⊆ H := Finset.filter_subset _ _
  rw [Set.mem_ofPred_eq, mem_roundMatching_iff_conflicts hRsub]
  simp only [retainedSet, Finset.mem_filter, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨_, hA⟩, hcon⟩
    refine ⟨hA, fun g hg hgA => ?_⟩
    exact hcon g hg ⟨(Finset.mem_filter.mp hg).1, hgA⟩
  · rintro ⟨hA, hcon⟩
    refine ⟨⟨he, hA⟩, fun g hg hgR => ?_⟩
    exact hcon g hg hgR.2

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The matching-membership event is measurable. -/
theorem measurableSet_matchingEvent {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {e : Finset V} (he : e ∈ H) :
    MeasurableSet {ω | e ∈ roundMatching (retainedSet H ρ ω)} := by
  rw [matchingEvent_eq ρ he]
  exact (ρ.meas e).inter
    (MeasurableSet.biInter (conflicts H e).countable_toSet (fun g _ => (ρ.meas g).compl))

/-- Integral of the matching indicator: `∫ 1[e matched] = p·(1-p)^{c(e)}`. -/
theorem integral_matchingIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {e : Finset V} (he : e ∈ H) :
    ∫ ω, matchingIndicator ρ e ω ∂(ℙ : Measure Ω) = p * (1 - p) ^ (conflicts H e).card := by
  have hind : matchingIndicator ρ e
      = Set.indicator {ω | e ∈ roundMatching (retainedSet H ρ ω)} 1 := by
    funext ω; rw [matchingIndicator, Set.indicator_apply]; simp
  rw [hind, integral_indicator_one (measurableSet_matchingEvent ρ he),
    matchingEvent_eq ρ he, measureReal_def, edge_survives_prob ρ hp0 hp1 he,
    ENNReal.toReal_ofReal (mul_nonneg hp0 (pow_nonneg (by linarith) _))]

/-- The matching indicator is integrable (bounded and measurable). -/
theorem matchingIndicator_integrable {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {e : Finset V} (he : e ∈ H) :
    Integrable (matchingIndicator ρ e) (ℙ : Measure Ω) := by
  refine (integrable_const (1 : ℝ)).mono'
    (Measurable.ite (measurableSet_matchingEvent ρ he) measurable_const
      measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [matchingIndicator]; split_ifs <;> simp

/-- **covered-whp — expected matching size lower bound.**
`E[|roundMatching|] ≥ |H| · p·(1-p)^{rΔ}`. Together with `covered_card_eq` this gives
`E[|covered|] ≥ r·|H|·p·(1-p)^{rΔ}`: a definite fraction of vertices is covered per round. -/
theorem matchingSize_expectation_lower {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) :
    (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
      ≤ ∫ ω, ((roundMatching (retainedSet H ρ ω)).card : ℝ) ∂(ℙ : Measure Ω) := by
  have hcard : (fun ω => ((roundMatching (retainedSet H ρ ω)).card : ℝ))
      = fun ω => ∑ e ∈ H, matchingIndicator ρ e ω := by
    funext ω
    simp only [matchingIndicator]
    rw [Finset.sum_boole]
    have hsub : roundMatching (retainedSet H ρ ω) ⊆ H :=
      (roundMatching_subset _).trans (Finset.filter_subset _ _)
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rw [hcard, integral_finsetSum H (fun e he => matchingIndicator_integrable ρ he),
    Finset.sum_congr rfl (fun e he => integral_matchingIndicator ρ hp0 hp1 he)]
  calc (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
      = ∑ _e ∈ H, p * (1 - p) ^ (r * Δ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ e ∈ H, p * (1 - p) ^ (conflicts H e).card := by
        refine Finset.sum_le_sum (fun e he => ?_)
        refine mul_le_mul_of_nonneg_left ?_ hp0
        exact pow_le_pow_of_le_one (by linarith) (by linarith)
          (conflicts_card_le_of_uniform hr hΔ he)

/-- The matching-size random variable is integrable. -/
theorem integrable_matchingSize {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) :
    Integrable (fun ω => ((roundMatching (retainedSet H ρ ω)).card : ℝ)) (ℙ : Measure Ω) := by
  have hcard : (fun ω => ((roundMatching (retainedSet H ρ ω)).card : ℝ))
      = fun ω => ∑ e ∈ H, matchingIndicator ρ e ω := by
    funext ω
    simp only [matchingIndicator]
    rw [Finset.sum_boole]
    have hsub : roundMatching (retainedSet H ρ ω) ⊆ H :=
      (roundMatching_subset _).trans (Finset.filter_subset _ _)
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rw [hcard]
  exact integrable_finsetSum H (fun e he => matchingIndicator_integrable ρ he)

/-- **D3 (one-round existence) — probabilistic method.** There is an outcome whose round matching
has at least `|H|·p·(1-p)^{rΔ}` edges; hence a covered set of `≥ r·|H|·p·(1-p)^{rΔ}` vertices. This
is the single-round Rödl-nibble lower bound (the iterated `(1-β)` near-perfect version is the
capstone T3). -/
theorem exists_large_round_matching {H : Finset (Finset V)} {p : ℝ} {r Δ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hΔ : ∀ x, degree H x ≤ Δ) :
    ∃ ω, (H.card : ℝ) * (p * (1 - p) ^ (r * Δ))
      ≤ ((roundMatching (retainedSet H ρ ω)).card : ℝ) := by
  obtain ⟨ω, hω⟩ := exists_integral_le (integrable_matchingSize ρ)
  exact ⟨ω, le_trans (matchingSize_expectation_lower ρ hp0 hp1 hr hΔ) hω⟩

end LeanPool.AsymptoticTrianglePacking.Internal
