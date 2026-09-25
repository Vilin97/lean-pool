/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Conflict
public import LeanPool.AsymptoticTrianglePacking.Internal.Survival
public import LeanPool.AsymptoticTrianglePacking.Internal.Covered
public import LeanPool.AsymptoticTrianglePacking.Internal.CoveredExpectation
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverProb
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the joint matching probability of TWO edges

The variance of the safe degree (`LeanPool.AsymptoticTrianglePacking.Internal.safeDegree`) is
controlled by the *covariance* of the
covering events of two vertices, and the cancellation that makes that covariance small requires the
exact joint law of two edges entering the round matching:

* two edges that meet can never both be matched (`prob_two_matched_of_not_disjoint`);
* two disjoint edges `f, g` are both matched exactly when both are retained and no edge of
  `conflicts f ∪ conflicts g` is retained, an event of probability
  `p²(1−p)^{|conflicts f ∪ conflicts g|}` (`prob_two_matched_disjoint`);
* since `|A ∪ B| = |A| + |B| − |A ∩ B|` and `1 − (1−p)^k ≤ kp`, this differs from the *product*
  `p(1−p)^{c(f)} · p(1−p)^{c(g)}` of the two individual matching probabilities by at most
  `|conflicts f ∩ conflicts g|·p³` (`prob_two_matched_le`).

The last statement is the quantitative brick: summed over the edges at two distinct vertices, the
error carries a factor of the CODEGREE
(`LeanPool.AsymptoticTrianglePacking.Internal.sum_conflicts_inter_card_le`), which is what makes
the nibble's residual degrees concentrate.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- **The general retention pattern probability.**  For disjoint families `T, C ⊆ H`, the event
that every edge of `T` is retained and no edge of `C` is has probability `p^|T|·(1−p)^|C|`. -/
theorem prob_retain_avoid {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T C : Finset (Finset V)} (hT : T ⊆ H) (hC : C ⊆ H) (hTC : Disjoint T C) :
    (ℙ : Measure Ω) ((⋂ e ∈ T, ρ.A e) ∩ ⋂ h ∈ C, (ρ.A h)ᶜ)
      = ENNReal.ofReal (p ^ T.card * (1 - p) ^ C.card) := by
  classical
  have hpc : ∀ h ∈ C, (ℙ : Measure Ω) ((ρ.A h)ᶜ) = ENNReal.ofReal (1 - p) := by
    intro h hh
    have hp := ρ.prob h (hC hh)
    rw [measure_compl (ρ.meas h), hp]
    · rw [ENNReal.sub_eq_of_eq_add ENNReal.ofReal_ne_top]
      rw [← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ 1 - p) hp0]
      simp
    · exact hp ▸ ENNReal.ofReal_ne_top
  set S : Finset (Finset V) := T ∪ C with hS
  set G : Finset V → Set Ω := fun e => if e ∈ T then ρ.A e else (ρ.A e)ᶜ with hG
  have hinter : ⋂ e ∈ S, G e = (⋂ e ∈ T, ρ.A e) ∩ ⋂ h ∈ C, (ρ.A h)ᶜ := by
    ext ω
    simp only [hS, hG, Set.mem_iInter, Finset.mem_union, Set.mem_inter_iff]
    constructor
    · intro hall
      refine ⟨fun e he => ?_, fun h hh => ?_⟩
      · have := hall e (Or.inl he); simpa [he] using this
      · have hnT : h ∉ T := fun hx => (Finset.disjoint_left.mp hTC hx) hh
        have := hall h (Or.inr hh); simpa [hnT] using this
    · rintro ⟨h1, h2⟩ e he
      by_cases hT' : e ∈ T
      · simpa [hT'] using h1 e hT'
      · simp only [hT', ite_false]
        exact h2 e (he.resolve_left hT')
  rw [← hinter]
  have hindeps := ρ.indep S (f := fun i => G i) (by
    intro i _
    simp only [hG]
    by_cases hi : i ∈ T
    · simp only [hi, ite_true]
      exact MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
    · simp only [hi, ite_false]
      exact (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl)
  rw [ae_iff] at hindeps
  have hindeps' : (ℙ : Measure Ω) (⋂ e ∈ S, G e) = ∏ e ∈ S, (ℙ : Measure Ω) (G e) := by
    simpa using hindeps
  rw [hindeps', hS, Finset.prod_union hTC]
  have h1 : ∏ e ∈ T, (ℙ : Measure Ω) (G e) = ENNReal.ofReal p ^ T.card := by
    rw [Finset.prod_congr rfl (fun e he => by
      simp only [hG, he, ite_true]; exact ρ.prob e (hT he))]
    simp
  have h2 : ∏ e ∈ C, (ℙ : Measure Ω) (G e) = ENNReal.ofReal (1 - p) ^ C.card := by
    rw [Finset.prod_congr rfl (fun e he => by
      have hnT : e ∉ T := fun hx => (Finset.disjoint_left.mp hTC hx) he
      simp only [hG, hnT, ite_false]; exact hpc e he)]
    simp
  rw [h1, h2, ← ENNReal.ofReal_pow hp0, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ 1 - p),
    ← ENNReal.ofReal_mul (by positivity)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Two intersecting edges are never both in the round matching. -/
theorem prob_two_matched_of_not_disjoint {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {f g : Finset V} (hne : f ≠ g)
    (hmeet : ¬ Disjoint f g) :
    ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
        ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)}) = (∅ : Set Ω) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hf hg
  exact hmeet ((roundMatching_isMatching (subset_refl (retainedSet H ρ ω))).disjoint f hf g hg hne)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- **The joint matching event of two edges.**  Both `f` and `g` are matched exactly when
both are retained and nothing in `conflicts f ∪ conflicts g` is. -/
theorem twoMatchedEvent_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {f g : Finset V} (hf : f ∈ H) (hg : g ∈ H) :
    ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
        ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)})
      = (ρ.A f ∩ ρ.A g) ∩ ⋂ h ∈ (conflicts H f ∪ conflicts H g), (ρ.A h)ᶜ := by
  rw [matchingEvent_eq ρ hf, matchingEvent_eq ρ hg]
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union, Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨h1, h3⟩, fun h hh => hh.elim (h2 h) (h4 h)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, fun h hh => h3 h (Or.inl hh)⟩, ⟨h2, fun h hh => h3 h (Or.inr hh)⟩⟩

/-- **The joint matching probability of two disjoint edges.** -/
theorem prob_two_matched_disjoint {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset V} (hf : f ∈ H) (hg : g ∈ H) (hne : f ≠ g) (hdisj : Disjoint f g) :
    (ℙ : Measure Ω) ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
        ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)})
      = ENNReal.ofReal (p ^ 2 * (1 - p) ^ (conflicts H f ∪ conflicts H g).card) := by
  classical
  rw [twoMatchedEvent_eq ρ hf hg]
  have hpair : (ρ.A f ∩ ρ.A g) = ⋂ e ∈ ({f, g} : Finset (Finset V)), ρ.A e := by
    ext ω; simp [Finset.mem_insert]
  have hcard : ({f, g} : Finset (Finset V)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hTsub : ({f, g} : Finset (Finset V)) ⊆ H := by
    intro e he; rcases Finset.mem_insert.mp he with h | h
    · exact h ▸ hf
    · exact (Finset.mem_singleton.mp h) ▸ hg
  have hCsub : (conflicts H f ∪ conflicts H g) ⊆ H := by
    intro e he
    rcases Finset.mem_union.mp he with h | h <;> exact (Finset.mem_filter.mp h).1
  have hTC : Disjoint ({f, g} : Finset (Finset V)) (conflicts H f ∪ conflicts H g) := by
    rw [Finset.disjoint_left]
    intro e he hc
    have hfg : (f ∩ g) = (∅ : Finset V) := Finset.disjoint_iff_inter_eq_empty.mp hdisj
    rcases Finset.mem_insert.mp he with rfl | h
    · rcases Finset.mem_union.mp hc with h | h
      · exact (Finset.mem_filter.mp h).2.1 rfl
      · obtain ⟨_, _, hx⟩ := Finset.mem_filter.mp h
        rw [Finset.inter_comm] at hx
        exact (Finset.not_nonempty_empty (hfg ▸ hx))
    · have hef : e = g := Finset.mem_singleton.mp h
      subst hef
      rcases Finset.mem_union.mp hc with h | h
      · obtain ⟨_, _, hx⟩ := Finset.mem_filter.mp h
        exact (Finset.not_nonempty_empty (hfg ▸ hx))
      · exact (Finset.mem_filter.mp h).2.1 rfl
  rw [hpair, prob_retain_avoid ρ hp0 hp1 hTsub hCsub hTC, hcard]

/-- **The joint matching probability against the product of the individual ones.**  The two differ
by at most `|conflicts f ∩ conflicts g|·p³` — the brick that produces the codegree factor in the
variance of the safe degree. -/
theorem prob_two_matched_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset V} (hf : f ∈ H) (hg : g ∈ H) (hne : f ≠ g) :
    (ℙ : Measure Ω).real ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
        ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)})
      ≤ (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card)
        + ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3 := by
  classical
  have hq0 : (0:ℝ) ≤ 1 - p := by linarith only [hp1]
  have hrhs0 : 0 ≤ (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card) := by
    positivity
  have hrhs1 : 0 ≤ ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3 := by positivity
  by_cases hdisj : Disjoint f g
  · rw [measureReal_def, prob_two_matched_disjoint ρ hp0 hp1 hf hg hne hdisj,
      ENNReal.toReal_ofReal (by positivity)]
    set a := (conflicts H f).card
    set b := (conflicts H g).card
    set u := (conflicts H f ∪ conflicts H g).card
    set k := (conflicts H f ∩ conflicts H g).card
    have hsum : u + k = a + b := Finset.card_union_add_card_inter _ _
    have hab : ((1:ℝ) - p) ^ a * (1 - p) ^ b = (1 - p) ^ u * (1 - p) ^ k := by
      rw [← pow_add, ← pow_add, hsum]
    have hsplit : (p * (1 - p) ^ a) * (p * (1 - p) ^ b)
        = p ^ 2 * (1 - p) ^ u * (1 - p) ^ k := by
      rw [show (p * (1 - p) ^ a) * (p * (1 - p) ^ b) = p ^ 2 * ((1 - p) ^ a * (1 - p) ^ b) by ring,
        hab]; ring
    rw [hsplit]
    -- p²(1-p)^u ≤ p²(1-p)^u(1-p)^k + k p³
    have hbern : 1 - (k : ℝ) * p ≤ (1 - p) ^ k := by
      have := one_add_mul_le_pow (a := -p) (by linarith) k
      simpa [sub_eq_add_neg, mul_comm] using this
    have hpu : p ^ 2 * (1 - p) ^ u ≤ p ^ 2 := by
      nlinarith only [pow_le_one₀ hq0 (by linarith : (1:ℝ) - p ≤ 1) (n := u), sq_nonneg p,
        pow_nonneg hq0 u]
    have hpu0 : 0 ≤ p ^ 2 * (1 - p) ^ u := by positivity
    nlinarith [pow_nonneg hq0 k, mul_nonneg hpu0 (sub_nonneg.mpr hbern)]
  · rw [prob_two_matched_of_not_disjoint ρ hne hdisj]
    simp only [measureReal_empty]
    linarith only [hrhs0, hrhs1]

end LeanPool.AsymptoticTrianglePacking.Internal
