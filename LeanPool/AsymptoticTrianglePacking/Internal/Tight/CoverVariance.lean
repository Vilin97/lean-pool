/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import LeanPool.AsymptoticTrianglePacking.Internal.Conflict
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import LeanPool.AsymptoticTrianglePacking.Internal.Round
public import LeanPool.AsymptoticTrianglePacking.Internal.Survival
public import LeanPool.AsymptoticTrianglePacking.Internal.Covered
public import LeanPool.AsymptoticTrianglePacking.Internal.CoveredExpectation
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverProb



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

public section

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

end



/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the conflict-overlap count at two distinct vertices

Pure `Finset` combinatorics, no probability.  The variance estimate for the safe degree needs the
following triple count: summing, over the edges `f` through `u` and the edges `g` through a
DIFFERENT
vertex `u'`, the number of edges conflicting with both, one gets a bound carrying a factor of the
CODEGREE `κ`:

  `∑_{f ∋ u} ∑_{g ∋ u'} |conflicts f ∩ conflicts g| ≤ 4 r² κ Δ²`.

(The corresponding statement at `u = u'` is false — there the sum is of order `Δ³` — which is
exactly
why the residual degree of a vertex does not concentrate while its SAFE degree does.)

Proof.  Writing `S = ∑_{h ∈ H} a(h)·b(h)` with `a(h) = #{f ∋ u : h ∈ conflicts f}` and
`b(h) = #{g ∋ u' : h ∈ conflicts g}` (`conflictCountAt`), split on whether `u' ∈ h`:

* `∑_{h ∈ H} a(h) = ∑_{f ∋ u} |conflicts f| ≤ Δ·rΔ`;
* for `u' ∉ h`, every `g ∋ u'` meeting `h` does so at a vertex `w ≠ u'`, so `b(h) ≤ r·κ`;
* for `u' ∈ h` and `u ∈ h` there are at most `codeg(u,u') ≤ κ` such `h`, and `a(h), b(h) ≤ Δ`;
* for `u' ∈ h` and `u ∉ h` there are at most `deg(u') ≤ Δ` such `h`, `a(h) ≤ rκ` and `b(h) ≤ Δ`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open Finset Hypergraph

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V]

/-- The number of edges through `x` that conflict with a given edge `h`. -/
def conflictCountAt (H : Finset (Finset V)) (x : V) (h : Finset V) : ℕ :=
  ((H.filter (fun f => x ∈ f)).filter (fun f => h ∈ conflicts H f)).card

/-- `conflictCountAt` is bounded by the degree of `x`. -/
theorem conflictCountAt_le_degree (H : Finset (Finset V)) (x : V) (h : Finset V) :
    conflictCountAt H x h ≤ degree H x :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- If `x ∉ h`, then every edge through `x` conflicting with `h` meets `h` at a vertex `≠ x`, so
`conflictCountAt` is bounded by a sum of codegrees. -/
theorem conflictCountAt_le_sum_codegree (H : Finset (Finset V)) {x : V} {h : Finset V} :
    conflictCountAt H x h ≤ ∑ w ∈ h, codegree H x w := by
  classical
  have hsub : ((H.filter (fun f => x ∈ f)).filter (fun f => h ∈ conflicts H f))
      ⊆ h.biUnion (fun w => H.filter (fun f => x ∈ f ∧ w ∈ f)) := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_filter] at hf
    obtain ⟨⟨hfH, hxf⟩, hconf⟩ := hf
    obtain ⟨_, _, w, hw⟩ := Finset.mem_filter.mp hconf
    rw [Finset.mem_inter] at hw
    exact Finset.mem_biUnion.mpr ⟨w, hw.2, Finset.mem_filter.mpr ⟨hfH, hxf, hw.1⟩⟩
  calc conflictCountAt H x h ≤ (h.biUnion (fun w => H.filter (fun f => x ∈ f ∧ w ∈ f))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w ∈ h, (H.filter (fun f => x ∈ f ∧ w ∈ f)).card := Finset.card_biUnion_le
    _ = ∑ w ∈ h, codegree H x w := rfl

/-- With uniformity and a codegree bound: if `x ∉ h`, then `conflictCountAt H x h ≤ r·κ`. -/
theorem conflictCountAt_le_of_notMem {H : Finset (Finset V)} {r κ : ℕ} (hr : IsUniform H r)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) {x : V} {h : Finset V} (hh : h ∈ H)
    (hxh : x ∉ h) : conflictCountAt H x h ≤ r * κ := by
  calc conflictCountAt H x h ≤ ∑ w ∈ h, codegree H x w := conflictCountAt_le_sum_codegree H
    _ ≤ ∑ _w ∈ h, κ := Finset.sum_le_sum (fun w hw => hκ x w (fun hxw => hxh (hxw ▸ hw)))
    _ = r * κ := by rw [Finset.sum_const, smul_eq_mul, hr h hh]

/-- Double counting: summing `conflictCountAt H x ·` over all edges gives the total conflict count
of the edges through `x`. -/
theorem sum_conflictCountAt (H : Finset (Finset V)) (x : V) :
    ∑ h ∈ H, conflictCountAt H x h
      = ∑ f ∈ H.filter (fun f => x ∈ f), (conflicts H f).card := by
  classical
  simp only [conflictCountAt, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  ext h
  simp only [Finset.mem_filter]
  exact ⟨fun hh => hh.2, fun hh => ⟨(Finset.mem_filter.mp hh).1, hh⟩⟩

/-- The total conflict count of the edges through `x` is at most `Δ·rΔ`. -/
theorem sum_conflictCountAt_le {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y, degree H y ≤ Δ) (x : V) :
    ∑ h ∈ H, conflictCountAt H x h ≤ Δ * (r * Δ) := by
  classical
  rw [sum_conflictCountAt]
  calc ∑ f ∈ H.filter (fun f => x ∈ f), (conflicts H f).card
      ≤ ∑ _f ∈ H.filter (fun f => x ∈ f), r * Δ :=
        Finset.sum_le_sum (fun f hf =>
          conflicts_card_le_of_uniform hr hΔ (Finset.mem_filter.mp hf).1)
    _ = degree H x * (r * Δ) := by rw [Finset.sum_const, smul_eq_mul, degree]
    _ ≤ Δ * (r * Δ) := Nat.mul_le_mul_right _ (hΔ x)

/-- The double sum of conflict overlaps, written as a single sum over edges. -/
theorem sum_sum_conflicts_inter_eq (H : Finset (Finset V)) (u u' : V) :
    ∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
        (conflicts H f ∩ conflicts H g).card
      = ∑ h ∈ H, conflictCountAt H u h * conflictCountAt H u' h := by
  classical
  set A := H.filter (fun f => u ∈ f) with hA
  set B := H.filter (fun g => u' ∈ g) with hB
  have key : ∀ f g : Finset V, (conflicts H f ∩ conflicts H g).card
      = ∑ h ∈ H, (if h ∈ conflicts H f then 1 else 0) * (if h ∈ conflicts H g then 1 else 0) := by
    intro f g
    have hset : conflicts H f ∩ conflicts H g
        = H.filter (fun h => h ∈ conflicts H f ∧ h ∈ conflicts H g) := by
      ext h
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun hh => ⟨(Finset.mem_filter.mp hh.1).1, hh.1, hh.2⟩, fun hh => ⟨hh.2.1, hh.2.2⟩⟩
    rw [hset, Finset.card_filter]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases h1 : h ∈ conflicts H f <;> by_cases h2 : h ∈ conflicts H g <;> simp [h1, h2]
  simp only [key]
  rw [Finset.sum_congr rfl (fun f (_ : f ∈ A) => Finset.sum_comm
    (s := B) (t := H)
    (f := fun g h => (if h ∈ conflicts H f then 1 else 0) *
      (if h ∈ conflicts H g then 1 else 0))), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [conflictCountAt, conflictCountAt, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_mul_sum]

/-- **The conflict-overlap count at two DISTINCT vertices.** `∑_{f ∋ u} ∑_{g ∋ u'} |conf f ∩ conf g|
≤ 4 r² κ Δ²`, where `Δ` bounds the degrees and `κ` the codegrees of distinct pairs. -/
theorem sum_conflicts_inter_card_le {H : Finset (Finset V)} {r Δ κ : ℕ}
    (hr : IsUniform H r) (hr1 : 1 ≤ r) (hΔ : ∀ x, degree H x ≤ Δ)
    (hκ : ∀ x y : V, x ≠ y → codegree H x y ≤ κ)
    {u u' : V} (huu' : u ≠ u') :
    ∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
        (conflicts H f ∩ conflicts H g).card ≤ 4 * r ^ 2 * κ * Δ ^ 2 := by
  classical
  rw [sum_sum_conflicts_inter_eq]
  set a : Finset V → ℕ := fun h => conflictCountAt H u h with ha
  set b : Finset V → ℕ := fun h => conflictCountAt H u' h with hb
  -- split on whether `u' ∈ h`
  rw [← Finset.sum_filter_add_sum_filter_not H (fun h => u' ∈ h)]
  have hfar : ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * b h ≤ r ^ 2 * κ * Δ ^ 2 := by
    calc ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * b h
        ≤ ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * (r * κ) :=
          Finset.sum_le_sum (fun h hh => Nat.mul_le_mul_left _
            (conflictCountAt_le_of_notMem hr hκ (Finset.mem_filter.mp hh).1
              (Finset.mem_filter.mp hh).2))
      _ = (∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h) * (r * κ) := by rw [Finset.sum_mul]
      _ ≤ (∑ h ∈ H, a h) * (r * κ) := Nat.mul_le_mul_right _
          (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ ≤ (Δ * (r * Δ)) * (r * κ) := Nat.mul_le_mul_right _ (sum_conflictCountAt_le hr hΔ u)
      _ = r ^ 2 * κ * Δ ^ 2 := by ring
  have hnear : ∑ h ∈ H.filter (fun h => u' ∈ h), a h * b h ≤ κ * Δ ^ 2 + r * κ * Δ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (H.filter (fun h => u' ∈ h)) (fun h => u ∈ h)]
    have h1 : ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h), a h * b h
        ≤ κ * Δ ^ 2 := by
      calc ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h), a h * b h
          ≤ ∑ _h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h), Δ * Δ :=
            Finset.sum_le_sum (fun h _ => Nat.mul_le_mul
              (conflictCountAt_le_degree H u h |>.trans (hΔ u))
              (conflictCountAt_le_degree H u' h |>.trans (hΔ u')))
        _ = ((H.filter (fun h => u' ∈ h)).filter (fun h => u ∈ h)).card * (Δ * Δ) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ κ * (Δ * Δ) := by
            refine Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (hκ u u' huu'))
            rw [codegree]
            congr 1
            ext h
            simp only [Finset.mem_filter]
            tauto
        _ = κ * Δ ^ 2 := by ring
    have h2 : ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h), a h * b h
        ≤ r * κ * Δ ^ 2 := by
      calc ∑ h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h), a h * b h
          ≤ ∑ _h ∈ (H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h), (r * κ) * Δ :=
            Finset.sum_le_sum (fun h hh => Nat.mul_le_mul
              (conflictCountAt_le_of_notMem hr hκ
                (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
                (Finset.mem_filter.mp hh).2)
              (conflictCountAt_le_degree H u' h |>.trans (hΔ u')))
        _ = ((H.filter (fun h => u' ∈ h)).filter (fun h => ¬ u ∈ h)).card * ((r * κ) * Δ) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Δ * ((r * κ) * Δ) := by
            refine Nat.mul_le_mul_right _ ?_
            exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (hΔ u')
        _ = r * κ * Δ ^ 2 := by ring
    exact Nat.add_le_add h1 h2
  have h1 : κ * Δ ^ 2 ≤ r ^ 2 * κ * Δ ^ 2 := by
    have hp : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr1
    calc κ * Δ ^ 2 = 1 * (κ * Δ ^ 2) := by ring
      _ ≤ r ^ 2 * (κ * Δ ^ 2) := Nat.mul_le_mul_right _ hp
      _ = r ^ 2 * κ * Δ ^ 2 := by ring
  have h2 : r * κ * Δ ^ 2 ≤ r ^ 2 * κ * Δ ^ 2 := by
    have hp : r ≤ r ^ 2 := by nlinarith only []
    calc r * κ * Δ ^ 2 = r * (κ * Δ ^ 2) := by ring
      _ ≤ r ^ 2 * (κ * Δ ^ 2) := Nat.mul_le_mul_right _ hp
      _ = r ^ 2 * κ * Δ ^ 2 := by ring
  calc ∑ h ∈ H.filter (fun h => u' ∈ h), a h * b h
        + ∑ h ∈ H.filter (fun h => ¬ u' ∈ h), a h * b h
      ≤ (κ * Δ ^ 2 + r * κ * Δ ^ 2) + r ^ 2 * κ * Δ ^ 2 := Nat.add_le_add hnear hfar
    _ ≤ (r ^ 2 * κ * Δ ^ 2 + r ^ 2 * κ * Δ ^ 2) + r ^ 2 * κ * Δ ^ 2 :=
        Nat.add_le_add_right (Nat.add_le_add h1 h2) _
    _ = 3 * (r ^ 2 * κ * Δ ^ 2) := by ring
    _ ≤ 4 * (r ^ 2 * κ * Δ ^ 2) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * r ^ 2 * κ * Δ ^ 2 := by ring

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the CODEGREE-tightened pair excess and loss variance

`LeanPool.AsymptoticTrianglePacking.Internal.pair_excess_le` bounds the pair excess

  `ℙ(u, u' covered) − q_u q_{u'}  ≤  2 r Δ³ p³ + κ p`

by trading the crude product bound `deg(u)·deg(u')·p²` against the exact rates.  Its `Δ³p³` term is
too lossy for the nibble: fed into
`LeanPool.AsymptoticTrianglePacking.Internal.centered_second_moment_le` it contributes
`(r−1)²Δ² · 2rΔ³p³ ≈ Δ² γ³` to the variance of the loss weight (with `p = γ/((r−1)Δ)`), i.e. a
standard deviation of order `γ^{3/2}Δ`, whose Chebyshev failure probability at the natural scale
`t = ξγΔ` is `≈ γ/ξ²` — of the same order as the per-round covering rate `≈ γ`, hence useless for
an exceptional set that must be a *small* fraction of the coverage.

This file replaces that term by a CODEGREE-controlled one:

  `ℙ(u, u' covered) − q_u q_{u'}  ≤  κ p + 4 r² κ Δ² p³`     (`pair_excess_le_codegree`)

for distinct `u, u'`.  The proof is the exact edge-pair decomposition, not a union bound:

* `{u covered} ∩ {u' covered} = ⋃_{f ∋ u} ⋃_{g ∋ u'} (M_f ∩ M_g)` with `M_f` the event that `f`
  enters the round matching;
* for `f ≠ g` the joint matching probability differs from the product `q_f q_g` by at most
  `|conflicts f ∩ conflicts g|·p³`
  (`LeanPool.AsymptoticTrianglePacking.Internal.prob_two_matched_le` — zero when `f` and `g` meet);
* the diagonal `f = g` occurs for at most `codeg(u,u') ≤ κ` edges, each contributing at most `p`;
* `LeanPool.AsymptoticTrianglePacking.Internal.sum_conflicts_inter_card_le` sums the conflict
  overlaps to `4 r² κ Δ²`.

Consequently (`centered_second_moment_le_codegree`)

  `𝔼[(loss − 𝔼loss)²] ≤ κ·(r−1)Δ·(Δp) + (κp + 4r²κΔ²p³)·((r−1)Δ)²`,

which in the nibble regime `p = γ/((r−1)Δ)`, `κ = μΔ` is `O(r μ γ Δ²)` — a factor `μ` (the relative
codegree, which the nibble hypothesis lets us choose as small as we like) below the previous
`O(rγ³Δ²/(r−1))`, and it is the bound whose Chebyshev failure probability at scale `t = ξγΔ` is
`O(rμ/(ξ²γ))`, i.e. arbitrarily small compared with the covering rate `γ`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [Fintype V] in
/-- The matching event of a single edge has probability `p·(1−p)^{c(e)}`. -/
theorem prob_matchingEvent {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {e : Finset V} (he : e ∈ H) :
    (ℙ : Measure Ω).real {ω | e ∈ roundMatching (retainedSet H ρ ω)}
      = p * (1 - p) ^ (conflicts H e).card := by
  rw [measureReal_def, matchingEvent_eq ρ he, edge_survives_prob ρ hp0 hp1 he,
    ENNReal.toReal_ofReal (mul_nonneg hp0 (pow_nonneg (by linarith) _))]

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The joint covering event of two vertices is the union of the joint matching events of the edge
pairs through them. -/
theorem twoCovered_eq_biUnion {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u u' : V) :
    ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      = ⋃ f ∈ H.filter (fun f => u ∈ f), ⋃ g ∈ H.filter (fun g => u' ∈ g),
          ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
            ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)}) := by
  rw [vertexCovered_eq_biUnion ρ u, vertexCovered_eq_biUnion ρ u']
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨⟨f, hf, hfω⟩, ⟨g, hg, hgω⟩⟩
    exact ⟨f, hf, g, hg, hfω, hgω⟩
  · rintro ⟨f, hf, g, hg, hfω, hgω⟩
    exact ⟨⟨f, hf, hfω⟩, ⟨g, hg, hgω⟩⟩

omit [Fintype V] in
/-- **The codegree-tightened joint covering bound.**  For distinct `u, u'`,
`ℙ(u,u' covered) ≤ q_u q_{u'} + codeg(u,u')·p + (∑_{f ∋ u} ∑_{g ∋ u'} |conf f ∩ conf g|)·p³`. -/
theorem prob_two_vertices_covered_le_sum {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u u' : V) :
    (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ coverRate H p u * coverRate H p u' + (codegree H u u' : ℝ) * p
        + (∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
            ((conflicts H f ∩ conflicts H g).card : ℝ)) * p ^ 3 := by
  classical
  set Su := H.filter (fun f => u ∈ f) with hSu
  set Su' := H.filter (fun g => u' ∈ g) with hSu'
  -- term-by-term bound on the joint matching probabilities
  have hterm : ∀ f ∈ Su, ∀ g ∈ Su',
      (ℙ : Measure Ω).real ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
          ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)})
        ≤ (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card)
          + (if f = g then p else 0)
          + ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3 := by
    intro f hf g hg
    have hfH : f ∈ H := (Finset.mem_filter.mp hf).1
    have hgH : g ∈ H := (Finset.mem_filter.mp hg).1
    by_cases hfg : f = g
    · subst hfg
      have hself : ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
          ∩ {ω | f ∈ roundMatching (retainedSet H ρ ω)})
          = {ω | f ∈ roundMatching (retainedSet H ρ ω)} := Set.inter_self _
      rw [hself, prob_matchingEvent ρ hp0 hp1 hfH, ite_eq_left rfl]
      have h1 : p * (1 - p) ^ (conflicts H f).card ≤ p := by
        have : (1 - p) ^ (conflicts H f).card ≤ 1 :=
          pow_le_one₀ (by linarith) (by linarith)
        nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 - p) (conflicts H f).card]
      have h2 : 0 ≤ (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H f).card) :=
        mul_nonneg (mul_nonneg hp0 (pow_nonneg (by linarith) _))
          (mul_nonneg hp0 (pow_nonneg (by linarith) _))
      have h3 : 0 ≤ ((conflicts H f ∩ conflicts H f).card : ℝ) * p ^ 3 :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 3)
      linarith
    · rw [ite_eq_right hfg]
      have := prob_two_matched_le ρ hp0 hp1 hfH hgH hfg
      linarith
  -- sum the bounds
  have hmeas : (ℙ : Measure Ω).real
      ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ ∑ f ∈ Su, ∑ g ∈ Su', (ℙ : Measure Ω).real
          ({ω | f ∈ roundMatching (retainedSet H ρ ω)}
            ∩ {ω | g ∈ roundMatching (retainedSet H ρ ω)}) := by
    rw [twoCovered_eq_biUnion ρ u u']
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    exact Finset.sum_le_sum (fun f _ => measureReal_biUnion_finset_le _ _)
  refine le_trans hmeas ?_
  refine le_trans (Finset.sum_le_sum (fun f hf => Finset.sum_le_sum (fun g hg =>
    hterm f hf g hg))) ?_
  -- split the three contributions
  have hsplit : ∑ f ∈ Su, ∑ g ∈ Su',
        ((p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card)
          + (if f = g then p else 0)
          + ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3)
      = (∑ f ∈ Su, ∑ g ∈ Su',
            (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card))
        + (∑ f ∈ Su, ∑ g ∈ Su', (if f = g then p else 0))
        + (∑ f ∈ Su, ∑ g ∈ Su', ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun f _ => by rw [← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib])
  rw [hsplit]
  have h1 : (∑ f ∈ Su, ∑ g ∈ Su',
        (p * (1 - p) ^ (conflicts H f).card) * (p * (1 - p) ^ (conflicts H g).card))
      = coverRate H p u * coverRate H p u' := by
    rw [coverRate, coverRate, ← hSu, ← hSu', Finset.sum_mul_sum]
  have h2 : (∑ f ∈ Su, ∑ g ∈ Su', (if f = g then p else 0)) = (codegree H u u' : ℝ) * p := by
    have hin : ∀ f ∈ Su, (∑ g ∈ Su', (if f = g then p else 0))
        = if f ∈ Su' then p else 0 := by
      intro f _
      by_cases hf' : f ∈ Su'
      · rw [Finset.sum_ite_eq Su' f (fun _ => p), ite_eq_left hf']
      · rw [ite_eq_right hf']
        refine Finset.sum_eq_zero (fun g hg => ?_)
        rw [ite_eq_right (fun h => hf' (by rw [h]; exact hg))]
    rw [Finset.sum_congr rfl hin, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hcard : (Su ∩ Su').card = codegree H u u' := by
      have hset : Su ∩ Su' = H.filter (fun e => u ∈ e ∧ u' ∈ e) := by
        rw [hSu, hSu']
        ext e
        simp only [Finset.mem_inter, Finset.mem_filter]
        tauto
      rw [hset]; rfl
    rw [hcard]
  have h3 : (∑ f ∈ Su, ∑ g ∈ Su', ((conflicts H f ∩ conflicts H g).card : ℝ) * p ^ 3)
      = (∑ f ∈ Su, ∑ g ∈ Su', ((conflicts H f ∩ conflicts H g).card : ℝ)) * p ^ 3 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun f _ => by rw [Finset.sum_mul])
  rw [h1, h2, h3]

omit [Fintype V] in
/-- **The codegree-tightened pair excess.**  For distinct `u, u'`,

  `ℙ(u,u' covered) − q_u q_{u'} ≤ κ p + 4 r² κ Δ² p³`.

Both summands carry the codegree bound `κ`; in the nibble regime `κ = μΔ`, `p = γ/((r−1)Δ)` this is
`O(rμγ/(r−1))`, whereas `LeanPool.AsymptoticTrianglePacking.Internal.pair_excess_le` gives only
`O(rγ³/(r−1)³ + μγ/(r−1))`. -/
theorem pair_excess_le_codegree {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : IsUniform H r) (hr1 : 1 ≤ r) (hΔ : ∀ y, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) {u u' : V} (huu' : u ≠ u') :
    (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u'
      ≤ (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 := by
  classical
  have hmain := prob_two_vertices_covered_le_sum ρ hp0 hp1 u u'
  have hcod : ((codegree H u u' : ℕ) : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ u u' huu'
  have hcodp : (codegree H u u' : ℝ) * p ≤ (κ : ℝ) * p := mul_le_mul_of_nonneg_right hcod hp0
  have hsumnat := sum_conflicts_inter_card_le hr hr1 hΔ hκ huu'
  have hsum : (∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
      ((conflicts H f ∩ conflicts H g).card : ℝ))
      ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by
    have hcast : (∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
        ((conflicts H f ∩ conflicts H g).card : ℝ))
        = ((∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
            (conflicts H f ∩ conflicts H g).card : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast]
    have := (Nat.cast_le (α := ℝ)).mpr hsumnat
    calc ((∑ f ∈ H.filter (fun f => u ∈ f), ∑ g ∈ H.filter (fun g => u' ∈ g),
          (conflicts H f ∩ conflicts H g).card : ℕ) : ℝ)
        ≤ ((4 * r ^ 2 * κ * Δ ^ 2 : ℕ) : ℝ) := this
      _ = 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by push_cast; ring
  have hp3 : (0 : ℝ) ≤ p ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_right hsum hp3
  linarith

/-- **The codegree-tightened variance of the loss weight.**

  `𝔼[(loss − 𝔼loss)²] ≤ κ·(r−1)Δ·(Δp) + (κp + 4r²κΔ²p³)·((r−1)Δ)²`.

Compare `LeanPool.AsymptoticTrianglePacking.Internal.centered_second_moment_le_params`, whose second
factor is `Δ²p² + κp`: the term
`Δ²p²` (of order `γ²` with `p = γ/((r−1)Δ)`) is replaced by `4r²κΔ²p³` (of order `r²μγ³`), so the
whole bound acquires the codegree factor `κ`. -/
theorem centered_second_moment_le_codegree {H : Finset (Finset V)} {p : ℝ} {r Δ κ : ℕ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr1 : 1 ≤ r)
    (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω)
      ≤ (κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p)
        + ((κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3)
          * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := by
  classical
  set εp : ℝ := (κ : ℝ) * p + 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 with hεp
  have hε0 : 0 ≤ εp := by
    have h1 : (0 : ℝ) ≤ (κ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
    have h2 : (0 : ℝ) ≤ 4 * (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 * p ^ 3 :=
      mul_nonneg (by positivity) (pow_nonneg hp0 3)
    rw [hεp]; linarith
  have hq : ∀ x : V, coverRate H p x ≤ (Δ : ℝ) * p := by
    intro x
    refine le_trans (coverRate_le hp0 hp1 x) ?_
    have : (degree H x : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ x
    exact mul_le_mul_of_nonneg_right this hp0
  have hpair : ∀ x y : V, x ≠ y →
      (ℙ : Measure Ω).real ({ω | x ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | y ∈ covered (retainedSet H ρ ω)})
        - coverRate H p x * coverRate H p y ≤ εp := by
    intro x y hxy
    exact pair_excess_le_codegree ρ hp0 hp1 hr hr1 hΔ hκ hxy
  have hκv : ∀ x : V, x ≠ v → codegree H v x ≤ κ := fun x hx => hκ v x (fun h => hx h.symm)
  have hmain := centered_second_moment_le ρ hp0 hp1 v hκv hq hε0 hpair
  have hsum : ∑ x ∈ (Finset.univ : Finset V).erase v, (codegree H v x : ℝ)
      = ((r : ℝ) - 1) * (degree H v : ℝ) := by
    have h := sum_codegree_erase_eq hr v
    have hcast : ((∑ x ∈ (Finset.univ : Finset V).erase v, codegree H v x : ℕ) : ℝ)
        = ∑ x ∈ (Finset.univ : Finset V).erase v, (codegree H v x : ℝ) := by push_cast; ring
    rw [← hcast, h]
    push_cast [Nat.cast_sub hr1]
    ring
  rw [hsum] at hmain
  refine le_trans hmain ?_
  have hdv : (degree H v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  have hdv0 : (0 : ℝ) ≤ (degree H v : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  have hA : ((r : ℝ) - 1) * (degree H v : ℝ) ≤ ((r : ℝ) - 1) * (Δ : ℝ) :=
    mul_le_mul_of_nonneg_left hdv hr0
  have hA0 : (0 : ℝ) ≤ ((r : ℝ) - 1) * (degree H v : ℝ) := mul_nonneg hr0 hdv0
  have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := Nat.cast_nonneg _
  have hqhi0 : (0 : ℝ) ≤ (Δ : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsq : (((r : ℝ) - 1) * (degree H v : ℝ)) ^ 2 ≤ (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hA0 hA 2
  have ht1 : (κ : ℝ) * (((r : ℝ) - 1) * (degree H v : ℝ)) * ((Δ : ℝ) * p)
      ≤ (κ : ℝ) * (((r : ℝ) - 1) * (Δ : ℝ)) * ((Δ : ℝ) * p) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hκ0) hqhi0
  have ht2 : εp * (((r : ℝ) - 1) * (degree H v : ℝ)) ^ 2
      ≤ εp * (((r : ℝ) - 1) * (Δ : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hsq hε0
  rw [hεp] at ht2 ⊢
  linarith

end LeanPool.AsymptoticTrianglePacking.Internal

end


/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the VARIANCE of the covered count, and Chebyshev for
the coverage

`LeanPool.AsymptoticTrianglePacking.Internal.exists_tight_round_on` controls the coverage of a
nibble round by MARKOV applied to the
number of *uncovered* vertices.  That is extremely lossy: it only gives

  `ℙ(covered ≤ N·q/2) ≤ 1 − q/2`,

so the competing badness event has to have probability `< q/2 ≈ γ/2`, and the Markov bound on the
badness then forces the deviation tolerances `t, s` to be of the same order as the whole per-round
degree drop `γΔ` — a band far too wide to be iterated over `≍ γ^{-1}log(1/β)` rounds.

This file removes that bottleneck.  The covered count `Cov = ∑_v 1[v covered]` is a sum of
indicators whose pair covariances are exactly the pair excesses controlled by
`LeanPool.AsymptoticTrianglePacking.Internal.pair_excess_le_codegree`, so

  `Var(Cov) ≤ N·q_hi + N²·ε₂`,     (`coveredCount_variance_le`)

with `ε₂` the (codegree-controlled) pair excess.  Chebyshev then gives a coverage failure
probability `≤ 4·Var/Q²`, which in the nibble regime `Q ≈ Nγ`, `ε₂ ≈ μγ` is

  `4/(Nγ) + 4μ/γ`,

i.e. `≤ 1/2` as soon as `N ≥ 16/γ` and `μ ≤ γ/16` — INDEPENDENTLY of the deviation tolerances.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The centred covered count is the sum of the centred covering indicators. -/
theorem coveredCount_sub_mean_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (ω : Ω) :
    ((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v
      = ∑ v : V, coverIndC ρ v ω := by
  rw [coveredCount_eq_sum ρ ω, ← Finset.sum_sub_distrib]
  rfl

/-- The centred covered count is square integrable. -/
theorem integrable_sq_centered_coveredCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) :
    Integrable (fun ω => (((covered (retainedSet H ρ ω)).card : ℝ)
      - ∑ v : V, coverRate H p v) ^ 2) (ℙ : Measure Ω) := by
  have hexp : (fun ω => (((covered (retainedSet H ρ ω)).card : ℝ)
        - ∑ v : V, coverRate H p v) ^ 2)
      = fun ω => ∑ u : V, ∑ u' : V, coverIndC ρ u ω * coverIndC ρ u' ω := by
    funext ω
    rw [coveredCount_sub_mean_eq ρ ω, sq, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _
    (fun u _ => integrable_finsetSum _ (fun u' _ => integrable_coverIndC_mul ρ u u'))

/-- **The variance of the covered count, as an exact double sum of pair excesses.** -/
theorem integral_sq_centered_coveredCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω)
      = ∑ u : V, ∑ u' : V,
          ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
              ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
            - coverRate H p u * coverRate H p u') := by
  have hexp : ∀ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
      = ∑ u : V, ∑ u' : V, coverIndC ρ u ω * coverIndC ρ u' ω := by
    intro ω
    rw [coveredCount_sub_mean_eq ρ ω, sq, Finset.sum_mul_sum]
  simp only [hexp]
  rw [integral_finsetSum _
    (fun u _ => integrable_finsetSum _ (fun u' _ => integrable_coverIndC_mul ρ u u'))]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [integral_finsetSum _ (fun u' _ => integrable_coverIndC_mul ρ u u')]
  exact Finset.sum_congr rfl (fun u' _ => integral_coverIndC_mul ρ hp0 hp1 u u')

/-- **The variance bound for the covered count.**  With covering rates at most `q_hi` and pair
excesses at most `ε₂`, the covered count has variance at most `N·q_hi + N²·ε₂`. -/
theorem coveredCount_variance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {qhi ε₂ : ℝ} (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂) :
    ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω)
      ≤ (Fintype.card V : ℝ) * qhi + (Fintype.card V : ℝ) ^ 2 * ε₂ := by
  classical
  rw [integral_sq_centered_coveredCount ρ hp0 hp1]
  have hterm : ∀ u : V, ∀ u' : V,
      ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u')
      ≤ (if u = u' then qhi else 0) + ε₂ := by
    intro u u'
    by_cases huu' : u = u'
    · subst huu'
      have hself : ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u ∈ covered (retainedSet H ρ ω)}) = {ω | u ∈ covered (retainedSet H ρ ω)} :=
        Set.inter_self _
      rw [hself, prob_vertex_covered_eq ρ hp0 hp1 u, ite_eq_left rfl]
      have hqu0 : 0 ≤ coverRate H p u := coverRate_nonneg hp0 hp1 u
      nlinarith [hq u, mul_nonneg hqu0 hqu0]
    · rw [ite_eq_right huu']
      linarith only [hpair u u' huu']
  calc ∑ u : V, ∑ u' : V,
        ((ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
            ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
          - coverRate H p u * coverRate H p u')
      ≤ ∑ u : V, ∑ u' : V, ((if u = u' then qhi else 0) + ε₂) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun u' _ => hterm u u'))
    _ = (Fintype.card V : ℝ) * qhi + (Fintype.card V : ℝ) ^ 2 * ε₂ := by
        have hinner : ∀ u : V, ∑ u' : V, ((if u = u' then qhi else 0) + ε₂)
            = qhi + (Fintype.card V : ℝ) * ε₂ := by
          intro u
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          congr 1
          rw [Finset.sum_ite_eq (Finset.univ : Finset V) u (fun _ => qhi),
            ite_eq_left (Finset.mem_univ u)]
        rw [Finset.sum_congr rfl (fun u _ => hinner u), Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ]
        ring

/-- **Chebyshev for the coverage.**  If the mean coverage is at least `Q > 0` and the variance is at
most `Cvar`, the probability that the covered count deviates by `Q/2` or more is at most
`Cvar/(Q/2)²`. -/
theorem prob_coverage_deviation_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {Q Cvar : ℝ} (hQ : 0 < Q)
    (hvar : ∫ ω, (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2
        ∂(ℙ : Measure Ω) ≤ Cvar) :
    (ℙ : Measure Ω).real
        {ω | (Q / 2) ^ 2
          ≤ (((covered (retainedSet H ρ ω)).card : ℝ) - ∑ v : V, coverRate H p v) ^ 2}
      ≤ Cvar / (Q / 2) ^ 2 := by
  have hpos : (0 : ℝ) < (Q / 2) ^ 2 := by positivity
  refine le_trans (measureReal_ge_le_integral_div (fun ω => sq_nonneg _)
    (integrable_sq_centered_coveredCount ρ) hpos) ?_
  exact (div_le_div_iff_of_pos_right hpos).mpr hvar

end LeanPool.AsymptoticTrianglePacking.Internal
