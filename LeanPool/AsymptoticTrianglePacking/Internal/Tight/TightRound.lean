/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the TIGHT round

This is the analytic heart of the classical (tight-band) nibble: a SINGLE outcome of one nibble
round which simultaneously

* covers a fixed fraction of the vertices, and
* leaves all but a prescribed number of vertices with a safe degree in a TWO-SIDED band of width
  `2t + s` around the SAME centre `deg(v) − 𝔼[loss(v)]`.

The two bounds are centred at the same value — that is what "tight band" means, and it is what the
8:1-band single-round peeling (`LeanPool.AsymptoticTrianglePacking.Internal.CeilRoundInv`, refuted through `LeanPool.AsymptoticTrianglePacking.Internal.NibbleRoundProb`)
cannot deliver.

The proof avoids any union bound over the vertex set.  Instead the two failure modes are aggregated
into one nonnegative functional `tightBad` whose mean is small, and Markov's inequality is applied
twice: once to `tightBad` (too many irregular vertices) and once to the uncovered count (too little
coverage).  The two failure probabilities add up to `< 1`, so a good outcome exists.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverWeight
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverWeightMoments
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.PairWeightMean
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.Selection
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] [Fintype V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## Basic positivity and integrability -/

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem coverInd_nonneg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (u : V) (ω : Ω) : 0 ≤ coverInd ρ u ω := by
  rw [coverInd]; split_ifs <;> norm_num

omit [Fintype V] [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem pairCount_nonneg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) : 0 ≤ pairCount ρ v ω :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (coverInd_nonneg ρ _ ω) (coverInd_nonneg ρ _ ω))))

theorem integrable_sq_centered_lossWeight {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Integrable (fun ω => (lossWeight ρ v ω - lossWeightMean H p v) ^ 2) (ℙ : Measure Ω) := by
  have hexp : (fun ω => (lossWeight ρ v ω - lossWeightMean H p v) ^ 2)
      = fun ω => ∑ u ∈ (Finset.univ : Finset V).erase v,
          ∑ u' ∈ (Finset.univ : Finset V).erase v,
            (codegree H v u : ℝ) * (codegree H v u' : ℝ)
              * (coverIndC ρ u ω * coverIndC ρ u' ω) := by
    funext ω
    rw [lossWeight_sub_mean, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun u' _ => by ring))
  rw [hexp]
  exact integrable_finset_sum _ (fun u _ => integrable_finset_sum _
    (fun u' _ => (integrable_coverIndC_mul ρ u u').const_mul _))

/-! ## The covered count -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem coveredCount_eq_sum {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (ω : Ω) :
    ((covered (retainedSet H ρ ω)).card : ℝ) = ∑ v : V, coverInd ρ v ω := by
  classical
  have h : ∑ v : V, coverInd ρ v ω
      = ∑ v : V, (if v ∈ covered (retainedSet H ρ ω) then (1 : ℝ) else 0) := rfl
  rw [h, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  congr 1
  ext v
  simp

theorem integrable_coveredCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) :
    Integrable (fun ω => ((covered (retainedSet H ρ ω)).card : ℝ)) (ℙ : Measure Ω) := by
  have h : (fun ω => ((covered (retainedSet H ρ ω)).card : ℝ))
      = fun ω => ∑ v : V, coverInd ρ v ω := funext (coveredCount_eq_sum ρ)
  rw [h]
  exact integrable_finset_sum _ (fun v _ => integrable_coverInd ρ v)

theorem integral_coveredCount {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ ω, ((covered (retainedSet H ρ ω)).card : ℝ) ∂(ℙ : Measure Ω)
      = ∑ v : V, coverRate H p v := by
  have h : (fun ω => ((covered (retainedSet H ρ ω)).card : ℝ))
      = fun ω => ∑ v : V, coverInd ρ v ω := funext (coveredCount_eq_sum ρ)
  rw [h, integral_finset_sum _ (fun v _ => integrable_coverInd ρ v)]
  exact Finset.sum_congr rfl (fun v _ => integral_coverInd ρ hp0 hp1 v)

/-! ## The aggregated bad functional -/

/-- The aggregated badness of an outcome: `∑_v [(loss_v − 𝔼loss_v)²/t² + pairCount_v/s]`.
It dominates the number of vertices that fail either of the two tolerances. -/
noncomputable def tightBad {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t s : ℝ) (ω : Ω) : ℝ :=
  ∑ v : V, ((lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2 + pairCount ρ v ω / s)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem tightBad_nonneg {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (ω : Ω) :
    0 ≤ tightBad ρ t s ω :=
  Finset.sum_nonneg (fun v _ => add_nonneg
    (div_nonneg (sq_nonneg _) (le_of_lt (by positivity)))
    (div_nonneg (pairCount_nonneg ρ v ω) hs.le))

theorem integrable_tightBad {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (t s : ℝ) :
    Integrable (tightBad ρ t s) (ℙ : Measure Ω) := by
  have h : tightBad ρ t s = fun ω => ∑ v : V,
      ((lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2 + pairCount ρ v ω / s) := rfl
  rw [h]
  refine integrable_finset_sum _ (fun v _ => ?_)
  exact ((integrable_sq_centered_lossWeight ρ v).div_const _).add
    ((integrable_pairCount ρ v).div_const _)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The number of vertices failing either tolerance is at most the aggregated badness. -/
theorem card_tightBadSet_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (ω : Ω) :
    ((Finset.univ.filter (fun v : V =>
        t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω)).card : ℝ)
      ≤ tightBad ρ t s ω := by
  classical
  set f : V → ℝ := fun v =>
    (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2 + pairCount ρ v ω / s with hf
  have hf0 : ∀ v : V, 0 ≤ f v := fun v => add_nonneg
    (div_nonneg (sq_nonneg _) (le_of_lt (by positivity)))
    (div_nonneg (pairCount_nonneg ρ v ω) hs.le)
  have hone : ∀ v ∈ Finset.univ.filter (fun v : V =>
      t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω), (1 : ℝ) ≤ f v := by
    intro v hv
    rcases (Finset.mem_filter.mp hv).2 with hcase | hcase
    · have h1 : t ^ 2 ≤ (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 := by
        rw [← sq_abs (lossWeight ρ v ω - lossWeightMean H p v)]
        exact pow_le_pow_left₀ ht.le hcase 2
      have h2 : (1 : ℝ) ≤ (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2 :=
        (one_le_div (by positivity)).mpr h1
      have h3 : 0 ≤ pairCount ρ v ω / s := div_nonneg (pairCount_nonneg ρ v ω) hs.le
      rw [hf]; linarith only [h2, h3]
    · have h2 : (1 : ℝ) ≤ pairCount ρ v ω / s := (one_le_div hs).mpr hcase
      have h3 : 0 ≤ (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2 :=
        div_nonneg (sq_nonneg _) (le_of_lt (by positivity))
      rw [hf]; linarith only [h2, h3]
  calc ((Finset.univ.filter (fun v : V =>
          t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω)).card : ℝ)
      = ∑ _v ∈ Finset.univ.filter (fun v : V =>
          t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω), (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v : V =>
          t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω), f v :=
        Finset.sum_le_sum hone
    _ ≤ ∑ v : V, f v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun v _ _ => hf0 v)

/-- The mean of the aggregated badness, from per-vertex bounds. -/
theorem integral_tightBad_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {t s Vb Pb : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hVb : ∀ v : V, ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω) ≤ Vb)
    (hPb : ∀ v : V, ∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω) ≤ Pb) :
    ∫ ω, tightBad ρ t s ω ∂(ℙ : Measure Ω)
      ≤ (Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s) := by
  have hint : ∀ v : V, Integrable (fun ω =>
      (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2 + pairCount ρ v ω / s)
      (ℙ : Measure Ω) := fun v =>
    ((integrable_sq_centered_lossWeight ρ v).div_const _).add
      ((integrable_pairCount ρ v).div_const _)
  simp only [tightBad]
  rw [integral_finset_sum _ (fun v _ => hint v)]
  calc ∑ v : V, ∫ ω, ((lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2
        + pairCount ρ v ω / s) ∂(ℙ : Measure Ω)
      ≤ ∑ _v : V, (Vb / t ^ 2 + Pb / s) := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        have ia : Integrable (fun ω => (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 / t ^ 2)
            (ℙ : Measure Ω) := (integrable_sq_centered_lossWeight ρ v).div_const _
        have ib : Integrable (fun ω => pairCount ρ v ω / s) (ℙ : Measure Ω) :=
          (integrable_pairCount ρ v).div_const _
        rw [integral_add ia ib, integral_div, integral_div]
        have h1 : (∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω)) / t ^ 2
            ≤ Vb / t ^ 2 :=
          (div_le_div_iff_of_pos_right (by positivity)).mpr (hVb v)
        have h2 : (∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω)) / s ≤ Pb / s :=
          (div_le_div_iff_of_pos_right hs).mpr (hPb v)
        linarith only [h1, h2]
    _ = (Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-! ## The tight round -/

/-- **The tight round, relative to a good set.**  Only the vertices of `G` are required to have a
guaranteed covering rate, and only their number enters the coverage conclusion.  This is the form
consumed by the iteration, where `G` is the set of vertices still carrying a full degree. -/
theorem exists_tight_round_on {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (G : Finset V)
    {t s a Vb Pb qlo : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 < a)
    (hVb : ∀ v : V, ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω) ≤ Vb)
    (hPb : ∀ v : V, ∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω) ≤ Pb)
    (hqlo1 : qlo ≤ 1) (hqlo : ∀ v ∈ G, qlo ≤ coverRate H p v)
    (hN : 0 < Fintype.card V)
    (hsmall : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s))
        * (2 * (Fintype.card V : ℝ) - (G.card : ℝ) * qlo)
      < a * ((G.card : ℝ) * qlo)) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        (degree H v : ℝ) - lossWeightMean H p v - t
            ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
          ∧ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
            ≤ (degree H v : ℝ) - lossWeightMean H p v + t + s)
      ∧ (G.card : ℝ) * qlo / 2 < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  obtain ⟨v0⟩ := Fintype.card_pos_iff.mp hN
  have hN0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hN
  have hVb0 : 0 ≤ Vb :=
    le_trans (integral_nonneg (fun ω => sq_nonneg _)) (hVb v0)
  have hPb0 : 0 ≤ Pb :=
    le_trans (integral_nonneg (fun ω => pairCount_nonneg ρ v0 ω)) (hPb v0)
  have hΦ0 : 0 ≤ (Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s) := by
    have h1 : 0 ≤ Vb / t ^ 2 := div_nonneg hVb0 (by positivity)
    have h2 : 0 ≤ Pb / s := div_nonneg hPb0 hs.le
    have : 0 ≤ Vb / t ^ 2 + Pb / s := by linarith only [h1, h2]
    exact mul_nonneg hN0.le this
  have hG : (G.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_univ G
  have hG0 : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  -- positivity of the coverage rate is forced by the smallness hypothesis
  have hgq : 0 < (G.card : ℝ) * qlo := by
    by_contra hc
    push_neg at hc
    have h1 : 0 ≤ 2 * (Fintype.card V : ℝ) - (G.card : ℝ) * qlo := by linarith only [hc]
    nlinarith [hΦ0, ha, hsmall]
  -- Markov for the badness event
  have hP1 : (ℙ : Measure Ω).real {ω | a ≤ tightBad ρ t s ω}
      ≤ ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s)) / a := by
    refine le_trans (measureReal_ge_le_integral_div
      (fun ω => tightBad_nonneg ρ ht hs ω) (integrable_tightBad ρ t s) ha) ?_
    exact (div_le_div_iff_of_pos_right ha).mpr (integral_tightBad_le ρ ht hs hVb hPb)
  -- Markov for the coverage event
  have hQge : (G.card : ℝ) * qlo ≤ ∑ v : V, coverRate H p v := by
    calc (G.card : ℝ) * qlo = ∑ _v ∈ G, qlo := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ G, coverRate H p v := Finset.sum_le_sum hqlo
      _ ≤ ∑ v : V, coverRate H p v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
            (fun v _ _ => coverRate_nonneg hp0 hp1 v)
  have hqle : (G.card : ℝ) * qlo ≤ (Fintype.card V : ℝ) := by
    rcases le_or_gt qlo 0 with h | h
    · nlinarith only [h]
    · nlinarith only [hqlo1, hG]
  have hθpos : 0 < (Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2 := by linarith only [hgq, hqle]
  have hP2 : (ℙ : Measure Ω).real
      {ω | (Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2
            ≤ (Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ)}
      ≤ ((Fintype.card V : ℝ) - (G.card : ℝ) * qlo)
        / ((Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2) := by
    have hnn : ∀ ω : Ω, 0 ≤ (Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ) := by
      intro ω
      have : ((covered (retainedSet H ρ ω)).card : ℝ) ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast Finset.card_le_univ _
      linarith only [this]
    have hint : Integrable
        (fun ω => (Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ))
        (ℙ : Measure Ω) := (integrable_const _).sub (integrable_coveredCount ρ)
    have hmk := measureReal_ge_le_integral_div (f := fun ω =>
      (Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ)) hnn hint hθpos
    have hmean : ∫ ω, ((Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ))
        ∂(ℙ : Measure Ω) = (Fintype.card V : ℝ) - ∑ v : V, coverRate H p v := by
      rw [integral_sub (integrable_const _) (integrable_coveredCount ρ),
        integral_coveredCount ρ hp0 hp1, integral_const]
      simp
    rw [hmean] at hmk
    exact le_trans hmk ((div_le_div_iff_of_pos_right hθpos).mpr (by linarith))
  -- the two failure probabilities add up to less than one
  have hkey : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s)) / a
      + ((Fintype.card V : ℝ) - (G.card : ℝ) * qlo)
        / ((Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2) < 1 := by
    rw [div_add_div _ _ (ne_of_gt ha) (ne_of_gt hθpos), div_lt_one (by positivity)]
    have hhalf : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s))
        * (2 * (Fintype.card V : ℝ) - (G.card : ℝ) * qlo)
        = 2 * (((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s))
          * ((Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2)) := by ring
    rw [hhalf] at hsmall
    nlinarith only [hsmall]
  have hsum : (ℙ : Measure Ω).real {ω | a ≤ tightBad ρ t s ω}
      + (ℙ : Measure Ω).real
        {ω | (Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2
              ≤ (Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ)} < 1 := by
    linarith only [hP1, hP2, hkey]
  obtain ⟨ω, hω1, hω2⟩ := exists_notMem_of_measureReal_add_lt_one hsum
  refine ⟨ω, Finset.univ.filter (fun v : V =>
    t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω), ?_, ?_, ?_⟩
  · have h1 := card_tightBadSet_le ρ ht hs ω
    have h2 : tightBad ρ t s ω < a := by
      by_contra hc
      push_neg at hc
      exact hω1 hc
    linarith only [h1, h2]
  · intro v hv
    have hnot : ¬ (t ≤ |lossWeight ρ v ω - lossWeightMean H p v| ∨ s ≤ pairCount ρ v ω) := by
      intro h
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
    push_neg at hnot
    obtain ⟨hloss, hpair⟩ := hnot
    have habs := abs_lt.mp hloss
    have hlow := degree_le_safeDegree_add_coverWeight H v (covered (retainedSet H ρ ω))
    have hup := safeDegree_add_coverWeight_le H v (covered (retainedSet H ρ ω))
    have hlowR : (degree H v : ℝ)
        ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
          + (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ) := by exact_mod_cast hlow
    have hupR : (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
        + (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ)
        ≤ (degree H v : ℝ) + (pairWeight H v (covered (retainedSet H ρ ω)) : ℝ) := by
      exact_mod_cast hup
    have hcw : (coverWeight H v (covered (retainedSet H ρ ω)) : ℝ) = lossWeight ρ v ω :=
      lossWeight_eq' ρ v ω
    have hpw : (pairWeight H v (covered (retainedSet H ρ ω)) : ℝ) ≤ pairCount ρ v ω :=
      pairWeight_le_pairCount ρ v ω
    rw [hcw] at hlowR hupR
    exact ⟨by linarith [habs.2], by linarith [habs.1]⟩
  · have h2 : ¬ ((Fintype.card V : ℝ) - (G.card : ℝ) * qlo / 2
        ≤ (Fintype.card V : ℝ) - ((covered (retainedSet H ρ ω)).card : ℝ)) := hω2
    push_neg at h2
    linarith only [h2]

/-- **The tight round.**  There is an outcome of the nibble round which covers more than a
`qlo/2`-fraction of the vertices and, outside an exceptional set of fewer than `a` vertices, leaves
every safe degree in the two-sided band of width `2t + s` around `deg(v) − 𝔼[loss(v)]`. -/
theorem exists_tight_round {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {t s a Vb Pb qlo : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 < a)
    (hVb : ∀ v : V, ∫ ω, (lossWeight ρ v ω - lossWeightMean H p v) ^ 2 ∂(ℙ : Measure Ω) ≤ Vb)
    (hPb : ∀ v : V, ∫ ω, pairCount ρ v ω ∂(ℙ : Measure Ω) ≤ Pb)
    (hqlo1 : qlo ≤ 1) (hqlo : ∀ v : V, qlo ≤ coverRate H p v)
    (hN : 0 < Fintype.card V)
    (hsmall : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s)) * (2 - qlo) < a * qlo) :
    ∃ ω : Ω, ∃ B : Finset V, (B.card : ℝ) < a ∧
      (∀ v ∉ B,
        (degree H v : ℝ) - lossWeightMean H p v - t
            ≤ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
          ∧ (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
            ≤ (degree H v : ℝ) - lossWeightMean H p v + t + s)
      ∧ (Fintype.card V : ℝ) * qlo / 2 < ((covered (retainedSet H ρ ω)).card : ℝ) := by
  classical
  have hcard : ((Finset.univ : Finset V).card : ℝ) = (Fintype.card V : ℝ) := by
    rw [Finset.card_univ]
  have hN0 : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hN
  have hsmall' : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s))
      * (2 * (Fintype.card V : ℝ) - ((Finset.univ : Finset V).card : ℝ) * qlo)
      < a * (((Finset.univ : Finset V).card : ℝ) * qlo) := by
    rw [hcard]
    have h1 : ((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s))
        * (2 * (Fintype.card V : ℝ) - (Fintype.card V : ℝ) * qlo)
        = (((Fintype.card V : ℝ) * (Vb / t ^ 2 + Pb / s)) * (2 - qlo)) * (Fintype.card V : ℝ) := by
      ring
    have h2 : a * ((Fintype.card V : ℝ) * qlo) = (a * qlo) * (Fintype.card V : ℝ) := by ring
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hsmall hN0
  obtain ⟨ω, B, hB, hband, hcov⟩ :=
    exists_tight_round_on ρ hp0 hp1 (Finset.univ : Finset V) ht hs ha hVb hPb hqlo1
      (fun v _ => hqlo v) hN hsmall'
  rw [hcard] at hcov
  exact ⟨ω, B, hB, hband, hcov⟩

end LeanPool.AsymptoticTrianglePacking.Internal
