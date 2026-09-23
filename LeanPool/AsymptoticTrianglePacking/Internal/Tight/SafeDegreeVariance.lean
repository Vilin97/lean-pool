/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegree
public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.LossVariance
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the VARIANCE of the safe degree

The tight round of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.TightRound` controls the safe
degree through the LOSS WEIGHT
`∑_{u} codeg(v,u)·1[u covered]` and the PAIR COUNT correction.  The pair count has mean `≍ Δγ²` and
is handled by Markov, which forces the upper tolerance `s ≳ Δγ²/θ` — first order in `γ` once the
exceptional fraction `θ` is pushed down to the `≍ γ` demanded by a `γ^{-1}log(1/β)`-round schedule,
and therefore not summable over the schedule.

This file removes that bottleneck by treating the safe degree DIRECTLY:

  `safeDeg(v) = ∑_{e ∋ v} X_e`,  `X_e = 1[(e∖v) ∩ covered = ∅]`,

and bounding its variance.  The covariance of two edge indicators is exactly

  `Cov(X_e, X_{e'}) = ℙ(S_e ∩ S_{e'}) − ℙ(S_e)·ℙ(S_{e'})`,  `S_e = ⋃_{u ∈ e∖v} {u covered}`,

(`safeIndicator_covariance_eq`) and the two-sided second-order estimates give

  `Cov(X_e, X_{e'}) ≤ (r−1)²ε₂ + Q_e·B_{e'} + Q_{e'}·B_e + |(e ∩ e')∖v|·q_hi`

(`safeIndicator_covariance_le`), with `Q_e = ∑_{u ∈ e∖v} q_u ≤ (r−1)q_hi` the first-order weight,
`B_e ≤ (r−1)²(q_hi² + ε₂)` the Bonferroni correction and `ε₂` the pair excess.  The crucial point is
that the `Θ(γ²)` terms CANCEL: `∑_{u,u'} ℙ(u,u' covered) ≤ Q_eQ_{e'} + (r−1)²ε₂` is matched by the
Bonferroni lower bound `ℙ(S_e)ℙ(S_{e'}) ≥ Q_eQ_{e'} − Q_eB_{e'} − Q_{e'}B_e`.

Summing over the `deg(v)²` pairs and using `∑_{u≠v} codeg(v,u)² ≤ κ(r−1)deg(v)`:

  `Var(safeDeg(v)) ≤ Δ²((r−1)²ε₂ + 2(r−1)³q_hi(q_hi² + ε₂)) + q_hi·κ·(r−1)·Δ`

(`safeDegree_variance_le`).  In the nibble regime `q_hi = γ/r`, `ε₂ ≤ 2κγ/(rΔ)`, `κ ≤ γΔ/(2048r)`
this is `≈ 2γ³Δ²`, so Chebyshev at a deviation `t = ε·γΔ` — a factor `ε` below the first-order
per-round degree gain — has failure probability `≈ 2γ/ε²`.  This is a decisive improvement on the
`pairCount` route (whose tolerance is first order in `γ`), but see the caveat on
`safeDegree_variance_le_codegree`: the residual `Θ(γ³Δ²)` term is still a constant factor too large
for the round to be iterated, and removing it requires a third-order Bonferroni estimate.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The covariance of two edge indicators -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The product of two safe indicators is the indicator of the intersection of the safe events. -/
theorem safeIndicator_mul_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) (ω : Ω) :
    safeIndicator ρ v e ω * safeIndicator ρ v e' ω
      = if ω ∈ {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
            ∩ {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))} then 1 else 0 := by
  simp only [safeIndicator, Set.mem_inter_iff, Set.mem_ofPred_eq]
  split_ifs with h1 h2 h3 <;> simp_all

theorem integrable_safeIndicator_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) :
    Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω) (ℙ : Measure Ω) := by
  have hms : MeasurableSet ({ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
      ∩ {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))}) :=
    (measurableSet_safeEvent ρ v e).inter (measurableSet_safeEvent ρ v e')
  have hfun : (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω)
      = fun ω => if ω ∈ {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
            ∩ {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))} then (1 : ℝ) else 0 :=
    funext (safeIndicator_mul_eq ρ v e e')
  rw [hfun]
  refine (integrable_const (1 : ℝ)).mono'
    (Measurable.ite hms measurable_const measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  split_ifs <;> simp

/-- **The covariance of two edge indicators.**
`𝔼[X_e X_{e'}] = 1 − ℙ(S_e) − ℙ(S_{e'}) + ℙ(S_e ∩ S_{e'})`. -/
theorem integral_safeIndicator_mul {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) :
    ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
      = 1 - (ℙ : Measure Ω).real (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
        - (ℙ : Measure Ω).real (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
        + (ℙ : Measure Ω).real
            ((⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
              ∩ (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})) := by
  classical
  set A : Set Ω := ⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)} with hA
  set B : Set Ω := ⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)} with hB
  have hmA : MeasurableSet A :=
    Finset.measurableSet_biUnion _ (fun u _ => measurableSet_vertex_covered ρ u)
  have hmB : MeasurableSet B :=
    Finset.measurableSet_biUnion _ (fun u _ => measurableSet_vertex_covered ρ u)
  have hsafeA : {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))} = Aᶜ :=
    safeEvent_eq_compl ρ v e
  have hsafeB : {ω | Disjoint (e'.erase v) (covered (retainedSet H ρ ω))} = Bᶜ :=
    safeEvent_eq_compl ρ v e'
  have hind : (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω)
      = Set.indicator (Aᶜ ∩ Bᶜ) 1 := by
    funext ω
    have hA' : ω ∈ Aᶜ ↔ Disjoint (e.erase v) (covered (retainedSet H ρ ω)) :=
      (Set.ext_iff.mp hsafeA ω).symm
    have hB' : ω ∈ Bᶜ ↔ Disjoint (e'.erase v) (covered (retainedSet H ρ ω)) :=
      (Set.ext_iff.mp hsafeB ω).symm
    rw [safeIndicator, safeIndicator, Set.indicator_apply]
    by_cases h1 : Disjoint (e.erase v) (covered (retainedSet H ρ ω)) <;>
      by_cases h2 : Disjoint (e'.erase v) (covered (retainedSet H ρ ω)) <;>
      simp [h1, h2, hA', hB', Set.mem_inter_iff]
  rw [hind, integral_indicator_one (hmA.compl.inter hmB.compl)]
  have hcompl : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by rw [Set.compl_union]
  rw [hcompl, measureReal_compl (hmA.union hmB)]
  have hunion : (ℙ : Measure Ω).real (A ∪ B) + (ℙ : Measure Ω).real (A ∩ B)
      = (ℙ : Measure Ω).real A + (ℙ : Measure Ω).real B :=
    measureReal_union_add_inter (μ := (ℙ : Measure Ω)) (s := A) (t := B) hmB
      (measure_ne_top _ _) (measure_ne_top _ _)
  simp only [probReal_univ]
  linarith only [hunion]

/-- **The covariance of two edge indicators.**
`Cov(X_e, X_{e'}) = ℙ(S_e ∩ S_{e'}) − ℙ(S_e)·ℙ(S_{e'})`. -/
theorem safeIndicator_covariance_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e e' : Finset V) :
    ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
        - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
          * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω))
      = (ℙ : Measure Ω).real
            ((⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
              ∩ (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)}))
        - (ℙ : Measure Ω).real (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
          * (ℙ : Measure Ω).real (⋃ u ∈ e'.erase v, {ω | u ∈ covered (retainedSet H ρ ω)}) := by
  rw [integral_safeIndicator_mul, integral_safeIndicator, integral_safeIndicator]
  ring

/-! ## A union bound for the intersection of two unions -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `ℙ((⋃_{i∈s} f i) ∩ (⋃_{j∈t} g j)) ≤ ∑_i ∑_j ℙ(f i ∩ g j)`. -/
theorem measureReal_inter_biUnion_le {ι ι' : Type*} (s : Finset ι) (t : Finset ι')
    (f : ι → Set Ω) (g : ι' → Set Ω) :
    (ℙ : Measure Ω).real ((⋃ i ∈ s, f i) ∩ (⋃ j ∈ t, g j))
      ≤ ∑ i ∈ s, ∑ j ∈ t, (ℙ : Measure Ω).real (f i ∩ g j) := by
  have hset : ((⋃ i ∈ s, f i) ∩ (⋃ j ∈ t, g j)) = ⋃ i ∈ s, ⋃ j ∈ t, (f i ∩ g j) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
    tauto
  rw [hset]
  refine (measureReal_biUnion_finset_le s _).trans (Finset.sum_le_sum (fun i _ => ?_))
  exact measureReal_biUnion_finset_le t _

/-! ## The quantitative covariance bound -/

/-- Elementary inequality behind the cancellation of the first-order terms: if `a ≥ Q − B`,
`b ≥ Q' − B'` with everything in sight nonnegative, then `a·b ≥ Q·Q' − Q·B' − Q'·B`. -/
private theorem auxProd {a b Q Q' B B' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (h1 : Q - B ≤ a) (h2 : Q' - B' ≤ b) :
    Q * Q' - Q * B' - Q' * B ≤ a * b := by
  rcases le_or_gt 0 (Q - B) with h | h
  · rcases le_or_gt 0 (Q' - B') with h' | h'
    · nlinarith only [hB, hB', h1, h2, h, h']
    · nlinarith only [ha, hb, hB, hB', h, h']
  · nlinarith only [ha, hb, hQ, hQ', hB', h]

/-- **The covariance bound for two edge indicators.**  With covering rates at most `qhi`, pair
excesses at most `ε₂` and at most `n` non-`v` vertices per edge,

  `Cov(X_e, X_{e'}) ≤ n²ε₂ + |(e ∩ e')∖v|·qhi + 2·(n·qhi)·(n²(qhi² + ε₂))`.

The crucial point is that the first-order `Θ(n²qhi²)` terms CANCEL between the pairwise union bound
for `ℙ(S_e ∩ S_{e'})` and the second-order Bonferroni lower bound for `ℙ(S_e)·ℙ(S_{e'})`. -/
theorem safeIndicator_covariance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) (e e' : Finset V)
    {n : ℕ} {qhi ε₂ : ℝ}
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂)
    (hn : (e.erase v).card ≤ n) (hn' : (e'.erase v).card ≤ n) :
    ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
        - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
          * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω))
      ≤ (n : ℝ) ^ 2 * ε₂ + (((e ∩ e').erase v).card : ℝ) * qhi
        + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) := by
  classical
  set S := e.erase v with hSdef
  set S' := e'.erase v with hS'def
  set C : V → Set Ω := fun u => {ω | u ∈ covered (retainedSet H ρ ω)} with hCdef
  set A : Set Ω := ⋃ u ∈ S, C u with hAdef
  set B : Set Ω := ⋃ u ∈ S', C u with hBdef
  have hq0 : 0 ≤ qhi := le_trans (coverRate_nonneg hp0 hp1 v) (hq v)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set Q : ℝ := ∑ u ∈ S, coverRate H p u with hQdef
  set Q' : ℝ := ∑ u ∈ S', coverRate H p u with hQ'def
  set Bc : ℝ := ∑ u ∈ S, ∑ u' ∈ S.erase u, (ℙ : Measure Ω).real (C u ∩ C u') with hBcdef
  set Bc' : ℝ := ∑ u ∈ S', ∑ u' ∈ S'.erase u, (ℙ : Measure Ω).real (C u ∩ C u') with hBc'def
  -- basic nonnegativity / upper bounds on the first-order weights
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun u _ => coverRate_nonneg hp0 hp1 u
  have hQ'0 : 0 ≤ Q' := Finset.sum_nonneg fun u _ => coverRate_nonneg hp0 hp1 u
  have hQle : Q ≤ (n : ℝ) * qhi := by
    calc Q ≤ ∑ _u ∈ S, qhi := Finset.sum_le_sum fun u _ => hq u
      _ = (S.card : ℝ) * qhi := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * qhi := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hq0
  have hQ'le : Q' ≤ (n : ℝ) * qhi := by
    calc Q' ≤ ∑ _u ∈ S', qhi := Finset.sum_le_sum fun u _ => hq u
      _ = (S'.card : ℝ) * qhi := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * qhi := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hq0
  -- the Bonferroni corrections are nonnegative and small
  have hBc0 : 0 ≤ Bc :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => measureReal_nonneg
  have hBc'0 : 0 ≤ Bc' :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => measureReal_nonneg
  have hsq0 : 0 ≤ qhi ^ 2 + ε₂ := by positivity
  have hBcBound : ∀ (T : Finset V), T.card ≤ n →
      ∑ u ∈ T, ∑ u' ∈ T.erase u, (ℙ : Measure Ω).real (C u ∩ C u')
        ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := by
    intro T hT
    have hTn : (T.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hT
    calc ∑ u ∈ T, ∑ u' ∈ T.erase u, (ℙ : Measure Ω).real (C u ∩ C u')
        ≤ ∑ _u ∈ T, ∑ _u' ∈ T.erase _u, (qhi ^ 2 + ε₂) := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' hu' => ?_
          have hne : u ≠ u' := (Finset.mem_erase.mp hu').1.symm
          have := hpair u u' hne
          have h1 : coverRate H p u * coverRate H p u' ≤ qhi ^ 2 :=
            calc coverRate H p u * coverRate H p u'
                ≤ qhi * qhi := by
                  exact mul_le_mul (hq u) (hq u') (coverRate_nonneg hp0 hp1 u') hq0
              _ = qhi ^ 2 := by ring
          linarith only [this, h1]
      _ = ∑ u ∈ T, ((T.erase u).card : ℝ) * (qhi ^ 2 + ε₂) := by
          exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ _u ∈ T, (n : ℝ) * (qhi ^ 2 + ε₂) := by
          refine Finset.sum_le_sum fun u _ => ?_
          have : ((T.erase u).card : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast le_trans (Finset.card_erase_le) hT
          exact mul_le_mul_of_nonneg_right this hsq0
      _ = (T.card : ℝ) * ((n : ℝ) * (qhi ^ 2 + ε₂)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := by nlinarith [mul_nonneg hn0 hsq0]
  have hBcle : Bc ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := hBcBound S hn
  have hBc'le : Bc' ≤ (n : ℝ) ^ 2 * (qhi ^ 2 + ε₂) := hBcBound S' hn'
  -- lower bounds on ℙ(A), ℙ(B) via Bonferroni
  have hAlo : Q - Bc ≤ (ℙ : Measure Ω).real A := by
    have := measureReal_biUnion_ge_bonferroni (Ω := Ω) S C
      (fun u => measurableSet_vertex_covered ρ u)
    have hQeq : ∑ u ∈ S, (ℙ : Measure Ω).real (C u) = Q :=
      Finset.sum_congr rfl fun u _ => prob_vertex_covered_eq ρ hp0 hp1 u
    rw [hQeq] at this
    exact this
  have hBlo : Q' - Bc' ≤ (ℙ : Measure Ω).real B := by
    have := measureReal_biUnion_ge_bonferroni (Ω := Ω) S' C
      (fun u => measurableSet_vertex_covered ρ u)
    have hQeq : ∑ u ∈ S', (ℙ : Measure Ω).real (C u) = Q' :=
      Finset.sum_congr rfl fun u _ => prob_vertex_covered_eq ρ hp0 hp1 u
    rw [hQeq] at this
    exact this
  -- upper bound on ℙ(A ∩ B)
  have hterm : ∀ u u' : V, (ℙ : Measure Ω).real (C u ∩ C u')
      ≤ coverRate H p u * coverRate H p u' + ε₂ + (if u = u' then qhi else 0) := by
    intro u u'
    by_cases huu' : u = u'
    · subst huu'
      rw [Set.inter_self, prob_vertex_covered_eq ρ hp0 hp1 u, ite_eq_left rfl]
      have h0 : 0 ≤ coverRate H p u * coverRate H p u :=
        mul_nonneg (coverRate_nonneg hp0 hp1 u) (coverRate_nonneg hp0 hp1 u)
      linarith [hq u]
    · rw [ite_eq_right huu']
      linarith only [hpair u u' huu']
  have hInterCard : S ∩ S' = (e ∩ e').erase v := by
    ext u
    simp only [hSdef, hS'def, Finset.mem_inter, Finset.mem_erase]
    tauto
  have hAB : (ℙ : Measure Ω).real (A ∩ B)
      ≤ Q * Q' + (n : ℝ) ^ 2 * ε₂ + (((e ∩ e').erase v).card : ℝ) * qhi := by
    refine (measureReal_inter_biUnion_le S S' C C).trans ?_
    calc ∑ u ∈ S, ∑ u' ∈ S', (ℙ : Measure Ω).real (C u ∩ C u')
        ≤ ∑ u ∈ S, ∑ u' ∈ S',
            (coverRate H p u * coverRate H p u' + ε₂ + (if u = u' then qhi else 0)) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => hterm u u'
      _ = Q * Q' + ((S.card : ℝ) * (S'.card : ℝ)) * ε₂ + ((S ∩ S').card : ℝ) * qhi := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            Finset.sum_ite_eq, Finset.sum_ite_mem]
          rw [hQdef, hQ'def, Finset.sum_mul_sum]
          ring
      _ ≤ Q * Q' + (n : ℝ) ^ 2 * ε₂ + (((e ∩ e').erase v).card : ℝ) * qhi := by
          rw [hInterCard]
          have hcards : (S.card : ℝ) * (S'.card : ℝ) ≤ (n : ℝ) ^ 2 := by
            have h1 : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            have h2 : (S'.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
            nlinarith [Nat.cast_nonneg (α := ℝ) S.card, Nat.cast_nonneg (α := ℝ) S'.card]
          nlinarith [hε0]
  -- assemble
  rw [safeIndicator_covariance_eq ρ v e e']
  have hprod : Q * Q' - Q * Bc' - Q' * Bc
      ≤ (ℙ : Measure Ω).real A * (ℙ : Measure Ω).real B :=
    auxProd measureReal_nonneg measureReal_nonneg hQ0 hQ'0 hBc0 hBc'0 hAlo hBlo
  have hcross : Q * Bc' + Q' * Bc ≤ 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) := by
    have h1 : Q * Bc' ≤ ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) :=
      mul_le_mul hQle hBc'le hBc'0 (mul_nonneg hn0 hq0)
    have h2 : Q' * Bc ≤ ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)) :=
      mul_le_mul hQ'le hBcle hBc0 (mul_nonneg hn0 hq0)
    linarith only [h1, h2]
  linarith only [hAB, hprod, hcross]

/-! ## The variance of the safe degree -/

/-- The mean of the safe degree, written as the sum of the edge-indicator means. -/
noncomputable def safeDegMean {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) : ℝ :=
  ∑ e ∈ H.filter (fun e => v ∈ e), ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω)

theorem integral_safeDegree_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω)
      = safeDegMean ρ v := by
  rw [safeDegree_expectation_eq ρ v, safeDegMean]
  exact Finset.sum_congr rfl fun e _ => (integral_safeIndicator ρ v e).symm

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem safeDegree_sub_mean_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v
      = ∑ e ∈ H.filter (fun e => v ∈ e),
          (safeIndicator ρ v e ω - ∫ ω', safeIndicator ρ v e ω' ∂(ℙ : Measure Ω)) := by
  rw [Finset.sum_sub_distrib, ← safeDegree_eq_sum ρ v ω, safeDegMean]

/-- The centred safe degree has an integrable square (it is a bounded random variable). -/
theorem integrable_sq_centered_safeDegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Integrable (fun ω =>
        ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2)
      (ℙ : Measure Ω) := by
  classical
  set c : Finset V → ℝ := fun e => ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω) with hc
  have hfun : (fun ω => ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2)
      = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
          (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e') := by
    funext ω
    rw [safeDegree_sub_mean_eq ρ v ω, sq, Finset.sum_mul_sum]
  rw [hfun]
  refine integrable_finsetSum _ fun e _ => integrable_finsetSum _ fun e' _ => ?_
  have hprod : (fun ω => (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e'))
      = fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
        - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω + c e * c e' := by
    funext ω; ring
  rw [hprod]
  exact (((integrable_safeIndicator_mul ρ v e e').sub
    ((integrable_safeIndicator ρ v e).const_mul (c e'))).sub
    ((integrable_safeIndicator ρ v e').const_mul (c e))).add (integrable_const _)

/-- **The centred second moment of the safe degree as a double sum of covariances.** -/
theorem integral_sq_centered_safeDegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω)
      = ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
          (∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
            - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
              * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω))) := by
  classical
  set c : Finset V → ℝ := fun e => ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω) with hc
  have hrewrite : ∀ (e e' : Finset V) (ω : Ω),
      (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e')
        = safeIndicator ρ v e ω * safeIndicator ρ v e' ω
          - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω + c e * c e' := by
    intro e e' ω; ring
  have hfun : ∀ e e' : Finset V,
      (fun ω => (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e'))
        = fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
          - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω + c e * c e' :=
    fun e e' => funext fun ω => hrewrite e e' ω
  have hi1 : ∀ e e' : Finset V,
      Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω) (ℙ : Measure Ω) :=
    fun e e' => integrable_safeIndicator_mul ρ v e e'
  have hi2 : ∀ e e' : Finset V,
      Integrable (fun ω => c e' * safeIndicator ρ v e ω) (ℙ : Measure Ω) :=
    fun e e' => (integrable_safeIndicator ρ v e).const_mul (c e')
  have hi3 : ∀ e e' : Finset V,
      Integrable (fun ω => c e * safeIndicator ρ v e' ω) (ℙ : Measure Ω) :=
    fun e e' => (integrable_safeIndicator ρ v e').const_mul (c e)
  have hiAB : ∀ e e' : Finset V,
      Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
        - c e' * safeIndicator ρ v e ω) (ℙ : Measure Ω) :=
    fun e e' => (hi1 e e').sub (hi2 e e')
  have hiABC : ∀ e e' : Finset V,
      Integrable (fun ω => safeIndicator ρ v e ω * safeIndicator ρ v e' ω
        - c e' * safeIndicator ρ v e ω - c e * safeIndicator ρ v e' ω) (ℙ : Measure Ω) :=
    fun e e' => (hiAB e e').sub (hi3 e e')
  have hint : ∀ e e' : Finset V,
      Integrable (fun ω => (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e'))
        (ℙ : Measure Ω) := by
    intro e e'
    rw [hfun e e']
    exact (hiABC e e').add (integrable_const _)
  have hone : ∀ e e' : Finset V,
      ∫ ω, (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e') ∂(ℙ : Measure Ω)
        = ∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω) - c e * c e' := by
    intro e e'
    rw [hfun e e', integral_add (hiABC e e') (integrable_const _),
      integral_sub (hiAB e e') (hi3 e e'), integral_sub (hi1 e e') (hi2 e e'),
      integral_const_mul, integral_const_mul, integral_const]
    simp only [hc, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hexp : ∀ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
      = ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
          (safeIndicator ρ v e ω - c e) * (safeIndicator ρ v e' ω - c e') := by
    intro ω
    rw [safeDegree_sub_mean_eq ρ v ω, sq, Finset.sum_mul_sum]
  simp only [hexp]
  rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun e' _ => hint e e'))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum _ (fun e' _ => hint e e')]
  exact Finset.sum_congr rfl fun e' _ => hone e e'

/-- **The variance bound for the safe degree.**  With `deg(v) ≤ Δ` edges at `v`, at most `n`
other vertices per edge, covering rates at most `qhi`, pair excesses at most `ε₂`, and the
codegree-controlled overlap budget `∑_{e,e'∈H_v} |(e ∩ e')∖v| ≤ Ksum`,

  `Var(safeDeg v) ≤ Δ²·(n²ε₂ + 2n³qhi(qhi² + ε₂)) + Ksum·qhi`. -/
theorem safeDegree_variance_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V)
    {Δ n : ℕ} {qhi ε₂ Ksum : ℝ}
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂)
    (hdeg : (H.filter (fun e => v ∈ e)).card ≤ Δ)
    (hcard : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card ≤ n)
    (hK : ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
            (((e ∩ e').erase v).card : ℝ) ≤ Ksum) :
    ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω)
      ≤ (Δ : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ε₂
            + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)))
        + Ksum * qhi := by
  classical
  set Hv := H.filter (fun e => v ∈ e) with hHv
  have hq0 : 0 ≤ qhi := le_trans (coverRate_nonneg hp0 hp1 v) (hq v)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set Cst : ℝ := (n : ℝ) ^ 2 * ε₂ + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂))
    with hCst
  have hCst0 : 0 ≤ Cst := by
    have : 0 ≤ qhi ^ 2 + ε₂ := by positivity
    rw [hCst]; positivity
  rw [integral_sq_centered_safeDegree ρ v]
  have hstep : ∑ e ∈ Hv, ∑ e' ∈ Hv,
        (∫ ω, safeIndicator ρ v e ω * safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)
          - (∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω))
            * (∫ ω, safeIndicator ρ v e' ω ∂(ℙ : Measure Ω)))
      ≤ ∑ e ∈ Hv, ∑ e' ∈ Hv, (Cst + (((e ∩ e').erase v).card : ℝ) * qhi) := by
    refine Finset.sum_le_sum fun e he => Finset.sum_le_sum fun e' he' => ?_
    have := safeIndicator_covariance_le ρ hp0 hp1 v e e' hq hε0 hpair (hcard e he) (hcard e' he')
    rw [hCst]; linarith only [this]
  refine hstep.trans ?_
  have hsplit : ∑ e ∈ Hv, ∑ e' ∈ Hv, (Cst + (((e ∩ e').erase v).card : ℝ) * qhi)
      = (Hv.card : ℝ) * (Hv.card : ℝ) * Cst
        + (∑ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)) * qhi := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
    ring
  rw [hsplit]
  have hcardΔ : (Hv.card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hdeg
  have hcard0 : (0 : ℝ) ≤ (Hv.card : ℝ) := Nat.cast_nonneg _
  have hsq : (Hv.card : ℝ) * (Hv.card : ℝ) ≤ (Δ : ℝ) ^ 2 := by nlinarith only [hcardΔ]
  have h1 : (Hv.card : ℝ) * (Hv.card : ℝ) * Cst ≤ (Δ : ℝ) ^ 2 * Cst :=
    mul_le_mul_of_nonneg_right hsq hCst0
  have h2 : (∑ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)) * qhi ≤ Ksum * qhi :=
    mul_le_mul_of_nonneg_right hK hq0
  linarith only [h1, h2]

/-! ## The codegree budget for the overlap sum -/

/-- `∑_{e,e' ∋ v} |(e ∩ e')∖v| = ∑_{e ∋ v} ∑_{u ∈ e∖v} codeg(v,u) ≤ deg(v)·n·κ`:  the overlap
budget in `safeDegree_variance_le` is controlled by the codegree, NOT by `Δ²`. -/
theorem sum_pair_overlap_le_codegree {H : Finset (Finset V)} (v : V) {n κ : ℕ}
    (hcard : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card ≤ n)
    (hκ : ∀ u : V, u ≠ v → codegree H v u ≤ κ) :
    ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
        (((e ∩ e').erase v).card : ℝ)
      ≤ ((H.filter (fun e => v ∈ e)).card : ℝ) * (n : ℝ) * (κ : ℝ) := by
  classical
  set Hv := H.filter (fun e => v ∈ e) with hHv
  have hinner : ∀ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ) ≤ (n : ℝ) * (κ : ℝ) := by
    intro e he
    have hswap : ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)
        = ∑ u ∈ e.erase v, (codegree H v u : ℝ) := by
      have hpt : ∀ e' : Finset V, ((e ∩ e').erase v).card
          = ∑ u ∈ e.erase v, (if u ∈ e' then 1 else 0) := by
        intro e'
        rw [← Finset.card_filter]
        congr 1
        ext u
        simp only [Finset.mem_erase, Finset.mem_inter, Finset.mem_filter]
        tauto
      have : ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)
          = ∑ e' ∈ Hv, ∑ u ∈ e.erase v, (if u ∈ e' then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [hpt e']
        push_cast
        simp
      rw [this, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hfil : Hv.filter (fun e' => u ∈ e') = H.filter (fun e' => v ∈ e' ∧ u ∈ e') := by
        rw [hHv, Finset.filter_filter]
      rw [Finset.sum_boole, hfil]
      rfl
    rw [hswap]
    calc ∑ u ∈ e.erase v, (codegree H v u : ℝ)
        ≤ ∑ _u ∈ e.erase v, (κ : ℝ) := by
          refine Finset.sum_le_sum fun u hu => ?_
          exact_mod_cast hκ u (Finset.mem_erase.mp hu).1
      _ = ((e.erase v).card : ℝ) * (κ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * (κ : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard e he) (Nat.cast_nonneg _)
  calc ∑ e ∈ Hv, ∑ e' ∈ Hv, (((e ∩ e').erase v).card : ℝ)
      ≤ ∑ _e ∈ Hv, (n : ℝ) * (κ : ℝ) := Finset.sum_le_sum hinner
    _ = (Hv.card : ℝ) * (n : ℝ) * (κ : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The codegree-tightened variance of the safe degree.**  Combining
`safeDegree_variance_le` with the codegree budget `sum_pair_overlap_le_codegree`:

  `Var(safeDeg v) ≤ Δ²(n²ε₂ + 2n³qhi(qhi²+ε₂)) + Δ·n·κ·qhi`.

In the nibble regime `n = r−1`, `qhi = γ/r`, `ε₂ ≤ 2κγ/(rΔ)`, `κ ≤ γΔ/(2048r)` the right-hand side
is `≈ 2γ³Δ²`, i.e. `o(γ²Δ²)`:  the standard deviation `≃ √2·γ^{3/2}Δ` is a factor `√γ` below the
first-order per-round degree gain `≃ γΔ/8`, so Chebyshev at deviation `t = ε·γΔ` gives a bad
fraction `≈ 2γ/ε²` per round.

Caveat for the iteration:  a schedule that covers a `c ≃ γ/(8r)` fraction per round needs the bad
fraction to be `≪ c`, i.e. `2γ/ε² ≪ γ/(8r)` — a condition on CONSTANTS that no choice of `γ` can
satisfy (`ε ≤ 1`).  The obstruction is the `2·Q_e·B_{e'}` term, which comes from combining a
first-order union bound for `ℙ(S_e ∩ S_{e'})` with a SECOND-order Bonferroni lower bound for
`ℙ(S_e)·ℙ(S_{e'})`; the two errors add rather than cancel.  A third-order Bonferroni would replace
`Θ(γ³Δ²)` by `Θ(γ⁴Δ²)`, making the bad fraction `≈ Cγ²/ε² ≪ γ/(8r)` for all small enough `γ`.
That refinement is NOT part of this file. -/
theorem safeDegree_variance_le_codegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V)
    {Δ n κ : ℕ} {qhi ε₂ : ℝ}
    (hq : ∀ u : V, coverRate H p u ≤ qhi) (hε0 : 0 ≤ ε₂)
    (hpair : ∀ u u' : V, u ≠ u' →
      (ℙ : Measure Ω).real ({ω | u ∈ covered (retainedSet H ρ ω)}
          ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
        - coverRate H p u * coverRate H p u' ≤ ε₂)
    (hdeg : (H.filter (fun e => v ∈ e)).card ≤ Δ)
    (hcard : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card ≤ n)
    (hκ : ∀ u : V, u ≠ v → codegree H v u ≤ κ) :
    ∫ ω, ((safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) - safeDegMean ρ v) ^ 2
        ∂(ℙ : Measure Ω)
      ≤ (Δ : ℝ) ^ 2 * ((n : ℝ) ^ 2 * ε₂
            + 2 * ((n : ℝ) * qhi) * ((n : ℝ) ^ 2 * (qhi ^ 2 + ε₂)))
        + (Δ : ℝ) * (n : ℝ) * (κ : ℝ) * qhi := by
  have hq0 : 0 ≤ qhi := le_trans (coverRate_nonneg hp0 hp1 v) (hq v)
  have hK := sum_pair_overlap_le_codegree (H := H) v hcard hκ
  have hcardΔ : (((H.filter (fun e => v ∈ e)).card : ℝ)) ≤ (Δ : ℝ) := by exact_mod_cast hdeg
  have hK' : ∑ e ∈ H.filter (fun e => v ∈ e), ∑ e' ∈ H.filter (fun e => v ∈ e),
      (((e ∩ e').erase v).card : ℝ) ≤ (Δ : ℝ) * (n : ℝ) * (κ : ℝ) := by
    refine hK.trans ?_
    have h1 : (0 : ℝ) ≤ (n : ℝ) * (κ : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith only [hcardΔ, h1]
  exact safeDegree_variance_le ρ hp0 hp1 v hq hε0 hpair hdeg hcard hK'

end LeanPool.AsymptoticTrianglePacking.Internal
