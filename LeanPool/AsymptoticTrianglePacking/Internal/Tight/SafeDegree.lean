/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CoverProb
public import LeanPool.AsymptoticTrianglePacking.Internal.Measurable
public import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

/-!
# LeanPool.AsymptoticTrianglePacking.Internal — the SAFE degree and its SHARP expectation

The residual degree `deg_res(v)` of a vertex is *not* the right random variable for the nibble
invariant: it collapses to `0` on the event "`v` itself is covered", an event of constant
probability
`≈ γ`, so `deg_res(v)` has standard deviation of order `d` and cannot concentrate. The classical fix
is to track instead the **safe degree**

  `safeDegree H C v = #{e ∈ H : v ∈ e, (e \ {v}) ∩ C = ∅}`,

the number of edges at `v` whose OTHER vertices all survive the round.  It agrees with the residual
degree exactly on the event `{v ∉ C}` (`safeDegree_eq_residual_degree_of_not_covered`), which is the
only event on which the residual degree at `v` matters, and — unlike the residual degree — it is a
sum of `deg(v)` indicators none of which is governed by a single common event.

This file computes its expectation SHARPLY, two-sidedly:

  `∑_{e ∋ v} (1 − ∑_{u ∈ e∖v} q_u)  ≤  𝔼[safeDeg(v)]  ≤  ∑_{e ∋ v} (1 − ∑_{u ∈ e∖v} q_u + pairs)`,

with `q_u = coverRate H p u` the EXACT covering rate of `u` (`prob_vertex_covered_eq`) and `pairs`
the second-order Bonferroni correction, bounded by `prob_two_vertices_covered_le`.  The two bounds
agree to second order, which is exactly what the loose brackets
`residual_degree_expectation_lower/upper` fail to do.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Hypergraph
attribute [local instance] Classical.propDecidable

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The safe degree -/

/-- **The safe degree.**  The number of edges at `v` whose vertices OTHER than `v` all avoid `C`. -/
def safeDegree (H : Finset (Finset V)) (C : Finset V) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e ∧ Disjoint (e.erase v) C)).card

/-- On the event that `v` is not covered, the safe degree IS the residual degree. -/
theorem safeDegree_eq_residual_degree_of_not_covered {H R : Finset (Finset V)} {v : V}
    (hv : v ∉ covered R) : safeDegree H (covered R) v = degree (Hypergraph.residual H R) v := by
  unfold safeDegree degree Hypergraph.residual
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨heH, hve, hdisj⟩
    refine ⟨⟨heH, ?_⟩, hve⟩
    rw [Finset.disjoint_left]
    intro x hx hxC
    by_cases hxv : x = v
    · exact hv (hxv ▸ hxC)
    · exact (Finset.disjoint_left.mp hdisj (Finset.mem_erase.mpr ⟨hxv, hx⟩)) hxC
  · rintro ⟨⟨heH, hdisj⟩, hve⟩
    refine ⟨heH, hve, ?_⟩
    exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj

/-- The residual degree never exceeds the safe degree. -/
theorem residual_degree_le_safeDegree {H R : Finset (Finset V)} (v : V) :
    degree (Hypergraph.residual H R) v ≤ safeDegree H (covered R) v := by
  unfold safeDegree degree Hypergraph.residual
  refine Finset.card_le_card ?_
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨he.1.1, he.2, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) he.1.2⟩

/-! ## The safe-degree indicator and its expectation -/

/-- The indicator that all vertices of `e` other than `v` survive the round. -/
noncomputable def safeIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e : Finset V) (ω : Ω) : ℝ :=
  if Disjoint (e.erase v) (covered (retainedSet H ρ ω)) then 1 else 0

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The "all other vertices survive" event is the complement of the union of covering events. -/
theorem safeEvent_eq_compl {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e : Finset V) :
    {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))}
      = (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})ᶜ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists, exists_prop,
    not_and, Finset.disjoint_left]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem measurableSet_safeEvent {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e : Finset V) :
    MeasurableSet {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))} := by
  rw [safeEvent_eq_compl ρ v e]
  exact (Finset.measurableSet_biUnion _ (fun u _ => measurableSet_vertex_covered ρ u)).compl

theorem integrable_safeIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e : Finset V) :
    Integrable (safeIndicator ρ v e) (ℙ : Measure Ω) := by
  refine (integrable_const (1 : ℝ)).mono'
    (Measurable.ite (measurableSet_safeEvent ρ v e) measurable_const
      measurable_const).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [safeIndicator]; split_ifs <;> simp

/-- The expectation of the safe indicator is `1 − ℙ(some other vertex of `e` is covered)`. -/
theorem integral_safeIndicator {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (e : Finset V) :
    ∫ ω, safeIndicator ρ v e ω ∂(ℙ : Measure Ω)
      = 1 - (ℙ : Measure Ω).real (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)}) := by
  have hind : safeIndicator ρ v e
      = Set.indicator {ω | Disjoint (e.erase v) (covered (retainedSet H ρ ω))} 1 := by
    funext ω; rw [safeIndicator, Set.indicator_apply]; simp
  have hm : MeasurableSet (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)}) :=
    Finset.measurableSet_biUnion _ (fun u _ => measurableSet_vertex_covered ρ u)
  rw [hind, integral_indicator_one (measurableSet_safeEvent ρ v e), safeEvent_eq_compl ρ v e,
    measureReal_compl hm]
  simp

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The safe degree is the sum of the safe indicators of the edges through `v`. -/
theorem safeDegree_eq_sum {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) (ω : Ω) :
    (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)
      = ∑ e ∈ H.filter (fun e => v ∈ e), safeIndicator ρ v e ω := by
  unfold safeDegree safeIndicator
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  congr 1
  congr 1
  ext e
  simp only [Finset.mem_filter]
  tauto

theorem integrable_safeDegree {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    Integrable (fun ω => (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ)) (ℙ : Measure Ω) := by
  have h : (fun ω => (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ))
      = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e), safeIndicator ρ v e ω :=
    funext (fun ω => safeDegree_eq_sum ρ v ω)
  rw [h]
  exact integrable_finsetSum _ (fun e _ => integrable_safeIndicator ρ v e)

/-- The expectation of the safe degree, as a sum over the edges at `v`. -/
theorem safeDegree_expectation_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (v : V) :
    ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω)
      = ∑ e ∈ H.filter (fun e => v ∈ e),
          (1 - (ℙ : Measure Ω).real
            (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})) := by
  have h : (fun ω => (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ))
      = fun ω => ∑ e ∈ H.filter (fun e => v ∈ e), safeIndicator ρ v e ω :=
    funext (fun ω => safeDegree_eq_sum ρ v ω)
  rw [h, integral_finsetSum _ (fun e _ => integrable_safeIndicator ρ v e)]
  exact Finset.sum_congr rfl (fun e _ => integral_safeIndicator ρ v e)

/-! ## The sharp two-sided expectation -/

/-- **Sharp LOWER bound on the expected safe degree** (union bound on the covering events).
`𝔼[safeDeg(v)] ≥ ∑_{e ∋ v} (1 − ∑_{u ∈ e∖v} q_u)`. -/
theorem safeDegree_expectation_ge {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    ∑ e ∈ H.filter (fun e => v ∈ e), (1 - ∑ u ∈ e.erase v, coverRate H p u)
      ≤ ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω) := by
  rw [safeDegree_expectation_eq ρ v]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have hub : (ℙ : Measure Ω).real (⋃ u ∈ e.erase v, {ω | u ∈ covered (retainedSet H ρ ω)})
      ≤ ∑ u ∈ e.erase v, coverRate H p u := by
    refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl
      (fun u _ => prob_vertex_covered_eq ρ hp0 hp1 u))
  linarith

/-- **Sharp UPPER bound on the expected safe degree** (second Bonferroni inequality, with the
pairwise corrections).
`𝔼[safeDeg(v)] ≤ ∑_{e ∋ v} (1 − ∑_{u} q_u + ∑_{u ≠ u'} ℙ(u,u' both covered))`. -/
theorem safeDegree_expectation_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    ∫ ω, (safeDegree H (covered (retainedSet H ρ ω)) v : ℝ) ∂(ℙ : Measure Ω)
      ≤ ∑ e ∈ H.filter (fun e => v ∈ e),
        (1 - ∑ u ∈ e.erase v, coverRate H p u
          + ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
              ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p)) := by
  rw [safeDegree_expectation_eq ρ v]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have hbon := measureReal_biUnion_ge_bonferroni (Ω := Ω) (e.erase v)
    (fun u => {ω | u ∈ covered (retainedSet H ρ ω)})
    (fun u => measurableSet_vertex_covered ρ u)
  have hq : ∀ u ∈ e.erase v, (ℙ : Measure Ω).real {ω | u ∈ covered (retainedSet H ρ ω)}
      = coverRate H p u := fun u _ => prob_vertex_covered_eq ρ hp0 hp1 u
  rw [Finset.sum_congr rfl hq] at hbon
  have hpairs : ∀ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
      (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ ∑ u' ∈ (e.erase v).erase u,
        ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p) :=
    fun u _ => Finset.sum_le_sum (fun u' _ => prob_two_vertices_covered_le ρ hp0 u u')
  have hsum : ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
      (ℙ : Measure Ω).real
        ({ω | u ∈ covered (retainedSet H ρ ω)} ∩ {ω | u' ∈ covered (retainedSet H ρ ω)})
      ≤ ∑ u ∈ e.erase v, ∑ u' ∈ (e.erase v).erase u,
        ((degree H u : ℝ) * (degree H u' : ℝ) * p ^ 2 + (codegree H u u' : ℝ) * p) :=
    Finset.sum_le_sum hpairs
  linarith

end LeanPool.AsymptoticTrianglePacking.Internal
