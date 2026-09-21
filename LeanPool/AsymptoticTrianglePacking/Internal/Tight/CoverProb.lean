/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the SHARP one-round covering probabilities

Standalone, Mathlib-only.  This file supplies the *sharp* first-moment brick of one nibble round,
the one the loose brackets `residual_degree_expectation_lower` (`deg·(1 − rΔp)`) and
`residual_degree_expectation_upper` (`deg·(1 − p(1−p)^{rΔ})`) fail to give: the covering probability
of a vertex is computed EXACTLY, and the survival probability of an edge is sandwiched between two
expressions that agree to second order.

* `coverRate H p x` — the exact one-round covering rate `∑_{f ∋ x} p(1−p)^{c(f)}` of a vertex.
* `prob_vertex_covered_eq` — `ℙ(x covered) = coverRate H p x`.  The point: the events "`f` is in the
  round matching", for the edges `f ∋ x`, are pairwise DISJOINT (a matching has at most one edge at
  `x`), so the union bound `prob_vertex_covered` is in fact an equality.
* `measureReal_biUnion_ge_bonferroni` — the second Bonferroni inequality for a `Finset`-indexed
  family (not in Mathlib): `ℙ(⋃ᵢ Aᵢ) ≥ ∑ᵢ ℙ(Aᵢ) − ∑ᵢ∑_{j≠i} ℙ(Aᵢ ∩ Aⱼ)`.
* `prob_two_vertices_covered_le` — `ℙ(x covered ∧ y covered) ≤ deg(x)·deg(y)·p² + codeg(x,y)·p`
  for `x ≠ y`: the second-order term is quadratically small in the nibble regime `p ≈ γ/(rd)` as soon
  as the codegree is `o(d)`.

placeholder-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.Round
import LeanPool.AsymptoticTrianglePacking.Internal.Conflict
import LeanPool.AsymptoticTrianglePacking.Internal.Survival
import LeanPool.AsymptoticTrianglePacking.Internal.Covered
import LeanPool.AsymptoticTrianglePacking.Internal.CoveredExpectation
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory ProbabilityTheory Finset Hypergraph
open scoped Classical

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasureSpace Ω]
  [IsProbabilityMeasure (ℙ : Measure Ω)]

/-! ## The exact covering rate of a vertex -/

/-- **The exact one-round covering rate of a vertex.**  `∑_{f ∋ x} p·(1−p)^{c(f)}`, where `c(f)` is
the number of edges conflicting with `f`.  By `prob_vertex_covered_eq` this is *exactly* the
probability that `x` is covered by the round matching. -/
noncomputable def coverRate (H : Finset (Finset V)) (p : ℝ) (x : V) : ℝ :=
  ∑ f ∈ H.filter (fun f => x ∈ f), p * (1 - p) ^ (conflicts H f).card

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem coverRate_nonneg {H : Finset (Finset V)} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : V) :
    0 ≤ coverRate H p x :=
  Finset.sum_nonneg fun f _ => mul_nonneg hp0 (pow_nonneg (by linarith) _)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covering rate is at most `deg(x)·p`. -/
theorem coverRate_le {H : Finset (Finset V)} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : V) :
    coverRate H p x ≤ (degree H x : ℝ) * p := by
  have hterm : ∀ f ∈ H.filter (fun f => x ∈ f), p * (1 - p) ^ (conflicts H f).card ≤ p := by
    intro f _
    calc p * (1 - p) ^ (conflicts H f).card ≤ p * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (by linarith) (by linarith)) hp0
      _ = p := by ring
  calc coverRate H p x ≤ ∑ _f ∈ H.filter (fun f => x ∈ f), p := Finset.sum_le_sum hterm
    _ = (degree H x : ℝ) * p := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The covering event of a vertex is the (disjoint) union of the matching events of the edges
through it. -/
theorem vertexCovered_eq_biUnion {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (x : V) :
    {ω | x ∈ covered (retainedSet H ρ ω)}
      = ⋃ f ∈ H.filter (fun f => x ∈ f), {ω | f ∈ roundMatching (retainedSet H ρ ω)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, covered, support,
    Finset.mem_biUnion, id_eq, exists_prop]
  constructor
  · rintro ⟨f, hf, hxf⟩
    have hfH : f ∈ H := (Finset.filter_subset _ _) (roundMatching_subset _ hf)
    exact ⟨f, ⟨hfH, hxf⟩, hf⟩
  · rintro ⟨f, ⟨_, hxf⟩, hf⟩
    exact ⟨f, hf, hxf⟩

/-- **The exact per-vertex covering probability.**  `ℙ(x covered) = ∑_{f ∋ x} p(1−p)^{c(f)}`.
Equality (not just the union bound `prob_vertex_covered`) because the matching events of the edges
through `x` are pairwise disjoint. -/
theorem prob_vertex_covered_eq {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : V) :
    (ℙ : Measure Ω).real {ω | x ∈ covered (retainedSet H ρ ω)} = coverRate H p x := by
  have hdisj : (↑(H.filter (fun f => x ∈ f)) : Set (Finset V)).PairwiseDisjoint
      (fun f => {ω | f ∈ roundMatching (retainedSet H ρ ω)}) := by
    intro f hf g hg hfg
    simp only [Function.onFun, Set.disjoint_left, Set.mem_setOf_eq]
    intro ω hωf hωg
    have hxf : x ∈ f := (Finset.mem_filter.mp (Finset.mem_coe.mp hf)).2
    have hxg : x ∈ g := (Finset.mem_filter.mp (Finset.mem_coe.mp hg)).2
    have hd : Disjoint g f :=
      (roundMatching_isMatching (subset_refl (retainedSet H ρ ω))).disjoint g hωg f hωf
        (Ne.symm hfg)
    exact (Finset.disjoint_left.mp hd hxg) hxf
  have hmeas : ∀ f ∈ H.filter (fun f => x ∈ f),
      MeasurableSet {ω | f ∈ roundMatching (retainedSet H ρ ω)} :=
    fun f hf => measurableSet_matchingEvent ρ (Finset.mem_filter.mp hf).1
  rw [vertexCovered_eq_biUnion ρ x, measureReal_def, measure_biUnion_finset hdisj hmeas]
  rw [ENNReal.toReal_sum (fun f _ => measure_ne_top _ _)]
  refine Finset.sum_congr rfl (fun f hf => ?_)
  have hfH : f ∈ H := (Finset.mem_filter.mp hf).1
  rw [matchingEvent_eq ρ hfH, edge_survives_prob ρ hp0 hp1 hfH,
    ENNReal.toReal_ofReal (mul_nonneg hp0 (pow_nonneg (by linarith) _))]

/-! ## A Bonferroni inequality -/

/-- **The second Bonferroni inequality** for a `Finset`-indexed family of measurable sets:
`ℙ(⋃ᵢ Aᵢ) ≥ ∑ᵢ ℙ(Aᵢ) − ∑ᵢ ∑_{j ≠ i} ℙ(Aᵢ ∩ Aⱼ)`.  (Mathlib has the union bound but not this
complementary direction.) -/
theorem measureReal_biUnion_ge_bonferroni {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    ∑ i ∈ s, (ℙ : Measure Ω).real (A i)
        - ∑ i ∈ s, ∑ j ∈ s.erase i, (ℙ : Measure Ω).real (A i ∩ A j)
      ≤ (ℙ : Measure Ω).real (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hUmeas : MeasurableSet (⋃ i ∈ s, A i) :=
      MeasurableSet.biUnion s.countable_toSet (fun i _ => hA i)
    have hsplit : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
      simp
    have hadd : (ℙ : Measure Ω).real (A a ∪ ⋃ i ∈ s, A i)
        + (ℙ : Measure Ω).real (A a ∩ ⋃ i ∈ s, A i)
        = (ℙ : Measure Ω).real (A a) + (ℙ : Measure Ω).real (⋃ i ∈ s, A i) :=
      measureReal_union_add_inter (μ := (ℙ : Measure Ω)) (s := A a) hUmeas
        (measure_ne_top _ _) (measure_ne_top _ _)
    have hint : (ℙ : Measure Ω).real (A a ∩ ⋃ i ∈ s, A i)
        ≤ ∑ j ∈ s, (ℙ : Measure Ω).real (A a ∩ A j) := by
      have hsub : A a ∩ (⋃ i ∈ s, A i) = ⋃ i ∈ s, (A a ∩ A i) := by
        rw [Set.inter_iUnion₂]
      rw [hsub]
      exact measureReal_biUnion_finset_le _ _
    have hrow : ∑ j ∈ (insert a s).erase a, (ℙ : Measure Ω).real (A a ∩ A j)
        = ∑ j ∈ s, (ℙ : Measure Ω).real (A a ∩ A j) := by
      rw [Finset.erase_insert ha]
    have hmono : ∀ i ∈ s, ∑ j ∈ s.erase i, (ℙ : Measure Ω).real (A i ∩ A j)
        ≤ ∑ j ∈ (insert a s).erase i, (ℙ : Measure Ω).real (A i ∩ A j) := by
      intro i _
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => measureReal_nonneg)
      exact Finset.erase_subset_erase i (Finset.subset_insert a s)
    have hsum2 : ∑ i ∈ insert a s, ∑ j ∈ (insert a s).erase i,
          (ℙ : Measure Ω).real (A i ∩ A j)
        = ∑ j ∈ s, (ℙ : Measure Ω).real (A a ∩ A j)
          + ∑ i ∈ s, ∑ j ∈ (insert a s).erase i, (ℙ : Measure Ω).real (A i ∩ A j) := by
      rw [Finset.sum_insert ha, hrow]
    have hsum1 : ∑ i ∈ insert a s, (ℙ : Measure Ω).real (A i)
        = (ℙ : Measure Ω).real (A a) + ∑ i ∈ s, (ℙ : Measure Ω).real (A i) :=
      Finset.sum_insert ha
    rw [hsplit, hsum1, hsum2]
    have hbig : ∑ i ∈ s, ∑ j ∈ s.erase i, (ℙ : Measure Ω).real (A i ∩ A j)
        ≤ ∑ i ∈ s, ∑ j ∈ (insert a s).erase i, (ℙ : Measure Ω).real (A i ∩ A j) :=
      Finset.sum_le_sum hmono
    linarith only [hadd, hint, ih, hbig]

/-! ## Two vertices covered simultaneously -/

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- Two distinct edges are retained simultaneously with probability `p²` (pairwise independence). -/
theorem prob_two_retained {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) {f g : Finset V} (hf : f ∈ H) (hg : g ∈ H)
    (hne : f ≠ g) :
    (ℙ : Measure Ω) (ρ.A f ∩ ρ.A g) = ENNReal.ofReal p * ENNReal.ofReal p := by
  have h := (iIndepSet_iff (fun e => ρ.A e) (ℙ : Measure Ω)).mp ρ.indep {f, g}
    (f := fun e => ρ.A e)
    (fun i _ => MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _))
  have hint : (⋂ i ∈ ({f, g} : Finset (Finset V)), ρ.A i) = ρ.A f ∩ ρ.A g := by
    ext ω; simp
  rw [hint] at h
  rw [h, Finset.prod_pair hne, ρ.prob f hf, ρ.prob g hg]

/-- **A second-order bound on the joint covering probability.**  For `x ≠ y`,
`ℙ(x covered ∧ y covered) ≤ deg(x)·deg(y)·p² + codeg(x,y)·p`.  In the nibble regime `p = γ/(r d)`
with degrees `≈ d` and codegree `≤ μd` this is `O(γ²/r² + μγ/r)`, i.e. genuinely of second order
against the first-order covering rate `≈ γ/r`. -/
theorem prob_two_vertices_covered_le {H : Finset (Finset V)} {p : ℝ}
    (ρ : BernoulliRetention (Ω := Ω) H p) (hp0 : 0 ≤ p) (x y : V) :
    (ℙ : Measure Ω).real
        ({ω | x ∈ covered (retainedSet H ρ ω)} ∩ {ω | y ∈ covered (retainedSet H ρ ω)})
      ≤ (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 + (codegree H x y : ℝ) * p := by
  classical
  set Sx := H.filter (fun f => x ∈ f) with hSx
  set Sy := H.filter (fun f => y ∈ f) with hSy
  have hsub : ({ω | x ∈ covered (retainedSet H ρ ω)} ∩ {ω | y ∈ covered (retainedSet H ρ ω)})
      ⊆ (⋃ f ∈ Sx, ⋃ g ∈ Sy.erase f, (ρ.A f ∩ ρ.A g)) ∪ (⋃ f ∈ Sx ∩ Sy, ρ.A f) := by
    rintro ω ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, covered, support, Finset.mem_biUnion, id_eq] at hx hy
    obtain ⟨f, hfM, hxf⟩ := hx
    obtain ⟨g, hgM, hyg⟩ := hy
    have hfR : f ∈ retainedSet H ρ ω := roundMatching_subset _ hfM
    have hgR : g ∈ retainedSet H ρ ω := roundMatching_subset _ hgM
    have hfH : f ∈ H := (Finset.mem_filter.mp hfR).1
    have hgH : g ∈ H := (Finset.mem_filter.mp hgR).1
    have hfA : ω ∈ ρ.A f := (Finset.mem_filter.mp hfR).2
    have hgA : ω ∈ ρ.A g := (Finset.mem_filter.mp hgR).2
    by_cases hfg : f = g
    · refine Or.inr ?_
      rw [Set.mem_iUnion₂]
      refine ⟨f, ?_, hfA⟩
      rw [Finset.mem_inter, hSx, hSy]
      exact ⟨Finset.mem_filter.mpr ⟨hfH, hxf⟩, Finset.mem_filter.mpr ⟨hfH, hfg ▸ hyg⟩⟩
    · refine Or.inl ?_
      rw [Set.mem_iUnion₂]
      refine ⟨f, Finset.mem_filter.mpr ⟨hfH, hxf⟩, ?_⟩
      rw [Set.mem_iUnion₂]
      exact ⟨g, Finset.mem_erase.mpr ⟨fun h => hfg h.symm, Finset.mem_filter.mpr ⟨hgH, hyg⟩⟩,
        ⟨hfA, hgA⟩⟩
  have hpairs : ∀ f ∈ Sx, ∀ g ∈ Sy.erase f,
      (ℙ : Measure Ω).real (ρ.A f ∩ ρ.A g) ≤ p ^ 2 := by
    intro f hf g hg
    have hne : f ≠ g := fun h => (Finset.mem_erase.mp hg).1 h.symm
    have hfH : f ∈ H := (Finset.mem_filter.mp hf).1
    have hgH : g ∈ H := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hg)).1
    rw [measureReal_def, prob_two_retained ρ hfH hgH hne,
      ← ENNReal.ofReal_mul hp0, ENNReal.toReal_ofReal (by positivity)]
    linarith
  have hsingle : ∀ f ∈ Sx ∩ Sy, (ℙ : Measure Ω).real (ρ.A f) ≤ p := by
    intro f hf
    have hfH : f ∈ H := (Finset.mem_filter.mp (Finset.mem_of_mem_inter_left hf)).1
    rw [measureReal_def, ρ.prob f hfH, ENNReal.toReal_ofReal hp0]
  have hcard_inter : (Sx ∩ Sy).card = codegree H x y := by
    have : Sx ∩ Sy = H.filter (fun e => x ∈ e ∧ y ∈ e) := by
      rw [hSx, hSy]
      ext e
      simp [Finset.mem_filter, Finset.mem_inter]
      tauto
    rw [this]; rfl
  calc (ℙ : Measure Ω).real
        ({ω | x ∈ covered (retainedSet H ρ ω)} ∩ {ω | y ∈ covered (retainedSet H ρ ω)})
      ≤ (ℙ : Measure Ω).real ((⋃ f ∈ Sx, ⋃ g ∈ Sy.erase f, (ρ.A f ∩ ρ.A g))
          ∪ (⋃ f ∈ Sx ∩ Sy, ρ.A f)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (ℙ : Measure Ω).real (⋃ f ∈ Sx, ⋃ g ∈ Sy.erase f, (ρ.A f ∩ ρ.A g))
          + (ℙ : Measure Ω).real (⋃ f ∈ Sx ∩ Sy, ρ.A f) := measureReal_union_le _ _
    _ ≤ (∑ f ∈ Sx, ∑ g ∈ Sy.erase f, (ℙ : Measure Ω).real (ρ.A f ∩ ρ.A g))
          + ∑ f ∈ Sx ∩ Sy, (ℙ : Measure Ω).real (ρ.A f) := by
        refine add_le_add ?_ (measureReal_biUnion_finset_le _ _)
        refine le_trans (measureReal_biUnion_finset_le _ _) ?_
        exact Finset.sum_le_sum (fun f _ => measureReal_biUnion_finset_le _ _)
    _ ≤ (∑ _f ∈ Sx, ∑ _g ∈ Sy, p ^ 2) + ∑ _f ∈ Sx ∩ Sy, p := by
        refine add_le_add ?_ (Finset.sum_le_sum hsingle)
        refine Finset.sum_le_sum (fun f hf => ?_)
        refine le_trans (Finset.sum_le_sum (fun g hg => hpairs f hf g hg)) ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Sy.erase f).card : ℝ) ≤ (Sy.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
        nlinarith [sq_nonneg p]
    _ = (degree H x : ℝ) * (degree H y : ℝ) * p ^ 2 + (codegree H x y : ℝ) * p := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard_inter]
        have hdx : (Sx.card : ℝ) = (degree H x : ℝ) := rfl
        have hdy : (Sy.card : ℝ) = (degree H y : ℝ) := rfl
        rw [hdx, hdy]
        ring

end LeanPool.AsymptoticTrianglePacking.Internal
