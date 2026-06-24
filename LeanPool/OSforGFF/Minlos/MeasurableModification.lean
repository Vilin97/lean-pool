/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.Minlos.ProjectiveFamily
import LeanPool.OSforGFF.Minlos.MinlosConcentration
import Mathlib.Topology.Bases
import Mathlib.Topology.ExtendFrom
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable

/-!
# Measurable Modification for Minlos' Theorem

Constructs a measurable **pushforward** from the Kolmogorov extension to the
topological dual.

The key idea: instead of pulling back ν (a measure on E → ℝ) through the
embedding E' ↪ (E → ℝ), we push forward ν through a measurable projection
P : (E → ℝ) → WeakDual ℝ E that agrees with the identity on "good paths"
(ω that are ℚ-linear and bounded on a countable dense subset).

## Main definitions

- `qLinearPaths` — set of ω that are ℚ-linear on the dense sequence (Finsupp version)
- `boundedPaths` — set of ω bounded by a IsHilbertNuclear seminorm (Finsupp version)
- `goodPaths` — intersection (measurable, full measure under ν)
- `measurableProjection` — P : (E → ℝ) → WeakDual ℝ E
- `weakDualEmbed` — the embedding WeakDual ℝ E → (E → ℝ)

## Axioms (6 textbook results)

1. `extensionCLM` — BLT: construct ContinuousLinearMap from good path
2. `extensionCLM_eq_on_dense` — extension agrees with ω on dense sequence
3. `measurable_measurableProjection` — P is measurable
4. `qLinearPaths_ae` — ℚ-linearity a.e. (joint CF → X = 0 a.s.)
5. `boundedPaths_ae` — boundedness a.e. (Markov + CF continuity)
6. `projection_ae_eq` — P(ω)(f) = ω(f) ν-a.e.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3
- Minlos, "Generalized random processes and their extension to measures" (1959)
-/

open BigOperators MeasureTheory Complex TopologicalSpace Finsupp

noncomputable section

-- ae_eq_zero_of_charfun_eq_one is now in MinlosConcentration.lean

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

omit [ContinuousSMul ℝ E] in
/-- The finite supremum of topology-generating seminorms is continuous. -/
private lemma continuous_finset_sup_seminorm (p : ℕ → Seminorm ℝ E)
    (hp_top : WithSeminorms (fun n => p n)) (s : Finset ℕ) :
    Continuous (fun x : E => (s.sup p) x) := by
  refine Seminorm.continuous_of_le ?_ (Seminorm.finset_sup_le_sum p s)
  change Continuous (fun x => Seminorm.coeFnAddMonoidHom ℝ E (∑ i ∈ s, p i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact continuous_finsetSum _ (fun i _ => hp_top.continuous_seminorm i)

/-! ## Embedding: WeakDual ℝ E → (E → ℝ) -/

/-- The evaluation embedding sending a continuous linear functional to its
    underlying function. This is measurable (but NOT a MeasurableEmbedding
    when E is uncountable-dimensional).
-/
def weakDualEmbed (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [hAdd : IsTopologicalAddGroup E] [hSmul : ContinuousSMul ℝ E] :
    WeakDual ℝ E → (E → ℝ) :=
  let _ := hAdd
  let _ := hSmul
  fun l f => (l : E →L[ℝ] ℝ) f

lemma weakDualEmbed_apply (l : WeakDual ℝ E) (f : E) :
    weakDualEmbed E l f = l f := rfl

lemma weakDualEmbed_injective : Function.Injective (weakDualEmbed E) := by
  intro l₁ l₂ h
  have : ∀ f, (l₁ : E →L[ℝ] ℝ) f = (l₂ : E →L[ℝ] ℝ) f := congr_fun h
  exact ContinuousLinearMap.ext this

/-- The embedding is measurable: each coordinate l ↦ l(f) is measurable
    w.r.t. the cylinder σ-algebra (by definition).
-/
lemma measurable_weakDualEmbed : Measurable (weakDualEmbed E) := by
  apply measurable_pi_lambda
  intro f
  exact WeakDual.eval_measurable f

/-! ## Good Paths (Finsupp version) -/

/-- The set of "ℚ-linear paths" on a sequence d : ℕ → E.
    ω respects all finite ℚ-linear combinations:
    ω(∑ cᵢ • d(i)) = ∑ cᵢ * ω(d(i)) for every c : ℕ →₀ ℚ.

    This is a countable intersection (ℕ →₀ ℚ is countable) of measurable sets.
-/
def qLinearPaths (d : ℕ → E) : Set (E → ℝ) :=
  ⋂ (c : ℕ →₀ ℚ),
    { ω | ω (c.sum fun i a => (a : ℝ) • d i) =
      c.sum fun i a => (a : ℝ) * ω (d i) }

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
lemma qLinearPaths_measurableSet (d : ℕ → E) :
    MeasurableSet (qLinearPaths d) := by
  apply MeasurableSet.iInter; intro c
  apply measurableSet_eq_fun
  · exact measurable_pi_apply _
  · simp only [Finsupp.sum]
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply (d i)).const_mul _

/-- The set of "bounded paths" on a sequence d : ℕ → E with respect to
    seminorms p : ℕ → Seminorm ℝ E.
    ω is bounded on all finite ℚ-linear combinations:
    ∃ s : Finset ℕ, ∃ C : ℕ, ∀ c : ℕ →₀ ℚ,
    |ω(∑ cᵢ • d(i))| ≤ C * (s.sup p)(∑ cᵢ • d(i)).

    Combined with ℚ-linearity, this gives uniform continuity of ω on
    the ℚ-span of range(d).

    This is measurable (countable ⋃/⋂ over ℕ × ℕ × (ℕ →₀ ℚ)).
-/
def boundedPaths (d : ℕ → E) (p : ℕ → Seminorm ℝ E) : Set (E → ℝ) :=
  ⋃ (s : Finset ℕ) (C : ℕ), ⋂ (c : ℕ →₀ ℚ),
    { ω | |ω (c.sum fun i a => (a : ℝ) • d i)| ≤
        (C : ℝ) * (s.sup p) (c.sum fun i a => (a : ℝ) • d i) }

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
lemma boundedPaths_measurableSet (d : ℕ → E) (p : ℕ → Seminorm ℝ E) :
    MeasurableSet (boundedPaths d p) := by
  apply MeasurableSet.iUnion; intro s
  apply MeasurableSet.iUnion; intro C
  apply MeasurableSet.iInter; intro c
  exact measurableSet_le
    ((measurable_pi_apply (c.sum fun i a => (a : ℝ) • d i)).norm) measurable_const

/-- The "good paths" set: ω that are ℚ-linear and bounded on the dense sequence.
    This is measurable (countable Boolean operations on measurable sets).
-/
def goodPaths (d : ℕ → E) (p : ℕ → Seminorm ℝ E) : Set (E → ℝ) :=
  qLinearPaths d ∩ boundedPaths d p

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
lemma goodPaths_measurableSet (d : ℕ → E) (p : ℕ → Seminorm ℝ E) :
    MeasurableSet (goodPaths d p) :=
  (qLinearPaths_measurableSet d).inter (boundedPaths_measurableSet d p)

/-! ## Extension on Good Paths -/

/-- The continuous extension function on good paths.
    Uses extendFrom to continuously extend ω from range(d) to all of E.

    ## Construction (BLT / uniform extension theorem)
    1. **Continuous extension**: On good paths, ω restricted to range(d) satisfies
       |ω(d_i) - ω(d_j)| ≤ C * q(d_i - d_j) (from ℚ-linearity + boundedness).
       This gives uniform continuity w.r.t. the seminorm q, so extendFrom gives
       a continuous function g : E → ℝ with g(d_n) = ω(d_n).
    2. **ℚ-linearity of g**: g(a•x + b•y) = a•g(x) + b•g(y) for a, b ∈ ℚ.
       Both sides are continuous in x, y, and agree on range(d) × range(d).
    3. **ℝ-linearity**: g(r•x) = r•g(x) for r ∈ ℝ by density of ℚ in ℝ.

    Ref: Rudin, *Functional Analysis*, Thm 1.18 (bounded linear extension).
-/
noncomputable def extensionFun [hSep : SeparableSpace E] [hNuclear : IsHilbertNuclear E]
    [hNonempty : Nonempty E]
    (d : ℕ → E) (_hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (ω : E → ℝ) (_hω : ω ∈ goodPaths d p) : E → ℝ :=
  let _ := hSep
  let _ := hNuclear
  let _ := hNonempty
  let _ := _hd
  let _ := _hω
  extendFrom (Set.range d) ω

omit [ContinuousSMul ℝ E] in
private lemma extensionFun_eq (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ω : E → ℝ) (hω : ω ∈ goodPaths d p) (n : ℕ)
    [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    extensionFun d hd p ω hω (d n) = ω (d n) := by
  have h_cwat : ContinuousWithinAt ω (Set.range d) (d n) := by
    obtain ⟨hql, hbd⟩ := hω
    simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hbd
    obtain ⟨s, C, hC⟩ := hbd
    -- Key bound: |ω(d m) - ω(d n)| ≤ C * (s.sup p)(d m - d n)
    have h_bound : ∀ m : ℕ, |ω (d m) - ω (d n)| ≤ (C : ℝ) * (s.sup p) (d m - d n) := by
      intro m
      let c : ℕ →₀ ℚ := Finsupp.single m 1 + Finsupp.single n (-1)
      have hql_c := (Set.mem_iInter.mp hql) c
      simp only [Set.mem_setOf_eq] at hql_c
      have hbd_c := hC c
      have h1 : c.sum (fun i a => (a : ℝ) • d i) = d m - d n := by
        change (Finsupp.single m (1 : ℚ) + Finsupp.single n ((-1) : ℚ)).sum _ = _
        rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_smul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        simp [sub_eq_add_neg]
      have h2 : c.sum (fun i a => (a : ℝ) * ω (d i)) = ω (d m) - ω (d n) := by
        change (Finsupp.single m (1 : ℚ) + Finsupp.single n ((-1) : ℚ)).sum _ = _
        rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_mul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        ring
      rw [h1] at hql_c hbd_c
      rwa [(hql_c.trans h2).symm]
    -- Use the bound to prove ContinuousWithinAt
    change Filter.Tendsto ω (nhdsWithin (d n) (Set.range d)) (nhds (ω (d n)))
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCε : (0 : ℝ) < (C : ℝ) + 1 := by positivity
    rw [Filter.Eventually, mem_nhdsWithin]
    have h_cont_sp : Continuous (fun x : E => (s.sup p) x) :=
      continuous_finset_sup_seminorm p hp_top s
    refine ⟨{x | (s.sup p) (x - d n) < ε / ((C : ℝ) + 1)},
      isOpen_lt (h_cont_sp.comp (continuous_sub_right _)) continuous_const,
      by simp only [Set.mem_setOf_eq, sub_self, map_zero]; exact div_pos hε hCε, ?_⟩
    intro x ⟨hx_U, hx_range⟩
    obtain ⟨m, rfl⟩ := hx_range
    simp only [Set.mem_setOf_eq, Real.dist_eq] at hx_U ⊢
    calc |ω (d m) - ω (d n)|
        ≤ (↑C : ℝ) * (s.sup p) (d m - d n) := h_bound m
      _ ≤ (↑C + 1) * (s.sup p) (d m - d n) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
      _ < (↑C + 1) * (ε / (↑C + 1)) := by
          exact mul_lt_mul_of_pos_left hx_U hCε
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hCε)
  exact extendFrom_eq (subset_closure (Set.mem_range_self n)) h_cwat

omit [ContinuousSMul ℝ E] in
private lemma extensionFun_continuous (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ω : E → ℝ) (hω : ω ∈ goodPaths d p)
    [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    Continuous (extensionFun d hd p ω hω) := by
  apply continuous_extendFrom (show Dense (Set.range d) from hd)
  intro x
  obtain ⟨hql, hbd⟩ := hω
  simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hbd
  obtain ⟨s, C, hC⟩ := hbd
  have h_bound : ∀ m n : ℕ, |ω (d m) - ω (d n)| ≤ (C : ℝ) * (s.sup p) (d m - d n) := by
    intro m n
    let c : ℕ →₀ ℚ := Finsupp.single m 1 + Finsupp.single n (-1)
    have hql_c := (Set.mem_iInter.mp hql) c
    simp only [Set.mem_setOf_eq] at hql_c
    have hbd_c := hC c
    have h1 : c.sum (fun i a => (a : ℝ) • d i) = d m - d n := by
      change (Finsupp.single m (1 : ℚ) + Finsupp.single n ((-1) : ℚ)).sum _ = _
      rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_smul]),
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      simp [sub_eq_add_neg]
    have h2 : c.sum (fun i a => (a : ℝ) * ω (d i)) = ω (d m) - ω (d n) := by
      change (Finsupp.single m (1 : ℚ) + Finsupp.single n ((-1) : ℚ)).sum _ = _
      rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_mul]),
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      ring
    rw [h1] at hql_c hbd_c; rw [(hql_c.trans h2).symm]; exact hbd_c
  have h_cont_sp : Continuous (fun x : E => (s.sup p) x) :=
      continuous_finset_sup_seminorm p hp_top s
  -- Image filter is Cauchy in ℝ, hence convergent by completeness
  have h_cauchy : Cauchy (Filter.map ω (nhdsWithin x (Set.range d))) := by
    haveI : (nhdsWithin x (Set.range d)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp
        ((show Dense (Set.range d) from hd).closure_eq ▸ Set.mem_univ _)
    refine ⟨inferInstance, ?_⟩
    rw [Filter.prod_map_map_eq]
    intro V hV
    rw [Filter.mem_map]
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
    have hCε : (0 : ℝ) < (C : ℝ) + 1 := by positivity
    set δ := ε / (2 * ((C : ℝ) + 1)) with hδ_def
    have hδ : 0 < δ := div_pos hε (mul_pos two_pos hCε)
    set A := {y : E | (s.sup p) (y - x) < δ} ∩ Set.range d
    have hA : A ∈ nhdsWithin x (Set.range d) :=
      Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds <|
          (isOpen_lt (h_cont_sp.comp (continuous_sub_right x)) continuous_const).mem_nhds
            (by simp [sub_self, map_zero, hδ]))
        self_mem_nhdsWithin
    exact Filter.mem_prod_iff.mpr ⟨A, hA, A, hA, fun ⟨a, b⟩ ⟨ha, hb⟩ => by
      obtain ⟨m, rfl⟩ := ha.2
      obtain ⟨n, rfl⟩ := hb.2
      apply hεV
      rw [Real.dist_eq]
      calc |ω (d m) - ω (d n)|
          ≤ (C : ℝ) * (s.sup p) (d m - d n) := h_bound m n
        _ ≤ ((C : ℝ) + 1) * (s.sup p) (d m - d n) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
        _ ≤ ((C : ℝ) + 1) * ((s.sup p) (d m - x) + (s.sup p) (d n - x)) := by
            gcongr
            calc (s.sup p) (d m - d n)
                = (s.sup p) ((d m - x) + (x - d n)) := by congr 1; abel
              _ ≤ (s.sup p) (d m - x) + (s.sup p) (x - d n) := (s.sup p).add_le' _ _
              _ = (s.sup p) (d m - x) + (s.sup p) (d n - x) := by
                  congr 1; rw [show x - d n = -(d n - x) from by abel, map_neg_eq_map]
        _ < ((C : ℝ) + 1) * (δ + δ) := by
            apply mul_lt_mul_of_pos_left (add_lt_add ha.1 hb.1) hCε
        _ = ε := by rw [hδ_def]; field_simp; ring⟩
  exact CompleteSpace.complete h_cauchy

omit [ContinuousSMul ℝ E] in
private lemma extensionFun_map_add (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ω : E → ℝ) (hω : ω ∈ goodPaths d p)
    [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    ∀ x y, extensionFun d hd p ω hω (x + y) =
      extensionFun d hd p ω hω x + extensionFun d hd p ω hω y := by
  set g := extensionFun d hd p ω hω
  have hg_cont := extensionFun_continuous d hd p hp_top ω hω
  intro x y
  have hg_eq : ∀ n, g (d n) = ω (d n) := fun n => extensionFun_eq d hd p hp_top ω hω n
  have hql := hω.1
  have hbd : ω ∈ boundedPaths d p := hω.2
  simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hbd
  obtain ⟨s, C, hC⟩ := hbd
  have h_cont_sp : Continuous (fun x : E => (s.sup p) x) :=
      continuous_finset_sup_seminorm p hp_top s
  -- g(d m + d n) = g(d m) + g(d n) via ℚ-linearity + extendFrom_eq
  have hg_add_dense : ∀ m n, g (d m + d n) = g (d m) + g (d n) := by
    intro m n
    -- ℚ-linearity: ω(d m + d n) = ω(d m) + ω(d n)
    let c : ℕ →₀ ℚ := Finsupp.single m 1 + Finsupp.single n 1
    have hql_c := (Set.mem_iInter.mp hql) c
    simp only [Set.mem_setOf_eq] at hql_c
    have h1 : c.sum (fun i a => (a : ℝ) • d i) = d m + d n := by
      change (Finsupp.single m (1 : ℚ) + Finsupp.single n (1 : ℚ)).sum _ = _
      rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_smul]),
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      simp
    have h2 : c.sum (fun i a => (a : ℝ) * ω (d i)) = ω (d m) + ω (d n) := by
      change (Finsupp.single m (1 : ℚ) + Finsupp.single n (1 : ℚ)).sum _ = _
      rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_mul]),
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      simp
    rw [h1] at hql_c
    -- hql_c : ω(d m + d n) = c.sum ... and h2 gives c.sum ... = ω(d m) + ω(d n)
    -- Show g(d m + d n) = ω(d m + d n) using extendFrom_eq + Tendsto
    have hg_at : g (d m + d n) = ω (d m + d n) := by
      apply extendFrom_eq ((show Dense (Set.range d) from hd).closure_eq ▸ Set.mem_univ _)
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hCε : (0 : ℝ) < (C : ℝ) + 1 := by positivity
      rw [Filter.Eventually, mem_nhdsWithin]
      refine ⟨{z | (s.sup p) (z - (d m + d n)) < ε / ((C : ℝ) + 1)},
        isOpen_lt (h_cont_sp.comp (continuous_sub_right _)) continuous_const,
        by simp [sub_self, map_zero, div_pos hε hCε], ?_⟩
      intro z ⟨hz_U, hz_range⟩
      obtain ⟨k, rfl⟩ := hz_range
      simp only [Set.mem_setOf_eq, Real.dist_eq] at hz_U ⊢
      -- |ω(d k) - ω(d m + d n)| via Finsupp single k 1 + single m (-1) + single n (-1)
      let c' : ℕ →₀ ℚ := Finsupp.single k 1 + Finsupp.single m (-1) + Finsupp.single n (-1)
      have hql_c' := (Set.mem_iInter.mp hql) c'
      simp only [Set.mem_setOf_eq] at hql_c'
      have hbd_c' := hC c'
      have h1' : c'.sum (fun i a => (a : ℝ) • d i) = d k - (d m + d n) := by
        change (Finsupp.single k (1 : ℚ) + Finsupp.single m (-1 : ℚ) +
          Finsupp.single n (-1 : ℚ)).sum _ = _
        rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_smul]),
          Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_smul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
          Finsupp.sum_single_index (by simp)]
        simp [sub_eq_add_neg, neg_smul]; abel
      have h2' : c'.sum (fun i a => (a : ℝ) * ω (d i)) =
          ω (d k) - ω (d m) - ω (d n) := by
        change (Finsupp.single k (1 : ℚ) + Finsupp.single m (-1 : ℚ) +
          Finsupp.single n (-1 : ℚ)).sum _ = _
        rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_mul]),
          Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_mul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
          Finsupp.sum_single_index (by simp)]
        push_cast; ring
      rw [h1'] at hql_c' hbd_c'
      -- ω(d m + d n) = ω(d m) + ω(d n) from hql_c
      have h_ω_sum : ω (d m + d n) = ω (d m) + ω (d n) := hql_c.trans h2
      calc |ω (d k) - ω (d m + d n)|
          = |ω (d k - (d m + d n))| := by
              have := hql_c'.trans h2'  -- ω(dk-(dm+dn)) = ω(dk) - ω(dm) - ω(dn)
              rw [h_ω_sum]; congr 1; linarith
        _ ≤ (C : ℝ) * (s.sup p) (d k - (d m + d n)) := hbd_c'
        _ ≤ ((C : ℝ) + 1) * (s.sup p) (d k - (d m + d n)) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
        _ < ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := mul_lt_mul_of_pos_left hz_U hCε
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hCε)
    rw [hg_at, hql_c, h2, hg_eq, hg_eq]
  -- For fixed y ∈ range(d), x ↦ g(x + y) and x ↦ g(x) + g(y) are continuous
  -- and agree on range(d), hence equal everywhere.
  have h_fix_y : ∀ n, ∀ x', g (x' + d n) = g x' + g (d n) := by
    intro n
    exact congr_fun (Continuous.ext_on (show Dense (Set.range d) from hd)
      (hg_cont.comp (continuous_id.add continuous_const))
      (hg_cont.add continuous_const)
      (fun z hz => by obtain ⟨m, rfl⟩ := hz; exact hg_add_dense m n))
  exact congr_fun (Continuous.ext_on (show Dense (Set.range d) from hd)
    (hg_cont.comp (continuous_const.add continuous_id))
    (continuous_const.add hg_cont)
    (fun z hz => by obtain ⟨n, rfl⟩ := hz; exact h_fix_y n x)) y

private lemma extensionFun_map_smul (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ω : E → ℝ) (hω : ω ∈ goodPaths d p)
    [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    ∀ (r : ℝ) x, extensionFun d hd p ω hω (r • x) =
      r * extensionFun d hd p ω hω x := by
  set g := extensionFun d hd p ω hω
  have hg_cont := extensionFun_continuous d hd p hp_top ω hω
  have hg_eq : ∀ n, g (d n) = ω (d n) := fun n => extensionFun_eq d hd p hp_top ω hω n
  have hql := hω.1
  have hbd : ω ∈ boundedPaths d p := hω.2
  simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at hbd
  obtain ⟨s, C, hC⟩ := hbd
  -- Step 1: g(q • d n) = q * g(d n) for q : ℚ (from ℚ-linearity)
  have hg_rat_smul : ∀ (q : ℚ) (n : ℕ), g ((q : ℝ) • d n) = (q : ℝ) * g (d n) := by
    intro q n
    -- ℚ-linearity gives ω(q • d n) = q * ω(d n)
    let c : ℕ →₀ ℚ := Finsupp.single n q
    have hql_c := (Set.mem_iInter.mp hql) c
    simp only [Set.mem_setOf_eq] at hql_c
    have h1 : c.sum (fun i a => (a : ℝ) • d i) = (q : ℝ) • d n := by
      change (Finsupp.single n q).sum _ = _
      rw [Finsupp.sum_single_index (by simp)]
    have h2 : c.sum (fun i a => (a : ℝ) * ω (d i)) = (q : ℝ) * ω (d n) := by
      change (Finsupp.single n q).sum _ = _
      rw [Finsupp.sum_single_index (by simp)]
    rw [h1] at hql_c
    -- hql_c : ω(q • d n) = q * ω(d n) (after rw h2)
    -- Need: g(q • d n) = q * g(d n)
    -- Use extendFrom_eq to show g(q • d n) = ω(q • d n)
    have hg_at : g ((q : ℝ) • d n) = ω ((q : ℝ) • d n) := by
      change extendFrom (Set.range d) ω ((q : ℝ) • d n) = ω ((q : ℝ) • d n)
      apply extendFrom_eq ((show Dense (Set.range d) from hd).closure_eq ▸ Set.mem_univ _)
      -- Tendsto ω (nhdsWithin (q • d n) (range d)) (nhds (ω(q • d n)))
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hCε : (0 : ℝ) < (C : ℝ) + 1 := by positivity
      rw [Filter.Eventually, mem_nhdsWithin]
      have h_cont_sp : Continuous (fun x : E => (s.sup p) x) :=
      continuous_finset_sup_seminorm p hp_top s
      refine ⟨{x | (s.sup p) (x - (q : ℝ) • d n) < ε / ((C : ℝ) + 1)},
        isOpen_lt (h_cont_sp.comp (continuous_sub_right _)) continuous_const,
        by simp [sub_self, map_zero, div_pos hε hCε], ?_⟩
      intro x ⟨hx_U, hx_range⟩
      obtain ⟨m, rfl⟩ := hx_range
      simp only [Set.mem_setOf_eq, Real.dist_eq] at hx_U ⊢
      -- Bound |ω(d m) - ω(q • d n)| using Finsupp single m 1 + single n (-q)
      let c' : ℕ →₀ ℚ := Finsupp.single m 1 + Finsupp.single n (-q)
      have hql_c' := (Set.mem_iInter.mp hql) c'
      simp only [Set.mem_setOf_eq] at hql_c'
      have hbd_c' := hC c'
      have h1' : c'.sum (fun i a => (a : ℝ) • d i) = d m - (q : ℝ) • d n := by
        change (Finsupp.single m (1 : ℚ) + Finsupp.single n (-q)).sum _ = _
        rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_smul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        simp [sub_eq_add_neg, neg_smul]
      have h2' : c'.sum (fun i a => (a : ℝ) * ω (d i)) = ω (d m) - (q : ℝ) * ω (d n) := by
        change (Finsupp.single m (1 : ℚ) + Finsupp.single n (-q)).sum _ = _
        rw [Finsupp.sum_add_index (fun i => by simp) (fun i => by simp [add_mul]),
          Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
        push_cast; ring
      rw [h1'] at hql_c' hbd_c'
      -- hql_c' : ω(dm - q•dn) = ω(dm) - q*ω(dn), hql_c : ω(q•dn) = q*ω(dn)
      have h_ω_qn : ω ((q : ℝ) • d n) = (q : ℝ) * ω (d n) := hql_c.trans h2
      calc |ω (d m) - ω ((q : ℝ) • d n)|
          = |ω (d m) - (q : ℝ) * ω (d n)| := by rw [h_ω_qn]
        _ = |ω (d m - (q : ℝ) • d n)| := by
              have := hql_c'.trans h2'  -- ω(dm - q•dn) = ω(dm) - q*ω(dn)
              congr 1; linarith
        _ ≤ (C : ℝ) * (s.sup p) (d m - (q : ℝ) • d n) := hbd_c'
        _ ≤ ((C : ℝ) + 1) * (s.sup p) (d m - (q : ℝ) • d n) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)
        _ < ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := mul_lt_mul_of_pos_left hx_U hCε
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hCε)
    rw [hg_at, hql_c, h2, hg_eq]
  -- Step 2: For fixed x ∈ range(d), r ↦ g(r • x) and r ↦ r * g(x) are continuous
  -- and agree on ℚ (dense in ℝ), hence equal for all r ∈ ℝ.
  have h_fix_x : ∀ n, ∀ r : ℝ, g (r • d n) = r * g (d n) := by
    intro n
    have h_dense : Dense (Set.range (fun q : ℚ => (q : ℝ))) := Rat.denseRange_cast
    exact congr_fun (Continuous.ext_on h_dense
      (hg_cont.comp (continuous_id.smul continuous_const))
      (continuous_id.mul continuous_const)
      (fun r hr => by obtain ⟨q, rfl⟩ := hr; exact hg_rat_smul q n))
  -- Step 3: For all r, x ↦ g(r • x) and x ↦ r * g(x) are continuous and agree
  -- on range(d), hence equal everywhere.
  intro r
  exact congr_fun (Continuous.ext_on (show Dense (Set.range d) from hd)
    (hg_cont.comp (continuous_const.smul continuous_id))
    (continuous_const.mul hg_cont)
    (fun z hz => by obtain ⟨n, rfl⟩ := hz; exact h_fix_x n r))

/-- The continuous linear extension associated to a good path. -/
noncomputable def extensionCLM [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ω : E → ℝ) (hω : ω ∈ goodPaths d p) :
    WeakDual ℝ E :=
  ⟨{ toFun := extensionFun d hd p ω hω
     map_add' := extensionFun_map_add d hd p hp_top ω hω
     map_smul' := fun r x => by
       simp [extensionFun_map_smul d hd p hp_top ω hω r x, smul_eq_mul] },
   extensionFun_continuous d hd p hp_top ω hω⟩

/-- The extension agrees with ω on the dense sequence.
    Follows from the BLT construction: Dense.extend agrees with ω on range(d).

    Ref: follows from extensionCLM construction.
-/
theorem extensionCLM_eq_on_dense [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ω : E → ℝ) (hω : ω ∈ goodPaths d p) (n : ℕ) :
    (extensionCLM d hd p hp_top ω hω : E →L[ℝ] ℝ) (d n) = ω (d n) :=
  extensionFun_eq d hd p hp_top ω hω n

/-- For a continuous linear functional l, embed(l) ∈ goodPaths.
    Proof: l is ℝ-linear (hence ℚ-linear on all Finsupp combinations),
    and bounded by continuity.
-/
lemma embed_mem_goodPaths [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E)
    (hp_top : WithSeminorms (fun n => p n))
    (l : WeakDual ℝ E) :
    weakDualEmbed E l ∈ goodPaths d p := by
  constructor
  · -- ℚ-linearity: l is ℝ-linear, so l(∑ cᵢ • d(i)) = ∑ cᵢ * l(d(i))
    simp only [qLinearPaths, Set.mem_iInter, Set.mem_setOf_eq]
    intro c
    simp only [weakDualEmbed, Finsupp.sum]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
  · -- Boundedness: l is continuous, hence bounded by finitely many p_n
    simp only [boundedPaths, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
    -- View |l(·)| as a continuous seminorm and apply bound_of_continuous
    have hl_cont : Continuous ((normSeminorm ℝ ℝ).comp l.toLinearMap) := by
      change Continuous (fun x => ‖l x‖)
      exact continuous_norm.comp l.cont
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp_top _ hl_cont
    -- hC : (normSeminorm ℝ ℝ).comp l.toLinearMap ≤ C • s.sup p
    -- i.e., ‖l(x)‖ ≤ C * (s.sup p)(x) for all x
    refine ⟨s, ⌈(C : ℝ)⌉₊, fun c => ?_⟩
    set x := c.sum fun i a => (a : ℝ) • d i
    have h := hC x
    simp only [Seminorm.comp_apply, coe_normSeminorm, Seminorm.smul_apply,
      NNReal.smul_def] at h
    calc |weakDualEmbed E l x| = ‖l x‖ := (Real.norm_eq_abs _).symm
      _ ≤ (C : ℝ) * (s.sup p) x := h
      _ ≤ (↑⌈(C : ℝ)⌉₊ : ℝ) * (s.sup p) x := by
          apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
          exact Nat.le_ceil _

/-- The extension of embed(l) recovers l.
    Proof: both are ContinuousLinearMaps that agree on the dense set D,
    hence they agree everywhere by uniqueness of continuous extension.
-/
lemma extensionCLM_embed [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E)
    (hp_top : WithSeminorms (fun n => p n))
    (l : WeakDual ℝ E) :
    extensionCLM d hd p hp_top (weakDualEmbed E l) (embed_mem_goodPaths d p hp_top l) = l := by
  -- Both are ContinuousLinearMaps: show they're equal as functions E → ℝ
  apply ContinuousLinearMap.ext
  intro f
  -- Both sides are continuous functions E → ℝ that agree on range(d) (dense)
  -- Use Continuous.ext_on: two continuous functions to T2 space agreeing on dense set are equal
  have h_ext := Continuous.ext_on (show Dense (Set.range d) from hd)
    (extensionCLM d hd p hp_top (weakDualEmbed E l) (embed_mem_goodPaths d p hp_top l) :
      E →L[ℝ] ℝ).cont
    (l : E →L[ℝ] ℝ).cont
    (fun x hx => ?_)
  · exact congr_fun h_ext f
  · -- Show agreement on range(d): extensionCLM(embed(l))(d n) = l(d n)
    obtain ⟨n, rfl⟩ := hx
    exact extensionCLM_eq_on_dense d hd p hp_top (weakDualEmbed E l)
      (embed_mem_goodPaths d p hp_top l) n

/-! ## Measurable Projection -/

open Classical in
/-- Auxiliary projection given explicit dense sequence and seminorms.
    On good paths, extends ω to a ContinuousLinearMap; on bad paths, returns 0.
-/
def measurableProjectionAux [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (d : ℕ → E) (hd : DenseRange d)
    (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n)) :
    (E → ℝ) → WeakDual ℝ E :=
  fun ω =>
    if hω : ω ∈ goodPaths d p then
      extensionCLM d hd p hp_top ω hω
    else 0

/-- The measurable projection P : (E → ℝ) → WeakDual ℝ E.

    On good paths (ℚ-linear + bounded on dense sequence), P(ω) is the unique
    continuous linear extension of ω|_D. On bad paths, P(ω) = 0.
-/
def measurableProjection [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    (E → ℝ) → WeakDual ℝ E :=
  measurableProjectionAux (denseSeq E) (denseRange_denseSeq E)
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose_spec.2.1

/-- For each f : E, the evaluation ω ↦ P(ω)(f) is measurable as a function (E → ℝ) → ℝ.
    On goodPaths, P(ω)(f) = lim ω(dₙ) for dₙ → f (pointwise limit of measurable functions).
    On badPaths, P(ω)(f) = 0 (constant, measurable).
-/
private lemma measurable_eval_comp_projection
    [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] (f : E) :
    Measurable (fun ω : E → ℝ => (measurableProjection (E := E) ω : E →L[ℝ] ℝ) f) := by
  classical
  set d := denseSeq E
  set p := (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose
  have hp_top : WithSeminorms (fun n => p n) :=
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose_spec.2.1
  haveI : FirstCountableTopology E := hp_top.firstCountableTopology
  -- Get a sequence d(φ(k)) → f from the dense set
  have hf_mem : f ∈ closure (Set.range d) :=
    (denseRange_denseSeq E).closure_eq ▸ Set.mem_univ f
  obtain ⟨seq, hseq_mem, hseq_tendsto⟩ := mem_closure_iff_seq_limit.mp hf_mem
  choose φ hφ_eq using hseq_mem
  have hφ : Filter.Tendsto (fun k => d (φ k)) Filter.atTop (nhds f) := by
    convert hseq_tendsto using 1; ext k; exact hφ_eq k
  set gP := goodPaths d p
  have hgP_meas : MeasurableSet gP := goodPaths_measurableSet d p
  -- Define the target function
  set g : (E → ℝ) → ℝ := fun ω => (measurableProjection (E := E) ω : E →L[ℝ] ℝ) f
  -- Define approximating functions: F_k(ω) = if ω ∈ goodPaths then ω(d(φ(k))) else 0
  set F : ℕ → (E → ℝ) → ℝ := fun k ω => if ω ∈ gP then ω (d (φ k)) else 0
  have hF_meas : ∀ k, Measurable (F k) := fun k =>
    Measurable.ite hgP_meas (measurable_pi_apply _) measurable_const
  -- Show F_k → g pointwise (as functions in the function space)
  have hF_tendsto : Filter.Tendsto F Filter.atTop (nhds g) := by
    rw [tendsto_pi_nhds]
    intro ω
    show Filter.Tendsto (fun k => F k ω) Filter.atTop (nhds (g ω))
    change Filter.Tendsto (fun k => F k ω) Filter.atTop
      (nhds ((measurableProjectionAux d (denseRange_denseSeq E) p hp_top ω : E →L[ℝ] ℝ) f))
    by_cases hω : ω ∈ gP
    · -- On good paths: F_k(ω) = ω(d(φ(k))) → extensionFun(f) = P(ω)(f)
      simp only [F, if_pos hω]
      -- Unfold measurableProjectionAux using dif_pos
      have h_unfold : (measurableProjectionAux d (denseRange_denseSeq E) p hp_top ω
          : E →L[ℝ] ℝ) f = extensionFun d (denseRange_denseSeq E) p ω hω f := by
        unfold measurableProjectionAux
        rw [dif_pos hω]
        rfl
      rw [h_unfold]
      have hcont := extensionFun_continuous d (denseRange_denseSeq E) p hp_top ω hω
      have htend := hcont.continuousAt.tendsto.comp hφ
      -- extensionFun agrees with ω on d(φ(k))
      convert htend using 1
      ext k
      exact (extensionFun_eq d (denseRange_denseSeq E) p hp_top ω hω (φ k)).symm
    · -- On bad paths: F_k(ω) = 0 → 0 = P(ω)(f)
      simp only [F, if_neg hω]
      have h_unfold : (measurableProjectionAux d (denseRange_denseSeq E) p hp_top ω
          : E →L[ℝ] ℝ) f = 0 := by
        unfold measurableProjectionAux
        rw [dif_neg hω]
        rfl
      rw [h_unfold]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hF_meas hF_tendsto

/-- The projection map is measurable.
    Strategy: The MeasurableSpace on WeakDual is the cylinder σ-algebra (generated
    by evaluations). So measurability of P : (E → ℝ) → WeakDual reduces to showing
    each composition eval_f ∘ P is measurable, which is measurable_eval_comp_projection.

    Ref: standard measurability of piecewise + pointwise limits (Billingsley, §13).
-/
theorem measurable_measurableProjection [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    Measurable (measurableProjection (E := E)) := by
  -- Measurable means: comap P (cylinder σ-algebra) ≤ MeasurableSpace.pi
  -- Cylinder = ⨆_f comap eval_f (borel ℝ)
  -- comap P (⨆_f comap eval_f) = ⨆_f comap (eval_f ∘ P) (by comap_iSup)
  -- Each eval_f ∘ P is pi-measurable (measurable_eval_comp_projection).
  rw [measurable_iff_comap_le]
  change (⨆ (f : E), (borel ℝ).comap (fun l : WeakDual ℝ E =>
    (l : E →L[ℝ] ℝ) f)).comap measurableProjection ≤ MeasurableSpace.pi
  rw [MeasurableSpace.comap_iSup]
  exact iSup_le fun f => by
    rw [MeasurableSpace.comap_comp]
    exact (measurable_eval_comp_projection f).comap_le

/-- The projection composed with the embedding is the identity on WeakDual ℝ E.
    For l ∈ WeakDual ℝ E, embed(l) ∈ goodPaths (l is linear + bounded), and
    extensionCLM(embed(l)) = l by uniqueness of continuous extension from dense.
-/
lemma projection_embed_eq [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E] :
    (measurableProjection (E := E)) ∘ weakDualEmbed E = id := by
  ext l
  simp only [Function.comp_apply, id_eq]
  -- embed(l) ∈ goodPaths
  have hp_top : WithSeminorms (fun n =>
      (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose n) :=
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose_spec.2.1
  -- Unfold to measurableProjectionAux
  change measurableProjectionAux (denseSeq E) (denseRange_denseSeq E)
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose hp_top
    (weakDualEmbed E l) = l
  have h_mem := embed_mem_goodPaths (denseSeq E)
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose hp_top l
  -- dite picks the "if" branch
  simp only [measurableProjectionAux, dif_pos h_mem]
  -- extensionCLM recovers l
  exact extensionCLM_embed (denseSeq E) (denseRange_denseSeq E)
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose hp_top l

/-! ## Almost-everywhere properties

These axioms use the **joint characteristic function** hypothesis:
  h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
    ∫ ω, exp(I * ↑(∑ i, s i * ω(x i))) dν = Φ(∑ i, s i • x i)

This captures all finite-dimensional marginals of ν, not just the 1D marginals.
It is provable from the projective limit property.
-/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- ℚ-linearity holds ν-a.e.

    For fixed c : ℕ →₀ ℚ, the random variable
    X(ω) = ω(∑ cᵢ•dᵢ) - ∑ cᵢ*ω(dᵢ)
    has CF E[e^{itX}] = Φ(t·∑cᵢ•dᵢ - t·∑cᵢ•dᵢ) = Φ(0) = 1
    (using h_cf_joint with test vectors {∑cᵢ•dᵢ, d_{i₁}, ..., d_{iₖ}}
    and scalars {t, -tc₁, ..., -tcₖ}).
    Hence X = 0 a.s. (by Measure.ext_of_charFun with δ₀).
    Countable intersection over c ∈ ℕ →₀ ℚ preserves full measure.

    Ref: Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3.
-/
theorem qLinearPaths_ae [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ qLinearPaths (denseSeq E) := by
  -- For each c : ℕ →₀ ℚ, X(ω) = ω(∑ cᵢ•dᵢ) - ∑ cᵢ*ω(dᵢ) has CF = 1,
  -- hence X = 0 a.s. Countable intersection over ℕ →₀ ℚ.
  simp only [qLinearPaths, Set.mem_iInter, Set.mem_setOf_eq]
  rw [ae_all_iff]
  intro c
  set d := denseSeq E
  set y := c.sum (fun i a => (a : ℝ) • d i) with y_def
  -- Define X(ω) = ω(y) - ∑ cᵢ * ω(dᵢ)
  set X : (E → ℝ) → ℝ := fun ω => ω y - c.sum (fun i a => (a : ℝ) * ω (d i))
  -- X is measurable (difference of coordinate projections)
  have hX_meas : Measurable X := by
    apply Measurable.sub (measurable_pi_apply y)
    simp only [Finsupp.sum]
    exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply (d i)).const_mul _)
  -- Show CF of X is constantly 1, using h_cf_joint
  have hX_cf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * X ω)) ∂ν = 1 := by
    intro t
    -- Construct test vectors and scalars using Fin.cons
    set k := c.support.card with k_def
    -- σ maps Fin k to the support elements
    let σ : Fin k → ℕ := fun j => (c.support.equivFin.symm j : ℕ)
    -- Test vectors: y followed by d(σ(j))
    let x' : Fin (k + 1) → E := Fin.cons y (fun j => d (σ j))
    -- Scalars: t followed by -t * c(σ(j))
    let s' : Fin (k + 1) → ℝ := Fin.cons t (fun j => -t * (c (σ j) : ℝ))
    -- Apply h_cf_joint
    have h := h_cf_joint (k + 1) s' x'
    -- Show ∑ sᵢ • xᵢ = 0 and ∑ sᵢ * ω(xᵢ) = t * X(ω)
    have h_sum_x : ∑ i : Fin (k + 1), s' i • x' i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x']
      have h1 : ∑ j : Fin k, (-t * ↑(c (σ j))) • d (σ j) =
          -(∑ j : Fin k, (t * ↑(c (σ j))) • d (σ j)) := by
        rw [← Finset.sum_neg_distrib]; congr 1; ext j; simp [neg_smul, neg_mul]
      rw [h1]
      have h2 : ∑ j : Fin k, (t * ↑(c (σ j))) • d (σ j) =
          ∑ i ∈ c.support, (t * ↑(c i)) • d i := by
        simp only [← Finset.sum_coe_sort c.support, σ]
        exact Fintype.sum_equiv c.support.equivFin.symm _ _ (fun _ => rfl)
      rw [h2, y_def, Finsupp.sum]
      rw [show t • ∑ a ∈ c.support, (↑(c a) : ℝ) • d a =
          ∑ i ∈ c.support, (t * ↑(c i)) • d i from by
        rw [Finset.smul_sum]; congr 1; ext i; rw [smul_smul]]
      exact add_neg_cancel _
    have h_sum_ω : ∀ ω', (∑ i : Fin (k + 1), s' i * ω' (x' i)) = t * X ω' := by
      intro ω'
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, s', x', X, mul_sub]
      congr 1
      have h1 : ∑ j : Fin k, -t * ↑(c (σ j)) * ω' (d (σ j)) =
          -(t * ∑ j : Fin k, ↑(c (σ j)) * ω' (d (σ j))) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; congr 1; ext j; ring
      rw [h1]
      have h2 : ∑ j : Fin k, ↑(c (σ j)) * ω' (d (σ j)) =
          ∑ i ∈ c.support, ↑(c i) * ω' (d i) := by
        simp only [← Finset.sum_coe_sort c.support, σ]
        exact Fintype.sum_equiv c.support.equivFin.symm _ _ (fun _ => rfl)
      rw [h2, Finsupp.sum]
    rw [h_sum_x, h_normalized] at h
    rwa [show (fun ω' => exp (I * ↑(t * X ω'))) =
      (fun ω' => exp (I * ↑(∑ i : Fin (k + 1), s' i * ω' (x' i)))) from by
      funext ω'; congr 2; exact_mod_cast (h_sum_ω ω').symm]
  -- Apply ae_eq_zero_of_charfun_eq_one
  have := ae_eq_zero_of_charfun_eq_one hX_meas hX_cf
  filter_upwards [this] with ω hω
  -- X(ω) = 0 means ω(y) = ∑ cᵢ * ω(dᵢ)
  linarith [show X ω = 0 from hω]

/-- **Minlos concentration** — see `Minlos.MinlosConcentration`. -/
private lemma boundedPaths_tail_bound [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1)
    (d : ℕ → E) (p : ℕ → Seminorm ℝ E) (hp_top : WithSeminorms (fun n => p n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (C : ℕ),
      ν {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (s.sup p) (c.sum fun i a => (a : ℝ) • d i))} < ENNReal.ofReal ε := by
  set p' := (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose
  have hp'_data := (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose_spec
  have hp'_hilb : ∀ n, (p' n).IsHilbertian := hp'_data.1
  have hp'_top : WithSeminorms (fun n => p' n) := hp'_data.2.1
  have hp'_hs : ∀ n, (p' (n + 1)).IsHilbertSchmidtEmbedding (p' n) := hp'_data.2.2
  -- Apply concentration axiom to nuclear seminorms
  obtain ⟨m, C, hC⟩ := minlos_concentration (E := E) Φ ν h_cf_cont h_cf_joint h_normalized
    d p' hp'_top hp'_hilb hp'_hs ε hε
  have h_pm_cont : Continuous (p' m) := hp'_top.continuous_seminorm m
  obtain ⟨s₀, C', _, hC'⟩ := Seminorm.bound_of_continuous hp_top _ h_pm_cont
  refine ⟨s₀, C * ⌈C'⌉₊, ?_⟩
  apply lt_of_le_of_lt _ hC
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨c, hc⟩ := hω
  refine ⟨c, fun h_le => hc ?_⟩
  set x := c.sum fun i a => (a : ℝ) • d i
  have h_pm_bound : (p' m) x ≤ C' * (s₀.sup p) x := by
    have := hC' x
    simp only [Seminorm.smul_apply, NNReal.smul_def] at this
    exact this
  calc |ω x| ≤ ↑C * (p' m) x := h_le
    _ ≤ ↑C * (C' * (s₀.sup p) x) :=
        mul_le_mul_of_nonneg_left h_pm_bound (Nat.cast_nonneg _)
    _ = (↑C * C') * (s₀.sup p) x := by ring
    _ ≤ (↑C * ↑⌈C'⌉₊) * (s₀.sup p) x := by
        apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
        exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
    _ = (↑(C * ⌈C'⌉₊) : ℝ) * (s₀.sup p) x := by push_cast; ring

/-- Boundedness holds ν-a.e.

    For each element x in the ℚ-span, the Markov/Chebyshev inequality gives:
    P(|ω(x)| ≥ R) ≤ 2(1 - Re(Φ(tx))) for appropriate t.
    By continuity of Φ at 0, the numerator is small when x is in a seminorm ball.
    IsHilbertNuclear Hilbert-Schmidt embeddings give summability over countable
    ℚ-linear combinations, and Borel-Cantelli yields the result.

    Ref: Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3;
    also Billingsley, "Convergence of Probability Measures", §6.
-/
theorem boundedPaths_ae [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_cont : Continuous Φ)
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_normalized : Φ 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ boundedPaths (denseSeq E)
      (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose := by
  set d := denseSeq E
  set p := (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose
  have hp_top : WithSeminorms (fun n => p n) :=
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose_spec.2.1
  rw [ae_iff]
  by_contra h_pos
  rw [← Ne, ← pos_iff_ne_zero] at h_pos
  set ε₀ := (ν {ω | ω ∉ boundedPaths d p}).toReal with hε₀_def
  have hε₀_pos : 0 < ε₀ := by
    rw [hε₀_def]
    exact ENNReal.toReal_pos (ne_of_gt h_pos) (measure_ne_top ν _)
  obtain ⟨s, C, hC⟩ := boundedPaths_tail_bound Φ ν h_cf_cont h_cf_joint
    h_normalized d p hp_top ε₀ hε₀_pos
  have h_subset : {ω | ω ∉ boundedPaths d p} ⊆
      {ω | ∃ c : ℕ →₀ ℚ,
        ¬ (|ω (c.sum fun i a => (a : ℝ) • d i)| ≤
          (C : ℝ) * (s.sup p) (c.sum fun i a => (a : ℝ) • d i))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, boundedPaths, Set.mem_iUnion, Set.mem_iInter] at hω ⊢
    push Not at hω ⊢
    exact hω s C
  have h_lt := lt_of_le_of_lt (measure_mono h_subset) hC
  rw [hε₀_def, ENNReal.ofReal_toReal (measure_ne_top ν _)] at h_lt
  exact absurd h_lt (lt_irrefl _)

/-- The good paths have full ν-measure. Combines ℚ-linearity and boundedness a.e. -/
lemma goodPaths_ae [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_cf_cont : Continuous Φ)
    (h_normalized : Φ 0 = 1) :
    ∀ᵐ ω ∂ν, ω ∈ goodPaths (denseSeq E)
      (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose := by
  have hq := qLinearPaths_ae Φ ν h_cf_joint h_normalized
  have hb := boundedPaths_ae Φ ν h_cf_cont h_cf_joint h_normalized
  filter_upwards [hq, hb] with ω h1 h2
  exact ⟨h1, h2⟩

/-- For each f : E, P(ω)(f) = ω(f) for ν-a.e. ω.

    On good paths (full measure by goodPaths_ae):
    - P(ω)(d_n) = ω(d_n) for all n (by extensionCLM_eq_on_dense)
    - P(ω) is continuous, so P(ω)(d_n) → P(ω)(f) for any d_n → f
    - ω(d_n) → ω(f) in probability: using h_cf_joint with test vectors (f, d_n)
      and scalars (t, -t), CF = Φ(t(f-d_n)) → Φ(0) = 1 by continuity
    - A.s. + in-probability convergence to the same limit → P(ω)(f) = ω(f) a.e.

    Ref: Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. IV, §3.3.
-/
theorem projection_ae_eq [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_cf_cont : Continuous Φ)
    (f : E) :
    ∀ᵐ ω ∂ν, (measurableProjection ω : E →L[ℝ] ℝ) f = ω f := by
  -- Strategy: Define Z(ω) = P(ω)(f) - ω(f), show its CF is constantly 1,
  -- then apply ae_eq_zero_of_charfun_eq_one to get Z = 0 a.e.
  set d := denseSeq E
  set p := (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose
  have hp_top : WithSeminorms (fun n => p n) :=
    (IsHilbertNuclear.nuclear_hilbert_embeddings (E := E)).choose_spec.2.1
  -- Step 0: Derive Φ(0) = 1 from h_cf_joint with n=1
  have h_normalized : Φ 0 = 1 := by
    have h1 := h_cf_joint 1 (fun _ => 0) (fun _ => (0 : E))
    simp at h1
    exact h1.symm
  -- Step 1: Good paths have full measure
  have h_good := goodPaths_ae Φ ν h_cf_joint h_cf_cont h_normalized
  -- Step 2: Choose a sequence d(n_k) → f
  haveI : FirstCountableTopology E := hp_top.firstCountableTopology
  have hf_mem : f ∈ closure (Set.range d) :=
    (denseRange_denseSeq E).closure_eq ▸ Set.mem_univ f
  obtain ⟨seq, hseq_mem, hseq_tendsto⟩ := mem_closure_iff_seq_limit.mp hf_mem
  choose φ hφ_eq using hseq_mem
  have hφ : Filter.Tendsto (fun k => d (φ k)) Filter.atTop (nhds f) := by
    convert hseq_tendsto using 1; ext k; exact hφ_eq k
  -- Step 3: Define Z(ω) = P(ω)(f) - ω(f)
  set Z : (E → ℝ) → ℝ := fun ω => (measurableProjection ω : E →L[ℝ] ℝ) f - ω f
  -- Step 4: Z is measurable
  have hZ_meas : Measurable Z := by
    apply Measurable.sub
    · exact (WeakDual.eval_measurable f).comp measurable_measurableProjection
    · exact measurable_pi_apply f
  -- Step 5: Define approximating sequence Y_k(ω) = ω(d(φ(k))) - ω(f)
  set Y : ℕ → (E → ℝ) → ℝ := fun k ω => ω (d (φ k)) - ω f
  -- Step 6: Show CF of Y_k equals Φ(t(d(φ(k)) - f))
  have hY_cf : ∀ k t, ∫ ω, exp (I * ↑(t * Y k ω)) ∂ν = Φ (t • (d (φ k) - f)) := by
    intro k t
    have h2 := h_cf_joint 2 ![t, -t] ![d (φ k), f]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    have h_lhs : ∀ ω', t * ω' (d (φ k)) + -t * ω' f = t * Y k ω' := by
      intro ω'; simp only [Y]; ring
    conv at h2 =>
      lhs; arg 2; ext ω'
      rw [show t * ω' (d (φ k)) + -t * ω' f = t * Y k ω' from h_lhs ω']
    convert h2 using 2
    rw [smul_sub, sub_eq_add_neg, neg_smul]
  -- Step 7: On good paths, Y_k(ω) → Z(ω)
  have hY_tendsto_Z : ∀ᵐ ω ∂ν, Filter.Tendsto (fun k => Y k ω) Filter.atTop (nhds (Z ω)) := by
    filter_upwards [h_good] with ω hω
    have h_mem : ω ∈ goodPaths d p := hω
    have h_eq_dense : ∀ k, (measurableProjection ω : E →L[ℝ] ℝ) (d (φ k)) = ω (d (φ k)) := by
      intro k
      change (measurableProjectionAux d (denseRange_denseSeq E) p hp_top ω : E →L[ℝ] ℝ) (d (φ k)) =
        ω (d (φ k))
      simp only [measurableProjectionAux, dif_pos h_mem]
      exact extensionCLM_eq_on_dense d (denseRange_denseSeq E) p hp_top ω h_mem (φ k)
    have h_Pω_cont : Continuous (measurableProjection ω : E →L[ℝ] ℝ) :=
      (measurableProjection ω : E →L[ℝ] ℝ).cont
    have h_Pω_tendsto : Filter.Tendsto (fun k => (measurableProjection ω : E →L[ℝ] ℝ) (d (φ k)))
        Filter.atTop (nhds ((measurableProjection ω : E →L[ℝ] ℝ) f)) :=
      h_Pω_cont.continuousAt.tendsto.comp hφ
    have h_ω_tendsto : Filter.Tendsto (fun k => ω (d (φ k)))
        Filter.atTop (nhds ((measurableProjection ω : E →L[ℝ] ℝ) f)) := by
      convert h_Pω_tendsto using 1
      ext k; exact (h_eq_dense k).symm
    exact Filter.Tendsto.sub h_ω_tendsto tendsto_const_nhds
  -- Step 8: Apply DCT + CF convergence to show ∫ exp(it Z) = 1
  have hZ_cf : ∀ t : ℝ, ∫ ω, exp (I * ↑(t * Z ω)) ∂ν = 1 := by
    intro t
    have h_F_meas : ∀ k, AEStronglyMeasurable (fun ω => exp (I * ↑(t * Y k ω))) ν := by
      intro k
      have hY_meas : Measurable (Y k) :=
        (measurable_pi_apply (d (φ k))).sub (measurable_pi_apply f)
      apply Measurable.aestronglyMeasurable
      exact ((hY_meas.const_mul t).complex_ofReal.const_mul I).cexp
    have h_bound : ∀ k, ∀ᵐ ω ∂ν, ‖exp (I * ↑(t * Y k ω))‖ ≤ (1 : ℝ) := by
      intro k
      filter_upwards with ω
      simp [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have h_lim_ae : ∀ᵐ ω ∂ν, Filter.Tendsto (fun k => exp (I * ↑(t * Y k ω)))
        Filter.atTop (nhds (exp (I * ↑(t * Z ω)))) := by
      filter_upwards [hY_tendsto_Z] with ω hω
      apply (Complex.continuous_exp.tendsto _).comp
      apply Filter.Tendsto.const_mul
      exact (Complex.continuous_ofReal.tendsto _).comp (hω.const_mul t)
    have h_dct := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      h_F_meas (integrable_const (1 : ℝ)) h_bound h_lim_ae
    have h_cf_lim : Filter.Tendsto (fun k => ∫ ω, exp (I * ↑(t * Y k ω)) ∂ν)
        Filter.atTop (nhds 1) := by
      rw [show (fun k => ∫ ω, exp (I * ↑(t * Y k ω)) ∂ν) =
        (fun k => Φ (t • (d (φ k) - f))) from funext (fun k => hY_cf k t)]
      rw [← h_normalized]
      apply h_cf_cont.continuousAt.tendsto.comp
      have : Filter.Tendsto (fun k => d (φ k) - f) Filter.atTop (nhds 0) := by
        rw [show (0 : E) = f - f from (sub_self f).symm]
        exact Filter.Tendsto.sub hφ tendsto_const_nhds
      have h_smul := Filter.Tendsto.const_smul this t
      rwa [smul_zero] at h_smul
    exact tendsto_nhds_unique h_dct h_cf_lim
  -- Step 9: Apply ae_eq_zero_of_charfun_eq_one to get Z = 0 a.e.
  have hZ_zero := ae_eq_zero_of_charfun_eq_one hZ_meas hZ_cf
  filter_upwards [hZ_zero] with ω hω
  linarith

/-! ## Derived Properties -/

/-- The pushforward μ = ν.map P is a probability measure when P is measurable. -/
lemma isProbabilityMeasure_map_projection [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (ν.map (measurableProjection (E := E))) :=
  Measure.isProbabilityMeasure_map measurable_measurableProjection.aemeasurable

/-- The characteristic functional of ν.map P equals Φ. -/
lemma charFunctional_map_projection [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (h_cf_joint : ∀ (n : ℕ) (s : Fin n → ℝ) (x : Fin n → E),
      ∫ ω : E → ℝ, exp (I * ↑(∑ i, s i * ω (x i))) ∂ν =
        Φ (∑ i, s i • x i))
    (h_cf_cont : Continuous Φ) :
    ∀ f : E, ∫ l : WeakDual ℝ E, Complex.exp (Complex.I * ↑(l f))
      ∂(ν.map measurableProjection) = Φ f := by
  intro f
  -- Derive the single-variable CF
  have h_cf_single : ∀ f : E, ∫ ω : E → ℝ,
      Complex.exp (Complex.I * ↑(ω f)) ∂ν = Φ f := by
    intro f'
    have := h_cf_joint 1 (fun _ => 1) (fun _ => f')
    simpa using this
  rw [integral_map measurable_measurableProjection.aemeasurable]
  · have h_ae : ∀ᵐ ω ∂ν, (measurableProjection ω : E →L[ℝ] ℝ) f = ω f :=
      projection_ae_eq Φ ν h_cf_joint h_cf_cont f
    rw [← h_cf_single f]
    apply integral_congr_ae
    filter_upwards [h_ae] with ω hω
    simp [hω]
  · exact ((Complex.measurable_ofReal.comp (WeakDual.eval_measurable f)).const_mul
      Complex.I |>.cexp).aestronglyMeasurable

/-- Uniqueness via pushforward factoring: μ' = ν.map P. -/
lemma uniqueness_via_projection [SeparableSpace E] [IsHilbertNuclear E] [Nonempty E]
    (Φ : E → ℂ) (h_continuous : Continuous Φ)
    (h_positive_definite : IsPositiveDefinite Φ) (h_normalized : Φ 0 = 1)
    (ν : Measure (E → ℝ)) [IsProbabilityMeasure ν]
    (hν_eq : ν = marginalProjectiveLimit Φ h_continuous h_positive_definite h_normalized)
    (μ' : ProbabilityMeasure (WeakDual ℝ E))
    (hμ' : ∀ f : E, Φ f = ∫ ω, exp (I * (ω f)) ∂μ'.toMeasure) :
    μ' = ⟨ν.map measurableProjection, isProbabilityMeasure_map_projection ν⟩ := by
  -- Step 1: μ'.toMeasure.map embed = ν (via projective limit uniqueness)
  have h_mu'_proj : IsProjectiveLimit (μ'.toMeasure.map (weakDualEmbed E))
      (marginalFamily Φ h_continuous h_positive_definite h_normalized) := by
    intro J
    simp only [marginalFamily]
    suffices key : ((μ'.toMeasure.map (weakDualEmbed E)).map (Finset.restrict J)).map
        (finsetPiMeasEquiv J) =
        (marginalMeasure Φ h_continuous h_positive_definite h_normalized J :
          Measure _) by
      have := congr_arg (fun μ => μ.map (finsetPiMeasEquiv J).symm) key
      simp only [Measure.map_map (finsetPiMeasEquiv J).symm.measurable
        (finsetPiMeasEquiv J).measurable,
        (finsetPiMeasEquiv J).symm_comp_self, Measure.map_id] at this
      exact this
    apply Measure.ext_of_charFun
    ext ξ
    rw [marginalMeasure_charFun]
    rw [Measure.map_map (finsetPiMeasEquiv J).measurable (Finset.measurable_restrict J),
      Measure.map_map ((finsetPiMeasEquiv J).measurable.comp
        (Finset.measurable_restrict J)) measurable_weakDualEmbed]
    rw [charFun_apply,
      integral_map
        (((finsetPiMeasEquiv J).measurable.comp (Finset.measurable_restrict J)).comp
          measurable_weakDualEmbed).aemeasurable
        (by fun_prop : AEStronglyMeasurable _ _)]
    have h_inner_eq : ∀ l : WeakDual ℝ E,
        @inner ℝ _ _ (((⇑(finsetPiMeasEquiv J) ∘ Finset.restrict J) ∘
          weakDualEmbed E) l) ξ =
        l (∑ k : Fin J.card, (ξ k) • finsetTestVectors J k) := by
      intro l
      simp only [PiLp.inner_apply,
        finsetPiMeasEquiv, finsetReindexEquiv, finsetTestVectors,
        MeasurableEquiv.trans_apply, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        MeasurableEquiv.coe_toLp, Function.comp_apply, Finset.restrict,
        weakDualEmbed]
      simp only [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from
        fun a b => RCLike.inner_apply a b]
      rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
    simp_rw [h_inner_eq, mul_comm _ Complex.I]
    rw [← hμ']
    rfl
  have h_mu'_embed : μ'.toMeasure.map (weakDualEmbed E) = ν := by
    rw [hν_eq]
    exact marginalProjectiveLimit_unique Φ h_continuous h_positive_definite h_normalized
      h_mu'_proj
  -- Step 2: μ' = (μ'.map embed).map P = ν.map P = μ
  apply Subtype.ext
  change μ'.toMeasure = ν.map measurableProjection
  rw [← h_mu'_embed]
  rw [Measure.map_map measurable_measurableProjection measurable_weakDualEmbed]
  rw [show measurableProjection ∘ weakDualEmbed E = id from projection_embed_eq]
  simp [Measure.map_id]

end
