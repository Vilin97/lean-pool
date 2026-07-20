/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Unconditional Schauder Bases

Source: doi:10.1007/978-3-662-53294-2
Authors: Daniel Smania
Status: verified
Main declarations: `UnconditionalCriterion.exists_unconditionalSchauderBasis_of_finiteSignBound`
Tags: functional-analysis, banach-spaces, schauder-bases
MSC: 46B15
-/

/-!
# Schauder bases and the finite sign criterion

This file develops a small API for Schauder bases and proves a finite sign
criterion for constructing unconditional Schauder bases.

The main ingredients are:

* `SchauderBasis` and `UnconditionalSchauderBasis`, the usual `ℕ`-indexed
  notions. A Schauder expansion is ordered, so its convergence is expressed by
  initial partial sums.
* Rearrangement criteria for `SchauderBasis.IsUnconditional`, including
  `HasSum` reindexing, convergence over the finite-set filter, and the
  classical ordered partial-sum criterion for every permutation of `ℕ`.
* `UnconditionalSchauderBasisAbstractIndex` is indexed by an arbitrary type.
  Its expansion uses `HasSum`, which is the unconditional finite-set filter.
* `UnconditionalCriterion.exists_unconditionalSchauderBasisAbstractIndex_of_finiteSignBound`
  and `UnconditionalCriterion.exists_unconditionalSchauderBasis_of_finiteSignBound`,
  which package the construction of an unconditional Schauder basis from a
  uniform finite sign estimate, dense span, and nonzero vectors.

The finite sign criterion is first proved for an arbitrary index type. The
usual `ℕ`-indexed theorem is then recovered by enumeration with
`Equiv.refl ℕ`.
-/

noncomputable section

open Filter

open scoped BigOperators
open scoped Topology

/-!
## `ℕ`-indexed Schauder bases

The ordered notion of a Schauder sum is separated out because it is weaker than
`HasSum`: a Schauder basis need only converge along the initial segments
`Finset.range N`.
-/

/--
The ordered partial-sum convergence used by Schauder bases.

`HasSchauderSum basis a x` means that
`∑ n ∈ Finset.range N, a n • basis n` tends to `x` as `N → ∞`.
-/
def HasSchauderSum {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (basis : ℕ → E) (a : ℕ → 𝕜) (x : E) : Prop :=
  Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, a n • basis n) atTop (𝓝 x)

/--
A Schauder basis for a complete normed space.

For each vector `x`, the initial partial sums of the coordinate expansion
converge to `x`, and this expansion is unique. The coordinate maps are stored
as continuous linear maps.
-/
structure SchauderBasis (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- Basis vectors. -/
  basis : ℕ → E
  /-- Continuous coordinate maps. -/
  coeff : ℕ → E →L[𝕜] 𝕜
  /-- Every vector equals the limit of the initial partial sums of its expansion. -/
  hasSchauderSum_repr : ∀ x : E, HasSchauderSum basis (fun n : ℕ => coeff n x) x
  /-- Coefficients in this expansion are unique. -/
  unique_coeff :
    ∀ (x : E) (a : ℕ → 𝕜), HasSchauderSum basis a x →
      a = fun n : ℕ => coeff n x

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The `n`th coordinate of `x` in the basis `b`. -/
def coord (b : SchauderBasis 𝕜 E) (n : ℕ) (x : E) : 𝕜 :=
  b.coeff n x

@[simp]
private theorem hasSchauderSum_repr_apply (b : SchauderBasis 𝕜 E) (x : E) :
    HasSchauderSum b.basis (fun n : ℕ => b.coeff n x) x :=
  b.hasSchauderSum_repr x

/--
Combinatorial enumeration of a strictly increasing exhaustion by finite sets.

If `A 0 = ∅`, `A n` is strictly increasing, and the union of the `A n` is all
of `ℕ`, then one can enumerate the naturals block by block so that the initial
segments of the enumeration are exactly the sets `A n`.  The intended
checkpoints are `k n = (A n).card`.
-/
private theorem exists_perm_subseq_range_image_of_monotone_finset
    (A : ℕ → Finset ℕ)
    (hA_zero : A 0 = ∅)
    (hA_mono : Monotone A)
    (hA_strict : ∀ n : ℕ, A n ⊂ A (n + 1))
    (hA_cover : ∀ m : ℕ, ∃ n : ℕ, m ∈ A n) :
    ∃ σ : Equiv.Perm ℕ,
      ∀ n : ℕ, (Finset.range (A n).card).image (fun i : ℕ => σ i) = A n := by
  classical
  let block : ℕ → List ℕ := fun n => (A (n + 1) \ A n).sort (· ≤ ·)
  let L : ℕ → List ℕ := Nat.rec [] fun n l => l ++ block n
  have hL_succ (n : ℕ) : L (n + 1) = L n ++ block n := by
    simp [L]
  have hL_prefix_succ (n : ℕ) : L n <+: L (n + 1) := by
    rw [hL_succ n]
    exact (L n).prefix_append (block n)
  have hL_prefix : ∀ {n m : ℕ}, n ≤ m → L n <+: L m := by
    intro n m hnm
    induction hnm with
    | refl => rfl
    | step hnm ih => exact ih.trans (hL_prefix_succ _)
  have hL_toFinset : ∀ n : ℕ, (L n).toFinset = A n := by
    intro n
    induction n with
    | zero =>
        simp [L, hA_zero]
    | succ n ih =>
        rw [hL_succ n, List.toFinset_append, ih]
        simp [block, Finset.sort_toFinset, Finset.union_sdiff_of_subset (hA_mono (Nat.le_succ n))]
  have hL_nodup : ∀ n : ℕ, (L n).Nodup := by
    intro n
    induction n with
    | zero =>
        simp [L]
    | succ n ih =>
        rw [hL_succ n]
        refine ih.append ((A (n + 1) \ A n).sort_nodup (· ≤ ·)) ?_
        intro x hxL hxB
        have hxA : x ∈ A n := by
          simpa [← hL_toFinset n, List.mem_toFinset] using hxL
        have hxD : x ∈ A (n + 1) \ A n := by
          simpa [block, Finset.mem_sort] using hxB
        exact (Finset.mem_sdiff.mp hxD).2 hxA
  have hL_length (n : ℕ) : (L n).length = (A n).card := by
    simpa [hL_toFinset n] using (List.toFinset_card_of_nodup (hL_nodup n)).symm
  have hA_card_ge : ∀ n : ℕ, n ≤ (A n).card := by
    intro n
    induction n with
    | zero => simp [hA_zero]
    | succ n ih =>
        have hcard_lt : (A n).card < (A (n + 1)).card :=
          Finset.card_lt_card (hA_strict n)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hcard_lt)
  let σFun : ℕ → ℕ := fun i =>
    (L (i + 1)).get ⟨i, by
      rw [hL_length (i + 1)]
      exact (Nat.lt_succ_self i).trans_le (hA_card_ge (i + 1))⟩
  have hσFun_eq_get (n i : ℕ) (hi : i < (L n).length) :
      σFun i = (L n).get ⟨i, hi⟩ := by
    have hiσ : i < (L (i + 1)).length := by
      rw [hL_length (i + 1)]
      exact (Nat.lt_succ_self i).trans_le (hA_card_ge (i + 1))
    unfold σFun
    rcases le_total (i + 1) n with hin | hni
    · exact List.IsPrefix.getElem (hL_prefix hin) hiσ
    · exact (List.IsPrefix.getElem (hL_prefix hni) hi).symm
  have hσFun_inj : Function.Injective σFun := by
    intro i j hij
    let n := max (i + 1) (j + 1)
    have hiL : i < (L n).length := by
      rw [hL_length]
      exact (Nat.lt_succ_self i).trans_le
        ((Nat.le_max_left (i + 1) (j + 1)).trans (hA_card_ge n))
    have hjL : j < (L n).length := by
      rw [hL_length]
      exact (Nat.lt_succ_self j).trans_le
        ((Nat.le_max_right (i + 1) (j + 1)).trans (hA_card_ge n))
    have hget :
        (L n).get ⟨i, hiL⟩ = (L n).get ⟨j, hjL⟩ := by
      rw [← hσFun_eq_get n i hiL, ← hσFun_eq_get n j hjL, hij]
    exact congr_arg Fin.val ((hL_nodup n).injective_get hget)
  have hσFun_surj : Function.Surjective σFun := by
    intro x
    obtain ⟨n, hxA⟩ := hA_cover x
    have hxL : x ∈ L n := by
      simpa [← hL_toFinset n, List.mem_toFinset] using hxA
    obtain ⟨i, hix⟩ := List.mem_iff_get.mp hxL
    refine ⟨i, ?_⟩
    rw [hσFun_eq_get n i i.2, hix]
  let σ : Equiv.Perm ℕ := Equiv.ofBijective σFun ⟨hσFun_inj, hσFun_surj⟩
  refine ⟨σ, ?_⟩
  intro n
  ext x
  constructor
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, hix⟩ := hx
    have hiL : i < (L n).length := by
      simpa [hL_length n] using hi
    have hxL : x ∈ L n := by
      rw [← hix]
      change σFun i ∈ L n
      rw [hσFun_eq_get n i hiL]
      exact List.get_mem _ _
    simpa [← hL_toFinset n, List.mem_toFinset] using hxL
  · intro hxA
    have hxL : x ∈ L n := by
      simpa [← hL_toFinset n, List.mem_toFinset] using hxA
    obtain ⟨i, hix⟩ := List.mem_iff_get.mp hxL
    rw [Finset.mem_image]
    refine ⟨i, ?_, ?_⟩
    · simpa [hL_length n] using i.2
    · change σFun i = x
      rw [hσFun_eq_get n i i.2, hix]

omit [CompleteSpace E] in
/--
Classical rearrangement criterion for unconditional summability of a sequence.

If every permutation has ordered initial partial sums tending to the same
limit, then the sequence is unconditionally summable with that limit.
-/
private theorem hasSum_of_forall_tendsto_sum_nat_rearranged
    {f : ℕ → E} {a : E}
    (h : ∀ σ : Equiv.Perm ℕ,
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N, f (σ n))
        atTop
        (𝓝 a)) :
    HasSum f a := by
  classical
  by_contra hsum
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop] at hsum
  push Not at hsum
  obtain ⟨ε, hε_pos, hε⟩ := hsum
  choose bad hbad_sub hbad_dist using hε
  let A : ℕ → Finset ℕ :=
    Nat.rec ∅ fun n s => bad ((s ∪ Finset.range (n + 1)) ∪ {s.sup id + 1})
  have hA_zero : A 0 = ∅ := by
    simp [A]
  have hA_succ (n : ℕ) :
      A (n + 1) =
        bad (((A n ∪ Finset.range (n + 1)) ∪ {(A n).sup id + 1})) := by
    simp [A]
  have hA_step (n : ℕ) : A n ⊆ A (n + 1) := by
    rw [hA_succ n]
    exact (Finset.subset_union_left.trans Finset.subset_union_left).trans (hbad_sub _)
  have hA_mono : Monotone A := monotone_nat_of_le_succ hA_step
  have hA_range (n : ℕ) : Finset.range (n + 1) ⊆ A (n + 1) := by
    rw [hA_succ n]
    exact (Finset.subset_union_right.trans Finset.subset_union_left).trans (hbad_sub _)
  have hA_fresh_not (n : ℕ) : (A n).sup id + 1 ∉ A n := by
    intro hx
    have hle : (A n).sup id + 1 ≤ (A n).sup id := by
      simpa using (Finset.le_sup (s := A n) (f := id) hx)
    exact Nat.not_succ_le_self _ hle
  have hA_fresh_mem (n : ℕ) : (A n).sup id + 1 ∈ A (n + 1) := by
    rw [hA_succ n]
    exact hbad_sub _ (by simp)
  have hA_strict (n : ℕ) : A n ⊂ A (n + 1) := by
    rw [Finset.ssubset_iff_of_subset (hA_step n)]
    exact ⟨(A n).sup id + 1, hA_fresh_mem n, hA_fresh_not n⟩
  have hA_cover : ∀ m : ℕ, ∃ n : ℕ, m ∈ A n := by
    intro m
    exact ⟨m + 1, hA_range m (by simp)⟩
  have hA_bad (n : ℕ) :
      ε ≤ dist (∑ m ∈ A (n + 1), f m) a := by
    rw [hA_succ n]
    exact hbad_dist ((A n ∪ Finset.range (n + 1)) ∪ {(A n).sup id + 1})
  obtain ⟨σ, hAσ⟩ :=
    exists_perm_subseq_range_image_of_monotone_finset A hA_zero hA_mono hA_strict hA_cover
  have hA_card_ge : ∀ n : ℕ, n ≤ (A n).card := by
    intro n
    induction n with
    | zero => simp [hA_zero]
    | succ n ih =>
        have hcard_lt : (A n).card < (A (n + 1)).card :=
          Finset.card_lt_card (hA_strict n)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hcard_lt)
  have hA_card_tendsto : Filter.Tendsto (fun n : ℕ => (A n).card) atTop atTop :=
    tendsto_atTop_atTop.mpr fun N =>
      ⟨N, fun n hn => hn.trans (hA_card_ge n)⟩
  have hσ : Filter.Tendsto
      (fun n : ℕ => ∑ m ∈ Finset.range (A n).card, f (σ m))
      atTop
      (𝓝 a) :=
    (h σ).comp hA_card_tendsto
  have hσ_bad (n : ℕ) :
      ε ≤ dist (∑ m ∈ Finset.range (A (n + 1)).card, f (σ m)) a := by
    have hsum_eq :
        (∑ m ∈ A (n + 1), f m) =
          ∑ m ∈ Finset.range (A (n + 1)).card, f (σ m) := by
      conv_lhs => rw [← hAσ (n + 1)]
      simp [Finset.sum_image]
    simpa [hsum_eq] using hA_bad n
  have hσ_lt : ∀ᶠ n : ℕ in atTop,
      dist (∑ m ∈ Finset.range (A n).card, f (σ m)) a < ε :=
    (Metric.tendsto_nhds.mp hσ) ε hε_pos
  rw [eventually_atTop] at hσ_lt
  obtain ⟨N, hN⟩ := hσ_lt
  exact not_lt_of_ge (hσ_bad N) (hN (N + 1) (Nat.le_succ N))

/--
A Schauder basis is unconditional if every basis expansion has a `HasSum`.

Since `HasSum` is Lean's unconditional finite-set notion of summability, this
immediately implies ordered convergence of every permuted expansion; see
`SchauderBasis.isUnconditional_tendsto_rearranged`.
-/
def IsUnconditional (b : SchauderBasis 𝕜 E) : Prop :=
  ∀ x : E, HasSum (fun n : ℕ => b.coeff n x • b.basis n) x

/--
`HasSum` unconditionality is invariant under every permutation of `ℕ`.

This is a useful technical form of unconditionality, but it is still phrased in
terms of `HasSum`, so it is mostly a reindexing statement.  For the ordered
partial-sum formulation, see `SchauderBasis.isUnconditional_tendsto_rearranged`.
-/
theorem isUnconditional_iff_hasSum_rearranged (b : SchauderBasis 𝕜 E) :
    b.IsUnconditional ↔
      ∀ (x : E) (σ : Equiv.Perm ℕ),
        HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x := by
  constructor
  · intro hb x σ
    let f : ℕ → E := fun n => b.coeff n x • b.basis n
    have hf : HasSum f x := hb x
    simpa [f, Function.comp_def] using (σ.hasSum_iff).2 hf
  · intro hb x
    simpa using hb x (Equiv.refl ℕ)

/--
Unconditionality is equivalent to strong convergence of all rearranged finite
partial-sum nets.

This is the same mathematical content as
`SchauderBasis.isUnconditional_iff_hasSum_rearranged`, but it exposes the
underlying `Filter.Tendsto` statement instead of the abbreviation `HasSum`.
The filter is `atTop` on `Finset ℕ`, so finite sets eventually contain any
prescribed finite set of indices.
-/
theorem isUnconditional_iff_tendsto_rearranged (b : SchauderBasis 𝕜 E) :
    b.IsUnconditional ↔
      ∀ (x : E) (σ : Equiv.Perm ℕ),
        Filter.Tendsto
          (fun s : Finset ℕ =>
            ∑ n ∈ s, b.coeff (σ n) x • b.basis (σ n))
          atTop
          (𝓝 x) := by
  constructor
  · intro hb x σ
    have hf : HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x :=
      (b.isUnconditional_iff_hasSum_rearranged.mp hb) x σ
    simpa [HasSum, SummationFilter.unconditional_filter] using hf
  · intro h x
    have hx := h x (Equiv.refl ℕ)
    simpa [HasSum, SummationFilter.unconditional_filter] using hx

/--
Unconditionality implies convergence of every permuted ordered expansion.

For every vector `x` and permutation `σ`, the initial partial sums
`∑ n ∈ Finset.range N, coeff (σ n) x • basis (σ n)` tend to `x` in the norm
topology.  This is the direct Lean version of the usual statement that every
rearrangement of the Schauder expansion converges to the same vector.
-/
theorem isUnconditional_tendsto_rearranged (b : SchauderBasis 𝕜 E) :
    b.IsUnconditional →
      ∀ (x : E) (σ : Equiv.Perm ℕ),
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ n ∈ Finset.range N, b.coeff (σ n) x • b.basis (σ n))
          atTop
          (𝓝 x) := by
  intro hb x σ
  let f : ℕ → E := fun n => b.coeff n x • b.basis n
  have hf : HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x := by
    simpa [f, Function.comp_def] using (σ.hasSum_iff).2 (hb x)
  exact hf.tendsto_sum_nat

/--
Unconditionality is equivalent to ordered convergence of every rearranged
expansion.

This is the classical rearrangement formulation: for every vector `x` and every
permutation `σ : Equiv.Perm ℕ`, the initial partial sums over `Finset.range N`
of the permuted expansion converge to `x`.
-/
theorem isUnconditional_iff_tendsto_ordered_rearranged (b : SchauderBasis 𝕜 E) :
    b.IsUnconditional ↔
      ∀ (x : E) (σ : Equiv.Perm ℕ),
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ n ∈ Finset.range N, b.coeff (σ n) x • b.basis (σ n))
          atTop
          (𝓝 x) := by
  constructor
  · exact b.isUnconditional_tendsto_rearranged
  · intro h x
    let f : ℕ → E := fun n => b.coeff n x • b.basis n
    have hf : HasSum f x :=
      hasSum_of_forall_tendsto_sum_nat_rearranged (a := x) (f := f) (by
        intro σ
        simpa [f] using h x σ)
    simpa [f] using hf

end SchauderBasis

/--
An unconditional Schauder basis with the usual `ℕ` index set.

This is a Schauder basis together with unconditional summability of every basis
expansion. The classical ordered rearrangement criterion is available as
`SchauderBasis.isUnconditional_iff_tendsto_ordered_rearranged`.
-/
structure UnconditionalSchauderBasis (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] where
  /-- Underlying Schauder basis. -/
  toSchauderBasis : SchauderBasis 𝕜 E
  /-- Every basis expansion converges unconditionally to the same sum. -/
  unconditional : toSchauderBasis.IsUnconditional

/-!
## Abstractly indexed unconditional bases

For an arbitrary index type there is no preferred order of partial sums. The
natural primitive statement is therefore unconditional summability over finite
subsets, i.e. `HasSum`.
-/

/--
An unconditional Schauder basis indexed by an arbitrary type.

Here `basis i` is the vector `φᵢ`, `coeff i` is the corresponding coordinate
functional, and every vector has a unique unconditional expansion over the whole
index type. This abstract version is the natural target for the finite sign
criterion, where no preferred order on the index set is needed.
-/
structure UnconditionalSchauderBasisAbstractIndex (𝕜 Index E : Type*)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] where
  /-- Basis vectors, indexed by an arbitrary type. -/
  basis : Index → E
  /-- Continuous coordinate functionals, with the same index type. -/
  coeff : Index → E →L[𝕜] 𝕜
  /-- Every vector is the unconditional sum of its abstractly indexed expansion. -/
  hasSum_repr : ∀ x : E, HasSum (fun i : Index => coeff i x • basis i) x
  /-- Coefficients in such an unconditional expansion are unique. -/
  unique_coeff :
    ∀ (x : E) (a : Index → 𝕜), HasSum (fun i : Index => a i • basis i) x →
      a = fun i : Index => coeff i x

namespace UnconditionalSchauderBasisAbstractIndex

variable {𝕜 Index E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The representation theorem of an abstract unconditional Schauder basis, as a simp lemma. -/
@[simp]
theorem hasSum_repr_apply (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E) (x : E) :
    HasSum (fun i : Index => b.coeff i x • b.basis i) x :=
  b.hasSum_repr x

/-- Coefficients in an abstract unconditional expansion are the stored coordinate maps. -/
theorem unique_coeff_apply (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E)
    (x : E) (a : Index → 𝕜) (ha : HasSum (fun i : Index => a i • b.basis i) x) :
    a = fun i : Index => b.coeff i x :=
  b.unique_coeff x a ha

/-!
### Coordinates of basis vectors

The next two lemmas extract the usual Kronecker-delta behaviour of the
coordinate maps from uniqueness of unconditional expansions.
-/

/-- The coordinate maps take value `1` on their own basis vector. -/
theorem coeff_basis_self (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E)
    (i : Index) :
    b.coeff i (b.basis i) = (1 : 𝕜) := by
  classical
  have hsingle :
      HasSum (fun k : Index => (if k = i then (1 : 𝕜) else 0) • b.basis k)
        (b.basis i) := by
    have hfun :
        (fun k : Index => (if k = i then (1 : 𝕜) else 0) • b.basis k)
          = Pi.single i (b.basis i) := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [Pi.single]
      · simp [Pi.single, hki]
    simpa [← hfun] using (hasSum_pi_single (β := Index) (α := E) i (b.basis i))
  have hcoeff :=
    congrFun (b.unique_coeff (b.basis i) (fun k : Index => if k = i then (1 : 𝕜) else 0)
      hsingle) i
  simpa using hcoeff.symm

/-- The coordinate maps vanish on the other basis vectors. -/
theorem coeff_basis_ne (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E)
    {i j : Index} (hji : j ≠ i) :
    b.coeff i (b.basis j) = 0 := by
  classical
  have hsingle :
      HasSum (fun k : Index => (if k = j then (1 : 𝕜) else 0) • b.basis k)
        (b.basis j) := by
    have hfun :
        (fun k : Index => (if k = j then (1 : 𝕜) else 0) • b.basis k)
          = Pi.single j (b.basis j) := by
      funext k
      by_cases hkj : k = j
      · subst k
        simp [Pi.single]
      · simp [Pi.single, hkj]
    simpa [← hfun] using (hasSum_pi_single (β := Index) (α := E) j (b.basis j))
  have hcoeff :=
    congrFun (b.unique_coeff (b.basis j) (fun k : Index => if k = j then (1 : 𝕜) else 0)
      hsingle) i
  have hij : i ≠ j := fun h => hji h.symm
  simpa [hij] using hcoeff.symm

/-!
### Enumerating an abstract basis

If an abstract index type is equivalent to `ℕ`, then any enumeration gives an
ordinary unconditional Schauder basis. The construction uses `HasSum` to get
the ordered Schauder convergence, and the Kronecker-delta lemmas above to prove
uniqueness of ordered coefficients.
-/

/--
Enumerating an abstract unconditional Schauder basis gives a usual
`ℕ`-indexed unconditional Schauder basis.

The equivalence `e : ℕ ≃ Index` provides the order used for the Schauder
partial sums. Unconditional summability supplies convergence for that order,
while uniqueness of abstract coordinates gives uniqueness of the ordered
coefficients.
-/
noncomputable def toUnconditionalSchauderBasis
    (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E) (e : ℕ ≃ Index) :
    UnconditionalSchauderBasis 𝕜 E :=
{
  toSchauderBasis :=
  {
    basis := fun n : ℕ => b.basis (e n)
    coeff := fun n : ℕ => b.coeff (e n)
    hasSchauderSum_repr := by
      intro x
      have hsum : HasSum (fun n : ℕ => b.coeff (e n) x • b.basis (e n)) x := by
        let f : Index → E := fun i => b.coeff i x • b.basis i
        have hf : HasSum f x := b.hasSum_repr x
        simpa [f, Function.comp_def] using (e.hasSum_iff).2 hf
      exact hsum.tendsto_sum_nat
    unique_coeff := by
      classical
      intro x a ha
      funext n
      let c : E →L[𝕜] 𝕜 := b.coeff (e n)
      -- Apply the `n`th coordinate functional to the ordered partial sums.
      have hmap :
          Filter.Tendsto
            (fun k : ℕ => c (∑ m ∈ Finset.range k, a m • b.basis (e m)))
            atTop
            (𝓝 (c x)) :=
        (c.continuous.tendsto x).comp ha
      have hpartial :
          ∀ᶠ k : ℕ in atTop,
            c (∑ m ∈ Finset.range k, a m • b.basis (e m)) = a n := by
        filter_upwards [eventually_gt_atTop n] with k hk
        have hnmem : n ∈ Finset.range k := Finset.mem_range.mpr hk
        -- Once `k > n`, the coordinate functional sees exactly the `n`th term.
        calc
          c (∑ m ∈ Finset.range k, a m • b.basis (e m))
              = ∑ m ∈ Finset.range k, c (a m • b.basis (e m)) := by
                  exact map_sum c (fun m => a m • b.basis (e m)) (Finset.range k)
          _ = ∑ m ∈ Finset.range k, (if m = n then a n else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  by_cases hmn : m = n
                  · subst m
                    simp [c, coeff_basis_self]
                  · have hemn : e m ≠ e n := by
                      intro h
                      exact hmn (e.injective h)
                    simp [c, hmn, coeff_basis_ne b hemn]
          _ = a n := by
                  exact
                    (Finset.sum_eq_single (s := Finset.range k) (a := n)
                      (f := fun m : ℕ => if m = n then a n else 0)
                      (fun m _hm hmn => if_neg hmn)
                      (fun hn => False.elim (hn hnmem))).trans (by simp)
      have hscalar :
          Filter.Tendsto
            (fun k : ℕ => c (∑ m ∈ Finset.range k, a m • b.basis (e m)))
            atTop
            (𝓝 (a n)) :=
        (tendsto_congr' hpartial).mpr tendsto_const_nhds
      -- The same scalar net tends to both `c x` and `a n`.
      exact tendsto_nhds_unique hscalar hmap
  }
  unconditional := by
    intro x
    let f : Index → E := fun i => b.coeff i x • b.basis i
    have hf : HasSum f x := b.hasSum_repr x
    simpa [f, Function.comp_def] using (e.hasSum_iff).2 hf
}

/-- Enumerating an abstract basis does not change the set of basis vectors. -/
theorem range_basis_toUnconditionalSchauderBasis
    (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E) (e : ℕ ≃ Index) :
    Set.range (toUnconditionalSchauderBasis b e).toSchauderBasis.basis =
      Set.range b.basis := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨e n, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp [toUnconditionalSchauderBasis]⟩

/-- Enumerating an abstract basis does not change the set of coordinate maps. -/
theorem range_coeff_toUnconditionalSchauderBasis
    (b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E) (e : ℕ ≃ Index) :
    Set.range (toUnconditionalSchauderBasis b e).toSchauderBasis.coeff =
      Set.range b.coeff := by
  ext c
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨e n, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp [toUnconditionalSchauderBasis]⟩

end UnconditionalSchauderBasisAbstractIndex

namespace UnconditionalSchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-!
## Basic API for unconditional Schauder bases

This namespace provides convenient projections to the underlying basis and
coordinate maps, plus the reverse conversion from the usual `ℕ`-indexed notion
to the abstract-index notion with `Index = ℕ`.
-/

instance : Coe (UnconditionalSchauderBasis 𝕜 E) (SchauderBasis 𝕜 E) where
  coe b := b.toSchauderBasis

/-- Basis vectors of an unconditional Schauder basis. -/
def basis (b : UnconditionalSchauderBasis 𝕜 E) : ℕ → E :=
  b.toSchauderBasis.basis

/-- Continuous coordinate maps of an unconditional Schauder basis. -/
def coeff (b : UnconditionalSchauderBasis 𝕜 E) : ℕ → E →L[𝕜] 𝕜 :=
  b.toSchauderBasis.coeff

@[simp]
private theorem hasSchauderSum_repr_apply (b : UnconditionalSchauderBasis 𝕜 E) (x : E) :
    HasSchauderSum b.basis (fun n : ℕ => b.coeff n x) x :=
  b.toSchauderBasis.hasSchauderSum_repr x

@[simp]
private theorem hasSum_repr_apply (b : UnconditionalSchauderBasis 𝕜 E) (x : E) :
    HasSum (fun n : ℕ => b.coeff n x • b.basis n) x :=
  b.unconditional x

private theorem hasSum_rearranged (b : UnconditionalSchauderBasis 𝕜 E)
    (x : E) (σ : Equiv.Perm ℕ) :
    HasSum (fun n : ℕ => b.coeff (σ n) x • b.basis (σ n)) x :=
  by
    let f : ℕ → E := fun n => b.coeff n x • b.basis n
    have hf : HasSum f x := b.unconditional x
    simpa [f, Function.comp_def] using (σ.hasSum_iff).2 hf

/--
Forget the order on an unconditional Schauder basis and regard it as an
abstractly indexed basis over `ℕ`.

The `HasSum` part of unconditionality becomes the representation theorem for
the abstract basis, while uniqueness is inherited from the ordered Schauder
basis by passing a `HasSum` to its ordered partial sums.
-/
def toUnconditionalSchauderBasisAbstractIndex (b : UnconditionalSchauderBasis 𝕜 E) :
    UnconditionalSchauderBasisAbstractIndex 𝕜 ℕ E :=
{
  basis := b.basis
  coeff := b.coeff
  hasSum_repr := by
    intro x
    exact b.unconditional x
  unique_coeff := by
    intro x a ha
    exact b.toSchauderBasis.unique_coeff x a (by simpa [basis] using! ha.tendsto_sum_nat)
}

/-- Every unconditional Schauder basis gives an abstractly indexed one over `ℕ`
with the same basis vectors and coordinate maps. -/
theorem exists_unconditionalSchauderBasisAbstractIndex_nat
    (b : UnconditionalSchauderBasis 𝕜 E) :
    ∃ b' : UnconditionalSchauderBasisAbstractIndex 𝕜 ℕ E,
      b'.basis = b.basis ∧ b'.coeff = b.coeff :=
  ⟨b.toUnconditionalSchauderBasisAbstractIndex, rfl, rfl⟩

end UnconditionalSchauderBasis

/-!
## Finite sign criterion

This section proves a practical criterion for building unconditional Schauder
bases from finite estimates.

The core theorem is indexed by an arbitrary type `Index`. The hypotheses are:

* `x : Index → E` has dense closed linear span,
* no vector `x i` is zero,
* and if finite signed sums satisfy
  `‖∑ i ∈ s, (ε i * a i) • x i‖ ≤ C * ‖∑ i ∈ s, a i • x i‖`,

then `x` determines an `UnconditionalSchauderBasisAbstractIndex`.

The usual `ℕ`-indexed theorem is recovered at the end by specializing
`Index = ℕ` and enumerating with `Equiv.refl ℕ`.
-/

namespace UnconditionalCriterion

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/--
The closed linear span of `x` is all of `E`.

In infinite-dimensional Banach spaces, this is the right meaning of
"the vectors `x i` span `E`".
-/
def HasDenseSpan {Index : Type*} (x : Index → E) : Prop :=
  closure ((Submodule.span 𝕜 (Set.range x) : Submodule 𝕜 E) : Set E) = Set.univ

/--
Finite sign estimate for the family `x`.

This says that changing finitely many coefficients by signs can increase the
norm of the corresponding finite sum by at most the factor `C`:

`‖∑_{i ∈ s} ε_i a_i x_i‖ ≤ C ‖∑_{i ∈ s} a_i x_i‖`,

with each `ε_i` equal to `1` or `-1` on the finite set `s`.
-/
def HasFiniteSignBound {Index : Type*} (x : Index → E) (C : ℝ) : Prop :=
  ∀ (s : Finset Index) (a ε : Index → 𝕜),
    (∀ i ∈ s, ε i = 1 ∨ ε i = -1) →
      ‖∑ i ∈ s, (ε i * a i) • x i‖
        ≤ C * ‖∑ i ∈ s, a i • x i‖

/-!
### From signs to projection bounds

The sign estimate is first converted into a uniform bound for finite coordinate
projections. This is the finite-dimensional algebraic part of the argument.
-/

/--
Sign function equal to `1` on `t` and `-1` outside `t`.

In practice we apply it on a finite set `s` with `t ⊆ s`.
-/
private def projectionSigns {Index : Type*} [DecidableEq Index]
    (t : Finset Index) : Index → 𝕜 :=
  fun i => if i ∈ t then 1 else -1

omit [CharZero 𝕜] [CompleteSpace 𝕜] in
@[simp]
private lemma projectionSigns_of_mem {Index : Type*} [DecidableEq Index]
    (t : Finset Index) {i : Index} (hi : i ∈ t) :
    projectionSigns (𝕜 := 𝕜) t i = (1 : 𝕜) := by
  simp [projectionSigns, hi]

omit [CharZero 𝕜] [CompleteSpace 𝕜] in
@[simp]
private lemma projectionSigns_of_not_mem {Index : Type*} [DecidableEq Index]
    (t : Finset Index) {i : Index} (hi : i ∉ t) :
    projectionSigns (𝕜 := 𝕜) t i = (-1 : 𝕜) := by
  simp [projectionSigns, hi]

omit [CharZero 𝕜] [CompleteSpace 𝕜] in
private lemma projectionSigns_is_sign {Index : Type*} [DecidableEq Index]
    (s t : Finset Index) :
    ∀ i ∈ s,
      projectionSigns (𝕜 := 𝕜) t i = (1 : 𝕜) ∨
        projectionSigns (𝕜 := 𝕜) t i = (-1 : 𝕜) := by
  intro i _hi
  by_cases hit : i ∈ t
  · left
    simp [projectionSigns, hit]
  · right
    simp [projectionSigns, hit]

omit [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] in
/--
Algebraic identity used for the projection estimate.

Choosing signs `+1` on `t` and `-1` on `s \ t` gives a signed sum equal to
`2` times the projection onto `t`, minus the original sum.
-/
private lemma signed_sum_eq_two_projection_sub_sum
    {Index : Type*} [DecidableEq Index]
    (x : Index → E)
    (s t : Finset Index)
    (hts : t ⊆ s)
    (a : Index → 𝕜) :
    (∑ i ∈ s, (projectionSigns (𝕜 := 𝕜) t i * a i) • x i)
      =
    (2 : 𝕜) • (∑ i ∈ t, a i • x i)
      -
    (∑ i ∈ s, a i • x i) := by
  classical
  have hproj :
      (∑ i ∈ s, (((if i ∈ t then (2 : 𝕜) else 0) * a i) • x i))
        = (2 : 𝕜) • (∑ i ∈ t, a i • x i) := by
    calc
      (∑ i ∈ s, (((if i ∈ t then (2 : 𝕜) else 0) * a i) • x i))
          = ∑ i ∈ t, (((if i ∈ t then (2 : 𝕜) else 0) * a i) • x i) := by
            exact (Finset.sum_subset
              (s₁ := t) (s₂ := s)
              (f := fun i => (((if i ∈ t then (2 : 𝕜) else 0) * a i) • x i))
              hts (by
                intro i _his hit
                simp [hit])).symm
      _ = ∑ i ∈ t, ((2 : 𝕜) * a i) • x i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hi]
      _ = (2 : 𝕜) • (∑ i ∈ t, a i • x i) := by
            rw [Finset.smul_sum]
            change (∑ i ∈ t, ((2 : 𝕜) * a i) • x i)
              = ∑ i ∈ t, (2 : 𝕜) • (a i • x i)
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [mul_smul]
  rw [← hproj, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases hit : i ∈ t
  · rw [projectionSigns_of_mem (𝕜 := 𝕜) t hit]
    simp only [one_mul]
    rw [← sub_smul]
    congr 1
    simp [hit]
    ring
  · rw [projectionSigns_of_not_mem (𝕜 := 𝕜) t hit]
    simp [hit, neg_smul]

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/--
The finite sign estimate gives a uniform bound for finite coordinate
projections.

Concretely, for `t ⊆ s`:

`‖∑ i ∈ t, a i • x i‖ ≤ ‖(2 : 𝕜)⁻¹‖ * (C + 1) * ‖∑ i ∈ s, a i • x i‖`.
-/
private lemma finite_projection_bound_of_sign_bound
    {Index : Type*}
    (x : Index → E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := 𝕜) x C)
    (s t : Finset Index)
    (hts : t ⊆ s)
    (a : Index → 𝕜) :
    ‖∑ i ∈ t, a i • x i‖
      ≤ (‖((2 : 𝕜)⁻¹)‖ * (C + 1)) * ‖∑ i ∈ s, a i • x i‖ := by
  classical
  have _hC_plus_one : 0 ≤ C + 1 := add_nonneg hC zero_le_one
  let p : E := ∑ i ∈ t, a i • x i
  let y : E := ∑ i ∈ s, a i • x i
  let z : E := ∑ i ∈ s, (projectionSigns (𝕜 := 𝕜) t i * a i) • x i
  have hz_bound : ‖z‖ ≤ C * ‖y‖ := by
    simpa [z, y] using
      h_sign s a (projectionSigns (𝕜 := 𝕜) t)
        (projectionSigns_is_sign (𝕜 := 𝕜) s t)
  have hz_eq : z = (2 : 𝕜) • p - y := by
    simpa [z, p, y] using signed_sum_eq_two_projection_sub_sum x s t hts a
  have hp_eq : p = ((2 : 𝕜)⁻¹) • (z + y) := by
    rw [hz_eq]
    simp [p]
  have hnorm :
      ‖p‖ ≤ ‖((2 : 𝕜)⁻¹)‖ * (‖z‖ + ‖y‖) := by
    calc
      ‖p‖ = ‖((2 : 𝕜)⁻¹) • (z + y)‖ := by rw [hp_eq]
      _ = ‖((2 : 𝕜)⁻¹)‖ * ‖z + y‖ := by
            rw [norm_smul]
      _ ≤ ‖((2 : 𝕜)⁻¹)‖ * (‖z‖ + ‖y‖) := by
            exact mul_le_mul_of_nonneg_left (norm_add_le z y) (norm_nonneg _)
  have hzy : ‖z‖ + ‖y‖ ≤ (C + 1) * ‖y‖ := by
    calc
      ‖z‖ + ‖y‖ ≤ C * ‖y‖ + ‖y‖ := by
        exact add_le_add hz_bound le_rfl
      _ = (C + 1) * ‖y‖ := by ring
  have hmain : ‖p‖ ≤ (‖((2 : 𝕜)⁻¹)‖ * (C + 1)) * ‖y‖ := by
    calc
      ‖p‖ ≤ ‖((2 : 𝕜)⁻¹)‖ * (‖z‖ + ‖y‖) := hnorm
      _ ≤ ‖((2 : 𝕜)⁻¹)‖ * ((C + 1) * ‖y‖) := by
            exact mul_le_mul_of_nonneg_left hzy (norm_nonneg _)
      _ = (‖((2 : 𝕜)⁻¹)‖ * (C + 1)) * ‖y‖ := by ring
  simpa [p, y] using hmain

/--
Uniform bound for all finite coordinate projections of `x`.

If `t ⊆ s`, then the partial sum over `t` is at most `K` times the partial
sum over `s`.
-/
private def FiniteProjectionBound {Index : Type*} (x : Index → E) (K : ℝ) : Prop :=
  ∀ (s t : Finset Index), t ⊆ s → ∀ a : Index → 𝕜,
    ‖∑ i ∈ t, a i • x i‖ ≤ K * ‖∑ i ∈ s, a i • x i‖

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/-- The finite sign estimate implies `FiniteProjectionBound`. -/
private lemma finiteProjectionBound_of_signBound
    {Index : Type*}
    (x : Index → E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := 𝕜) x C) :
    FiniteProjectionBound (𝕜 := 𝕜) x (‖((2 : 𝕜)⁻¹)‖ * (C + 1)) := by
  intro s t hts a
  exact finite_projection_bound_of_sign_bound x C hC h_sign s t hts a

/-!
### Algebraic coordinates on the span

The projection bound implies linear independence and bounds the coordinate
functionals on the algebraic span. Density then lets us extend those
functionals continuously to all of `E`.
-/

omit [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace E] in
/--
From singleton and projection estimates, we get linear independence of `x`.

This is the first purely algebraic step after the projection bound.
-/
private lemma linearIndependent_of_finiteProjectionBound
    {Index : Type*}
    (x : Index → E)
    (hx_ne : ∀ i, x i ≠ 0)
    (K : ℝ)
    (h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K) :
    LinearIndependent 𝕜 x := by
  classical
  rw [linearIndependent_iff']
  intro s a hsum i hi
  have hsingleton :
      ‖∑ j ∈ ({i} : Finset Index), a j • x j‖ ≤ K * ‖∑ j ∈ s, a j • x j‖ :=
    h_proj s ({i} : Finset Index) (by
      intro j hj
      have hji : j = i := by simpa using hj
      simpa [hji] using hi) a
  have hsingleton_zero : ∑ j ∈ ({i} : Finset Index), a j • x j = 0 := by
    have hnorm_le_zero : ‖∑ j ∈ ({i} : Finset Index), a j • x j‖ ≤ 0 := by
      simpa [hsum] using hsingleton
    exact norm_eq_zero.mp (le_antisymm hnorm_le_zero (norm_nonneg _))
  have hai_smul : a i • x i = 0 := by
    simpa using hsingleton_zero
  exact (smul_eq_zero.mp hai_smul).resolve_right (hx_ne i)

/--
Compatibility of coordinate maps with finite expansions.

For vectors written as finite sums, the `n`th coordinate map returns the
expected coefficient.
-/
private def CoordMapsAgreeOnFiniteSpans {Index : Type*} [DecidableEq Index]
    (x : Index → E) (coeff : Index → E →L[𝕜] 𝕜) : Prop :=
  ∀ (s : Finset Index) (a : Index → 𝕜) (i : Index),
    coeff i (∑ j ∈ s, a j • x j) = if i ∈ s then a i else 0

omit [CharZero 𝕜] [CompleteSpace E] in
/--
Existence of coordinate maps from finite projection bounds.

We first define coordinates on the algebraic span, then extend continuously to
all of `E`.
-/
private lemma exists_coordMaps_of_finiteProjectionBound
    {Index : Type*} [DecidableEq Index]
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (h_li : LinearIndependent 𝕜 x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K) :
    ∃ coeff : Index → E →L[𝕜] 𝕜, CoordMapsAgreeOnFiniteSpans (𝕜 := 𝕜) x coeff := by
  classical
  let S : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range x)
  let e : S →ₗ[𝕜] E := Submodule.subtype S
  let coordLin : Index → S →ₗ[𝕜] 𝕜 :=
    fun i => (Finsupp.lapply i : (Index →₀ 𝕜) →ₗ[𝕜] 𝕜).comp h_li.repr
  have h_dense : DenseRange e := by
    rw [denseRange_iff_closure_range]
    simpa [HasDenseSpan, S, e, LinearMap.range_eq_map, Submodule.range_subtype] using hx_dense
  -- The projection bound controls each algebraic coordinate by the ambient norm.
  have h_norm : ∀ n, ∃ C : ℝ, ∀ y : S, ‖coordLin n y‖ ≤ C * ‖e y‖ := by
    intro n
    refine ⟨K / ‖x n‖, ?_⟩
    intro y
    let c : Index →₀ 𝕜 := h_li.repr y
    have hxpos : 0 < ‖x n‖ := norm_pos_iff.mpr (h_li.ne_zero n)
    have hK_nonneg : 0 ≤ K := by
      have hself :
          ‖∑ j ∈ ({n} : Finset Index), (if j = n then (1 : 𝕜) else 0) • x j‖
            ≤ K * ‖∑ j ∈ ({n} : Finset Index), (if j = n then (1 : 𝕜) else 0) • x j‖ :=
        h_proj ({n} : Finset Index) ({n} : Finset Index) (by intro j hj; simpa using hj)
          (fun j => if j = n then (1 : 𝕜) else 0)
      have hself' : ‖x n‖ ≤ K * ‖x n‖ := by
        simpa using hself
      have hright_nonneg : 0 ≤ K * ‖x n‖ :=
        (norm_nonneg (x n)).trans hself'
      exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hright_nonneg) hxpos
    by_cases hcn : c n = 0
    · have hzero : (coordLin n) y = 0 := by simp [coordLin, c, hcn]
      rw [hzero, norm_zero]
      exact mul_nonneg (div_nonneg hK_nonneg (norm_nonneg _)) (norm_nonneg _)
    · have hnmem : n ∈ c.support := Finsupp.mem_support_iff.mpr hcn
      have hsingleton_subset : ({n} : Finset Index) ⊆ c.support := by
        intro j hj
        have hji : j = n := by simpa using hj
        simpa [hji] using hnmem
      have hproj_single :
          ‖∑ j ∈ ({n} : Finset Index), c j • x j‖
            ≤ K * ‖∑ j ∈ c.support, c j • x j‖ :=
        h_proj c.support ({n} : Finset Index) hsingleton_subset (fun j => c j)
      have hsupport_sum : ∑ j ∈ c.support, c j • x j = (y : E) := by
        simpa [c, Finsupp.linearCombination_apply, Finsupp.sum] using
          h_li.linearCombination_repr y
      have hbound : ‖c n • x n‖ ≤ K * ‖(y : E)‖ := by
        simpa [hsupport_sum] using hproj_single
      have hmul : ‖c n‖ * ‖x n‖ ≤ K * ‖(y : E)‖ := by
        simpa [norm_smul] using hbound
      calc
        ‖coordLin n y‖ = ‖c n‖ := by
          simp [coordLin, c]
        _ = (‖c n‖ * ‖x n‖) / ‖x n‖ := by
          exact (mul_div_cancel_right₀ ‖c n‖ hxpos.ne').symm
        _ ≤ (K * ‖(y : E)‖) / ‖x n‖ := by
          exact div_le_div_of_nonneg_right hmul (le_of_lt hxpos)
        _ = (K / ‖x n‖) * ‖e y‖ := by
          simp [e]
          ring
  -- Extend the bounded algebraic coordinate maps from the dense span to `E`.
  let coeff : Index → E →L[𝕜] 𝕜 := fun n => (coordLin n).extendOfNorm e
  refine ⟨coeff, ?_⟩
  intro s a n
  let r : Finset Index := s
  let y : S := ⟨∑ i ∈ r, a i • x i, by
    refine Submodule.sum_mem S ?_
    intro i _hi
    exact Submodule.smul_mem S (a i) (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hy : e y = ∑ i ∈ r, a i • x i := rfl
  have hcoeff_apply :
      coeff n (∑ i ∈ r, a i • x i) = coordLin n y := by
    rw [← hy]
    exact LinearMap.extendOfNorm_eq h_dense (h_norm n) y
  let ftrunc : Index → 𝕜 := fun i => if i ∈ r then a i else 0
  have hftrunc : ∀ i, ftrunc i ≠ 0 → i ∈ r := by
      intro i hi
      by_contra hir
      simp [ftrunc, hir] at hi
  let l : Index →₀ 𝕜 := Finsupp.onFinset r ftrunc hftrunc
  have hl_apply_n : l n = if n ∈ r then a n else 0 := by
    by_cases hnmem : n ∈ r <;> simp [l, ftrunc, hnmem]
  have hl_lc : Finsupp.linearCombination 𝕜 x l = (y : E) := by
    rw [show l = Finsupp.onFinset r ftrunc hftrunc by rfl]
    rw [Finsupp.linearCombination_onFinset]
    simp [ftrunc, y]
  have hrepr : h_li.repr y = l := h_li.repr_eq hl_lc
  calc
    coeff n (∑ i ∈ s, a i • x i)
        = coeff n (∑ i ∈ r, a i • x i) := by rfl
    _ = coordLin n y := hcoeff_apply
    _ = l n := by simp [coordLin, hrepr]
    _ = if n ∈ s then a n else 0 := by simpa [r] using hl_apply_n

/--
Chosen coordinate maps produced by
`exists_coordMaps_of_finiteProjectionBound`.
-/
private noncomputable def coordMaps_of_finiteProjectionBound
    {Index : Type*} [DecidableEq Index]
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (h_li : LinearIndependent 𝕜 x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K) :
    Index → E →L[𝕜] 𝕜 :=
  Classical.choose
    (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)

/-!
### Convergence and uniqueness of the constructed expansion

The analytic core proves that the finite coordinate projections converge to
the identity along the finite-set filter. This gives the `HasSum`
representation. Uniqueness follows by applying coordinate functionals to any
other unconditional expansion.
-/

omit [CharZero 𝕜] [CompleteSpace E] in
/--
Finite partial-sum projections from the constructed coordinates converge to the
identity.

This is the analytic core: projection bounds give uniform control, and density
identifies the limit.
-/
private lemma coordMaps_tendsto_finite_partial_sums_of_finiteProjectionBound
    {Index : Type*} [DecidableEq Index]
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (h_li : LinearIndependent 𝕜 x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K)
    (hK : 0 ≤ K)
    (y : E) :
    Filter.Tendsto
      (fun s : Finset Index =>
        ∑ n ∈ s, coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj n y • x n)
      atTop
      (𝓝 y) := by
  classical
  let coeff := coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj
  let P : Finset Index → E → E := fun s y => ∑ n ∈ s, coeff n y • x n
  let S : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range x)
  let e : S →ₗ[𝕜] E := Submodule.subtype S
  have h_dense : DenseRange e := by
    rw [denseRange_iff_closure_range]
    simpa [HasDenseSpan, S, e, LinearMap.range_eq_map, Submodule.range_subtype] using hx_dense
  -- On the algebraic span, sufficiently large finite projections are exact.
  have hP_span_exact :
      ∀ (s : Finset Index) (z : S),
        (h_li.repr z).support ⊆ s → P s (z : E) = (z : E) := by
    intro s z hzs
    let c : Index →₀ 𝕜 := h_li.repr z
    have hzsum : ∑ n ∈ c.support, c n • x n = (z : E) := by
      simpa [c, Finsupp.linearCombination_apply, Finsupp.sum] using
        h_li.linearCombination_repr z
    have hcoord : ∀ n, coeff n (z : E) = if n ∈ c.support then c n else 0 := by
      intro n
      have h :=
        Classical.choose_spec
          (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
          c.support (fun i => c i) n
      simpa [coeff, coordMaps_of_finiteProjectionBound, hzsum] using h
    calc
      P s (z : E)
          = ∑ n ∈ s, (if n ∈ c.support then c n else 0) • x n := by
            refine Finset.sum_congr rfl ?_
            intro n _hn
            rw [hcoord n]
      _ = ∑ n ∈ s, c n • x n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hnc : n ∈ c.support
            · simp [hnc]
            · have hcn : c n = 0 := by simpa [Finsupp.mem_support_iff] using hnc
              simp [hnc, hcn]
      _ = ∑ n ∈ c.support, c n • x n := by
            exact (Finset.sum_subset hzs (by
              intro n _hns hnc
              have hcn : c n = 0 := by simpa [Finsupp.mem_support_iff] using hnc
              simp [hcn])).symm
      _ = (z : E) := hzsum
  -- The projection bound gives a uniform operator bound on the dense span.
  have hP_span_bound :
      ∀ (s : Finset Index) (z : S), ‖P s (z : E)‖ ≤ K * ‖(z : E)‖ := by
    intro s z
    let c : Index →₀ 𝕜 := h_li.repr z
    have hzsum : ∑ n ∈ c.support, c n • x n = (z : E) := by
      simpa [c, Finsupp.linearCombination_apply, Finsupp.sum] using
        h_li.linearCombination_repr z
    have hcoord : ∀ n, coeff n (z : E) = if n ∈ c.support then c n else 0 := by
      intro n
      have h :=
        Classical.choose_spec
          (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
          c.support (fun i => c i) n
      simpa [coeff, coordMaps_of_finiteProjectionBound, hzsum] using h
    have hP_eq :
        P s (z : E) = ∑ n ∈ s ∩ c.support, c n • x n := by
      calc
        P s (z : E)
            = ∑ n ∈ s, (if n ∈ c.support then c n else 0) • x n := by
              refine Finset.sum_congr rfl ?_
              intro n _hn
              rw [hcoord n]
        _ = ∑ n ∈ s ∩ c.support, (if n ∈ c.support then c n else 0) • x n := by
              exact (Finset.sum_subset (Finset.inter_subset_left) (by
                intro n _hns hninter
                have hnc : n ∉ c.support := by
                  intro hnc
                  exact hninter (Finset.mem_inter.mpr ⟨_hns, hnc⟩)
                simp [hnc])).symm
        _ = ∑ n ∈ s ∩ c.support, c n • x n := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hnc : n ∈ c.support := (Finset.mem_inter.mp hn).2
              simp [hnc]
    have hproj_bound :
        ‖∑ n ∈ s ∩ c.support, c n • x n‖
          ≤ K * ‖∑ n ∈ c.support, c n • x n‖ :=
      h_proj c.support (s ∩ c.support) (Finset.inter_subset_right) (fun n => c n)
    simpa [hP_eq, hzsum]
      using hproj_bound
  have hP_bound :
      ∀ (s : Finset Index) (y : E), ‖P s y‖ ≤ K * ‖y‖ := by
    intro s y
    exact h_dense.induction_on y
      (isClosed_le (by fun_prop) (by fun_prop))
      (fun z => by simpa [e] using hP_span_bound s z)
  -- Approximate an arbitrary vector by the dense span, then use exactness
  -- once the finite set contains the support of that approximation.
  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε hε
  have hK1_pos : 0 < K + 1 := by linarith
  let δ : ℝ := ε / (K + 1)
  have hδ_pos : 0 < δ := div_pos hε hK1_pos
  obtain ⟨z, hzdist⟩ := h_dense.exists_dist_lt y hδ_pos
  let c : Index →₀ 𝕜 := h_li.repr z
  refine ⟨c.support, ?_⟩
  intro s hs
  have hPz : P s (z : E) = (z : E) :=
    hP_span_exact s z (by simpa [c] using hs)
  have hP_sub :
      P s (y - (z : E)) = P s y - P s (z : E) := by
    simp [P, map_sub, sub_smul, Finset.sum_sub_distrib]
  have hdecomp :
      P s y - y = P s (y - (z : E)) + ((z : E) - y) := by
    rw [hP_sub, hPz]
    abel
  have hynorm_lt : ‖y - (z : E)‖ < δ := by
    simpa [dist_eq_norm, e] using hzdist
  calc
    ‖P s y - y‖ = ‖P s (y - (z : E)) + ((z : E) - y)‖ := by rw [hdecomp]
    _ ≤ ‖P s (y - (z : E))‖ + ‖(z : E) - y‖ := norm_add_le _ _
    _ ≤ K * ‖y - (z : E)‖ + ‖(z : E) - y‖ := by
          exact add_le_add (hP_bound s (y - (z : E))) le_rfl
    _ = (K + 1) * ‖y - (z : E)‖ := by
          rw [norm_sub_rev]
          ring
    _ < (K + 1) * δ := mul_lt_mul_of_pos_left hynorm_lt hK1_pos
    _ = ε := by
          dsimp [δ]
          field_simp [hK1_pos.ne']

omit [CharZero 𝕜] [CompleteSpace E] in
/-- The extended coordinate maps reconstruct every vector unconditionally. -/
private lemma coordMaps_hasSum_repr_abstract_of_finiteProjectionBound
    {Index : Type*} [DecidableEq Index]
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (h_li : LinearIndependent 𝕜 x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K)
    (hK : 0 ≤ K)
    (y : E) :
    HasSum
      (fun i : Index =>
        coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj i y • x i)
      y := by
  simpa [HasSum, SummationFilter.unconditional_filter] using
    coordMaps_tendsto_finite_partial_sums_of_finiteProjectionBound
      x hx_dense h_li K h_proj hK y

omit [CharZero 𝕜] [CompleteSpace E] in
/-- The coefficients in the abstractly indexed expansion are unique. -/
private lemma coordMaps_unique_hasSum_of_finiteProjectionBound
    {Index : Type*} [DecidableEq Index]
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (h_li : LinearIndependent 𝕜 x)
    (K : ℝ)
    (h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K) :
    ∀ (y : E) (a : Index → 𝕜),
      HasSum (fun i : Index => a i • x i) y →
        a = fun i : Index =>
          coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj i y := by
  classical
  intro y a ha
  funext i
  let coeff := coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj
  have hmap : HasSum (fun j : Index => coeff i (a j • x j)) (coeff i y) :=
    ha.mapL (coeff i)
  -- Every sufficiently large finite set contains `i`; on such sets the
  -- coordinate map extracts exactly the `i`th coefficient.
  have hpartial :
      ∀ᶠ s : Finset Index in atTop,
        (∑ j ∈ s, coeff i (a j • x j)) = a i := by
    filter_upwards [eventually_ge_atTop ({i} : Finset Index)] with s hs
    have his : i ∈ s := hs (by simp)
    have hcoord :=
      Classical.choose_spec
        (exists_coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj)
        s a i
    calc
      (∑ j ∈ s, coeff i (a j • x j))
          = coeff i (∑ j ∈ s, a j • x j) := by
            exact (map_sum (coeff i) (fun j => a j • x j) s).symm
      _ = a i := by
            simpa [coeff, coordMaps_of_finiteProjectionBound, his] using hcoord
  have hscalar : HasSum (fun j : Index => coeff i (a j • x j)) (a i) := by
    rw [HasSum, SummationFilter.unconditional_filter]
    exact (tendsto_congr' hpartial).mpr tendsto_const_nhds
  exact HasSum.unique hscalar hmap

/-!
### Packaging the basis

The private constructor packages the coordinate maps and the two analytic facts
into `UnconditionalSchauderBasisAbstractIndex`. The public theorems below expose
only existence and keep the construction details hidden.
-/

/--
Construct the abstractly indexed unconditional Schauder basis promised by the
finite sign criterion.

This private definition contains the actual choice of coordinate functionals.
The public theorem below exposes only the resulting existence statement.
-/
private noncomputable def unconditionalSchauderBasisAbstractIndex_of_finiteSignBound
    {Index : Type*}
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (hx_ne : ∀ i, x i ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := 𝕜) x C) :
    UnconditionalSchauderBasisAbstractIndex 𝕜 Index E := by
  classical
  let K : ℝ := ‖((2 : 𝕜)⁻¹)‖ * (C + 1)
  have hK : 0 ≤ K :=
    mul_nonneg (norm_nonneg _) (add_nonneg hC zero_le_one)
  have h_proj : FiniteProjectionBound (𝕜 := 𝕜) x K :=
    finiteProjectionBound_of_signBound x C hC h_sign
  have h_li : LinearIndependent 𝕜 x :=
    linearIndependent_of_finiteProjectionBound x hx_ne K h_proj
  exact
  {
    basis := x
    coeff := coordMaps_of_finiteProjectionBound x hx_dense h_li K h_proj
    hasSum_repr :=
      coordMaps_hasSum_repr_abstract_of_finiteProjectionBound x hx_dense h_li K h_proj hK
    unique_coeff :=
      coordMaps_unique_hasSum_of_finiteProjectionBound x hx_dense h_li K h_proj
  }

/--
Construct a usual `ℕ`-indexed unconditional Schauder basis from the finite sign
criterion.

This is only a specialization of the abstract-index construction to
`Index = ℕ`, followed by the canonical enumeration `Equiv.refl ℕ`.
-/
private noncomputable def unconditionalSchauderBasis_of_finiteSignBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (hx_ne : ∀ i, x i ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := 𝕜) x C) :
    UnconditionalSchauderBasis 𝕜 E :=
  let b := unconditionalSchauderBasisAbstractIndex_of_finiteSignBound
    x hx_dense hx_ne C hC h_sign
  b.toUnconditionalSchauderBasis (Equiv.refl ℕ)

/--
Abstract-index finite sign criterion.

If `x` has dense closed linear span, no vector `x i` is zero, and finite sign
changes are uniformly bounded by `C`, then there is an abstractly indexed
unconditional Schauder basis whose basis family is exactly `x`.
-/
theorem exists_unconditionalSchauderBasisAbstractIndex_of_finiteSignBound
    {Index : Type*}
    (x : Index → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (hx_ne : ∀ i, x i ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := 𝕜) x C) :
    ∃ b : UnconditionalSchauderBasisAbstractIndex 𝕜 Index E, b.basis = x := by
  refine
    ⟨unconditionalSchauderBasisAbstractIndex_of_finiteSignBound
      x hx_dense hx_ne C hC h_sign, ?_⟩
  rfl

/--
Main finite sign criterion for sequences.

If `x : ℕ → E` has dense closed linear span, no vector `x n` is zero, and finite
sign changes are uniformly bounded by `C`, then `x` is the basis sequence of an
unconditional Schauder basis.

This theorem is kept for the usual `ℕ`-indexed API; internally it is just the
abstract-index criterion specialized to `ℕ`.
-/
theorem exists_unconditionalSchauderBasis_of_finiteSignBound
    (x : ℕ → E)
    (hx_dense : HasDenseSpan (𝕜 := 𝕜) x)
    (hx_ne : ∀ i, x i ≠ 0)
    (C : ℝ)
    (hC : 0 ≤ C)
    (h_sign : HasFiniteSignBound (𝕜 := 𝕜) x C) :
    ∃ b : UnconditionalSchauderBasis 𝕜 E, b.basis = x := by
  refine ⟨unconditionalSchauderBasis_of_finiteSignBound x hx_dense hx_ne C hC h_sign, ?_⟩
  rfl

end UnconditionalCriterion
