/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Entropy
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fin.Rev
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Tactic

/-! # Core Encoding -/

@[expose] public section

namespace BeyondBethe

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Whether the assignment `σ` uses one of the two prescribed matching edges
at row `i`. -/
def UsesCoreEdge (f g σ : Equiv.Perm α) (i : α) : Prop :=
  σ i = f i ∨ σ i = g i

/-- The paper's core encoding for a two-regular bipartite multigraph written
as the union of two perfect matchings.  `none` is the symbol `star`; an escaped
edge records its column exactly. -/
noncomputable def twoMatchingEncoding (f g σ : Equiv.Perm α) : α → Option α := by
  classical
  exact fun i ↦ if UsesCoreEdge f g σ i then none else some (σ i)

/-- The permutation of row vertices obtained by following an `f`-edge and
then returning along a `g`-edge.  Its nontrivial cycles are precisely the
components containing at least two rows. -/
def alternatingRowPerm (f g : Equiv.Perm α) : Equiv.Perm α :=
  f.trans g.symm

@[simp]
theorem alternatingRowPerm_apply (f g : Equiv.Perm α) (i : α) :
    alternatingRowPerm f g i = g.symm (f i) := rfl

theorem same_twoMatchingEncoding_core_iff
    {f g σ τ : Equiv.Perm α}
    (henc : twoMatchingEncoding f g σ = twoMatchingEncoding f g τ)
    (i : α) :
    UsesCoreEdge f g σ i ↔ UsesCoreEdge f g τ i := by
  classical
  have hi := congrFun henc i
  constructor
  · intro hσ
    by_contra hτ
    simpa [twoMatchingEncoding, hσ, hτ] using hi
  · intro hτ
    by_contra hσ
    simpa [twoMatchingEncoding, hσ, hτ] using hi

theorem same_twoMatchingEncoding_of_escape
    {f g σ τ : Equiv.Perm α}
    (henc : twoMatchingEncoding f g σ = twoMatchingEncoding f g τ)
    {i : α} (hσ : ¬ UsesCoreEdge f g σ i) :
    σ i = τ i := by
  classical
  have hi := congrFun henc i
  have hτ : ¬ UsesCoreEdge f g τ i := by
    exact fun h ↦ hσ ((same_twoMatchingEncoding_core_iff henc i).2 h)
  simpa [twoMatchingEncoding, hσ, hτ] using hi

theorem alternatingRowPerm_fixed_iff
    (f g : Equiv.Perm α) (i : α) :
    alternatingRowPerm f g i = i ↔ f i = g i := by
  constructor
  · intro h
    have hg := congrArg g h
    simpa [alternatingRowPerm] using hg
  · intro h
    apply g.injective
    simp [alternatingRowPerm, h]

/-- One oriented disagreement propagates by one step around the alternating
cycle.  This is the direct form of the paper's "paths have unique perfect
matchings" observation. -/
theorem oriented_disagreement_step
    {f g σ τ : Equiv.Perm α}
    (henc : twoMatchingEncoding f g σ = twoMatchingEncoding f g τ)
    {i : α} (hσi : σ i = f i) (hτi : τ i = g i)
    (hfg : f i ≠ g i) :
    σ (alternatingRowPerm f g i) = f (alternatingRowPerm f g i) ∧
      τ (alternatingRowPerm f g i) = g (alternatingRowPerm f g i) := by
  let j := alternatingRowPerm f g i
  have hgj : g j = f i := by
    simp [j, alternatingRowPerm]
  have hji : j ≠ i := by
    intro h
    apply hfg
    rw [← hgj, h]
  let k := τ.symm (f i)
  have hτk : τ k = f i := by simp [k]
  have hki : k ≠ i := by
    intro h
    apply hfg
    rw [← hτk, h, hτi]
  have hσk_ne : σ k ≠ f i := by
    intro h
    exact hki (σ.injective (h.trans hσi.symm))
  have hτcore : UsesCoreEdge f g τ k := by
    by_contra hk
    have hσescape : ¬ UsesCoreEdge f g σ k := by
      exact fun h ↦ hk ((same_twoMatchingEncoding_core_iff henc k).1 h)
    have heq := same_twoMatchingEncoding_of_escape henc hσescape
    exact hσk_ne (heq.trans hτk)
  have hτk_g : τ k = g k := by
    rcases hτcore with hτk_f | hτk_g
    · exact absurd (f.injective (hτk_f.symm.trans hτk)) hki
    · exact hτk_g
  have hkj : k = j := by
    apply g.injective
    rw [← hτk_g, hτk, hgj]
  have hτj_g : τ j = g j := by
    rw [← hkj]
    exact hτk_g
  have hσcore : UsesCoreEdge f g σ j :=
    (same_twoMatchingEncoding_core_iff henc j).2 (Or.inr hτj_g)
  have hσj_g_ne : σ j ≠ g j := by
    intro h
    apply hji
    exact (σ.injective (hσi.trans (hgj.symm.trans h.symm))).symm
  refine ⟨?_, hτj_g⟩
  rcases hσcore with h | h
  · exact h
  · exact absurd h hσj_g_ne

/-- A disagreement in either orientation propagates by one alternating step. -/
theorem disagreement_step
    {f g σ τ : Equiv.Perm α}
    (henc : twoMatchingEncoding f g σ = twoMatchingEncoding f g τ)
    {i : α} (hne : σ i ≠ τ i) :
    σ (alternatingRowPerm f g i) ≠ τ (alternatingRowPerm f g i) := by
  have hσcore : UsesCoreEdge f g σ i := by
    by_contra h
    exact hne (same_twoMatchingEncoding_of_escape henc h)
  have hτcore : UsesCoreEdge f g τ i :=
    (same_twoMatchingEncoding_core_iff henc i).1 hσcore
  rcases hσcore with hσf | hσg <;> rcases hτcore with hτf | hτg
  · exact absurd (hσf.trans hτf.symm) hne
  · obtain h := oriented_disagreement_step henc hσf hτg
      (fun hfg ↦ hne (hσf.trans (hfg.trans hτg.symm)))
    intro heq
    have hstepFixed : alternatingRowPerm f g (alternatingRowPerm f g i) =
        alternatingRowPerm f g i :=
      (alternatingRowPerm_fixed_iff f g _).2 (h.1.symm.trans (heq.trans h.2))
    have hiFixed : alternatingRowPerm f g i = i := by
      exact (alternatingRowPerm f g).injective hstepFixed
    have hfg0 : f i = g i :=
      (alternatingRowPerm_fixed_iff f g i).1 hiFixed
    exact hne (hσf.trans (hfg0.trans hτg.symm))
  · obtain h := oriented_disagreement_step henc.symm hτf hσg
      (fun hfg ↦ hne ((hσg.trans hfg.symm).trans hτf.symm))
    intro heq
    have hstepFixed : alternatingRowPerm f g (alternatingRowPerm f g i) =
        alternatingRowPerm f g i :=
      (alternatingRowPerm_fixed_iff f g _).2 (h.1.symm.trans (heq.symm.trans h.2))
    have hiFixed : alternatingRowPerm f g i = i := by
      exact (alternatingRowPerm f g).injective hstepFixed
    have hfg0 : f i = g i :=
      (alternatingRowPerm_fixed_iff f g i).1 hiFixed
    exact hne (hσg.trans (hfg0.symm.trans hτf.symm))
  · exact absurd (hσg.trans hτg.symm) hne

theorem disagreement_pow
    {f g σ τ : Equiv.Perm α}
    (henc : twoMatchingEncoding f g σ = twoMatchingEncoding f g τ)
    {i : α} (hne : σ i ≠ τ i) :
    ∀ k : ℕ,
      σ (((alternatingRowPerm f g) ^ k) i) ≠
        τ (((alternatingRowPerm f g) ^ k) i) := by
  intro k
  induction k with
  | zero => simpa using hne
  | succ k ih =>
      simpa only [← Equiv.Perm.mul_apply, ← pow_succ'] using
        disagreement_step henc ih

/-- A chosen row in the support of a nontrivial alternating cycle. -/
noncomputable def cycleRepresentative
    (h : Equiv.Perm α) (c : h.cycleFactorsFinset) : α :=
  Classical.choose
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support)

theorem cycleRepresentative_mem
    (h : Equiv.Perm α) (c : h.cycleFactorsFinset) :
    cycleRepresentative h c ∈ (c : Equiv.Perm α).support :=
  Classical.choose_spec
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support)

/-- One Boolean choice for every nontrivial alternating cycle. -/
noncomputable def cycleSignature
    (f g σ : Equiv.Perm α) :
    (alternatingRowPerm f g).cycleFactorsFinset → Bool :=
  fun c ↦ decide (σ (cycleRepresentative (alternatingRowPerm f g) c) =
    f (cycleRepresentative (alternatingRowPerm f g) c))

theorem cycleSignature_injective_on_encoding_fiber
    {f g : Equiv.Perm α} {y : α → Option α} :
    Set.InjOn (cycleSignature f g)
      {σ | twoMatchingEncoding f g σ = y} := by
  intro σ hσ τ hτ hsig
  have henc : twoMatchingEncoding f g σ = twoMatchingEncoding f g τ :=
    hσ.trans hτ.symm
  ext i
  by_contra hne
  let h := alternatingRowPerm f g
  have hsupport : i ∈ h.support := by
    rw [Equiv.Perm.mem_support]
    intro hfix
    have hfg : f i = g i :=
      (alternatingRowPerm_fixed_iff f g i).1 hfix
    have hσcore : UsesCoreEdge f g σ i := by
      by_contra hout
      exact hne (same_twoMatchingEncoding_of_escape henc hout)
    have hτcore : UsesCoreEdge f g τ i :=
      (same_twoMatchingEncoding_core_iff henc i).1 hσcore
    rcases hσcore with hσf | hσg <;> rcases hτcore with hτf | hτg <;>
      apply hne <;> simp_all
  let c : h.cycleFactorsFinset :=
    ⟨h.cycleOf i, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hsupport⟩
  have hirep : h.SameCycle i (cycleRepresentative h c) := by
    apply (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hsupport
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.property
        (cycleRepresentative_mem h c))).2
    simpa [c] using
      (Equiv.Perm.cycle_is_cycleOf (cycleRepresentative_mem h c) c.property)
  obtain ⟨k, hk⟩ := hirep.exists_nat_pow_eq
  have hneRep :
      σ (cycleRepresentative h c) ≠ τ (cycleRepresentative h c) := by
    rw [← hk]
    exact disagreement_pow henc hne k
  have hsigc := congrFun hsig c
  change decide (σ (cycleRepresentative h c) = f (cycleRepresentative h c)) =
      decide (τ (cycleRepresentative h c) = f (cycleRepresentative h c)) at hsigc
  have hsigc' :
      (σ (cycleRepresentative h c) = f (cycleRepresentative h c)) ↔
        τ (cycleRepresentative h c) = f (cycleRepresentative h c) := by
    exact decide_eq_decide.mp hsigc
  have hσcore : UsesCoreEdge f g σ (cycleRepresentative h c) := by
    by_contra hout
    exact hneRep (same_twoMatchingEncoding_of_escape henc hout)
  have hτcore : UsesCoreEdge f g τ (cycleRepresentative h c) :=
    (same_twoMatchingEncoding_core_iff henc _).1 hσcore
  rcases hσcore with hσf | hσg <;> rcases hτcore with hτf | hτg
  · exact hneRep (hσf.trans hτf.symm)
  · exact hneRep (hσf.trans (hsigc'.mp hσf).symm)
  · exact hneRep ((hsigc'.mpr hτf).trans hτf.symm)
  · exact hneRep (hσg.trans hτg.symm)

/-- Graph-specific fiber bound in paper Lemma 9.  A completed two-regular
bipartite multigraph is written as the union of perfect matchings `f` and `g`;
its components with at least two rows are the nontrivial cycles of
`alternatingRowPerm f g`. -/
theorem twoMatchingEncoding_fiber_card_le
    (f g : Equiv.Perm α) (y : α → Option α) :
    (Finset.univ.filter fun σ : Equiv.Perm α ↦
        twoMatchingEncoding f g σ = y).card ≤
      2 ^ (alternatingRowPerm f g).cycleFactorsFinset.card := by
  let S := Finset.univ.filter fun σ : Equiv.Perm α ↦
    twoMatchingEncoding f g σ = y
  let sigType := (alternatingRowPerm f g).cycleFactorsFinset → Bool
  let encode : ↥S → sigType := fun σ ↦ cycleSignature f g σ.1
  have hinj : Function.Injective encode := by
    intro σ τ h
    apply Subtype.ext
    have hσ : twoMatchingEncoding f g σ.1 = y := by
      have hp := σ.property
      dsimp only [S] at hp
      exact (Finset.mem_filter.mp hp).2
    have hτ : twoMatchingEncoding f g τ.1 = y := by
      have hp := τ.property
      dsimp only [S] at hp
      exact (Finset.mem_filter.mp hp).2
    exact cycleSignature_injective_on_encoding_fiber hσ hτ h
  calc
    S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card sigType := Fintype.card_le_of_injective encode hinj
    _ = 2 ^ (alternatingRowPerm f g).cycleFactorsFinset.card := by
      simp [sigType, Fintype.card_fun]

/-- A spanning two-regular bipartite multigraph.  The two slots at each row
record its two incident edges, while `columnDegree` says that every column is
incident to exactly two edge slots.  Parallel edges are represented by equal
values in the two row slots. -/
structure TwoRegularBipartiteMultigraph (α : Type*) [Fintype α]
    [DecidableEq α] where
  /-- The target column of each of the two edge slots at a row vertex. -/
  edge : α → Fin 2 → α
  columnDegree : ∀ j,
    (∑ i, ∑ k : Fin 2, if edge i k = j then 1 else 0) = 2

namespace TwoRegularBipartiteMultigraph

variable (K : TwoRegularBipartiteMultigraph α)

/-- Column neighbors of one row, with parallel edges ignored. -/
noncomputable def neighbors (i : α) : Finset α := by
  classical
  exact Finset.univ.image (K.edge i)

theorem mem_neighbors_iff (i j : α) :
    j ∈ K.neighbors i ↔ ∃ k : Fin 2, K.edge i k = j := by
  classical
  simp [neighbors, eq_comm]

private theorem localColumnCount_le_two (s : Finset α) (j : α) :
    (∑ i ∈ s, ∑ k : Fin 2, if K.edge i k = j then 1 else 0) ≤ 2 := by
  calc
    (∑ i ∈ s, ∑ k : Fin 2, if K.edge i k = j then 1 else 0) ≤
        ∑ i, ∑ k : Fin 2, if K.edge i k = j then 1 else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact Finset.sum_nonneg (fun k _ ↦ by positivity)
    _ = 2 := K.columnDegree j

private theorem localColumnCount_eq_zero_of_notMem
    (s : Finset α) {j : α} (hj : j ∉ s.biUnion K.neighbors) :
    (∑ i ∈ s, ∑ k : Fin 2, if K.edge i k = j then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro k _
  have hne : K.edge i k ≠ j := by
    intro h
    apply hj
    rw [Finset.mem_biUnion]
    exact ⟨i, hi, (K.mem_neighbors_iff i j).2 ⟨k, h⟩⟩
  simp [hne]

/-- The neighborhood family of a two-regular bipartite multigraph satisfies
Hall's condition.  Multiplicities are essential in the proof: `2|S|` edge
slots leave `S`, while at most `2|N(S)|` slots enter its neighborhood. -/
theorem hall_condition (s : Finset α) :
    s.card ≤ (s.biUnion K.neighbors).card := by
  let L : α → ℕ := fun j ↦
    ∑ i ∈ s, ∑ k : Fin 2, if K.edge i k = j then 1 else 0
  have hpartition : 2 * s.card = ∑ j, L j := by
    dsimp [L]
    calc
      2 * s.card = ∑ i ∈ s, ∑ _k : Fin 2, 1 := by simp [mul_comm]
      _ = ∑ i ∈ s, ∑ k : Fin 2, ∑ j, if K.edge i k = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        simp
      _ = ∑ i ∈ s, ∑ j, ∑ k : Fin 2,
          if K.edge i k = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ j, ∑ i ∈ s, ∑ k : Fin 2,
          if K.edge i k = j then 1 else 0 := by
        exact Finset.sum_comm
  have hrestrict :
      (∑ j, L j) = ∑ j ∈ s.biUnion K.neighbors, L j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact K.localColumnCount_eq_zero_of_notMem s hj
  have hbound :
      (∑ j ∈ s.biUnion K.neighbors, L j) ≤
        ∑ _j ∈ s.biUnion K.neighbors, 2 := by
    apply Finset.sum_le_sum
    intro j _
    exact K.localColumnCount_le_two s j
  have htwice : 2 * s.card ≤ 2 * (s.biUnion K.neighbors).card := by
    rw [hpartition, hrestrict]
    simpa [mul_comm] using hbound
  omega

private theorem finTwo_eq_or_eq_rev (k chosen : Fin 2) :
    k = chosen ∨ k = Fin.rev chosen := by
  fin_cases k <;> fin_cases chosen <;> simp

private theorem sum_finTwo_split (a : Fin 2 → ℕ) (chosen : Fin 2) :
    (∑ k, a k) = a chosen + a (Fin.rev chosen) := by
  fin_cases chosen <;> simp [Fin.sum_univ_two, add_comm]

/-- Every spanning two-regular bipartite multigraph is the union of two
perfect matchings.  This is the precise edge-coloring fact needed to pass
from the paper's stub completion to `twoMatchingEncoding`. -/
theorem exists_twoMatching_decomposition :
    ∃ f g : Equiv.Perm α,
      (∀ i, (∃ k : Fin 2, K.edge i k = f i) ∧
        ∃ k : Fin 2, K.edge i k = g i) ∧
      ∀ i k, K.edge i k = f i ∨ K.edge i k = g i := by
  classical
  obtain ⟨p, hpInjective, hpEdge⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective K.neighbors).1
      K.hall_condition
  have hpBijective : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).2 ⟨hpInjective, rfl⟩
  let f : Equiv.Perm α := Equiv.ofBijective p hpBijective
  have hfEdge : ∀ i, ∃ k : Fin 2, K.edge i k = f i := by
    intro i
    exact (K.mem_neighbors_iff i (f i)).1 (hpEdge i)
  let chosen : α → Fin 2 := fun i ↦ Classical.choose (hfEdge i)
  have hchosen : ∀ i, K.edge i (chosen i) = f i := fun i ↦
    Classical.choose_spec (hfEdge i)
  let q : α → α := fun i ↦ K.edge i (Fin.rev (chosen i))
  have hresidual : ∀ j,
      (∑ i, if q i = j then 1 else 0) = 1 := by
    intro j
    have hsplit :
        (∑ i, ∑ k : Fin 2, if K.edge i k = j then 1 else 0) =
          (∑ i, if f i = j then 1 else 0) +
            ∑ i, if q i = j then 1 else 0 := by
      calc
        (∑ i, ∑ k : Fin 2, if K.edge i k = j then 1 else 0) =
            ∑ i, ((if K.edge i (chosen i) = j then 1 else 0) +
              if K.edge i (Fin.rev (chosen i)) = j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact sum_finTwo_split
            (fun k ↦ if K.edge i k = j then 1 else 0) (chosen i)
        _ = (∑ i, if f i = j then 1 else 0) +
            ∑ i, if q i = j then 1 else 0 := by
          rw [Finset.sum_add_distrib]
          simp only [hchosen, q]
    have hchosenCount : (∑ i, if f i = j then 1 else 0) = 1 := by
      simp_rw [f.apply_eq_iff_eq_symm_apply]
      rw [Finset.sum_ite_eq' Finset.univ (f.symm j)]
      simp
    rw [K.columnDegree j, hchosenCount] at hsplit
    omega
  have hqInjective : Function.Injective q := by
    intro i i' hii'
    let fiber := Finset.univ.filter fun r ↦ q r = q i
    have hcard : fiber.card = 1 := by
      rw [Finset.card_filter]
      exact hresidual (q i)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hi : i ∈ fiber := by simp [fiber]
    have hi' : i' ∈ fiber := by simp [fiber, hii']
    have hia : i = a := by simpa [ha] using hi
    have hi'a : i' = a := by simpa [ha] using hi'
    exact hia.trans hi'a.symm
  have hqBijective : Function.Bijective q :=
    (Fintype.bijective_iff_injective_and_card q).2 ⟨hqInjective, rfl⟩
  let g : Equiv.Perm α := Equiv.ofBijective q hqBijective
  refine ⟨f, g, ?_, ?_⟩
  · intro i
    exact ⟨hfEdge i, ⟨Fin.rev (chosen i), rfl⟩⟩
  · intro i k
    rcases finTwo_eq_or_eq_rev k (chosen i) with hk | hk
    · left
      rw [hk, hchosen]
    · right
      exact hk ▸ rfl

end TwoRegularBipartiteMultigraph

end BeyondBethe
