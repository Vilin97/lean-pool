/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Pressure Gradient Origin Clause Exhaustion

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set Metric

noncomputable section

namespace CKN.Core.Step4

/-!
# Exhausting an open order-connected set of times by compact order-connected sets

A set `I ⊆ ℝ` that is open and order-connected is the increasing union of compact
order-connected subsets, and every compact subset of `I` is already contained in one of
them. Concretely, for each `n : ℕ` we take the points whose `1 / (n + 1)`-neighbourhood
lies in `I` and which themselves lie in the ambient interval `[-n, n]`, and then we close
that set. Each stage is compact, order-connected, contained in `I`, the stages increase,
their union is all of `I`, and compact subsets are absorbed because a compact subset of an
open set has a positive Lebesgue number.

This is the elementary device that turns a local, bounded-time construction on an open
order-connected time interval into a construction on the whole interval: every compact
piece of the interval is contained in a single compact stage.
-/

/-- The raw (pre-closure) `n`-th stage of the exhaustion of `I`: points in the ambient
interval `[-n, n]` whose closed `1 / (n + 1)`-ball is contained in `I`. -/
def originClauseCore (I : Set ℝ) (n : ℕ) : Set ℝ :=
  Set.Icc (-(n : ℝ)) (n : ℝ) ∩
    {t : ℝ | Metric.closedBall t (1 / ((n : ℝ) + 1)) ⊆ I}

/-- Membership in the raw `n`-th stage unwinds to the ambient interval bound together with
the containment of the closed neighbourhood. -/
private lemma mem_originClauseCore {I : Set ℝ} {n : ℕ} {t : ℝ} :
    t ∈ originClauseCore I n ↔
      t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∧
        Metric.closedBall t (1 / ((n : ℝ) + 1)) ⊆ I := by
  simp [originClauseCore]

/-- Centres of closed balls of a fixed radius contained in an order-connected set are
themselves order-connected. -/
private lemma originClauseBallCentres_ordConnected {I : Set ℝ} (hI : I.OrdConnected)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ({t : ℝ | Metric.closedBall t δ ⊆ I} : Set ℝ).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro x hx y hy hxy z hz s hs
  rw [Metric.mem_closedBall] at hs
  rcases le_total s x with hsx | hxs
  · refine hx ?_
    rw [Metric.mem_closedBall]
    have h₂ : dist s x ≤ dist s z := by
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hsx),
        abs_of_nonpos (sub_nonpos.2 (le_trans hsx hz.1))]
      linarith only [hz.1]
    linarith only [h₂, hs]
  · rcases le_total y s with hys | hsy
    · refine hy ?_
      rw [Metric.mem_closedBall]
      have h₂ : dist s y ≤ dist s z := by
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hys),
          abs_of_nonneg (sub_nonneg.2 (le_trans hz.2 hys))]
        linarith only [hz.2]
      linarith only [h₂, hs]
    · exact hI.out (hx (Metric.mem_closedBall_self hδ))
        (hy (Metric.mem_closedBall_self hδ)) ⟨hxs, hsy⟩

/-- Each raw stage is order-connected when `I` is. -/
private lemma originClauseCore_ordConnected {I : Set ℝ} (hI : I.OrdConnected) (n : ℕ) :
    (originClauseCore I n).OrdConnected := by
  rw [originClauseCore]
  exact Set.OrdConnected.inter Set.ordConnected_Icc
    (originClauseBallCentres_ordConnected hI (by positivity))

/-- The raw stages increase with `n`. -/
private lemma originClauseCore_mono (I : Set ℝ) : Monotone (originClauseCore I) := by
  intro m n hmn t ht
  rw [mem_originClauseCore] at ht ⊢
  obtain ⟨htIcc, htball⟩ := ht
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc] at htIcc ⊢
    exact ⟨le_trans (neg_le_neg hmn') htIcc.1, le_trans htIcc.2 hmn'⟩
  · refine (Metric.closedBall_subset_closedBall ?_).trans htball
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hmn'])

/-- The closure of a raw stage is still contained in `I`. -/
private lemma originClauseClosureCore_subset_I (I : Set ℝ) (n : ℕ) :
    closure (originClauseCore I n) ⊆ I := by
  intro t ht
  rw [Metric.mem_closure_iff] at ht
  obtain ⟨t', ht', hdist⟩ := ht (1 / ((n : ℝ) + 1)) (by positivity)
  exact (mem_originClauseCore.1 ht').2 (by rw [Metric.mem_closedBall]; exact le_of_lt hdist)

/-- The closure of a raw stage is compact: it is a closed subset of the ambient interval
`[-n, n]`. -/
private lemma originClauseIsCompactClosureCore (I : Set ℝ) (n : ℕ) :
    IsCompact (closure (originClauseCore I n)) :=
  IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (-(n : ℝ)) (n : ℝ)))
    isClosed_closure
    (closure_minimal (fun _ ht => (mem_originClauseCore.1 ht).1) isClosed_Icc)

/-- The closures of the raw stages cover an open set `I`. -/
private lemma originClauseIUnionClosureCore_eq {I : Set ℝ} (hopen : IsOpen I) :
    (⋃ n, closure (originClauseCore I n)) = I := by
  refine Set.Subset.antisymm
    (Set.iUnion_subset fun n => originClauseClosureCore_subset_I I n) ?_
  intro t ht
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨δ, hδpos, hδsub⟩ := hopen t ht
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt |t|
  obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδpos
  have hn₀' : (n₀ : ℝ) ≤ (max n₀ n₁ : ℕ) := by exact_mod_cast le_max_left n₀ n₁
  have hn₁' : (n₁ : ℝ) ≤ (max n₀ n₁ : ℕ) := by exact_mod_cast le_max_right n₀ n₁
  have hle : 1 / ((max n₀ n₁ : ℕ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith only [hn₁'])
  refine Set.mem_iUnion.2 ⟨max n₀ n₁, subset_closure ?_⟩
  rw [mem_originClauseCore]
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc]
    have ht_lower : -(n₀ : ℝ) ≤ t :=
      le_trans (neg_le_neg (le_of_lt hn₀)) (neg_abs_le t)
    have ht_upper : t ≤ (max n₀ n₁ : ℕ) :=
      le_trans (le_trans (le_abs_self t) (le_of_lt hn₀)) hn₀'
    exact ⟨le_trans (neg_le_neg hn₀') ht_lower, ht_upper⟩
  · refine (Metric.closedBall_subset_ball (lt_of_le_of_lt hle hn₁)).trans hδsub

/-- Every compact subset of an open set `I` is contained in some raw stage. -/
private lemma originClauseExistsSubsetCore {I : Set ℝ} (hopen : IsOpen I) {T : Set ℝ}
    (hT : IsCompact T) (hTI : T ⊆ I) : ∃ n, T ⊆ originClauseCore I n := by
  obtain ⟨δ, hδpos, hδsub⟩ := hT.exists_thickening_subset_open hopen hTI
  obtain ⟨R, hR⟩ := hT.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt R
  obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδpos
  have hn₀' : (n₀ : ℝ) ≤ (max n₀ n₁ : ℕ) := by exact_mod_cast le_max_left n₀ n₁
  have hn₁' : (n₁ : ℝ) ≤ (max n₀ n₁ : ℕ) := by exact_mod_cast le_max_right n₀ n₁
  have hRle : R ≤ (max n₀ n₁ : ℕ) := le_trans (le_of_lt hn₀) hn₀'
  have hr : 1 / ((max n₀ n₁ : ℕ) + 1) < δ := by
    have hle : 1 / ((max n₀ n₁ : ℕ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith only [hn₁'])
    linarith only [hle, hn₁]
  refine ⟨max n₀ n₁, fun t ht => ?_⟩
  rw [mem_originClauseCore]
  refine ⟨?_, ?_⟩
  · have hRt : t ∈ Set.Icc (0 - R) (0 + R) := by
      simpa only [Real.closedBall_eq_Icc] using hR ht
    rw [Set.mem_Icc] at hRt
    rw [Set.mem_Icc]
    exact ⟨by linarith only [hRt.1, hRle], by linarith only [hRt.2, hRle]⟩
  · intro s hs
    rw [Metric.mem_closedBall] at hs
    exact hδsub (Metric.mem_thickening_iff.2 ⟨t, ht, lt_of_le_of_lt hs hr⟩)

/-- **Exhaustion of an open order-connected set of times.** An open order-connected
`I ⊆ ℝ` is the increasing union of compact order-connected subsets, and every compact
subset of `I` is contained in one of them. -/
theorem originClauseTimeExhaustion {I : Set ℝ}
    (hopen : IsOpen I) (hord : I.OrdConnected) :
    ∃ J : ℕ → Set ℝ,
      Monotone J ∧
      (∀ n, (J n).OrdConnected) ∧
      (∀ n, IsCompact (J n)) ∧
      (∀ n, J n ⊆ I) ∧
      (⋃ n, J n) = I ∧
      (∀ T : Set ℝ, IsCompact T → T ⊆ I → ∃ n, T ⊆ J n) := by
  refine ⟨fun n => closure (originClauseCore I n), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m n hmn => closure_mono (originClauseCore_mono I hmn)
  · intro n
    exact ((originClauseCore_ordConnected hord n).isPreconnected.closure).ordConnected
  · intro n
    exact originClauseIsCompactClosureCore I n
  · intro n
    exact originClauseClosureCore_subset_I I n
  · exact originClauseIUnionClosureCore_eq hopen
  · intro T hT hTI
    obtain ⟨n, hn⟩ := originClauseExistsSubsetCore hopen hT hTI
    exact ⟨n, hn.trans subset_closure⟩

end CKN.Core.Step4
