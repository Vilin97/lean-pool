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
# Pressure Gradient Origin Cell Instance Exhaustion

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set Metric

noncomputable section

namespace CKN.Core.Step4.OriginInstance

/-- The points of the closed interval `[-n, n]` whose closed `1/(n+1)`-ball lies in `I`. -/
def exhaustionCore (I : Set ℝ) (n : ℕ) : Set ℝ :=
  Set.Icc (-(n : ℝ)) (n : ℝ) ∩ {t : ℝ | Metric.closedBall t (1 / ((n : ℝ) + 1)) ⊆ I}

private lemma mem_exhaustionCore {I : Set ℝ} {n : ℕ} {t : ℝ} :
    t ∈ exhaustionCore I n ↔
      t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ∧
        Metric.closedBall t (1 / ((n : ℝ) + 1)) ⊆ I := by
  simp [exhaustionCore]

/-- If `I` is order-connected, the centres of the closed `δ`-balls contained in `I` form an
order-connected set. -/
private lemma ordConnected_ballCentres {I : Set ℝ} (hI : I.OrdConnected) {δ : ℝ} (hδ : 0 ≤ δ) :
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

private lemma exhaustionCore_ordConnected {I : Set ℝ} (hI : I.OrdConnected) (n : ℕ) :
    (exhaustionCore I n).OrdConnected := by
  rw [exhaustionCore]
  exact Set.OrdConnected.inter Set.ordConnected_Icc (ordConnected_ballCentres hI (by positivity))

private lemma exhaustionCore_mono (I : Set ℝ) : Monotone (exhaustionCore I) := by
  intro m n hmn t ht
  rw [mem_exhaustionCore] at ht ⊢
  obtain ⟨htIcc, htball⟩ := ht
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc] at htIcc ⊢
    exact ⟨le_trans (neg_le_neg hmn') htIcc.1, le_trans htIcc.2 hmn'⟩
  · refine (Metric.closedBall_subset_closedBall ?_).trans htball
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hmn'])

private lemma closure_exhaustionCore_subset_I (I : Set ℝ) (n : ℕ) :
    closure (exhaustionCore I n) ⊆ I := by
  intro t ht
  rw [Metric.mem_closure_iff] at ht
  obtain ⟨t', ht', hdist⟩ := ht (1 / ((n : ℝ) + 1)) (by positivity)
  exact (mem_exhaustionCore.1 ht').2 (by rw [Metric.mem_closedBall]; exact le_of_lt hdist)

private lemma isCompact_closure_exhaustionCore (I : Set ℝ) (n : ℕ) :
    IsCompact (closure (exhaustionCore I n)) :=
  IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (-(n : ℝ)) (n : ℝ)))
    isClosed_closure
    (closure_minimal (fun _ ht => (mem_exhaustionCore.1 ht).1) isClosed_Icc)

private lemma iUnion_closure_exhaustionCore_eq {I : Set ℝ} (hopen : IsOpen I) :
    (⋃ n, closure (exhaustionCore I n)) = I := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => closure_exhaustionCore_subset_I I n) ?_
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
  rw [mem_exhaustionCore]
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc]
    have ht_lower : -(n₀ : ℝ) ≤ t := le_trans (neg_le_neg (le_of_lt hn₀)) (neg_abs_le t)
    have ht_upper : t ≤ (max n₀ n₁ : ℕ) := le_trans (le_trans (le_abs_self t) (le_of_lt hn₀)) hn₀'
    exact ⟨le_trans (neg_le_neg hn₀') ht_lower, ht_upper⟩
  · refine (Metric.closedBall_subset_ball (lt_of_le_of_lt hle hn₁)).trans hδsub

private lemma exists_subset_exhaustionCore {I : Set ℝ} (hopen : IsOpen I) {T : Set ℝ}
    (hT : IsCompact T) (hTI : T ⊆ I) : ∃ n, T ⊆ exhaustionCore I n := by
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
  rw [mem_exhaustionCore]
  refine ⟨?_, ?_⟩
  · have hRt : t ∈ Set.Icc (0 - R) (0 + R) := by
      simpa only [Real.closedBall_eq_Icc] using hR ht
    rw [Set.mem_Icc] at hRt
    rw [Set.mem_Icc]
    exact ⟨by linarith only [hRt.1, hRle], by linarith only [hRt.2, hRle]⟩
  · intro s hs
    rw [Metric.mem_closedBall] at hs
    exact hδsub (Metric.mem_thickening_iff.2 ⟨t, ht, lt_of_le_of_lt hs hr⟩)

/-- An open, order-connected subset of the line is the increasing union of compact
order-connected subsets, and every compact subset is contained in one of them. -/
theorem exists_compact_ordConnected_exhaustion {I : Set ℝ}
    (hopen : IsOpen I) (hord : I.OrdConnected) :
    ∃ J : ℕ → Set ℝ,
      Monotone J ∧
      (∀ n, (J n).OrdConnected) ∧
      (∀ n, IsCompact (J n)) ∧
      (∀ n, J n ⊆ I) ∧
      (⋃ n, J n) = I ∧
      (∀ T : Set ℝ, IsCompact T → T ⊆ I → ∃ n, T ⊆ J n) := by
  refine ⟨fun n => closure (exhaustionCore I n), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m n hmn => closure_mono (exhaustionCore_mono I hmn)
  · intro n
    exact ((exhaustionCore_ordConnected hord n).isPreconnected.closure).ordConnected
  · intro n
    exact isCompact_closure_exhaustionCore I n
  · intro n
    exact closure_exhaustionCore_subset_I I n
  · exact iUnion_closure_exhaustionCore_eq hopen
  · intro T hT hTI
    obtain ⟨n, hn⟩ := exists_subset_exhaustionCore hopen hT hTI
    exact ⟨n, hn.trans subset_closure⟩

end CKN.Core.Step4.OriginInstance
