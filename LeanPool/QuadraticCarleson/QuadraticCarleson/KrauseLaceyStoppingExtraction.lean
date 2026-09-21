/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyScaleMaximal

/-!
# Actual finite stopping extraction for the Krause--Lacey recursion

This is the finite version of the extraction following KL18 Lemma 3.5:
select the maximal intervals where either input average exceeds ten times
the parent average. The selected children, their packing, and the bounded
averages on the remaining collection are conclusions, not supplied stopping
or sparse hypotheses. The only structural input is laminarity of the finite
interval collection, as holds in each source dyadic grid.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyStoppingExtraction


theorem interval_eq_of_carrier_subset_of_length_le {I J : RealInterval}
    (hsub : I.carrier ⊆ J.carrier) (hlen : J.length ≤ I.length) : I = J := by
  have he := (Ioc_subset_Ioc_iff I.left_lt_right).mp hsub
  have hl : I.left = J.left := by dsimp [RealInterval.length] at hlen; linarith
  have hr : I.right = J.right := by dsimp [RealInterval.length] at hlen; linarith
  cases I
  cases J
  simp_all

/-- The literal two-function threshold-ten test in the source recursion. -/
def IsBadDescendant (f g : ℝ → ℂ) (I J : RealInterval) : Prop :=
  J.carrier ⊆ I.carrier ∧
    (10 * intervalL1Average f I < intervalL1Average f J ∨
      10 * intervalL1Average g I < intervalL1Average g J)

/-- The selected intervals that satisfy the bad-descendant stopping criterion. -/
noncomputable def badDescendants
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter (IsBadDescendant f g I)

/-- Inclusion-maximal bad intervals, constructed directly from the finite
candidate collection. -/
noncomputable def stoppingChildren
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact (badDescendants S f g I).filter fun J ↦
    ∀ K ∈ badDescendants S f g I, J.carrier ⊆ K.carrier → K = J

theorem mem_badDescendants_iff
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval} :
    J ∈ badDescendants S f g I ↔ J ∈ S ∧ IsBadDescendant f g I J := by
  classical
  simp [badDescendants]

theorem mem_stoppingChildren_iff
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval} :
    J ∈ stoppingChildren S f g I ↔
      J ∈ badDescendants S f g I ∧
        ∀ K ∈ badDescendants S f g I, J.carrier ⊆ K.carrier → K = J := by
  classical
  simp [stoppingChildren]

theorem stoppingChildren_subset
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) :
    stoppingChildren S f g I ⊆ S := by
  intro J hJ
  exact (mem_badDescendants_iff.mp (mem_stoppingChildren_iff.mp hJ).1).1

theorem stoppingChildren_bad
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval}
    (hJ : J ∈ stoppingChildren S f g I) : IsBadDescendant f g I J :=
  (mem_badDescendants_iff.mp (mem_stoppingChildren_iff.mp hJ).1).2

theorem self_not_badDescendant (f g : ℝ → ℂ) (I : RealInterval) :
    ¬ IsBadDescendant f g I I := by
  rintro ⟨_, hf | hg⟩
  · linarith [intervalL1Average_nonneg f I]
  · linarith [intervalL1Average_nonneg g I]

theorem self_not_mem_stoppingChildren
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) :
    I ∉ stoppingChildren S f g I := fun h ↦
  self_not_badDescendant f g I (stoppingChildren_bad h)

/-- Every actual bad interval lies in a selected maximal child. The finite
maximal element is obtained by maximizing interval length among bad
ancestors; no stopping-family existence is assumed. -/
theorem badDescendant_subset_stoppingChild
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval}
    (hJ : J ∈ badDescendants S f g I) :
    ∃ K ∈ stoppingChildren S f g I, J.carrier ⊆ K.carrier := by
  classical
  let A := (badDescendants S f g I).filter fun K ↦ J.carrier ⊆ K.carrier
  have hA : A.Nonempty := ⟨J, Finset.mem_filter.mpr ⟨hJ, Subset.rfl⟩⟩
  obtain ⟨K, hKA, hmax⟩ := A.exists_max_image RealInterval.length hA
  have hKbad := (Finset.mem_filter.mp hKA).1
  have hJK := (Finset.mem_filter.mp hKA).2
  refine ⟨K, mem_stoppingChildren_iff.mpr ⟨hKbad, ?_⟩, hJK⟩
  intro L hL hKL
  have hLA : L ∈ A := Finset.mem_filter.mpr ⟨hL, hJK.trans hKL⟩
  exact (interval_eq_of_carrier_subset_of_length_le hKL (hmax L hLA)).symm

/-- Distinct maximal stopping children are disjoint, derived from the
laminar geometry of the candidate intervals. -/
theorem stoppingChildren_pairwiseDisjoint
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.Pairwise (↑(stoppingChildren S f g I) : Set RealInterval)
      (Disjoint on fun J : RealInterval ↦ J.carrier) := by
  intro J hJ K hK hJK
  rcases hlam (stoppingChildren_subset S f g I hJ)
    (stoppingChildren_subset S f g I hK) hJK with hsub | hsub | hdis
  · exact (hJK ((mem_stoppingChildren_iff.mp hJ).2 K
      (mem_stoppingChildren_iff.mp hK).1 hsub).symm).elim
  · exact (hJK ((mem_stoppingChildren_iff.mp hK).2 J
      (mem_stoppingChildren_iff.mp hJ).1 hsub)).elim
  · exact hdis

/-- The remaining collection on which the local oscillatory estimate must
be proved: discard every interval contained in a selected child. -/
noncomputable def goodCollection
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun J ↦ ¬ ∃ K ∈ stoppingChildren S f g I, J.carrier ⊆ K.carrier

/-- The exact bounded-average hypotheses of KL18 Lemma 3.5 hold on the
constructed remaining collection with `K = 10`. -/
theorem goodCollection_averages_le
    {S : Finset RealInterval} {f g : ℝ → ℂ} {I J : RealInterval}
    (hsub : ∀ K ∈ S, K.carrier ⊆ I.carrier)
    (hJ : J ∈ goodCollection S f g I) :
    intervalL1Average f J ≤ 10 * intervalL1Average f I ∧
      intervalL1Average g J ≤ 10 * intervalL1Average g I := by
  classical
  have hmem := Finset.mem_filter.mp hJ
  have hnot : ¬ IsBadDescendant f g I J := by
    intro hb
    exact hmem.2 (badDescendant_subset_stoppingChild
      (mem_badDescendants_iff.mpr ⟨hmem.1, hb⟩))
  constructor
  · by_contra hf
    exact hnot ⟨hsub J hmem.1, Or.inl (lt_of_not_ge hf)⟩
  · by_contra hg
    exact hnot ⟨hsub J hmem.1, Or.inr (lt_of_not_ge hg)⟩

/-- The actual maximal-child extraction consumes at most one fifth of the
parent's length, by the already proved source packing argument. -/
theorem stoppingChildren_length_le_fifth
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hf : IntegrableOn f I.carrier) (hg : IntegrableOn g I.carrier)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    ∑ J ∈ stoppingChildren S f g I, J.length ≤ I.length / 5 := by
  exact krauseLacey_stoppingChildren_length_le_fifth
    (stoppingChildren S f g I) id I f g
    (stoppingChildren_pairwiseDisjoint f g I hlam)
    (fun _ hJ ↦ (stoppingChildren_bad hJ).1) hf hg
    (fun _ hJ ↦ (stoppingChildren_bad hJ).2)

theorem stoppingMajorSubset_measure_ge_four_fifths
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hf : IntegrableOn f I.carrier) (hg : IntegrableOn g I.carrier)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    4 / 5 * I.length ≤ (volume
      (krauseLaceyStoppingMajorSubset (stoppingChildren S f g I) id I)).toReal := by
  exact krauseLacey_stoppingMajorSubset_measure_ge_four_fifths
    (stoppingChildren S f g I) id I f g
    (stoppingChildren_pairwiseDisjoint f g I hlam)
    (fun _ hJ ↦ (stoppingChildren_bad hJ).1) hf hg
    (fun _ hJ ↦ (stoppingChildren_bad hJ).2)

/-- The parent interval together with its immediate stopping children. -/
noncomputable def stoppingStepFamily
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact insert I (stoppingChildren S f g I)

/-- The root together with its actually extracted children is `1/4` sparse.
No selected-family, packing, or tree-separation hypothesis is supplied. -/
theorem root_insert_stoppingChildren_isSparse
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hf : Integrable f) (hg : Integrable g)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    IsSparse (1 / 4) (↑(stoppingStepFamily S f g I) : Set RealInterval) := by
  classical
  unfold stoppingStepFamily
  let C := stoppingChildren S f g I
  let children : RealInterval → Finset RealInterval := fun J ↦ if J = I then C else ∅
  have hdis := stoppingChildren_pairwiseDisjoint f g I hlam
  apply krauseLacey_finiteStoppingTree_isSparse (insert I C) children f g hf hg
  · intro J hJ
    by_cases hJI : J = I
    · simpa only [children, hJI, ite_true] using hdis
    · simp only [children, ite_eq_right hJI, Finset.coe_empty, Set.pairwise_empty]
  · intro J hJ K hK
    by_cases hJI : J = I
    · subst J
      exact (stoppingChildren_bad (by simpa [children, C] using hK)).1
    · simp [children, hJI] at hK
  · intro J hJ K hK
    by_cases hJI : J = I
    · subst J
      exact (stoppingChildren_bad (by simpa [children, C] using hK)).2
    · simp [children, hJI] at hK
  · intro J hJ K hK hJK
    rcases Finset.mem_insert.mp hJ with rfl | hJ
    · have hKC : K ∈ C := (Finset.mem_insert.mp hK).resolve_left hJK.symm
      exact Or.inr (Or.inl ⟨K, by simpa [children] using hKC, Subset.rfl⟩)
    · rcases Finset.mem_insert.mp hK with rfl | hK
      · exact Or.inr (Or.inr ⟨J, by simpa [children] using hJ, Subset.rfl⟩)
      · exact Or.inl (hdis hJ hK hJK)

/-- The selected intervals contained in a given parent interval. -/
noncomputable def childCollection
    (S : Finset RealInterval) (K : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun J ↦ J.carrier ⊆ K.carrier

/-- Different selected children receive disjoint collections of interval
indices, a consequence of spatial disjointness and nonempty intervals. -/
theorem childCollections_pairwiseDisjoint
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.PairwiseDisjoint (↑(stoppingChildren S f g I) : Set RealInterval)
      (childCollection S) := by
  classical
  intro K hK L hL hKL
  apply Finset.disjoint_left.mpr
  intro J hJK hJL
  have hsubK := (Finset.mem_filter.mp hJK).2
  have hsubL := (Finset.mem_filter.mp hJL).2
  have hxJ : J.right ∈ J.carrier := ⟨J.left_lt_right, le_rfl⟩
  exact Set.disjoint_left.mp
    (stoppingChildren_pairwiseDisjoint f g I hlam hK hL hKL)
    (hsubK hxJ) (hsubL hxJ)

/-- Exact finite sum decomposition into the bounded-average collection and
the collections passed to the recursively selected children. -/
theorem sum_eq_good_add_sum_children
    {S : Finset RealInterval} (f g : ℝ → ℂ) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (F : RealInterval → ℂ) :
    (∑ J ∈ S, F J) = (∑ J ∈ goodCollection S f g I, F J) +
      ∑ K ∈ stoppingChildren S f g I, ∑ J ∈ childCollection S K, F J := by
  classical
  let P := fun J : RealInterval ↦
    ∃ K ∈ stoppingChildren S f g I, J.carrier ⊆ K.carrier
  have hunion : (stoppingChildren S f g I).biUnion (childCollection S) = S.filter P := by
    ext J
    simp only [Finset.mem_biUnion, childCollection, Finset.mem_filter, P]
    constructor
    · rintro ⟨K, hK, hJS, hJK⟩
      exact ⟨hJS, K, hK, hJK⟩
    · rintro ⟨hJS, K, hK, hJK⟩
      exact ⟨K, hK, hJS, hJK⟩
  rw [← Finset.sum_biUnion (childCollections_pairwiseDisjoint f g I hlam), hunion]
  change (∑ J ∈ S, F J) = (∑ J ∈ S.filter (fun J ↦ ¬ P J), F J) +
    ∑ J ∈ S.filter P, F J
  rw [add_comm, Finset.sum_filter_add_sum_filter_not]


end KrauseLaceyStoppingExtraction
end QuadraticCarleson
