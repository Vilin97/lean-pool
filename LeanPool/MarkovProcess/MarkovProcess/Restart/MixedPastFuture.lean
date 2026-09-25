/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Path.DenseFiltration
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.DenseTimeFiniteShift
public import LeanPool.MarkovProcess.MarkovProcess.DenseTime.PhysicalReindex
public import Mathlib.Data.Finset.Sum
public import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelMixedPullback


/-!
# Mixed past-future coordinates and the cut factorization

This file merges the following former modules, one section each:

* `MixedPastFutureCoordinates`: Finite coordinates mixing a rational past and shifted future
* `MixedPastFutureCutCoordinates`: Finite mixed coordinates split at their rational terminal time
* `MixedPastFutureCutFactorization`: Factoring finite mixed past/future coordinates at a
    rational cut
-/

@[expose] public section

noncomputable section PortComputability

namespace MarkovProcess

section MixedPastFutureCoordinates

open MeasureTheory


section

namespace MixedPastFuture

/-- Past labels occurring in a finite mixed-coordinate set, viewed as dense absolute times. -/
def pastFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  I.toLeft.map
    ⟨(fun r ↦ r.1), fun _ _ h ↦ Subtype.ext h⟩

/-- Future labels occurring in a finite mixed-coordinate set. -/
def futureFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  I.toRight

@[simp]
theorem mem_pastFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : DenseTime) :
    r ∈ pastFinset S I ↔ ∃ h : r ≤ S, Sum.inl ⟨r, h⟩ ∈ I := by
  rw [pastFinset, Finset.mem_map]
  constructor
  · rintro ⟨t, ht, htr⟩
    subst r
    refine ⟨t.property, ?_⟩
    exact Finset.mem_toLeft.mp ht
  · rintro ⟨hrS, hrI⟩
    exact ⟨⟨r, hrS⟩, Finset.mem_toLeft.mpr hrI, rfl⟩

@[simp]
theorem mem_futureFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (r : DenseTime) :
    r ∈ futureFinset S I ↔ Sum.inr r ∈ I := by
  exact Finset.mem_toRight

/-- The finite set of absolute dense times observed by a mixed past/future coordinate set. -/
def absoluteFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Finset DenseTime :=
  pastFinset S I ∪ DenseTime.addFinset S (futureFinset S I)

@[simp]
theorem mem_absoluteFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : DenseTime) :
    r ∈ absoluteFinset S I ↔
      (∃ h : r ≤ S, Sum.inl ⟨r, h⟩ ∈ I) ∨
        ∃ t ∈ futureFinset S I, S + t = r := by
  rw [absoluteFinset, Finset.mem_union, mem_pastFinset, DenseTime.mem_addFinset]

/-- Send a mixed label to the absolute dense time which it observes.  This map need not be
injective: the terminal past label and future zero both map to `S`. -/
def absoluteTime (S : DenseTime) : Set.Iic S ⊕ DenseTime → DenseTime
  | Sum.inl r => r.1
  | Sum.inr t => S + t

@[simp]
theorem absoluteTime_inl (S : DenseTime) (r : Set.Iic S) :
    absoluteTime S (Sum.inl r) = r := rfl

@[simp]
theorem absoluteTime_inr (S t : DenseTime) :
    absoluteTime S (Sum.inr t) = S + t := rfl

@[simp]
theorem absoluteTime_terminal_eq_zeroFuture (S : DenseTime) :
    absoluteTime S (Sum.inl ⟨S, show S ≤ S from le_rfl⟩) =
      absoluteTime S (Sum.inr 0) := by
  simp only [absoluteTime_inl, absoluteTime_inr, add_zero]

/-- Every label in `I` has its absolute time in `absoluteFinset S I`. -/
def absoluteIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    absoluteFinset S I := by
  refine ⟨absoluteTime S i, ?_⟩
  cases hi : i.1 with
  | inl r =>
    have hir : Sum.inl r ∈ I := by simpa only [hi] using i.property
    change r.1 ∈ pastFinset S I ∪ DenseTime.addFinset S (futureFinset S I)
    apply Finset.mem_union_left
    rw [pastFinset, Finset.mem_map]
    exact ⟨r, Finset.mem_toLeft.mpr hir, rfl⟩
  | inr t =>
    have hit : Sum.inr t ∈ I := by simpa only [hi] using i.property
    apply Finset.mem_union_right
    rw [DenseTime.mem_addFinset]
    exact ⟨t, Finset.mem_toRight.mpr hit, rfl⟩

@[simp]
theorem absoluteIndex_val (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    (absoluteIndex S I i : DenseTime) = absoluteTime S i := rfl

/-- The physical nonnegative-real times corresponding to a finite mixed-coordinate set. -/
def absolutePhysicalFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet (absoluteFinset S I)

/-- The physical-time coordinate selected by a mixed label. -/
def absolutePhysicalIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    absolutePhysicalFinset S I :=
  DenseTime.physicalSetEquiv (absoluteFinset S I) (absoluteIndex S I i)

@[simp]
theorem absolutePhysicalIndex_val (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    (absolutePhysicalIndex S I i : NNReal) =
      DenseTime.castOrderEmbedding (absoluteTime S i) := rfl

/-- Pull physical absolute-time coordinates back to their mixed labels.  This merely duplicates a
coordinate when past terminal time and future zero both occur. -/
def pullbackAbsolutePhysical {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinset S I → alpha) : I → alpha :=
  fun i ↦ path (absolutePhysicalIndex S I i)

@[simp]
theorem pullbackAbsolutePhysical_apply {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinset S I → alpha) (i : I) :
    pullbackAbsolutePhysical S I path i = path (absolutePhysicalIndex S I i) := rfl

variable {alpha : Type*} [MeasurableSpace alpha]

/-- Pullback from absolute physical coordinates to mixed labels is measurable. -/
theorem measurable_pullbackAbsolutePhysical (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (pullbackAbsolutePhysical (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (absolutePhysicalIndex S I i)

end MixedPastFuture

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The rational past through `S` and the rational coordinates of the future shifted at `S`,
combined into a single sum-indexed path. -/
def mixedPastShiftedCoordinates (S : DenseTime) (omega : ContinuousPath alpha) :
    Set.Iic S ⊕ DenseTime → alpha
  | Sum.inl r => omega (DenseTime.castOrderEmbedding r)
  | Sum.inr t => denseRestriction (shift (DenseTime.castOrderEmbedding S) omega) t

@[simp]
theorem mixedPastShiftedCoordinates_inl (S : DenseTime) (omega : ContinuousPath alpha)
    (r : Set.Iic S) :
    mixedPastShiftedCoordinates S omega (Sum.inl r) =
      omega (DenseTime.castOrderEmbedding r) := rfl

@[simp]
theorem mixedPastShiftedCoordinates_inr (S t : DenseTime) (omega : ContinuousPath alpha) :
    mixedPastShiftedCoordinates S omega (Sum.inr t) =
      omega (DenseTime.castOrderEmbedding (S + t)) := by
  simp only [mixedPastShiftedCoordinates, denseRestriction_apply, shift_apply,
    DenseTime.castOrderEmbedding_add]

/-- Mixed shifted coordinates depend only on the corresponding absolute dense time. -/
theorem mixedPastShiftedCoordinates_eq_absoluteTime (S : DenseTime)
    (omega : ContinuousPath alpha) (i : Set.Iic S ⊕ DenseTime) :
    mixedPastShiftedCoordinates S omega i =
      omega (DenseTime.castOrderEmbedding (MixedPastFuture.absoluteTime S i)) := by
  rcases i with r | t
  · rfl
  · exact mixedPastShiftedCoordinates_inr S t omega

/-- Restricting the mixed rational past and shifted future is evaluation on the one finite set of
absolute physical times followed by the canonical (possibly noninjective) coordinate pullback. -/
theorem restrict_mixedPastShiftedCoordinates (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (omega : ContinuousPath alpha) :
    I.restrict (mixedPastShiftedCoordinates S omega) =
      MixedPastFuture.pullbackAbsolutePhysical S I
        (fun t : MixedPastFuture.absolutePhysicalFinset S I ↦ omega t) := by
  funext i
  change mixedPastShiftedCoordinates S omega i =
    omega (MixedPastFuture.absolutePhysicalIndex S I i)
  rw [mixedPastShiftedCoordinates_eq_absoluteTime]
  exact congrArg omega (MixedPastFuture.absolutePhysicalIndex_val S I i).symm

variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- The mixed rational-past/shifted-future coordinate map is Borel measurable. -/
theorem measurable_mixedPastShiftedCoordinates (S : DenseTime) :
    Measurable (mixedPastShiftedCoordinates (alpha := alpha) S) := by
  rw [measurable_pi_iff]
  rintro (r | t)
  · exact measurable_coordinateProcess (DenseTime.castOrderEmbedding r)
  · rw [show (fun omega ↦ mixedPastShiftedCoordinates S omega (Sum.inr t)) =
        coordinateProcess (alpha := alpha) (DenseTime.castOrderEmbedding (S + t)) by
          funext omega
          exact mixedPastShiftedCoordinates_inr S t omega]
    exact measurable_coordinateProcess (DenseTime.castOrderEmbedding (S + t))

end ContinuousPath

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The mixed-coordinate map is literally the existing complete rational-past restriction paired
with the dense restriction of the shifted future.  This bridge contains no probability algebra. -/
theorem mixedPastShiftedCoordinates_eq_densePast_sumElim (S : DenseTime)
    (omega : ContinuousPath alpha) :
    mixedPastShiftedCoordinates S omega =
      Sum.elim (densePastRestriction S omega)
        (denseRestriction (shift (DenseTime.castOrderEmbedding S) omega)) := by
  funext i
  rcases i with r | t
  · rfl
  · rfl

end ContinuousPath
end

end MixedPastFutureCoordinates

section MixedPastFutureCutCoordinates

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MixedPastFuture

section

private theorem sort_union_eq_append {beta : Type*} [LinearOrder beta]
    (A B : Finset beta) (hAB : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    (A ∪ B).sort = A.sort ++ B.sort := by
  apply (A ∪ B).sortedLT_sort.eq_of_mem_iff
  · rw [List.sortedLT_iff_pairwise, List.pairwise_append]
    exact ⟨A.sortedLT_sort.pairwise, B.sortedLT_sort.pairwise, fun a ha b hb ↦
      hAB a ((A.mem_sort (· ≤ ·)).mp ha) b ((B.mem_sort (· ≤ ·)).mp hb)⟩
  · intro x
    simp only [Finset.mem_sort, Finset.mem_union, List.mem_append]

/-- Past observation times with the cut inserted, whether or not the mixed labels observe it. -/
def pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  pastFinset S I ∪ {S}

@[simp]
theorem mem_pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (r : DenseTime) :
    r ∈ pastWithTerminalFinset S I ↔
      (∃ h : r ≤ S, Sum.inl ⟨r, h⟩ ∈ I) ∨ r = S := by
  simp only [pastWithTerminalFinset, Finset.mem_union, mem_pastFinset,
    Finset.mem_singleton]

/-- Strictly positive elapsed future times.  Future zero is represented by the terminal past
coordinate instead of a second coordinate in the ordered concatenation. -/
def positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  (futureFinset S I).filter (0 < ·)

@[simp]
theorem mem_positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (t : DenseTime) :
    t ∈ positiveFutureFinset S I ↔ Sum.inr t ∈ I ∧ 0 < t := by
  simp only [positiveFutureFinset, Finset.mem_filter, mem_futureFinset]

/-- The absolute observation set after inserting the cut. -/
def absoluteFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset DenseTime :=
  absoluteFinset S I ∪ {S}

/-- The cut-augmented absolute set is the union of the augmented past and the translate of the
strictly positive future.  Thus future zero creates no second ordered coordinate. -/
theorem absoluteFinsetWithTerminal_eq (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    absoluteFinsetWithTerminal S I =
      pastWithTerminalFinset S I ∪ DenseTime.addFinset S (positiveFutureFinset S I) := by
  ext r
  simp only [absoluteFinsetWithTerminal, Finset.mem_union, mem_absoluteFinset,
    Finset.mem_singleton, mem_pastWithTerminalFinset, DenseTime.mem_addFinset,
    mem_positiveFutureFinset]
  constructor
  · rintro ((hp | ⟨t, htI, htr⟩) | hrS)
    · exact Or.inl (Or.inl hp)
    · by_cases ht0 : t = 0
      · exact Or.inl (Or.inr (by simpa only [ht0, add_zero] using htr.symm))
      · exact Or.inr ⟨t,
          ⟨(mem_futureFinset S I t).mp htI, bot_lt_iff_ne_bot.mpr ht0⟩, htr⟩
    · exact Or.inl (Or.inr hrS)
  · rintro ((hp | hrS) | ⟨t, ⟨htI, _⟩, htr⟩)
    · exact Or.inl (Or.inl hp)
    · exact Or.inr hrS
    · exact Or.inl (Or.inr ⟨t, (mem_futureFinset S I t).mpr htI, htr⟩)

theorem le_terminal_of_mem_pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) {r : DenseTime}
    (hr : r ∈ pastWithTerminalFinset S I) : r ≤ S := by
  rcases (mem_pastWithTerminalFinset S I r).mp hr with ⟨h, _⟩ | rfl
  · exact h
  · exact le_rfl

theorem terminal_lt_of_mem_add_positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) {r : DenseTime}
    (hr : r ∈ DenseTime.addFinset S (positiveFutureFinset S I)) : S < r := by
  obtain ⟨t, ht, rfl⟩ := (DenseTime.mem_addFinset S (positiveFutureFinset S I) r).mp hr
  exact lt_add_of_pos_right S ((mem_positiveFutureFinset S I t).mp ht).2

/-- The two sides of the cut are disjoint after future zero has been represented by the cut. -/
theorem disjoint_pastWithTerminalFinset_add_positiveFutureFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Disjoint (pastWithTerminalFinset S I)
      (DenseTime.addFinset S (positiveFutureFinset S I)) := by
  rw [Finset.disjoint_left]
  intro r hrPast hrFuture
  exact (not_lt_of_ge (le_terminal_of_mem_pastWithTerminalFinset S I hrPast))
    (terminal_lt_of_mem_add_positiveFutureFinset S I hrFuture)

/-- Cardinality splits as strict future plus cut-augmented past.  The order matches the
`n + (m + 1)` convention of finite-time concatenation. -/
theorem card_absoluteFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (absoluteFinsetWithTerminal S I).card =
      (positiveFutureFinset S I).card + (pastWithTerminalFinset S I).card := by
  rw [absoluteFinsetWithTerminal_eq,
    Finset.card_union_of_disjoint
      (disjoint_pastWithTerminalFinset_add_positiveFutureFinset S I),
    DenseTime.addFinset, Finset.card_map, Nat.add_comm]

/-- Number of past coordinates strictly before the final slot occupied by the cut. -/
def pastPredecessorCard (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : ℕ :=
  (pastWithTerminalFinset S I).card - 1

theorem card_pastWithTerminalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (pastWithTerminalFinset S I).card = pastPredecessorCard S I + 1 := by
  symm
  exact Nat.sub_add_cancel
    (Finset.one_le_card.mpr ⟨S,
      Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩)

/-- Physical-time version of the cut-augmented absolute set. -/
def absolutePhysicalFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet (absoluteFinsetWithTerminal S I)

/-- Physical coordinates of the cut-augmented past. -/
def pastPhysicalFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet (pastWithTerminalFinset S I)

/-- Absolute physical coordinates of the strictly positive future. -/
def positiveFutureAbsolutePhysicalFinset (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) : Finset NNReal :=
  SubMarkovKernelSemigroup.denseTimePhysicalSet
    (DenseTime.addFinset S (positiveFutureFinset S I))

theorem absolutePhysicalFinsetWithTerminal_eq_union (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    absolutePhysicalFinsetWithTerminal S I =
      pastPhysicalFinsetWithTerminal S I ∪ positiveFutureAbsolutePhysicalFinset S I := by
  simp only [absolutePhysicalFinsetWithTerminal, absoluteFinsetWithTerminal_eq,
    pastPhysicalFinsetWithTerminal, positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.map_union]

theorem pastPhysical_lt_positiveFutureAbsolutePhysical (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    ∀ a ∈ pastPhysicalFinsetWithTerminal S I,
      ∀ b ∈ positiveFutureAbsolutePhysicalFinset S I, a < b := by
  intro a ha b hb
  rw [pastPhysicalFinsetWithTerminal,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ha
  rw [positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at hb
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact DenseTime.castOrderEmbedding.strictMono
    (lt_of_le_of_lt (le_terminal_of_mem_pastWithTerminalFinset S I hr)
      (terminal_lt_of_mem_add_positiveFutureFinset S I ht))

theorem card_absolutePhysicalFinsetWithTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (absolutePhysicalFinsetWithTerminal S I).card =
      (positiveFutureFinset S I).card + (pastPredecessorCard S I + 1) := by
  rw [absolutePhysicalFinsetWithTerminal,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
    card_absoluteFinsetWithTerminal, card_pastWithTerminalFinset]

/-- Reindex the cut cardinality by the cardinality of the augmented absolute physical set. -/
def cutOrderEmbedding (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Fin ((positiveFutureFinset S I).card + (pastPredecessorCard S I + 1)) ↪o
      Fin (absolutePhysicalFinsetWithTerminal S I).card :=
  (Fin.castOrderIso (card_absolutePhysicalFinsetWithTerminal S I).symm).toOrderEmbedding

/-- Increasing physical times of the cut-augmented mixed set, cast to the cardinal convention
expected by finite-time concatenation. -/
def cutOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes
      ((positiveFutureFinset S I).card + (pastPredecessorCard S I + 1)) :=
  (cutOrderEmbedding S I).trans
    (SubMarkovKernelSemigroup.finiteSetTimes (absolutePhysicalFinsetWithTerminal S I))

/-- Sorted physical coordinates of the augmented past, with its cardinality written as a
successor. -/
def cutPastOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes (pastPredecessorCard S I + 1) :=
  (Fin.castOrderIso (by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset])).toOrderEmbedding.trans
    (SubMarkovKernelSemigroup.finiteSetTimes (pastPhysicalFinsetWithTerminal S I))

/-- Sorted physical elapsed times of the strictly positive future. -/
def positiveFutureOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes (positiveFutureFinset S I).card :=
  (Fin.castOrderIso (by
    rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map])).toOrderEmbedding.trans
    (SubMarkovKernelSemigroup.finiteSetTimes
      (SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)))

/-- The initial block of the sorted augmented absolute times is exactly the augmented past. -/
theorem cutOrderedPhysicalTimes_initialSegment (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) =
      cutPastOrderedPhysicalTimes S I := by
  apply DFunLike.ext _ _
  intro i
  change
    (absolutePhysicalFinsetWithTerminal S I).orderEmbOfFin
      (card_absolutePhysicalFinsetWithTerminal S I)
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.castAdd (positiveFutureFinset S I).card i)) =
      (pastPhysicalFinsetWithTerminal S I).orderEmbOfFin
        (by rw [pastPhysicalFinsetWithTerminal,
          SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
          card_pastWithTerminalFinset]) i
  have hsort : (absolutePhysicalFinsetWithTerminal S I).sort =
      (pastPhysicalFinsetWithTerminal S I).sort ++
        (positiveFutureAbsolutePhysicalFinset S I).sort := by
    rw [absolutePhysicalFinsetWithTerminal_eq_union]
    exact sort_union_eq_append _ _
      (pastPhysical_lt_positiveFutureAbsolutePhysical S I)
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  simp only [hsort]
  have hcardPast : (pastPhysicalFinsetWithTerminal S I).card = pastPredecessorCard S I + 1 := by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  have hb : i.val < (pastPhysicalFinsetWithTerminal S I).sort.length := by
    rw [Finset.length_sort, hcardPast]
    exact i.isLt
  exact List.getElem_append_left hb

theorem cutPastOrderedPhysicalTimes_last (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    cutPastOrderedPhysicalTimes S I (Fin.last (pastPredecessorCard S I)) =
      DenseTime.castOrderEmbedding S := by
  let A := pastPhysicalFinsetWithTerminal S I
  have hcard : A.card = pastPredecessorCard S I + 1 := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  change A.orderEmbOfFin hcard (Fin.last (pastPredecessorCard S I)) = _
  have hi : Fin.last (pastPredecessorCard S I) =
      ⟨pastPredecessorCard S I + 1 - 1,
        Nat.sub_lt (Nat.succ_pos _) Nat.zero_lt_one⟩ := by
    apply Fin.ext
    simp only [Fin.last, Nat.add_sub_cancel_right]
  rw [hi]
  rw [Finset.orderEmbOfFin_last hcard (Nat.succ_pos _)]
  have hS : DenseTime.castOrderEmbedding S ∈ A := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
    exact ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S), rfl⟩
  have hA : A.Nonempty := ⟨DenseTime.castOrderEmbedding S, hS⟩
  apply (Finset.max'_eq_iff (s := A) (H := hA)
    (DenseTime.castOrderEmbedding S)).mpr
  constructor
  · exact hS
  · intro a ha
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    exact DenseTime.castOrderEmbedding.monotone
      (le_terminal_of_mem_pastWithTerminalFinset S I hr)

theorem cutOrderedPhysicalTimes_future_mem (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (i : Fin (positiveFutureFinset S I).card) :
    cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.natAdd (pastPredecessorCard S I + 1) i)) ∈
      positiveFutureAbsolutePhysicalFinset S I := by
  change
    (absolutePhysicalFinsetWithTerminal S I).orderEmbOfFin
      (card_absolutePhysicalFinsetWithTerminal S I)
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.natAdd (pastPredecessorCard S I + 1) i)) ∈ _
  rw [Finset.orderEmbOfFin_apply]
  have hsort : (absolutePhysicalFinsetWithTerminal S I).sort =
      (pastPhysicalFinsetWithTerminal S I).sort ++
        (positiveFutureAbsolutePhysicalFinset S I).sort := by
    rw [absolutePhysicalFinsetWithTerminal_eq_union]
    exact sort_union_eq_append _ _
      (pastPhysical_lt_positiveFutureAbsolutePhysical S I)
  simp only [hsort]
  let k := pastPredecessorCard S I + 1 + i.val
  change
    (((pastPhysicalFinsetWithTerminal S I).sort ++
      (positiveFutureAbsolutePhysicalFinset S I).sort)[k]'(by
          dsimp only [k]
          simp only [List.length_append, Finset.length_sort,
            pastPhysicalFinsetWithTerminal,
            positiveFutureAbsolutePhysicalFinset,
            SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
            DenseTime.addFinset, Finset.card_map, card_pastWithTerminalFinset]
          exact Nat.add_lt_add_left i.isLt _))
      ∈ positiveFutureAbsolutePhysicalFinset S I
  rw [List.getElem_append_right (h₁ := by
    rw [Finset.length_sort, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
    dsimp only [k]
    omega)]
  apply (Finset.mem_sort (r := (· ≤ ·))).mp
  exact List.getElem_mem _

/-- The final block, shifted back by the cut, is exactly the sorted strictly positive relative
future. -/
theorem cutOrderedPhysicalTimes_relativeFinalSegment (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes.relativeFinalSegment
        (cutOrderedPhysicalTimes S I) =
      positiveFutureOrderedPhysicalTimes S I := by
  let F := SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)
  have hcard : F.card = (positiveFutureFinset S I).card := by
    simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map]
  change FiniteOrderedTimes.relativeFinalSegment
      (cutOrderedPhysicalTimes S I) = F.orderEmbOfFin hcard
  apply Finset.orderEmbOfFin_unique' hcard
  intro i
  have hcut : cutOrderedPhysicalTimes S I
      (cutIndexOrderIso (pastPredecessorCard S I)
        (positiveFutureFinset S I).card
        (Fin.castAdd (positiveFutureFinset S I).card
          (Fin.last (pastPredecessorCard S I)))) =
      DenseTime.castOrderEmbedding S := by
    change FiniteOrderedTimes.initialSegment
      (cutOrderedPhysicalTimes S I) (Fin.last (pastPredecessorCard S I)) = _
    rw [cutOrderedPhysicalTimes_initialSegment, cutPastOrderedPhysicalTimes_last]
  have hfut := cutOrderedPhysicalTimes_future_mem S I i
  rw [positiveFutureAbsolutePhysicalFinset,
    SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map] at hfut
  obtain ⟨u, hu, hu_eq⟩ := hfut
  obtain ⟨t, ht, hut⟩ :=
    (DenseTime.mem_addFinset S (positiveFutureFinset S I) u).mp hu
  subst u
  simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
  refine ⟨t, ht, ?_⟩
  rw [FiniteOrderedTimes.relativeFinalSegment_apply,
    hcut, ← hu_eq]
  change DenseTime.castOrderEmbedding t =
    DenseTime.castOrderEmbedding (S + t) - DenseTime.castOrderEmbedding S
  rw [DenseTime.castOrderEmbedding_add, add_tsub_cancel_left]

/-- Position of an augmented-past coordinate in the initial ordered block. -/
def pastCutOrderIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : pastWithTerminalFinset S I) : Fin (pastPredecessorCard S I + 1) :=
  Fin.cast (by
    rw [pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset])
    (((pastPhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
      (DenseTime.physicalSetEquiv (pastWithTerminalFinset S I) r))

/-- Position of a positive relative-future coordinate in the final ordered block. -/
def positiveFutureOrderIndex (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : positiveFutureFinset S I) : Fin (positiveFutureFinset S I).card :=
  Fin.cast (by
    rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map])
    ((((SubMarkovKernelSemigroup.denseTimePhysicalSet
      (positiveFutureFinset S I)).orderIsoOfFin rfl).symm
        (DenseTime.physicalSetEquiv (positiveFutureFinset S I) t)))

@[simp]
theorem cutPastOrderedPhysicalTimes_pastCutOrderIndex
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : pastWithTerminalFinset S I) :
    cutPastOrderedPhysicalTimes S I (pastCutOrderIndex S I r) =
      DenseTime.castOrderEmbedding r := by
  let A := pastPhysicalFinsetWithTerminal S I
  have hcard : A.card = pastPredecessorCard S I + 1 := by
    simp only [A, pastPhysicalFinsetWithTerminal,
      SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
      card_pastWithTerminalFinset]
  change A.orderEmbOfFin hcard
    (Fin.cast hcard ((A.orderIsoOfFin rfl).symm
      (DenseTime.physicalSetEquiv (pastWithTerminalFinset S I) r))) = _
  have hx := congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply
    (DenseTime.physicalSetEquiv (pastWithTerminalFinset S I) r))
  simpa only [Finset.coe_orderIsoOfFin_apply,
    DenseTime.physicalSetEquiv_apply] using! hx

@[simp]
theorem positiveFutureOrderedPhysicalTimes_positiveFutureOrderIndex
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : positiveFutureFinset S I) :
    positiveFutureOrderedPhysicalTimes S I (positiveFutureOrderIndex S I t) =
      DenseTime.castOrderEmbedding t := by
  let F := SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)
  have hcard : F.card = (positiveFutureFinset S I).card := by
    simp only [F, SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map]
  change F.orderEmbOfFin hcard
    (Fin.cast hcard ((F.orderIsoOfFin rfl).symm
      (DenseTime.physicalSetEquiv (positiveFutureFinset S I) t))) = _
  have hx := congrArg Subtype.val ((F.orderIsoOfFin rfl).apply_symm_apply
    (DenseTime.physicalSetEquiv (positiveFutureFinset S I) t))
  simpa only [Finset.coe_orderIsoOfFin_apply,
    DenseTime.physicalSetEquiv_apply] using! hx

/-- Reindex a split ordered path by augmented-past and positive-future dense labels. -/
def orderedSplitToCutCoordinates {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (z : (Fin (pastPredecessorCard S I + 1) → alpha) ×
      (Fin (positiveFutureFinset S I).card → alpha)) :
    (pastWithTerminalFinset S I → alpha) × (positiveFutureFinset S I → alpha) :=
  (fun r ↦ z.1 (pastCutOrderIndex S I r),
    fun t ↦ z.2 (positiveFutureOrderIndex S I t))

theorem measurable_orderedSplitToCutCoordinates {alpha : Type*} [MeasurableSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (orderedSplitToCutCoordinates (alpha := alpha) S I) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro r
    exact (measurable_pi_apply (pastCutOrderIndex S I r)).comp measurable_fst
  · rw [measurable_pi_iff]
    intro t
    exact (measurable_pi_apply (positiveFutureOrderIndex S I t)).comp measurable_snd

/-- A past label as a coordinate of the cut-augmented past set. -/
def pastCutIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : I.toLeft) : pastWithTerminalFinset S I :=
  ⟨r.1.1, (mem_pastWithTerminalFinset S I r).mpr
    (Or.inl ⟨r.1.property, Finset.mem_toLeft.mp r.property⟩)⟩

@[simp]
theorem pastCutIndex_val (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (r : I.toLeft) : (pastCutIndex S I r : DenseTime) = r := rfl

/-- A positive future label is a coordinate of the strict future set; future zero is sent to
`none`, meaning that concatenation should read the terminal past coordinate. -/
def futureCutIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : I.toRight) : Option (positiveFutureFinset S I) :=
  if ht : t.1 = 0 then none else
    some ⟨t, (mem_positiveFutureFinset S I t).mpr
      ⟨Finset.mem_toRight.mp t.property, bot_lt_iff_ne_bot.mpr ht⟩⟩

@[simp]
theorem futureCutIndex_eq_none_iff (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (t : I.toRight) :
    futureCutIndex S I t = none ↔ (t : DenseTime) = 0 := by
  simp only [futureCutIndex]
  split <;> simp_all

variable {alpha : Type*}

/-- Select the augmented-past or strict-future coordinate represented by a mixed label. -/
def cutCoordinateIndex (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) (i : I) :
    pastWithTerminalFinset S I ⊕ positiveFutureFinset S I := by
  cases hi : i.1 with
  | inl r =>
      exact Sum.inl ⟨r, (mem_pastWithTerminalFinset S I r).mpr
        (Or.inl ⟨r.property, by simpa only [hi] using i.property⟩)⟩
  | inr t =>
      if ht : t = 0 then
        exact Sum.inl ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩
      else
        exact Sum.inr ⟨t, (mem_positiveFutureFinset S I t).mpr
          ⟨by simpa only [hi] using i.property, bot_lt_iff_ne_bot.mpr ht⟩⟩

/-- Pull coordinates indexed by the augmented past and the strictly positive relative future
back to the original mixed labels. -/
def pullbackCutCoordinates (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (z : (pastWithTerminalFinset S I → alpha) × (positiveFutureFinset S I → alpha)) :
    I → alpha := fun i ↦ Sum.elim z.1 z.2 (cutCoordinateIndex S I i)

variable [MeasurableSpace alpha]

theorem measurable_pullbackCutCoordinates (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (pullbackCutCoordinates (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro i
  cases h : cutCoordinateIndex S I i with
  | inl r =>
      simpa only [pullbackCutCoordinates, h, Sum.elim_inl] using!
        ((measurable_pi_apply r).comp measurable_fst)
  | inr t =>
      simpa only [pullbackCutCoordinates, h, Sum.elim_inr] using!
        ((measurable_pi_apply t).comp measurable_snd)

/-- Include an original absolute physical coordinate into the cut-augmented set. -/
def includeAbsolutePhysical (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (t : absolutePhysicalFinset S I) : absolutePhysicalFinsetWithTerminal S I :=
  ⟨t, by
    exact (Finset.map_subset_map.mpr Finset.subset_union_left) t.property⟩

/-- Restrict a path on the augmented absolute set to the actually observed absolute set. -/
def restrictAugmentedAbsolute {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinsetWithTerminal S I → alpha) :
    absolutePhysicalFinset S I → alpha :=
  fun t ↦ path (includeAbsolutePhysical S I t)

/-- Read the augmented absolute path as an augmented past and a strictly positive relative
future. -/
def splitAugmentedAbsolute {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinsetWithTerminal S I → alpha) :
    (pastWithTerminalFinset S I → alpha) × (positiveFutureFinset S I → alpha) :=
  (fun r ↦ path ⟨DenseTime.castOrderEmbedding r, by
      rw [absolutePhysicalFinsetWithTerminal,
        SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
      exact ⟨r, (absoluteFinsetWithTerminal_eq S I).symm.le
        (Finset.mem_union_left _ r.property), rfl⟩⟩,
    fun t ↦ path ⟨DenseTime.castOrderEmbedding (S + t), by
      rw [absolutePhysicalFinsetWithTerminal,
        SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.mem_map]
      exact ⟨S + t, (absoluteFinsetWithTerminal_eq S I).symm.le
        (Finset.mem_union_right _ ((DenseTime.mem_addFinset S
          (positiveFutureFinset S I) (S + t)).mpr ⟨t, t.property, rfl⟩)), rfl⟩⟩)

theorem measurable_splitAugmentedAbsolute {alpha : Type*} [MeasurableSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (splitAugmentedAbsolute (alpha := alpha) S I) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro r
    exact measurable_pi_apply _
  · rw [measurable_pi_iff]
    intro t
    exact measurable_pi_apply _

/-- Splitting the canonical ordered augmented path gives its augmented-past coordinates and its
strictly positive relative-future coordinates. -/
theorem orderedSplitToCutCoordinates_splitFinitePath_restrictPath
    {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    orderedSplitToCutCoordinates (alpha := alpha) S I ∘
          SubMarkovKernelSemigroup.splitFinitePath ∘
          FiniteOrderedTimes.restrictPath (cutOrderEmbedding S I) =
      splitAugmentedAbsolute S I ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet
          (absolutePhysicalFinsetWithTerminal S I) := by
  funext path
  apply Prod.ext
  · funext r
    change path _ = path _
    apply congrArg path
    apply (SubMarkovKernelSemigroup.finiteSetTimes
      (absolutePhysicalFinsetWithTerminal S I)).injective
    rw [show
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (cutOrderEmbedding S I
            (cutIndexOrderIso (pastPredecessorCard S I)
              (positiveFutureFinset S I).card
              (Fin.castAdd (positiveFutureFinset S I).card (pastCutOrderIndex S I r)))) =
        cutOrderedPhysicalTimes S I
          (cutIndexOrderIso (pastPredecessorCard S I)
            (positiveFutureFinset S I).card
            (Fin.castAdd (positiveFutureFinset S I).card (pastCutOrderIndex S I r))) by
      rfl]
    change FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) (pastCutOrderIndex S I r) =
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
            ⟨DenseTime.castOrderEmbedding r, _⟩)
    rw [cutOrderedPhysicalTimes_initialSegment,
      cutPastOrderedPhysicalTimes_pastCutOrderIndex]
    change DenseTime.castOrderEmbedding r =
      (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl)
        (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
          ⟨DenseTime.castOrderEmbedding r, _⟩) :
        absolutePhysicalFinsetWithTerminal S I)
    rw [OrderIso.apply_symm_apply]
  · funext t
    change path _ = path _
    apply congrArg path
    apply (SubMarkovKernelSemigroup.finiteSetTimes
      (absolutePhysicalFinsetWithTerminal S I)).injective
    rw [show
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (cutOrderEmbedding S I
            (cutIndexOrderIso (pastPredecessorCard S I)
              (positiveFutureFinset S I).card
              (Fin.natAdd (pastPredecessorCard S I + 1)
                (positiveFutureOrderIndex S I t)))) =
        cutOrderedPhysicalTimes S I
          (cutIndexOrderIso (pastPredecessorCard S I)
            (positiveFutureFinset S I).card
            (Fin.natAdd (pastPredecessorCard S I + 1)
              (positiveFutureOrderIndex S I t))) by
      rfl]
    change cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.natAdd (pastPredecessorCard S I + 1) (positiveFutureOrderIndex S I t))) =
      (SubMarkovKernelSemigroup.finiteSetTimes
        (absolutePhysicalFinsetWithTerminal S I))
          (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
            ⟨DenseTime.castOrderEmbedding (S + t), _⟩)
    have hcut : cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.castAdd (positiveFutureFinset S I).card
            (Fin.last (pastPredecessorCard S I)))) =
        DenseTime.castOrderEmbedding S := by
      change FiniteOrderedTimes.initialSegment
        (cutOrderedPhysicalTimes S I) (Fin.last (pastPredecessorCard S I)) = _
      rw [cutOrderedPhysicalTimes_initialSegment, cutPastOrderedPhysicalTimes_last]
    have hrelative :
        cutOrderedPhysicalTimes S I
            (cutIndexOrderIso (pastPredecessorCard S I)
              (positiveFutureFinset S I).card
              (Fin.natAdd (pastPredecessorCard S I + 1)
                (positiveFutureOrderIndex S I t))) -
          DenseTime.castOrderEmbedding S = DenseTime.castOrderEmbedding t := by
      rw [← hcut,
        ← FiniteOrderedTimes.relativeFinalSegment_apply,
        cutOrderedPhysicalTimes_relativeFinalSegment,
        positiveFutureOrderedPhysicalTimes_positiveFutureOrderIndex]
    have hle : DenseTime.castOrderEmbedding S ≤
        cutOrderedPhysicalTimes S I
          (cutIndexOrderIso (pastPredecessorCard S I)
            (positiveFutureFinset S I).card
            (Fin.natAdd (pastPredecessorCard S I + 1)
              (positiveFutureOrderIndex S I t))) := by
      rw [← hcut]
      apply (cutOrderedPhysicalTimes S I).monotone
      apply (cutIndexOrderIso
        (pastPredecessorCard S I) (positiveFutureFinset S I).card).monotone
      apply Fin.mk_le_mk.mpr
      change pastPredecessorCard S I ≤
        pastPredecessorCard S I + 1 + (positiveFutureOrderIndex S I t).val
      omega
    have habsolute : cutOrderedPhysicalTimes S I
        (cutIndexOrderIso (pastPredecessorCard S I)
          (positiveFutureFinset S I).card
          (Fin.natAdd (pastPredecessorCard S I + 1)
            (positiveFutureOrderIndex S I t))) =
        DenseTime.castOrderEmbedding (S + t) := by
      calc
        _ = DenseTime.castOrderEmbedding t + DenseTime.castOrderEmbedding S :=
          (tsub_eq_iff_eq_add_of_le hle).mp hrelative
        _ = DenseTime.castOrderEmbedding S + DenseTime.castOrderEmbedding t :=
          add_comm _ _
        _ = DenseTime.castOrderEmbedding (S + t) :=
          (DenseTime.castOrderEmbedding_add S t).symm
    rw [habsolute]
    change DenseTime.castOrderEmbedding (S + t) =
      (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl)
        (((absolutePhysicalFinsetWithTerminal S I).orderIsoOfFin rfl).symm
          ⟨DenseTime.castOrderEmbedding (S + t), _⟩) :
        absolutePhysicalFinsetWithTerminal S I)
    rw [OrderIso.apply_symm_apply]

/-- Splitting an augmented absolute path and pulling it back to mixed labels is exactly the
original possibly noninjective absolute-coordinate pullback. -/
theorem pullbackCutCoordinates_splitAugmentedAbsolute {alpha : Type*}
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : absolutePhysicalFinsetWithTerminal S I → alpha) :
    pullbackCutCoordinates S I (splitAugmentedAbsolute S I path) =
      pullbackAbsolutePhysical S I (restrictAugmentedAbsolute S I path) := by
  funext i
  rcases i with ⟨r | t, hi⟩
  · simp only [pullbackCutCoordinates, cutCoordinateIndex, splitAugmentedAbsolute,
      pullbackAbsolutePhysical_apply, restrictAugmentedAbsolute]
    apply congrArg path
    apply Subtype.ext
    change DenseTime.castOrderEmbedding r = DenseTime.castOrderEmbedding r
    rfl
  · by_cases ht : t = 0
    · subst t
      simp only [pullbackCutCoordinates, cutCoordinateIndex, ↓reduceDIte,
        splitAugmentedAbsolute, pullbackAbsolutePhysical_apply, restrictAugmentedAbsolute]
      apply congrArg path
      apply Subtype.ext
      change DenseTime.castOrderEmbedding S = DenseTime.castOrderEmbedding (S + 0)
      rw [add_zero]
    · simp only [pullbackCutCoordinates, cutCoordinateIndex, ht, ↓reduceDIte,
        splitAugmentedAbsolute, pullbackAbsolutePhysical_apply, restrictAugmentedAbsolute]
      apply congrArg path
      apply Subtype.ext
      change DenseTime.castOrderEmbedding (S + t) = DenseTime.castOrderEmbedding (S + t)
      rfl

theorem absolutePhysicalFinset_subset_withTerminal (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    absolutePhysicalFinset S I ⊆ absolutePhysicalFinsetWithTerminal S I := by
  exact Finset.map_subset_map.mpr Finset.subset_union_left

theorem restrictAugmentedAbsolute_eq_restrict₂ {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    restrictAugmentedAbsolute (alpha := alpha) S I =
      Finset.restrict₂ (π := fun _ ↦ alpha)
        (absolutePhysicalFinset_subset_withTerminal S I) := by
  rfl

end
end MixedPastFuture

namespace SubMarkovKernelSemigroup
namespace IsConservative

/-- The mixed marginal may be computed from the cut-augmented finite-set law, split into the
augmented past and strict future.  This is the projective reduction which makes omission of `S`
and duplication at future zero harmless before applying ordered concatenation. -/
theorem finiteSetKernel_map_pullbackAbsolutePhysical_eq_cutAugmented
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P
      (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) =
      (MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P
        (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I)).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.splitAugmentedAbsolute S I) := by
  rw [hP.finiteSetKernel_map_restrict₂ P
    (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I)]
  let K := MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P
    (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I)
  change
    (K.map (Finset.restrict₂ (π := fun _ ↦ alpha)
      (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I))).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) = _
  calc
    (K.map (Finset.restrict₂ (π := fun _ ↦ alpha)
        (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I))).map
          (MixedPastFuture.pullbackAbsolutePhysical S I) =
        K.map (MixedPastFuture.pullbackAbsolutePhysical S I ∘
          Finset.restrict₂ (π := fun _ ↦ alpha)
            (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I)) := by
      exact (ProbabilityTheory.Kernel.map_comp_right K
        (Finset.measurable_restrict₂ (X := fun _ ↦ alpha)
          (MixedPastFuture.absolutePhysicalFinset_subset_withTerminal S I))
        (MixedPastFuture.measurable_pullbackAbsolutePhysical S I)).symm
    _ = K.map (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.splitAugmentedAbsolute S I) := by
      congr 1
      funext path
      exact (MixedPastFuture.pullbackCutCoordinates_splitAugmentedAbsolute S I path).symm

/-- Canonical mixed-cut specialization of finite-time concatenation.  Arbitrary label maps may
omit either side, and mapping a future label to `none` reads the terminal past coordinate. -/
theorem finiteTimeKernel_map_pullbackSplit_cutOrderedPhysicalTimes
    {alpha pastLabel futureLabel : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (pastIndex : pastLabel → Fin (MixedPastFuture.pastPredecessorCard S I + 1))
    (futureIndex : futureLabel →
      Option (Fin (MixedPastFuture.positiveFutureFinset S I).card)) :
    (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
      (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
        (MarkovProcess.SubMarkovKernelSemigroup.pullbackSplitFinitePath
          (alpha := alpha) pastIndex futureIndex ∘
          MarkovProcess.SubMarkovKernelSemigroup.splitFinitePath
            (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I)
            (n := (MixedPastFuture.positiveFutureFinset S I).card)) =
      (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.cutPastOrderedPhysicalTimes S I) ⊗ₖ
        (MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (MarkovProcess.SubMarkovKernelSemigroup.splitPastTerminal
              (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            MarkovProcess.SubMarkovKernelSemigroup.measurable_splitPastTerminal).map
        (MarkovProcess.SubMarkovKernelSemigroup.pullbackSplitFinitePath
          (alpha := alpha) pastIndex futureIndex) := by
  rw [← MixedPastFuture.cutOrderedPhysicalTimes_initialSegment S I,
    ← MixedPastFuture.cutOrderedPhysicalTimes_relativeFinalSegment S I]
  exact hP.finiteTimeKernel_map_pullbackSplitFinitePath P
    (MixedPastFuture.pastPredecessorCard S I)
    (MixedPastFuture.positiveFutureFinset S I).card
    (MixedPastFuture.cutOrderedPhysicalTimes S I) pastIndex futureIndex

end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutCoordinates

section MixedPastFutureCutFactorization

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace SubMarkovKernelSemigroup
namespace IsConservative

/-- A mixed finite marginal factors into its cut-augmented past law and the strict relative-future
law started from the terminal past coordinate. -/
theorem finiteSetKernel_map_pullbackAbsolutePhysical_eq_cutFactorized
    {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (finiteSetKernel P (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) =
      ((finiteTimeKernel P (MixedPastFuture.cutPastOrderedPhysicalTimes S I)) ⊗ₖ
        (finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (splitPastTerminal (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            measurable_splitPastTerminal).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.orderedSplitToCutCoordinates S I) := by
  rw [hP.finiteSetKernel_map_pullbackAbsolutePhysical_eq_cutAugmented P S I,
    finiteSetKernel_eq_map]
  let G := MixedPastFuture.pullbackCutCoordinates (alpha := alpha) S I ∘
    MixedPastFuture.orderedSplitToCutCoordinates S I
  have hG : Measurable G :=
    (MixedPastFuture.measurable_pullbackCutCoordinates S I).comp
      (MixedPastFuture.measurable_orderedSplitToCutCoordinates S I)
  have hsplit : Measurable
      (splitFinitePath (alpha := alpha)
        (m := MixedPastFuture.pastPredecessorCard S I)
        (n := (MixedPastFuture.positiveFutureFinset S I).card)) :=
    measurable_splitFinitePath
  have hreindex : Measurable
      (FiniteOrderedTimes.restrictPath (MixedPastFuture.cutOrderEmbedding S I) :
        (Fin (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I).card → alpha) →
          Fin ((MixedPastFuture.positiveFutureFinset S I).card +
            (MixedPastFuture.pastPredecessorCard S I + 1)) → alpha) :=
    FiniteOrderedTimes.measurable_restrictPath _
  let K := finiteTimeKernel P
    (finiteSetTimes (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))
  calc
    (K.map (orderedPathToFiniteSet
        (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))).map
          (MixedPastFuture.pullbackCutCoordinates S I ∘
            MixedPastFuture.splitAugmentedAbsolute S I) =
        K.map ((MixedPastFuture.pullbackCutCoordinates S I ∘
            MixedPastFuture.splitAugmentedAbsolute S I) ∘
          orderedPathToFiniteSet
            (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I)) := by
      exact (Kernel.map_comp_right K
        (measurable_orderedPathToFiniteSet
          (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))
        ((MixedPastFuture.measurable_pullbackCutCoordinates S I).comp
          (MixedPastFuture.measurable_splitAugmentedAbsolute S I))).symm
    _ = K.map ((G ∘ splitFinitePath) ∘
          FiniteOrderedTimes.restrictPath (MixedPastFuture.cutOrderEmbedding S I)) := by
      congr 1
      funext path
      exact congrArg (MixedPastFuture.pullbackCutCoordinates S I)
        (congrFun
          (MixedPastFuture.orderedSplitToCutCoordinates_splitFinitePath_restrictPath
            (alpha := alpha) S I) path).symm
    _ = (K.map (FiniteOrderedTimes.restrictPath
          (MixedPastFuture.cutOrderEmbedding S I))).map
          (G ∘ splitFinitePath) := by
      exact Kernel.map_comp_right K hreindex (hG.comp hsplit)
    _ = (finiteTimeKernel P (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
          (G ∘ splitFinitePath) := by
      rw [hP.finiteTimeKernel_map_restrictPath P
        (finiteSetTimes (MixedPastFuture.absolutePhysicalFinsetWithTerminal S I))
        (MixedPastFuture.cutOrderEmbedding S I)]
      rfl
    _ = ((finiteTimeKernel P (MixedPastFuture.cutOrderedPhysicalTimes S I)).map
          splitFinitePath).map G := by
      exact Kernel.map_comp_right _ hsplit hG
    _ = ((finiteTimeKernel P
            (FiniteOrderedTimes.initialSegment
              (MixedPastFuture.cutOrderedPhysicalTimes S I))) ⊗ₖ
          (finiteTimeKernel P
            (FiniteOrderedTimes.relativeFinalSegment
              (MixedPastFuture.cutOrderedPhysicalTimes S I))).comap
              (splitPastTerminal (alpha := alpha)
                (m := MixedPastFuture.pastPredecessorCard S I))
              measurable_splitPastTerminal).map G := by
      rw [hP.finiteTimeKernel_map_splitFinitePath P
        (MixedPastFuture.pastPredecessorCard S I)
        (MixedPastFuture.positiveFutureFinset S I).card
        (MixedPastFuture.cutOrderedPhysicalTimes S I)]
    _ = _ := by
      rw [MixedPastFuture.cutOrderedPhysicalTimes_initialSegment,
        MixedPastFuture.cutOrderedPhysicalTimes_relativeFinalSegment]

end IsConservative
end SubMarkovKernelSemigroup

end MixedPastFutureCutFactorization

end MarkovProcess

end PortComputability
