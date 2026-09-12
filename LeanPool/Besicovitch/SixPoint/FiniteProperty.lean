/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Score

/-!
# The finite six-point property

This file states the compactified finite property and removes zero-radius labels from strict
witnesses.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- Every admissible configuration at `s` has a compactified packing of nonnegative score. -/
def SixPointFiniteProperty (s : ℝ) : Prop :=
  ∀ configuration : SixPointConfiguration, configuration.IsAdmissibleAt s →
    ∃ packing : SixPointPacking configuration, 0 ≤ packing.score s

namespace SixPointPacking

variable {configuration : SixPointConfiguration} (packing : SixPointPacking configuration)

/-- A packing is genuine when every radius on its support is positive. -/
def HasPositiveRadii : Prop :=
  ∀ i : packing.support, 0 < (packing.radius i : ℝ)

/-- The labels carrying positive radius in a compactified packing. -/
def positiveSupport : Finset SixPointIndex :=
  packing.support.filter fun index ↦
    ∃ hindex : index ∈ packing.support, 0 < (packing.radius ⟨index, hindex⟩ : ℝ)

/-- Membership in the positive support is exactly positivity of the corresponding radius. -/
theorem mem_positiveSupport_iff {index : SixPointIndex} :
    index ∈ packing.positiveSupport ↔
      ∃ hindex : index ∈ packing.support, 0 < (packing.radius ⟨index, hindex⟩ : ℝ) := by
  rw [positiveSupport, Finset.mem_filter]
  constructor
  · exact And.right
  · rintro ⟨hindex, hpositive⟩
    exact ⟨hindex, hindex, hpositive⟩

/-- The positive support is contained in the compactified support. -/
theorem positiveSupport_subset : packing.positiveSupport ⊆ packing.support := by
  exact Finset.filter_subset _ _

private def positiveRestriction
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport) :
    SixPointPacking configuration where
  support := packing.positiveSupport
  meets_color := hmeets
  radius i := packing.radius ⟨i, packing.positiveSupport_subset i.2⟩
  same_color_disjoint i j hij hcolor := by
    apply packing.same_color_disjoint
    · intro h
      apply hij
      apply Subtype.ext
      exact congrArg (fun x : packing.support ↦ (x : SixPointIndex)) h
    · exact hcolor

private theorem positiveRestriction_hasPositiveRadii
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport) :
    (packing.positiveRestriction hmeets).HasPositiveRadii := by
  intro i
  exact (packing.mem_positiveSupport_iff.1 i.2).choose_spec

private theorem positiveRestriction_radius_le {cap : ℝ}
    (hcap : ∀ i : packing.support, (packing.radius i : ℝ) ≤ cap)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport) :
    ∀ i : (packing.positiveRestriction hmeets).support,
      ((packing.positiveRestriction hmeets).radius i : ℝ) ≤ cap := by
  intro i
  exact hcap ⟨i, packing.positiveSupport_subset i.2⟩

private theorem positiveRestriction_totalRadius
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport) :
    (packing.positiveRestriction hmeets).totalRadius = packing.totalRadius := by
  change (∑ i ∈ packing.positiveSupport.attach,
      (packing.radius ⟨i, packing.positiveSupport_subset i.2⟩ : ℝ)) =
    ∑ i ∈ packing.support.attach, (packing.radius i : ℝ)
  calc
    _ = ∑ i ∈ packing.support.attach.filter fun i ↦ 0 < (packing.radius i : ℝ),
          (packing.radius i : ℝ) := by
      refine Finset.sum_bij (fun i _ ↦ ⟨i, packing.positiveSupport_subset i.2⟩) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_filter.2
          ⟨Finset.mem_attach _ _, (packing.mem_positiveSupport_iff.1 i.2).choose_spec⟩
      · intro i₁ hi₁ i₂ hi₂ heq
        apply Subtype.ext
        exact congrArg (fun x : packing.support ↦ (x : SixPointIndex)) heq
      · intro j hj
        refine ⟨⟨j, packing.mem_positiveSupport_iff.2 ⟨j.2, (Finset.mem_filter.1 hj).2⟩⟩,
          Finset.mem_attach _ _, ?_⟩
        rfl
      · intro i hi
        rfl
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      apply le_antisymm
      · exact not_lt.mp fun hpositive ↦ hnot (Finset.mem_filter.2 ⟨hi, hpositive⟩)
      · exact (packing.radius i).property.1

private theorem positiveRestriction_virtualDiameter_le
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport) :
    (packing.positiveRestriction hmeets).virtualDiameter ≤ packing.virtualDiameter := by
  unfold virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  exact packing.pair_le_virtualDiameter
    ⟨i, packing.positiveSupport_subset i.2⟩ ⟨j, packing.positiveSupport_subset j.2⟩

private theorem score_le_positiveRestriction {beta : ℝ} (hbeta : 0 < beta)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport) :
    packing.score beta ≤ (packing.positiveRestriction hmeets).score beta := by
  simp only [score]
  rw [packing.positiveRestriction_totalRadius hmeets]
  gcongr
  exact packing.positiveRestriction_virtualDiameter_le hmeets

private def radiusValue (index : SixPointIndex) : ℝ :=
  if hindex : index ∈ packing.support then packing.radius ⟨index, hindex⟩ else 0

private theorem radiusValue_nonneg (index : SixPointIndex) : 0 ≤ packing.radiusValue index := by
  rw [radiusValue]
  split_ifs with hindex
  · exact (packing.radius ⟨index, hindex⟩).property.1
  · exact le_rfl

private theorem totalRadius_eq_sum_radiusValue :
    packing.totalRadius = ∑ index ∈ packing.support, packing.radiusValue index := by
  rw [totalRadius]
  calc
    _ = ∑ i ∈ packing.support.attach, packing.radiusValue i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [radiusValue, i.2, dite_true]
    _ = _ := Finset.sum_attach _ _

private theorem totalRadius_eq_sum_positiveSupport :
    packing.totalRadius = ∑ index ∈ packing.positiveSupport, packing.radiusValue index := by
  rw [packing.totalRadius_eq_sum_radiusValue]
  symm
  apply Finset.sum_subset packing.positiveSupport_subset
  intro index hindex hpositive
  simp only [radiusValue, hindex, dite_true]
  apply le_antisymm
  · apply not_lt.mp
    intro hradius
    exact hpositive (packing.mem_positiveSupport_iff.2 ⟨hindex, hradius⟩)
  · exact (packing.radius ⟨index, hindex⟩).property.1

private def addIsolated (index : SixPointIndex)
    (habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index})
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    SixPointPacking configuration where
  support := packing.positiveSupport ∪ {index}
  meets_color := hmeets
  radius i := if hpositive : (i : SixPointIndex) ∈ packing.positiveSupport then
    packing.radius ⟨i, packing.positiveSupport_subset hpositive⟩
  else ⟨epsilon, hepsilon.le, hepsilon_one⟩
  same_color_disjoint i j hij hcolor := by
    classical
    by_cases hi : (i : SixPointIndex) ∈ packing.positiveSupport
    · by_cases hj : (j : SixPointIndex) ∈ packing.positiveSupport
      · simp only [hi, hj, dite_true]
        apply packing.same_color_disjoint
        · intro h
          apply hij
          apply Subtype.ext
          exact congrArg (fun x : packing.support ↦ (x : SixPointIndex)) h
        · exact hcolor
      · have hjindex : (j : SixPointIndex) = index :=
          Finset.mem_singleton.1 ((Finset.mem_union.1 j.2).resolve_left hj)
        exact (habsent i hi (hcolor.trans (congrArg Prod.fst hjindex))).elim
    · by_cases hj : (j : SixPointIndex) ∈ packing.positiveSupport
      · have hiindex : (i : SixPointIndex) = index :=
          Finset.mem_singleton.1 ((Finset.mem_union.1 i.2).resolve_left hi)
        exact (habsent j hj (hcolor.symm.trans (congrArg Prod.fst hiindex))).elim
      · have hiindex : (i : SixPointIndex) = index :=
          Finset.mem_singleton.1 ((Finset.mem_union.1 i.2).resolve_left hi)
        have hjindex : (j : SixPointIndex) = index :=
          Finset.mem_singleton.1 ((Finset.mem_union.1 j.2).resolve_left hj)
        exact (hij (Subtype.ext (hiindex.trans hjindex.symm))).elim

private theorem addIsolated_hasPositiveRadii (index : SixPointIndex)
    (habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index})
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).HasPositiveRadii := by
  intro i
  simp only [addIsolated]
  split_ifs with hpositive
  · exact (packing.mem_positiveSupport_iff.1 hpositive).choose_spec
  · exact hepsilon

private theorem addIsolated_radius_le (index : SixPointIndex)
    (habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index})
    {epsilon cap : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hepsilon_cap : epsilon ≤ cap)
    (hcap : ∀ i : packing.support, (packing.radius i : ℝ) ≤ cap) :
    ∀ i : (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).support,
      ((packing.addIsolated index habsent hmeets hepsilon hepsilon_one).radius i : ℝ) ≤
        cap := by
  intro i
  simp only [addIsolated]
  split_ifs with hpositive
  · exact hcap ⟨i, packing.positiveSupport_subset hpositive⟩
  · exact hepsilon_cap

private theorem totalRadius_le_addIsolated (index : SixPointIndex)
    (habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index})
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    packing.totalRadius ≤
      (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).totalRadius := by
  rw [packing.totalRadius_eq_sum_positiveSupport,
    (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).totalRadius_eq_sum_radiusValue]
  calc
    ∑ i ∈ packing.positiveSupport, packing.radiusValue i =
        ∑ i ∈ packing.positiveSupport,
          (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).radiusValue i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [radiusValue, packing.positiveSupport_subset hi, dite_true]
      have hi' : i ∈ (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).support :=
        Finset.mem_union_left _ hi
      rw [dif_pos hi']
      simp only [addIsolated, hi, dite_true]
    _ ≤ ∑ i ∈ (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).support,
          (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).radiusValue i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro i hi hpositive
      exact (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).radiusValue_nonneg i

private theorem addIsolated_virtualDiameter_le (index : SixPointIndex)
    (hindex : index ∈ packing.support)
    (habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1)
    (hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index})
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    (packing.addIsolated index habsent hmeets hepsilon hepsilon_one).virtualDiameter ≤
      packing.virtualDiameter + 2 * epsilon := by
  let completed := packing.addIsolated index habsent hmeets hepsilon hepsilon_one
  have old_mem (i : completed.support) : (i : SixPointIndex) ∈ packing.support := by
    rcases Finset.mem_union.1 i.2 with hpositive | hi
    · exact packing.positiveSupport_subset hpositive
    · have hi' : (i : SixPointIndex) = index := by
        simpa only [Finset.mem_singleton] using hi
      exact hi' ▸ hindex
  have radius_le (i : completed.support) :
      (completed.radius i : ℝ) ≤ packing.radius ⟨i, old_mem i⟩ + epsilon := by
    dsimp only [completed, addIsolated]
    split_ifs with hpositive
    · exact le_add_of_nonneg_right hepsilon.le
    · exact le_add_of_nonneg_left (packing.radius ⟨i, old_mem i⟩).property.1
  change completed.virtualDiameter ≤ packing.virtualDiameter + 2 * epsilon
  unfold virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  calc
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          completed.radius i + completed.radius j ≤
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          (packing.radius ⟨i, old_mem i⟩ + epsilon) +
            (packing.radius ⟨j, old_mem j⟩ + epsilon) :=
      add_le_add (add_le_add le_rfl (radius_le i)) (radius_le j)
    _ = (dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius ⟨i, old_mem i⟩ + packing.radius ⟨j, old_mem j⟩) +
            2 * epsilon := by ring
    _ ≤ packing.virtualDiameter + 2 * epsilon :=
      add_le_add_left
        (packing.pair_le_virtualDiameter ⟨i, old_mem i⟩ ⟨j, old_mem j⟩) (2 * epsilon)

private theorem score_sub_error_le (packing' : SixPointPacking configuration) {beta epsilon : ℝ}
    (hbeta : 0 < beta) (htotal : packing.totalRadius ≤ packing'.totalRadius)
    (hvirtual : packing'.virtualDiameter ≤ packing.virtualDiameter + 2 * epsilon) :
    packing.score beta - epsilon / beta ≤ packing'.score beta := by
  simp only [score]
  calc
    packing.totalRadius - packing.virtualDiameter / (2 * beta) - epsilon / beta =
        packing.totalRadius - (packing.virtualDiameter + 2 * epsilon) / (2 * beta) := by
      field_simp
      ring
    _ ≤ packing'.totalRadius - packing'.virtualDiameter / (2 * beta) :=
      sub_le_sub htotal ((div_le_div_iff_of_pos_right (by positivity : 0 < 2 * beta)).2 hvirtual)

private def twoIsolated (_packing : SixPointPacking configuration)
    (redLabel blueLabel : SixPointLabel) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) : SixPointPacking configuration where
  support := {(.red, redLabel), (.blue, blueLabel)}
  meets_color color := by
    cases color
    · exact ⟨redLabel, by simp⟩
    · exact ⟨blueLabel, by simp⟩
  radius _ := ⟨epsilon, hepsilon.le, hepsilon_one⟩
  same_color_disjoint i j hij hcolor := by
    have hi := i.2
    have hj := j.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi
    · rcases hj with hj | hj
      · exact (hij (Subtype.ext (hi.trans hj.symm))).elim
      · simp [hi, hj] at hcolor
    · rcases hj with hj | hj
      · simp [hi, hj] at hcolor
      · exact (hij (Subtype.ext (hi.trans hj.symm))).elim

private theorem twoIsolated_hasPositiveRadii (redLabel blueLabel : SixPointLabel)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    (packing.twoIsolated redLabel blueLabel hepsilon hepsilon_one).HasPositiveRadii := by
  intro i
  exact hepsilon

private theorem twoIsolated_radius_le (redLabel blueLabel : SixPointLabel)
    {epsilon cap : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hepsilon_cap : epsilon ≤ cap) :
    ∀ i : (packing.twoIsolated redLabel blueLabel hepsilon hepsilon_one).support,
      ((packing.twoIsolated redLabel blueLabel hepsilon hepsilon_one).radius i : ℝ) ≤ cap := by
  intro i
  exact hepsilon_cap

private theorem twoIsolated_virtualDiameter_le (redLabel blueLabel : SixPointLabel)
    (hred : (.red, redLabel) ∈ packing.support) (hblue : (.blue, blueLabel) ∈ packing.support)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) :
    (packing.twoIsolated redLabel blueLabel hepsilon hepsilon_one).virtualDiameter ≤
      packing.virtualDiameter + 2 * epsilon := by
  let completed := packing.twoIsolated redLabel blueLabel hepsilon hepsilon_one
  have old_mem (i : completed.support) : (i : SixPointIndex) ∈ packing.support := by
    have hi := i.2
    dsimp only [completed, twoIsolated] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact hi ▸ hred
    · exact hi ▸ hblue
  have radius_le (i : completed.support) :
      (completed.radius i : ℝ) ≤ packing.radius ⟨i, old_mem i⟩ + epsilon := by
    dsimp only [completed, twoIsolated]
    exact le_add_of_nonneg_left (packing.radius ⟨i, old_mem i⟩).property.1
  change completed.virtualDiameter ≤ packing.virtualDiameter + 2 * epsilon
  unfold virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  calc
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          completed.radius i + completed.radius j ≤
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          (packing.radius ⟨i, old_mem i⟩ + epsilon) +
            (packing.radius ⟨j, old_mem j⟩ + epsilon) :=
      add_le_add (add_le_add le_rfl (radius_le i)) (radius_le j)
    _ = (dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius ⟨i, old_mem i⟩ + packing.radius ⟨j, old_mem j⟩) +
            2 * epsilon := by ring
    _ ≤ packing.virtualDiameter + 2 * epsilon :=
      add_le_add_left
        (packing.pair_le_virtualDiameter ⟨i, old_mem i⟩ ⟨j, old_mem j⟩) (2 * epsilon)

private theorem exists_cleanup_of_both_colors {beta cap a : ℝ} (hbeta : 0 < beta)
    (hcap : ∀ i : packing.support, (packing.radius i : ℝ) ≤ cap)
    (hscore : a < packing.score beta)
    (hred : ∃ label, (.red, label) ∈ packing.positiveSupport)
    (hblue : ∃ label, (.blue, label) ∈ packing.positiveSupport) :
    ∃ packing' : SixPointPacking configuration, packing'.HasPositiveRadii ∧
      (∀ i : packing'.support, (packing'.radius i : ℝ) ≤ cap) ∧
      a < packing'.score beta := by
  have hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport := by
    intro color
    cases color
    · exact hred
    · exact hblue
  let packing' := packing.positiveRestriction hmeets
  refine ⟨packing', packing.positiveRestriction_hasPositiveRadii hmeets,
    packing.positiveRestriction_radius_le hcap hmeets, ?_⟩
  exact hscore.trans_le (packing.score_le_positiveRestriction hbeta hmeets)

private theorem exists_cleanup_of_red_only {beta cap a epsilon : ℝ} (hbeta : 0 < beta)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) (hepsilon_cap : epsilon ≤ cap)
    (hcap : ∀ i : packing.support, (packing.radius i : ℝ) ≤ cap)
    (hstrict : a < packing.score beta - epsilon / beta)
    (hred : ∃ label, (.red, label) ∈ packing.positiveSupport)
    (hblue : ¬ ∃ label, (.blue, label) ∈ packing.positiveSupport) :
    ∃ packing' : SixPointPacking configuration, packing'.HasPositiveRadii ∧
      (∀ i : packing'.support, (packing'.radius i : ℝ) ≤ cap) ∧
      a < packing'.score beta := by
  obtain ⟨blueLabel, hblueLabel⟩ := packing.meets_color .blue
  let index : SixPointIndex := (.blue, blueLabel)
  have habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1 := by
    rintro ⟨color, label⟩ hi hcolor
    apply hblue
    dsimp only [index] at hcolor
    subst color
    exact ⟨label, hi⟩
  have hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index} := by
    intro color
    cases color
    · obtain ⟨label, hlabel⟩ := hred
      exact ⟨label, Finset.mem_union_left _ hlabel⟩
    · exact ⟨blueLabel, Finset.mem_union_right _ (Finset.mem_singleton_self index)⟩
  let packing' := packing.addIsolated index habsent hmeets hepsilon hepsilon_one
  refine ⟨packing', packing.addIsolated_hasPositiveRadii index habsent hmeets hepsilon
    hepsilon_one, packing.addIsolated_radius_le index habsent hmeets hepsilon hepsilon_one
    hepsilon_cap hcap, ?_⟩
  apply hstrict.trans_le
  exact packing.score_sub_error_le packing' hbeta
    (packing.totalRadius_le_addIsolated index habsent hmeets hepsilon hepsilon_one)
    (packing.addIsolated_virtualDiameter_le index hblueLabel habsent hmeets hepsilon hepsilon_one)

private theorem exists_cleanup_of_blue_only {beta cap a epsilon : ℝ} (hbeta : 0 < beta)
    (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1) (hepsilon_cap : epsilon ≤ cap)
    (hcap : ∀ i : packing.support, (packing.radius i : ℝ) ≤ cap)
    (hstrict : a < packing.score beta - epsilon / beta)
    (hred : ¬ ∃ label, (.red, label) ∈ packing.positiveSupport)
    (hblue : ∃ label, (.blue, label) ∈ packing.positiveSupport) :
    ∃ packing' : SixPointPacking configuration, packing'.HasPositiveRadii ∧
      (∀ i : packing'.support, (packing'.radius i : ℝ) ≤ cap) ∧
      a < packing'.score beta := by
  obtain ⟨redLabel, hredLabel⟩ := packing.meets_color .red
  let index : SixPointIndex := (.red, redLabel)
  have habsent : ∀ i ∈ packing.positiveSupport, i.1 ≠ index.1 := by
    rintro ⟨color, label⟩ hi hcolor
    apply hred
    dsimp only [index] at hcolor
    subst color
    exact ⟨label, hi⟩
  have hmeets : ∀ color, ∃ label, (color, label) ∈ packing.positiveSupport ∪ {index} := by
    intro color
    cases color
    · exact ⟨redLabel, Finset.mem_union_right _ (Finset.mem_singleton_self index)⟩
    · obtain ⟨label, hlabel⟩ := hblue
      exact ⟨label, Finset.mem_union_left _ hlabel⟩
  let packing' := packing.addIsolated index habsent hmeets hepsilon hepsilon_one
  refine ⟨packing', packing.addIsolated_hasPositiveRadii index habsent hmeets hepsilon
    hepsilon_one, packing.addIsolated_radius_le index habsent hmeets hepsilon hepsilon_one
    hepsilon_cap hcap, ?_⟩
  apply hstrict.trans_le
  exact packing.score_sub_error_le packing' hbeta
    (packing.totalRadius_le_addIsolated index habsent hmeets hepsilon hepsilon_one)
    (packing.addIsolated_virtualDiameter_le index hredLabel habsent hmeets hepsilon hepsilon_one)

private theorem exists_cleanup_of_no_positive_radii {beta cap a epsilon : ℝ}
    (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hepsilon_cap : epsilon ≤ cap) (hstrict : a < packing.score beta - epsilon / beta)
    (hred : ¬ ∃ label, (.red, label) ∈ packing.positiveSupport)
    (hblue : ¬ ∃ label, (.blue, label) ∈ packing.positiveSupport) :
    ∃ packing' : SixPointPacking configuration, packing'.HasPositiveRadii ∧
      (∀ i : packing'.support, (packing'.radius i : ℝ) ≤ cap) ∧
      a < packing'.score beta := by
  obtain ⟨redLabel, hredLabel⟩ := packing.meets_color .red
  obtain ⟨blueLabel, hblueLabel⟩ := packing.meets_color .blue
  have hpositive_empty : packing.positiveSupport = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.1
    rintro ⟨⟨color, label⟩, hlabel⟩
    cases color
    · exact hred ⟨label, hlabel⟩
    · exact hblue ⟨label, hlabel⟩
  have htotal_zero : packing.totalRadius = 0 := by
    rw [packing.totalRadius_eq_sum_positiveSupport, hpositive_empty]
    simp
  let packing' := packing.twoIsolated redLabel blueLabel hepsilon hepsilon_one
  refine ⟨packing', packing.twoIsolated_hasPositiveRadii redLabel blueLabel hepsilon
    hepsilon_one, packing.twoIsolated_radius_le redLabel blueLabel hepsilon hepsilon_one
    hepsilon_cap, ?_⟩
  apply hstrict.trans_le
  apply packing.score_sub_error_le packing' hbeta
  · rw [htotal_zero]
    exact packing'.totalRadius_nonneg
  · exact packing.twoIsolated_virtualDiameter_le redLabel blueLabel hredLabel hblueLabel
      hepsilon hepsilon_one

/-- A strict compactified score has a genuine witness below the same positive radius cap. -/
theorem exists_positiveRadii_score_gt {beta cap a : ℝ} (hbeta : 0 < beta)
    (hcap_pos : 0 < cap) (hcap_one : cap ≤ 1)
    (hcap : ∀ i : packing.support, (packing.radius i : ℝ) ≤ cap)
    (hscore : a < packing.score beta) :
    ∃ packing' : SixPointPacking configuration, packing'.HasPositiveRadii ∧
      (∀ i : packing'.support, (packing'.radius i : ℝ) ≤ cap) ∧
      a < packing'.score beta := by
  let epsilon := min cap (beta * (packing.score beta - a) / 2)
  have hgap : 0 < packing.score beta - a := sub_pos.mpr hscore
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    rw [lt_min_iff]
    exact ⟨hcap_pos, div_pos (mul_pos hbeta hgap) (by norm_num)⟩
  have hepsilon_cap : epsilon ≤ cap := by
    dsimp only [epsilon]
    exact min_le_left _ _
  have hepsilon_one : epsilon ≤ 1 := hepsilon_cap.trans hcap_one
  have herror : epsilon / beta < packing.score beta - a := by
    apply (div_lt_iff₀ hbeta).2
    have hepsilon_gain := min_le_right cap (beta * (packing.score beta - a) / 2)
    nlinarith [mul_pos hbeta hgap]
  have hstrict : a < packing.score beta - epsilon / beta := by linarith
  by_cases hred : ∃ label, (.red, label) ∈ packing.positiveSupport
  · by_cases hblue : ∃ label, (.blue, label) ∈ packing.positiveSupport
    · exact packing.exists_cleanup_of_both_colors hbeta hcap hscore hred hblue
    · exact packing.exists_cleanup_of_red_only hbeta hepsilon hepsilon_one hepsilon_cap
        hcap hstrict hred hblue
  · by_cases hblue : ∃ label, (.blue, label) ∈ packing.positiveSupport
    · exact packing.exists_cleanup_of_blue_only hbeta hepsilon hepsilon_one hepsilon_cap
        hcap hstrict hred hblue
    · exact packing.exists_cleanup_of_no_positive_radii hbeta hepsilon hepsilon_one
        hepsilon_cap hstrict hred hblue

end SixPointPacking

end LeanPool.Besicovitch
