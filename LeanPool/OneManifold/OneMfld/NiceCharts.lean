/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib
import LeanPool.OneManifold.OneMfld.LocallyConnected
import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers

variable
  {M : Type*}
  [TopologicalSpace M]

noncomputable def improved_chart (φ : OpenPartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) :
  { ψ : OpenPartialHomeomorph M NNReal | (x ∈ ψ.source ∧ Bornology.IsBounded ψ.target) } := by

  let y := φ.toFun x

  by_cases h0 : y > 0
  · let interval := Set.Ioo (y-1) (y+1)
    let t := φ.target ∩ interval
    let s := φ.symm '' t
    let sOpen : IsOpen s := by
      apply (OpenPartialHomeomorph.isOpen_symm_image_iff_of_subset_target φ (by exact
        Set.inter_subset_left)).mpr
      exact IsOpen.inter φ.open_target isOpen_Ioo
    let φ' := φ.restrOpen s sOpen

    use φ'
    apply And.intro
    · dsimp [φ']
      simp only [Set.mem_inter_iff]
      apply And.intro
      · exact h
      · dsimp [s]
        simp only [Set.mem_image]
        use y
        apply And.intro
        · apply Set.mem_inter
          · exact PartialEquiv.map_source φ.toPartialEquiv h
          · apply Set.mem_Ioo.mpr
            apply And.intro
            · refine NNReal.coe_lt_coe.mp ?_
              simp only [NNReal.coe_lt_coe, tsub_lt_self_iff, zero_lt_one, and_true]
              exact h0
            · simp only [lt_add_iff_pos_right, zero_lt_one]
        · exact OpenPartialHomeomorph.left_inv φ h
    · have bi : Bornology.IsBounded interval := Metric.isBounded_Ioo (y - 1) (y + 1)
      apply Bornology.IsBounded.subset bi
      intro z hz
      have hz' : z ∈ φ.target ∩ ↑φ.symm ⁻¹' (↑φ.symm '' t) := hz
      rw [restrOpen_symm_image_target φ (t := t) Set.inter_subset_left] at hz'
      exact Set.mem_of_mem_inter_right hz'

  · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h0
    let interval := Set.Iio (1 : NNReal)
    let t := φ.target ∩ interval
    let s := φ.symm '' t
    let sOpen : IsOpen s := by
      apply (OpenPartialHomeomorph.isOpen_symm_image_iff_of_subset_target φ (by exact
        Set.inter_subset_left)).mpr
      exact IsOpen.inter φ.open_target isOpen_Iio
    let φ' := φ.restrOpen s sOpen

    use φ'
    apply And.intro
    · dsimp [φ']
      simp only [Set.mem_inter_iff]
      apply And.intro
      · exact h
      · dsimp [s]
        simp only [Set.mem_image]
        use y
        apply And.intro
        · apply Set.mem_inter
          · exact PartialEquiv.map_source φ.toPartialEquiv h
          · exact Set.mem_Iio.mpr (by
                                     rw [h0]
                                     exact zero_lt_one' NNReal)
        · exact OpenPartialHomeomorph.left_inv φ h
    · have bi : Bornology.IsBounded interval := by
        have : interval = Set.Ico 0 1 := by
          dsimp [interval]
          ext z
          simp only [Set.mem_Iio, Set.mem_Ico, zero_le, true_and]
        rw [this]
        exact Metric.isBounded_Ico 0 1
      apply Bornology.IsBounded.subset bi
      intro z hz
      have hz' : z ∈ φ.target ∩ ↑φ.symm ⁻¹' (↑φ.symm '' t) := hz
      rw [restrOpen_symm_image_target φ (t := t) Set.inter_subset_left] at hz'
      exact Set.mem_of_mem_inter_right hz'

noncomputable def improved_chart' (φ : OpenPartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) (bounded : Bornology.IsBounded φ.target) :
  { ψ : OpenPartialHomeomorph M NNReal | x ∈ ψ.source ∧ Bornology.IsBounded ψ.target ∧ ConnectedSpace ψ.target } := by

  let y := φ.toFun x

  let t := connectedComponentIn φ.target y
  let s := φ.symm '' t

  let sOpen : IsOpen s := by
    apply OpenPartialHomeomorph.isOpen_image_symm_of_subset_target φ
    apply IsOpen.connectedComponentIn
    · exact φ.open_target
    · exact connectedComponentIn_subset φ.target y

  let ψ := φ.restrOpen s sOpen
  use ψ

  apply And.intro
  · dsimp [ψ]
    simp only [Set.mem_inter_iff]
    apply And.intro
    · exact h
    · dsimp [s]
      simp only [Set.mem_image]
      use y
      apply And.intro
      · apply mem_connectedComponentIn
        exact PartialEquiv.map_source φ.toPartialEquiv h
      · exact OpenPartialHomeomorph.left_inv φ h
  · apply And.intro
    · have : ψ.target ⊆ φ.target := by
        intro z hz
        exact Set.mem_of_mem_inter_left hz
      exact Bornology.IsBounded.subset bounded this
    · dsimp [ψ]
      apply isConnected_iff_connectedSpace.mp
      dsimp [s]
      have : (φ.target ∩ ↑φ.symm ⁻¹' (↑φ.symm '' t)) = t :=
        restrOpen_symm_image_target φ (t := t) (connectedComponentIn_subset φ.target y)
      rw [this]
      apply isConnected_connectedComponentIn_iff.mpr
      exact PartialEquiv.map_source φ.toPartialEquiv h

noncomputable def nice_chart (φ : OpenPartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) :
  { ψ : OpenPartialHomeomorph M NNReal | x ∈ ψ.source ∧ Bornology.IsBounded ψ.target ∧ ConnectedSpace ψ.target } := by
  rcases (improved_chart φ x h) with ⟨ φ', h1, h2 ⟩
  rcases (improved_chart' φ' x h1 h2) with ⟨ φ'', h1, h2, h3 ⟩
  use φ''
  simp only [Set.mem_ofPred_eq]
  exact ⟨ h1, ⟨ h2, h3 ⟩ ⟩

lemma nice_chart_source {φ : OpenPartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  x ∈ (nice_chart φ x h).1.source := by
    let c := nice_chart φ x h
    have : c = nice_chart φ x h := rfl
    rw [←this]
    exact c.2.1

lemma nice_chart_bounded {φ : OpenPartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  Bornology.IsBounded (nice_chart φ x h).1.target := by
    let c := nice_chart φ x h
    have : c = nice_chart φ x h := rfl
    rw [←this]
    exact c.2.2.1

lemma nice_chart_connected {φ : OpenPartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  ConnectedSpace (nice_chart φ x h).1.target := by
    let c := nice_chart φ x h
    have : c = nice_chart φ x h := rfl
    rw [←this]
    exact c.2.2.2

structure NiceChartAt (x : M) where
  chart : OpenPartialHomeomorph M NNReal
  mem_chart_source : x ∈ chart.source
  bounded : Bornology.IsBounded chart.target
  connected : ConnectedSpace chart.target

class NicelyChartedSpace (H : Type*) [TopologicalSpace H] [Bornology H] (M : Type*) [TopologicalSpace M] extends ChartedSpace H M where
    is_bounded (φ : OpenPartialHomeomorph M H) (h : φ ∈ atlas) : Bornology.IsBounded φ.target
    is_connected (φ : OpenPartialHomeomorph M H) (h : φ ∈ atlas) : ConnectedSpace φ.target

@[instance_reducible] noncomputable def nicely_charted (ht : ChartedSpace NNReal M) : NicelyChartedSpace NNReal M where
  chartAt := by
    intro x
    let c := ht.chartAt x
    let c' := nice_chart (ht.chartAt x) x (ht.mem_chart_source x)
    exact c'.1
  atlas := let f x := (nice_chart (ht.chartAt x) x (ht.mem_chart_source x)).1
    Set.image f (Set.univ : Set M)
  mem_chart_source (x : M) := by
    simp only [Set.mem_ofPred_eq]
    exact nice_chart_source
  chart_mem_atlas (x : M) := by
    simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range, exists_apply_eq_apply]
  is_bounded (φ : OpenPartialHomeomorph M NNReal) := by
    intro h
    dsimp [atlas] at h
    simp at h
    rcases h with ⟨ y, hy ⟩
    rw [←hy]
    apply nice_chart_bounded
  is_connected (φ : OpenPartialHomeomorph M NNReal) := by
    intro h
    dsimp [atlas] at h
    simp at h
    rcases h with ⟨ y, hy ⟩
    rw [←hy]
    apply nice_chart_connected
