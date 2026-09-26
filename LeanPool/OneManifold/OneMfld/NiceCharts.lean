/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.LocallyConnected
public import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers


/-!
# NiceCharts

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

variable
  {M : Type*}
  [TopologicalSpace M]

/-- Restrict a chart around the specified point to a bounded target. -/
noncomputable def improvedChart (φ : OpenPartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) :
  { ψ : OpenPartialHomeomorph M NNReal | (x ∈ ψ.source ∧ Bornology.IsBounded ψ.target) } := by
  let y := φ x
  let t := φ.target ∩ Set.Iio (y + 1)
  let s := φ.symm '' t
  have sOpen : IsOpen s :=
    (φ.isOpen_symm_image_iff_of_subset_target Set.inter_subset_left).mpr
      (φ.open_target.inter isOpen_Iio)
  refine ⟨φ.restrOpen s sOpen, ?_, ?_⟩
  · exact ⟨h, ⟨y, ⟨φ.map_source h, lt_add_one y⟩, φ.left_inv h⟩⟩
  · apply (Metric.isBounded_Ico (0 : NNReal) (y + 1)).subset
    intro z hz
    have hz' : z ∈ φ.target ∩ ↑φ.symm ⁻¹' (↑φ.symm '' t) := hz
    rw [restrOpen_symm_image_target φ (t := t) Set.inter_subset_left] at hz'
    exact ⟨zero_le, hz'.2⟩

/-- Restrict a bounded chart to the connected component containing the specified point. -/
noncomputable def improvedChart' (φ : OpenPartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source)
    (bounded : Bornology.IsBounded φ.target) :
  { ψ : OpenPartialHomeomorph M NNReal | x ∈ ψ.source ∧ Bornology.IsBounded ψ.target ∧
      ConnectedSpace ψ.target } := by
  let y := φ.toFun x
  let t := connectedComponentIn φ.target y
  let s := φ.symm '' t
  let sOpen : IsOpen s := by
    apply OpenPartialHomeomorph.isOpen_image_symm_of_subset_target φ
    · apply IsOpen.connectedComponentIn
      exact φ.open_target
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

/-- Choose a chart around the specified point with a bounded connected target. -/
noncomputable def niceChart (φ : OpenPartialHomeomorph M NNReal) (x : M) (h : x ∈ φ.source) :
  { ψ : OpenPartialHomeomorph M NNReal | x ∈ ψ.source ∧ Bornology.IsBounded ψ.target ∧
      ConnectedSpace ψ.target } := by
  rcases (improvedChart φ x h) with ⟨ φ', h1, h2 ⟩
  rcases (improvedChart' φ' x h1 h2) with ⟨ φ'', h1, h2, h3 ⟩
  use φ''
  simp only [Set.mem_ofPred_eq]
  exact ⟨ h1, ⟨ h2, h3 ⟩ ⟩

lemma nice_chart_source {φ : OpenPartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  x ∈ (niceChart φ x h).1.source := by
    let c := niceChart φ x h
    have : c = niceChart φ x h := rfl
    rw [←this]
    exact c.2.1

lemma nice_chart_bounded {φ : OpenPartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  Bornology.IsBounded (niceChart φ x h).1.target := by
    let c := niceChart φ x h
    have : c = niceChart φ x h := rfl
    rw [←this]
    exact c.2.2.1

lemma nice_chart_connected {φ : OpenPartialHomeomorph M NNReal} {x : M} {h : x ∈ φ.source} :
  ConnectedSpace (niceChart φ x h).1.target := by
    let c := niceChart φ x h
    have : c = niceChart φ x h := rfl
    rw [←this]
    exact c.2.2.2

/-- A charted space whose atlas has bounded connected targets. -/
class NicelyChartedSpace (H : Type*) [TopologicalSpace H] [Bornology H] (M : Type*)
    [TopologicalSpace M] extends ChartedSpace H M where
    is_bounded (φ : OpenPartialHomeomorph M H) (h : φ ∈ atlas) : Bornology.IsBounded φ.target
    is_connected (φ : OpenPartialHomeomorph M H) (h : φ ∈ atlas) : ConnectedSpace φ.target

/-- Replace an atlas by one with bounded connected chart targets. -/
@[instance_reducible] noncomputable def nicelyCharted (ht : ChartedSpace NNReal M) :
    NicelyChartedSpace NNReal M where
  chartAt := by
    intro x
    let c := ht.chartAt x
    let c' := niceChart (ht.chartAt x) x (ht.mem_chart_source x)
    exact c'.1
  atlas := let f x := (niceChart (ht.chartAt x) x (ht.mem_chart_source x)).1
    Set.image f (Set.univ : Set M)
  mem_chart_source (x : M) := by
    simp only [Set.mem_ofPred_eq]
    exact nice_chart_source
  chart_mem_atlas (x : M) := by
    simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range, exists_apply_eq_apply]
  is_bounded (φ : OpenPartialHomeomorph M NNReal) := by
    intro h
    dsimp [atlas] at h
    simp only [Set.image_univ, Set.mem_range] at h
    rcases h with ⟨y, hy⟩
    rw [←hy]
    apply nice_chart_bounded
  is_connected (φ : OpenPartialHomeomorph M NNReal) := by
    intro h
    dsimp [atlas] at h
    simp only [Set.image_univ, Set.mem_range] at h
    rcases h with ⟨y, hy⟩
    rw [←hy]
    apply nice_chart_connected

end OneMfld
