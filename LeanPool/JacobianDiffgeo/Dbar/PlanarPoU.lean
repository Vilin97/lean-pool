/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Finite smooth partitions of unity on planar open sets (`Jacobian/Dbar/PlanarPoU.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` §4.4, §7.1). Mathlib-only, planar,
project-independent (design D10).

Builds a finite smooth partition of unity on an open `V ⊆ ℂ`, subordinate to a given finite open
cover `W : Fin n → Set ℂ`, from scratch: shrink the cover in the (normal, being metrizable)
subtype `↥V` via `exists_subset_iUnion_closure_subset`, push the shrunk sets back to `ℂ`
(`IsOpen.isOpenMap_subtype_val`, `closure_subtype`), build one compactly-conditioned bump per
piece via `IsOpen.exists_contDiff_support_eq`, and normalize by the (pointwise positive on `V`)
sum. This is risk item R5 of the design; the from-scratch route (rather than reusing mathlib's
`SmoothPartitionOfUnity`, which needs a *closed* base set and bundles into `M → ℝ` smooth maps,
not the plain functions with prescribed exact `support` needed here) was confirmed as the right
call by an upstream investigation of the manifold `PartitionOfUnity` API.
-/

noncomputable section

open scoped ContDiff
open Set Filter Topology

namespace RS

/-- A finite smooth partition of unity on an open planar set `V`, subordinate to a finite open
cover `W`: each `ψ i` is smooth on `V`, nonnegative, supported in `W i`, summing to `1` on `V`,
and eventually zero near any point of `V` outside `W i`. -/
theorem exists_smooth_partition_of_finite_cover {V : Set ℂ} (hV : IsOpen V) {n : ℕ}
    {W : Fin n → Set ℂ} (hWo : ∀ i, IsOpen (W i)) (_hWV : ∀ i, W i ⊆ V)
    (hcov : V ⊆ ⋃ i, W i) :
    ∃ ψ : Fin n → ℂ → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (ψ i) V) ∧ (∀ i z, 0 ≤ ψ i z) ∧
      (∀ z ∈ V, ∑ i, ψ i z = 1) ∧
      (∀ i, Function.support (ψ i) ⊆ W i) ∧
      (∀ i, ∀ z ∈ V, z ∉ W i → ∀ᶠ w in 𝓝 z, ψ i w = 0) := by
  -- Step 1: shrink the cover inside the (normal) subtype `↥V`.
  have hv : ∀ i, IsOpen (Subtype.val ⁻¹' (W i) : Set V) := fun i => (hWo i).preimage
    continuous_subtype_val
  have hcov' : (Set.univ : Set V) ⊆ ⋃ i, (Subtype.val ⁻¹' (W i) : Set V) := by
    intro q _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov q.2)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨u, huniv, huo, hucl⟩ :=
    exists_subset_iUnion_closure_subset isClosed_univ hv
      (fun _ _ => Set.toFinite _) hcov'
  have husub : ∀ i, u i ⊆ (Subtype.val ⁻¹' (W i) : Set V) := fun i =>
    (subset_closure).trans (hucl i)
  -- Step 2: push the shrunk pieces back to `ℂ`.
  set W' : Fin n → Set ℂ := fun i => Subtype.val '' (u i) with hW'_def
  have hW'o : ∀ i, IsOpen (W' i) := fun i => hV.isOpenMap_subtype_val _ (huo i)
  have hW'sub : ∀ i, W' i ⊆ W i := by
    rintro i y ⟨q, hq, rfl⟩
    exact husub i hq
  have hcovV : V ⊆ ⋃ i, W' i := by
    intro z hz
    set q : V := ⟨z, hz⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (huniv (Set.mem_univ q))
    exact Set.mem_iUnion.2 ⟨i, q, hi, rfl⟩
  have hclosure : ∀ i, ∀ z ∈ V, z ∈ closure (W' i) → z ∈ W i := by
    intro i z hz hzcl
    set q : V := ⟨z, hz⟩
    have hqcl : q ∈ closure (u i) := closure_subtype.2 hzcl
    have := hucl i hqcl
    exact this
  -- Step 3: one bump function per piece.
  choose φ hφsupp hφcd hφrange using fun i => (hW'o i).exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hφnonneg : ∀ i z, 0 ≤ φ i z := fun i z => (hφrange i (Set.mem_range_self z)).1
  set S : ℂ → ℝ := fun z => ∑ i, φ i z with hS_def
  have hScd : ContDiff ℝ ∞ S := ContDiff.sum fun i _ => hφcd i
  have hSnonneg : ∀ z, 0 ≤ S z := fun z => Finset.sum_nonneg fun i _ => hφnonneg i z
  have hSpos : ∀ z ∈ V, 0 < S z := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcovV hz)
    have hφi_pos : 0 < φ i z := by
      have : φ i z ≠ 0 := by rw [← Function.mem_support, hφsupp i]; exact hi
      exact lt_of_le_of_ne (hφnonneg i z) (Ne.symm this)
    exact lt_of_lt_of_le hφi_pos
        (Finset.single_le_sum (fun j _ => hφnonneg j z) (Finset.mem_univ i))
  refine ⟨fun i z => φ i z / S z, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ContDiffOn.div (hφcd i).contDiffOn hScd.contDiffOn
    intro z hz
    exact ne_of_gt (hSpos z hz)
  · intro i z
    exact div_nonneg (hφnonneg i z) (hSnonneg z)
  · intro z hz
    have hSz : S z ≠ 0 := ne_of_gt (hSpos z hz)
    rw [← Finset.sum_div, hS_def]
    exact div_self hSz
  · intro i z hz
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hz
    have hz1 : z ∈ Function.support (φ i) := hz.1
    rw [hφsupp i] at hz1
    exact hW'sub i hz1
  · intro i z hz hznW
    have hznW' : z ∉ closure (W' i) := fun hmem => hznW (hclosure i z hz hmem)
    have hopen : IsOpen (closure (W' i))ᶜ := isClosed_closure.isOpen_compl
    filter_upwards [hopen.mem_nhds hznW'] with w hw
    have : φ i w = 0 := by
      by_contra hne
      exact hw (subset_closure (hφsupp i ▸ hne))
    rw [this, zero_div]

/-- Extending a `PoU`-weighted term by zero outside its supporting open set stays smooth on `U`,
provided `ψ` vanishes near any point of `U` outside `W`. -/
theorem contDiffOn_indicator_smul_of_eventually_zero {U W V : Set ℂ} (_hU : IsOpen U)
    (hW : IsOpen W) {ψ : ℂ → ℝ} {f : ℂ → ℂ} (hUV : U ⊆ V)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hf : ContDiffOn ℝ ∞ f (U ∩ W))
    (hvan : ∀ z ∈ U, z ∉ W → ∀ᶠ w in 𝓝 z, ψ w = 0) :
    ContDiffOn ℝ ∞ (W.indicator fun z => ψ z • f z) U := by
  intro z hz
  by_cases hzW : z ∈ W
  · rw [← contDiffWithinAt_inter (hW.mem_nhds hzW)]
    apply ContDiffWithinAt.congr_of_eventuallyEq
      (((hψ.mono (Set.inter_subset_left.trans hUV)).smul hf).contDiffWithinAt
        ⟨hz, hzW⟩ : ContDiffWithinAt ℝ ∞ (fun z => ψ z • f z) (U ∩ W) z)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact Set.indicator_of_mem hw.2 _
    · exact Set.indicator_of_mem hzW _
  · have hzero : ∀ᶠ w in 𝓝 z, W.indicator (fun z => ψ z • f z) w = 0 := by
      filter_upwards [hvan z hz hzW] with w hw
      by_cases hwW : w ∈ W
      · rw [Set.indicator_of_mem hwW, hw, zero_smul]
      · exact Set.indicator_of_notMem hwW _
    apply ContDiffWithinAt.congr_of_eventuallyEq
      (contDiffWithinAt_const : ContDiffWithinAt ℝ ∞ (fun _ => (0 : ℂ)) U z)
      (hzero.filter_mono nhdsWithin_le_nhds)
    exact hzero.self_of_nhds

end RS

end
