/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.ExceptionalSet

/-!
# Connectedness of the nonvanishing locus

Removing a proper scalar holomorphic zero set from a connected open subset of a
finite-dimensional complex space leaves a connected set. Extend the bounded locally constant
separator of a hypothetical separation and apply the identity principle. More generally, the
same holds for relatively closed sets locally contained in proper analytic zero sets, by the
locally bounded Riemann extension theorem. This consequence is kept above removability to
preserve the dependency order.

## Main results

`isConnected_nonzero_of_analyticOnNhd` is connectedness of the nonvanishing locus of a nonzero
scalar holomorphic function. `isConnected_sdiff_of_locallyContainedInAnalyticZeroSet` is the
corresponding statement for a relatively closed thin exceptional set.
-/

public section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

/-- A relatively closed set locally contained in proper analytic zero sets cannot disconnect a
connected open domain. No positive-dimension hypothesis is needed. -/
theorem isConnected_sdiff_of_locallyContainedInAnalyticZeroSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U S : Set E} (hc : IsConnected U)
    (hUS : IsOpen (U \ S)) (hS : LocallyContainedInAnalyticZeroSet U S) :
    IsConnected (U \ S) := by
  classical
  let V := U \ S
  have hVo : IsOpen V := hUS
  refine ⟨?_, ?_⟩
  · by_contra h
    have he : U \ S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    obtain ⟨a, ha⟩ := hc.nonempty
    have := hS.subset_closure ha
    simp [he] at this
  change IsPreconnected V
  intro s t hs ht hcover hVs hVt
  by_contra hmeet
  have hdis : ∀ z ∈ V, z ∈ s → z ∈ t → False := by
    intro z hz hzs hzt
    exact hmeet ⟨z, hz, hzs, hzt⟩
  let f : E → ℂ := fun z => if z ∈ s then 1 else 0
  have hfs : ∀ z ∈ s, f =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
    intro z hz
    filter_upwards [hs.mem_nhds hz] with y hy
    simp [f, hy]
  have hft : ∀ z ∈ V ∩ t, f =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    intro z hz
    filter_upwards [(hVo.inter ht).mem_nhds hz] with y hy
    simp [f, show y ∉ s from fun hys => hdis y hy.1 hys hy.2]
  have hf : AnalyticOnNhd ℂ f V := by
    intro z hz
    rcases hcover hz with hzs | hzt
    · exact (analyticAt_congr (hfs z hzs)).mpr analyticAt_const
    · exact (analyticAt_congr (hft z ⟨hz, hzt⟩)).mpr analyticAt_const
  have hb : ∀ a ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ,
      ∀ z ∈ ball a r ∩ V, ‖f z‖ ≤ C := by
    intro a _
    refine ⟨1, zero_lt_one, 1, fun z _ => ?_⟩
    dsimp [f]
    split_ifs <;> simp
  obtain ⟨F, hF, hEq⟩ := exists_analyticOnNhd_extension_across_locallyContainedZeroSet hUS hS hf hb
  obtain ⟨a, ha, has⟩ := hVs
  have hFone : F =ᶠ[𝓝 a] (fun _ => (1 : ℂ)) := by
    filter_upwards [hVo.mem_nhds ha, hfs a has] with z hz hfz
    exact (hEq hz).trans hfz
  have hconst := hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc.isPreconnected
    ha.1 hFone
  obtain ⟨b, hbV, hbt⟩ := hVt
  have hbzero : F b = 0 := (hEq hbV).trans ((hft b ⟨hbV, hbt⟩).self_of_nhds)
  have hbone : F b = 1 := hconst hbV.1
  exact zero_ne_one (hbzero.symm.trans hbone)

/-- A proper holomorphic zero set cannot disconnect a connected open domain. No positive-dimension
hypothesis is needed. -/
theorem isConnected_nonzero_of_analyticOnNhd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∃ z ∈ U, g z ≠ 0) :
    IsConnected (U \ g ⁻¹' {0}) := by
  obtain ⟨z, hz, hgz⟩ := hne
  apply isConnected_sdiff_of_locallyContainedInAnalyticZeroSet ⟨⟨z, hz⟩, hc⟩
    (hg.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl)
  apply locallyContainedInAnalyticZeroSet_zeroSet hU hg
  intro a ha hzero
  exact hgz (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc ha hzero hz)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
