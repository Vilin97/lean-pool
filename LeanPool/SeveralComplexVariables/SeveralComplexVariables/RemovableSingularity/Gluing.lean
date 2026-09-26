/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity

/-!
# Gluing local analytic extensions from a dense subset

Local continuous extensions of a function on a dense subset agree. The filter limit along that
subset therefore gives a single analytic extension on the whole domain. This elementary
construction uses no sheaf machinery and imposes no connectedness.

## Main results

`exists_analyticOnNhd_extension_of_local` glues local analytic extensions from a dense subset.
`subset_closure_nonzero_of_nonzero_germs` is density of the nonvanishing locus from nonzero
germs, without analyticity of a global function.
-/

public noncomputable section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [NormedSpace ℂ E] in
/-- A function with nonzero germs everywhere on an open set has dense nonvanishing locus. This
topological statement needs no analyticity assumption. -/
theorem subset_closure_nonzero_of_nonzero_germs {U : Set E} (hU : IsOpen U)
    {g : E → ℂ} (hne : ∀ a ∈ U, ¬ g =ᶠ[𝓝 a] 0) :
    U ⊆ closure (U \ g ⁻¹' {0}) := by
  intro a ha
  rw [Metric.mem_closure_iff]
  intro r hr
  by_contra! h
  apply hne a ha
  filter_upwards [hU.mem_nhds ha, ball_mem_nhds a hr] with z hz hzr
  by_contra hgz
  exact not_lt_of_ge (h z ⟨hz, hgz⟩) (by simpa [dist_comm] using hzr)

/-- Local analytic extensions from a relatively dense subset glue to an extension on an open set.
Uniqueness is only asserted on that set, not outside it. -/
theorem exists_analyticOnNhd_extension_of_local
    {U S : Set E} {f : E → F} (hSU : S ⊆ U) (hdense : U ⊆ closure S)
    (hloc : ∀ a ∈ U, ∃ (V : Set E) (H : E → F), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      AnalyticOnNhd ℂ H V ∧ EqOn H f (V ∩ S)) :
    ∃ H : E → F, AnalyticOnNhd ℂ H U ∧ EqOn H f S := by
  let H : E → F := fun a => limUnder (𝓝[S] a) f
  have heq : ∀ (V : Set E) (G : E → F), IsOpen V → V ⊆ U →
      AnalyticOnNhd ℂ G V → EqOn G f (V ∩ S) → EqOn H G V := by
    intro V G hV hVU hG hGf a ha
    have : (𝓝[S] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense (hVU ha))
    have he : G =ᶠ[𝓝[S] a] f := by
      filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds ha), self_mem_nhdsWithin] with z hz hzs
      exact hGf ⟨hz, hzs⟩
    have ht : Tendsto f (𝓝[S] a) (𝓝 (G a)) :=
      ((hG a ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he
    exact ht.limUnder_eq
  refine ⟨H, ?_, ?_⟩
  · intro a ha
    obtain ⟨V, G, hV, haV, hVU, hG, hGf⟩ := hloc a ha
    have he : H =ᶠ[𝓝 a] G :=
      Filter.mem_of_superset (hV.mem_nhds haV) (fun z hz => heq V G hV hVU hG hGf hz)
    exact (analyticAt_congr he).mpr (hG a haV)
  · intro a ha
    obtain ⟨V, G, hV, haV, hVU, hG, hGf⟩ := hloc a (hSU ha)
    exact (heq V G hV hVU hG hGf haV).trans (hGf ⟨haV, ha⟩)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
