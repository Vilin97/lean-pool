/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.IsolatedSingularity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Local

/-!
# Zero sets in several complex variables

The identity-principle consequences in `ZeroSets.Basic` and the local zero-set comparison
theorems in `ZeroSets.Local` are re-exported here. Isolated scalar zeros are excluded by the
proved puncture-removal theorem applied to the reciprocal.

Reference: [Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Corollary 2.1.3.

## Main results

* `frequently_zero_punctured_of_analyticAt`: A scalar holomorphic function in complex dimension at
  least two cannot have an isolated zero.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A scalar holomorphic function in complex dimension at least two cannot have an isolated zero.
See [Jakóbczak–Jarnicki][JakobczakJarnicki2021] Corollary 2.1.3. Applying Hartogs extension to
the reciprocal would contradict an isolated zero. The scalar target and dimension restriction
are essential: vector-valued maps and functions of one variable can have isolated zeros. -/
theorem frequently_zero_punctured_of_analyticAt
    [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E)
    {f : E → ℂ} {a : E} (hf : AnalyticAt ℂ f a) (ha : f a = 0) :
    ∃ᶠ z in 𝓝[≠] a, f z = 0 := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  by_contra hn
  have hne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 := not_frequently.mp hn
  have hn' : ∀ᶠ z in 𝓝 a, z ≠ a → f z ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using eventually_nhdsWithin_iff.mp hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hn')
  have hfi : AnalyticOnNhd ℂ (fun z => (f z)⁻¹) (ball a r \ {a}) :=
    fun z hz => ((hball hz.1).1).inv ((hball hz.1).2 hz.2)
  obtain ⟨g, hg, he⟩ := exists_analyticOnNhd_extension_diff_singleton hdim isOpen_ball
    (mem_ball_self hr) hfi
  have heq : (fun z => f z * g z) =ᶠ[𝓝[≠] a] (fun _ => (1 : ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hr), eventually_mem_nhdsWithin] with z hz
      hza
    rw [he ⟨hz, hza⟩]
    exact mul_inv_cancel₀ ((hball hz).2 hza)
  have hlim := (hf.continuousAt.mul (hg a (mem_ball_self hr)).continuousAt).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {a}ᶜ))
  have hval : f a * g a = 1 := tendsto_nhds_unique hlim (Tendsto.congr' heq.symm tendsto_const_nhds)
  simp [ha] at hval

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
