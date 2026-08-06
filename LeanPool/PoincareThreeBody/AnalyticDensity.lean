/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Density from one-dimensional analytic nonvanishing

This file packages the isolated-zero argument used in Poincaré's perturbing-function
calculation.  A real-analytic function on a connected open set that is nonzero at one point is
nonzero on a dense subset of that set.
-/

namespace LeanPool.PoincareThreeBody

open Filter Set Topology

/-- The nonzero locus of a nontrivial real-analytic function is dense in any connected open
domain.  The set is regarded as a subset of the domain subtype. -/
theorem dense_nonzero_of_analyticOnNhd
    {f : ℝ → ℝ} {U : Set ℝ}
    (hUopen : IsOpen U) (hUconnected : IsConnected U)
    (hf : AnalyticOnNhd ℝ f U) {witness : ℝ}
    (hwitness : witness ∈ U) (hfwitness : f witness ≠ 0) :
    Dense {x : U | f x.1 ≠ 0} := by
  have hcodiscrete : f ⁻¹' {0}ᶜ ∈ codiscreteWithin U :=
    hf.preimage_zero_mem_codiscreteWithin hfwitness hwitness hUconnected
  apply Subtype.dense_iff.mpr
  intro x hx
  have hpunctured : f ⁻¹' {0}ᶜ ∪ Uᶜ ∈ 𝓝[≠] x :=
    (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hcodiscrete) x hx
  have hdomain : U ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hx)
  have hnonzeroWithin : (f ⁻¹' {0}ᶜ ∩ U) ∈ 𝓝[≠] x := by
    simpa only [union_inter_distrib_right, compl_inter_self, union_empty] using
      inter_mem hpunctured hdomain
  rw [mem_closure_iff_nhdsWithin_neBot]
  have himage : ((↑) '' {x : U | f x.1 ≠ 0}) = f ⁻¹' {0}ᶜ ∩ U := by
    ext y
    simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right,
      exists_eq_right, mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
    tauto
  exact (inferInstance : NeBot (𝓝[≠] x)).mono (by
    refine le_inf inf_le_left ?_
    rw [le_principal_iff]
    rwa [himage])

end LeanPool.PoincareThreeBody
