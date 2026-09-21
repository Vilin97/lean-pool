/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SphericalShell

/-!
# Removal of isolated singularities

An arbitrary finite-dimensional complex normed source is reduced by a continuous linear
coordinate equivalence to the proved punctured-polydisc theorem. The extension is then glued to
the original function. No boundedness hypothesis is imposed near the puncture. Reference:
[Scheidemann][Scheidemann2005] (2005), Corollary 2.3.2.

## Main results

`exists_analyticOnNhd_extension_diff_singleton` removes an isolated singularity of a Banach-valued
holomorphic map on an open set in complex dimension at least two, without a local boundedness
hypothesis.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Metric Filter
open scoped Topology

namespace SeveralComplexVariables

/-- An isolated singularity is removable on any open set in complex dimension at least two. The
target is any complex Banach space, and the domain need not be connected. -/
theorem exists_analyticOnNhd_extension_diff_singleton
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hdim : 2 ≤ Module.finrank ℂ E) {U : Set E} (ho : IsOpen U)
    {a : E} (ha : a ∈ U) {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ {a})) :
    ∃ g, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ {a}) := by
  classical
  let d := Module.finrank ℂ E - 1
  have hd : 0 < d := by dsimp [d]; omega
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdim' : Module.finrank ℂ E = Module.finrank ℂ ((Fin d → ℂ) × ℂ) := by
    simp only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin]
    dsimp [d]
    omega
  let L : E ≃L[ℂ] ((Fin d → ℂ) × ℂ) := ContinuousLinearEquiv.ofFinrankEq hdim'
  have hc : Continuous (fun p => a + L.symm p) := continuous_const.add L.symm.continuous
  have hn : {p | a + L.symm p ∈ U} ∈ 𝓝 (0 : (Fin d → ℂ) × ℂ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using ho.mem_nhds ha)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hn
  have hfun : AnalyticOnNhd ℂ (fun p => f (a + L.symm p))
      ((ball 0 r ×ˢ ball 0 r) \ {0}) := by
    intro p hp
    have hpU : a + L.symm p ∈ U :=
      hrU (by simpa only [Prod.zero_eq_mk, ball_prod_same] using hp.1)
    have hpne : a + L.symm p ≠ a := by
      intro he
      apply hp.2
      have he' : L.symm p = 0 := by simpa only [add_eq_left] using he
      simpa using congrArg L he'
    exact (hf _ ⟨hpU, hpne⟩).comp (f := fun q => a + L.symm q)
      (analyticAt_const.add (L.symm.toContinuousLinearMap.analyticAt p))
  obtain ⟨g, hg, heq⟩ := exists_extension_punctured_polydisc hr hr hfun
  let G := Function.update f a (g 0)
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    by_cases hxa : x = a
    · subst x
      have hga : AnalyticAt ℂ (fun x => g (L (x - a))) a :=
        (hg 0 ⟨mem_ball_self hr, mem_ball_self hr⟩).comp_of_eq
          ((L.toContinuousLinearMap.analyticAt (a - a)).comp (f := fun x : E => x - a)
            (analyticAt_id.sub analyticAt_const)) (by simp)
      apply hga.congr
      have hn' : {x | L (x - a) ∈ ball 0 r} ∈ 𝓝 a :=
        (L.continuous.comp (continuous_id.sub continuous_const)).continuousAt.preimage_mem_nhds
          (by simpa using ball_mem_nhds (0 : (Fin d → ℂ) × ℂ) hr)
      filter_upwards [hn'] with x hx
      by_cases hxa : x = a
      · subst x; simp [G]
      · have hp : L (x - a) ∈ (ball 0 r ×ˢ ball 0 r) \ {0} := by
          refine ⟨by simpa only [Prod.zero_eq_mk, ball_prod_same] using hx, ?_⟩
          intro hzero
          apply hxa
          apply sub_eq_zero.mp
          have h := congrArg L.symm hzero
          simpa using h
        simpa [G, hxa] using heq hp
    · apply (hf x ⟨hx, hxa⟩).congr
      filter_upwards [isOpen_compl_singleton.mem_nhds hxa] with y hy
      exact (Function.update_of_ne hy _ _).symm
  · intro x hx
    exact Function.update_of_ne hx.2 _ _

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
