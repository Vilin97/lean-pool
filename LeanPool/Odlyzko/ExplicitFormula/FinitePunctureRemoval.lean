/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.LogDerivativeResidue

/-!
# Finite Puncture Removal

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology Set

namespace NumberField.Odlyzko

/-- A fill finite punctures used in the Odlyzko-bound argument. -/
noncomputable def fillFinitePunctures (f : ℂ → ℂ) (S : Finset ℂ) : ℂ → ℂ :=
  fun z ↦ if z ∈ S then Filter.limUnder (𝓝[≠] z) f else f z

@[simp]
theorem fillFinitePunctures_apply_of_mem {f : ℂ → ℂ} {S : Finset ℂ} {z : ℂ}
    (hz : z ∈ S) :
    fillFinitePunctures f S z = Filter.limUnder (𝓝[≠] z) f := by
  simp [fillFinitePunctures, hz]

@[simp]
theorem fillFinitePunctures_apply_of_notMem {f : ℂ → ℂ} {S : Finset ℂ} {z : ℂ}
    (hz : z ∉ S) :
    fillFinitePunctures f S z = f z := by
  simp [fillFinitePunctures, hz]

theorem fillFinitePunctures_eventuallyEq_nhdsNE
    (f : ℂ → ℂ) (S : Finset ℂ) (p : ℂ) :
    fillFinitePunctures f S =ᶠ[𝓝[≠] p] f := by
  have hcompl : {z : ℂ | z ∉ S} ∈ cofinite := by
    rw [mem_cofinite]
    convert S.finite_toSet using 1
    grind
  filter_upwards [(nhdsNE_le_cofinite p) hcompl] with z hz
  simp_all

theorem analyticAt_fillFinitePunctures_of_mem
    {f g : ℂ → ℂ} {S : Finset ℂ} {p : ℂ}
    (hp : p ∈ S) (hg : AnalyticAt ℂ g p)
    (hfg : f =ᶠ[𝓝[≠] p] g) :
    AnalyticAt ℂ (fillFinitePunctures f S) p := by
  have hlim : Filter.limUnder (𝓝[≠] p) f = g p :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      |>.congr' hfg.symm).limUnder_eq
  apply hg.congr
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact hfg.symm.trans
      (fillFinitePunctures_eventuallyEq_nhdsNE f S p).symm
  · simp [hp, hlim]

theorem analyticAt_fillFinitePunctures_of_notMem
    {f : ℂ → ℂ} {S : Finset ℂ} {p : ℂ}
    (hp : p ∉ S) (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (fillFinitePunctures f S) p := by
  apply hf.congr
  apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE
  · exact (fillFinitePunctures_eventuallyEq_nhdsNE f S p).symm
  · simp [hp]

end NumberField.Odlyzko
