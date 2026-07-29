/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.LogDerivativeResidue
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Weighted Disk Argument Principle

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

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

end

section

open Complex Filter Function Metric Topology Set

namespace NumberField.Odlyzko

/-- A weighted log deriv finite remainder used in the Odlyzko-bound argument. -/
noncomputable def weightedLogDerivFiniteRemainder
    (f h : ℂ → ℂ) (S : Finset ℂ) (order : ℂ → ℤ) : ℂ → ℂ :=
  fun z ↦ h z * logDeriv f z -
    ∑ p ∈ S, (h p * (order p : ℂ)) / (z - p)

theorem exists_analytic_weightedLogDerivFiniteRemainder_of_mem
    {f h : ℂ → ℂ} {S : Finset ℂ} {order : ℂ → ℤ} {p : ℂ}
    (hp : p ∈ S) (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = (order p : WithTop ℤ))
    (hh : AnalyticAt ℂ h p) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      weightedLogDerivFiniteRemainder f h S order =ᶠ[𝓝[≠] p] g := by
  obtain ⟨u, hu, hfu⟩ :=
    exists_analytic_logDeriv_remainder_of_meromorphicOrderAt hf horder
  let g : ℂ → ℂ := fun z ↦
    h z * u z + (order p : ℂ) * dslope h p z -
      ∑ q ∈ S.erase p, (h q * (order q : ℂ)) / (z - q)
  have hg : AnalyticAt ℂ g p := by
    have hdslope : AnalyticAt ℂ (dslope h p) p := by
      obtain ⟨P, hP⟩ := hh
      exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
    apply (hh.mul hu).add (analyticAt_const.mul hdslope) |>.sub
    change AnalyticAt ℂ
      (fun z : ℂ ↦ ∑ q ∈ S.erase p, (h q * (order q : ℂ)) / (z - q)) p
    convert
      Finset.analyticAt_sum (𝕜 := ℂ)
        (f := fun q (z : ℂ) ↦ (h q * (order q : ℂ)) / (z - q))
        (S.erase p) (fun q hq ↦ by
          have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
          exact analyticAt_const.div
            (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hqp.symm)) using 1
    ext z
    simp
  refine ⟨g, hg, ?_⟩
  filter_upwards [hfu, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z ≠ p := hzp
  simp only [weightedLogDerivFiniteRemainder, g, Pi.sub_apply] at hz ⊢
  rw [← Finset.sum_erase_add _ _ hp, ← hz]
  rw [dslope_of_ne h hzp']
  simp only [slope, vsub_eq_sub, smul_eq_mul]
  grind

theorem analyticAt_weightedLogDerivFiniteRemainder_of_notMem
    {f h : ℂ → ℂ} {S : Finset ℂ} {order : ℂ → ℤ} {z : ℂ}
    (hz : z ∉ S) (hf : AnalyticAt ℂ f z) (hfz : f z ≠ 0)
    (hh : AnalyticAt ℂ h z) :
    AnalyticAt ℂ (weightedLogDerivFiniteRemainder f h S order) z := by
  apply (hh.mul (hf.deriv.div hf hfz)).sub
  change AnalyticAt ℂ
    (fun w : ℂ ↦ ∑ p ∈ S, (h p * (order p : ℂ)) / (w - p)) z
  convert
    Finset.analyticAt_sum (𝕜 := ℂ)
      (f := fun p (w : ℂ) ↦ (h p * (order p : ℂ)) / (w - p))
      S (fun p hp ↦ by
        have hzp : z ≠ p := by grind
        exact analyticAt_const.div
          (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzp)) using 1
  ext w
  simp

theorem analyticAt_fill_weightedLogDerivFiniteRemainder
    {f h : ℂ → ℂ} {S : Finset ℂ} {order : ℂ → ℤ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hh : AnalyticAt ℂ h z)
    (hzero : f z = 0 → z ∈ S)
    (horder : ∀ p ∈ S,
      meromorphicOrderAt f p = (order p : WithTop ℤ)) :
    AnalyticAt ℂ
      (fillFinitePunctures (weightedLogDerivFiniteRemainder f h S order) S) z := by
  by_cases hz : z ∈ S
  · obtain ⟨g, hg, hfg⟩ :=
      exists_analytic_weightedLogDerivFiniteRemainder_of_mem hz hf.meromorphicAt
        (horder z hz) hh
    exact analyticAt_fillFinitePunctures_of_mem hz hg hfg
  · apply analyticAt_fillFinitePunctures_of_notMem hz
    exact analyticAt_weightedLogDerivFiniteRemainder_of_notMem hz hf
      (fun hfz ↦ hz (hzero hfz)) hh

end NumberField.Odlyzko

end
