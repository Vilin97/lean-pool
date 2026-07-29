/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.FinitePunctureRemoval
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Weighted Disk Argument Principle

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

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
