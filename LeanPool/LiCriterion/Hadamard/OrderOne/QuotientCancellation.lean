/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order

/-!
Local quotient cancellation at a zero, counting multiplicity.

If `f` and `g` are analytic at `a` and have the same (finite) vanishing order at `a`, then the
quotient `f/g` has a removable singularity at `a`. We package this by constructing an explicit
piecewise definition that is analytic at `a`.

This is the pointwise ingredient needed to upgrade the “simple zeros” quotient arguments to the
general multiplicity regime.
-/

open Complex Filter Topology
open scoped Topology

namespace Hadamard
namespace OrderOne

theorem exists_analyticAt_update_div_of_analyticOrderNatAt_eq
    {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hf' : analyticOrderAt f a ≠ ⊤) (hg' : analyticOrderAt g a ≠ ⊤)
    (hord : analyticOrderNatAt f a = analyticOrderNatAt g a) :
    ∃ q : ℂ, AnalyticAt ℂ (fun z => if z = a then q else f z / g z) a := by
  classical
  set n : ℕ := analyticOrderNatAt f a
  obtain ⟨F, hF_an, hF_ne, hF_eq⟩ := (hf.analyticOrderAt_ne_top).1 hf'
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := (hg.analyticOrderAt_ne_top).1 hg'
  have hn : analyticOrderNatAt g a = n := by simpa [n] using hord.symm
  have hF_eq' : f =ᶠ[𝓝 a] fun z => (z - a) ^ n * F z := by
    filter_upwards [hF_eq] with z hz
    simpa [smul_eq_mul, n] using hz
  have hG_eq' : g =ᶠ[𝓝 a] fun z => (z - a) ^ n * G z := by
    filter_upwards [hG_eq] with z hz
    simpa [smul_eq_mul, hn, n] using hz
  let q : ℂ := F a / G a
  refine ⟨q, ?_⟩
  have h_model : AnalyticAt ℂ (fun z => F z / G z) a := hF_an.div hG_an hG_ne
  have h_model : AnalyticAt ℂ (fun z => F z / G z) a := hF_an.div hG_an hG_ne
  have h_congr :
      (fun z => F z / G z) =ᶠ[𝓝 a] (fun z => if z = a then q else f z / g z) := by
    filter_upwards [hF_eq', hG_eq'] with z hfz hgz
    by_cases hz : z = a
    · subst hz
      simp [q]
    · have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
      have hpow : (z - a) ^ n ≠ 0 := pow_ne_zero n hza
      have hquot : f z / g z = F z / G z := by
        calc
          f z / g z = ((z - a) ^ n * F z) / ((z - a) ^ n * G z) := by simp [hfz, hgz]
          _ = F z / G z := by
            simp [mul_div_mul_left (c := (z - a) ^ n) (F z) (G z) hpow]
      simp [q, hz, hquot]
  exact h_model.congr h_congr

end OrderOne
end Hadamard
