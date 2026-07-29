/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.NormalForm

/-! Adapted from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
by Alex Kontorovich and Terence Tao:
`ResidueCalcOnRectangles.lean` and `RectangleArgumentPrinciple.lean`, commit
`be5e07e04cde20c5ceabf63759bd097a9c88173f` (Apache-2.0). -/

@[expose] public section

noncomputable section

open Complex Filter Topology Set Asymptotics

namespace NumberField.Odlyzko

theorem exists_analytic_logDeriv_remainder_of_meromorphicOrderAt
    {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p)
    (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧
      (logDeriv f - fun s : ℂ ↦ (n : ℂ) / (s - p)) =ᶠ[𝓝[≠] p] g := by
  obtain ⟨u, hu_analytic, hu_ne, hfu⟩ :=
    (meromorphicOrderAt_eq_int_iff hf).1 hord
  let F : ℂ → ℂ := fun s ↦ (s - p) ^ n * u s
  have hfu_ne : f =ᶠ[𝓝[≠] p] F := by
    filter_upwards [hfu] with s hs
    simpa [F, smul_eq_mul] using hs
  have hderiv_ne : deriv f =ᶠ[𝓝[≠] p] deriv F :=
    hfu_ne.nhdsNE_deriv
  have hu_nonzero_ne : ∀ᶠ s in 𝓝[≠] p, u s ≠ 0 :=
    (hu_analytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp
      hu_ne |>.filter_mono nhdsWithin_le_nhds
  have hu_analytic_ne : ∀ᶠ s in 𝓝[≠] p, AnalyticAt ℂ u s :=
    hu_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  refine ⟨logDeriv u, ?_, ?_⟩
  · exact hu_analytic.deriv.div hu_analytic hu_ne
  · filter_upwards [hfu_ne, hderiv_ne, self_mem_nhdsWithin,
      hu_nonzero_ne, hu_analytic_ne]
      with s hfs hderiv hs_ne hus_ne hus_analytic
    have hpow_ne : (s - p) ^ n ≠ 0 :=
      zpow_ne_zero n (sub_ne_zero.mpr hs_ne)
    have hdiff_pow :
        DifferentiableAt ℂ (fun z : ℂ ↦ (z - p) ^ n) s :=
      ((by simp :
        DifferentiableAt ℂ (fun z : ℂ ↦ z - p) s)).zpow
          (Or.inl (sub_ne_zero.mpr hs_ne))
    have hlogF :
        logDeriv F s =
          logDeriv (fun z : ℂ ↦ (z - p) ^ n) s +
            logDeriv u s :=
      logDeriv_mul (f := fun z : ℂ ↦ (z - p) ^ n) (g := u) s
        hpow_ne hus_ne hdiff_pow hus_analytic.differentiableAt
    have hlogpow :
        logDeriv (fun z : ℂ ↦ (z - p) ^ n) s =
          (n : ℂ) / (s - p) := by
      rw [logDeriv_fun_zpow
        (f := fun z : ℂ ↦ z - p) (x := s) (by simp) n]
      simp [logDeriv_apply, div_eq_mul_inv]
    simp only [Pi.sub_apply]
    calc
      logDeriv f s - (n : ℂ) / (s - p) =
          logDeriv F s - (n : ℂ) / (s - p) := by
        simp [logDeriv_apply, hfs, hderiv]
      _ = logDeriv u s := by simp_all

end NumberField.Odlyzko
