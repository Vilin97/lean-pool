/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
public import LeanPool.Odlyzko.CompletedZeta.Xi

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Filter Ideal IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

theorem poleClearedCompletedDedekindZetaContinuation_eq_neg_finrank_mul_xi
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCompletedDedekindZetaContinuation K s =
      -(Module.finrank ℚ K : ℂ) * completedDedekindXi K s := by
  rw [poleClearedCompletedDedekindZetaContinuation_eq_completedDedekindZeta K hs,
    completedDedekindXi]
  ring

theorem poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    poleClearedCompletedDedekindZetaContinuation K s ≠ 0 := by
  rw [poleClearedCompletedDedekindZetaContinuation_eq_neg_finrank_mul_xi K hs]
  exact mul_ne_zero
    (neg_ne_zero.mpr (by
      exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))))
    (completedDedekindXi_ne_zero_of_one_lt_re K hs)

theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_rightHalfPlane
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s =
      logDeriv (completedDedekindXi K) s := by
  have heq :
      poleClearedCompletedDedekindZetaContinuation K =ᶠ[𝓝 s]
        fun z ↦ -(Module.finrank ℚ K : ℂ) * completedDedekindXi K z := by
    have hright :
        {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
      (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
    filter_upwards [hright] with z hz
    exact
      poleClearedCompletedDedekindZetaContinuation_eq_neg_finrank_mul_xi K hz
  have hn : -(Module.finrank ℚ K : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (by
      exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K))))
  rw [logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds,
    ← logDeriv_apply]
  exact logDeriv_const_mul s _ hn

theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_eq_primePower
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) s =
      1 / s + 1 / (s - 1) +
        Complex.log ((|(discr K : ℝ)| : ℝ) : ℂ) / 2 +
        nrComplexPlaces K *
          (Complex.digamma s - Complex.log (2 * (Real.pi : ℂ))) -
        ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          primePowerLogTerm K pe.1 pe.2 s := by
  rw [logDeriv_poleClearedCompletedDedekindZetaContinuation_rightHalfPlane K hs,
    logDeriv_completedDedekindXi_rightHalfPlane K hs]

theorem deriv_poleClearedCompletedDedekindZetaContinuation_one_sub
    (s : ℂ) :
    deriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -deriv (poleClearedCompletedDedekindZetaContinuation K) s := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hΞ : Differentiable ℂ Ξ :=
    differentiable_poleClearedCompletedDedekindZetaContinuation K
  have hfun : Ξ = fun z ↦ Ξ (1 - z) := by
    funext z
    exact poleClearedCompletedDedekindZetaContinuation_functionalEquation K z
  have hcomp :
      HasDerivAt (fun z ↦ Ξ (1 - z)) (-deriv Ξ (1 - s)) s := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_neg,
      mul_one] using
      (hΞ.differentiableAt.hasDerivAt.comp s
        ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)))
  have heq : deriv Ξ s = -deriv Ξ (1 - s) := by
    exact (congrArg (fun f : ℂ → ℂ ↦ deriv f s) hfun).trans hcomp.deriv
  grind

theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub
    {s : ℂ}
    (_hs : poleClearedCompletedDedekindZetaContinuation K s ≠ 0) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -logDeriv (poleClearedCompletedDedekindZetaContinuation K) s := by
  rw [logDeriv_apply, logDeriv_apply,
    deriv_poleClearedCompletedDedekindZetaContinuation_one_sub K s]
  rw [poleClearedCompletedDedekindZetaContinuation_functionalEquation K s]
  grind

theorem logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub_all
    (s : ℂ) :
    logDeriv (poleClearedCompletedDedekindZetaContinuation K) (1 - s) =
      -logDeriv (poleClearedCompletedDedekindZetaContinuation K) s := by
  by_cases hs :
      poleClearedCompletedDedekindZetaContinuation K s = 0
  · have hs' :
        poleClearedCompletedDedekindZetaContinuation K (1 - s) = 0 := by
      rw [← poleClearedCompletedDedekindZetaContinuation_functionalEquation K s]
      simp_all
    simp [logDeriv_apply, hs, hs']
  · exact
      logDeriv_poleClearedCompletedDedekindZetaContinuation_one_sub K hs

end NumberField.Odlyzko
