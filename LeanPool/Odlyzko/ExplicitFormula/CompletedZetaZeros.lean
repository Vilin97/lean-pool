/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
public import LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.LogDerivativeResidue

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Filter NumberField
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem analyticOnNhd_poleClearedCompletedDedekindZetaContinuation :
    AnalyticOnNhd ℂ
      (poleClearedCompletedDedekindZetaContinuation K) Set.univ :=
  DifferentiableOn.analyticOnNhd
    (differentiable_poleClearedCompletedDedekindZetaContinuation K).differentiableOn
    isOpen_univ

open Classical in
theorem meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_ne_top
    (s : ℂ) :
    meromorphicOrderAt
      (poleClearedCompletedDedekindZetaContinuation K) s ≠ ⊤ := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hmero : MeromorphicOn Ξ Set.univ :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).meromorphicOn
  have htwo : meromorphicOrderAt Ξ (2 : ℂ) ≠ ⊤ := by
    have hne : Ξ (2 : ℂ) ≠ 0 :=
      poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
        (by norm_num)
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
      (hmero (2 : ℂ) (Set.mem_univ _))).mpr
    exact
      ((analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
        (2 : ℂ) (Set.mem_univ _)).continuousAt.eventually_ne hne).filter_mono
        nhdsWithin_le_nhds
  exact hmero.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ s) htwo

open Classical in
theorem meromorphicOrderAt_poleClearedCompletedDedekindZetaContinuation_nonneg
    (s : ℂ) :
    0 ≤ meromorphicOrderAt
      (poleClearedCompletedDedekindZetaContinuation K) s :=
  (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K
    s (Set.mem_univ s)).meromorphicOrderAt_nonneg

open Classical in
/-- A completed dedekind zeta zero divisor used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindZetaZeroDivisor :
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
  MeromorphicOn.divisor
    (poleClearedCompletedDedekindZetaContinuation K) Set.univ

omit [IsTotallyComplex K] in
open Classical in
theorem completedDedekindZetaZeroDivisor_support_inter_compact_finite
    {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ (completedDedekindZetaZeroDivisor K).support).Finite := by
  classical
  let D := completedDedekindZetaZeroDivisor K
  have hloc :
      ∀ x ∈ S, ∃ V : Set ℂ, V ∈ 𝓝 x ∧
        Set.Finite (V ∩ D.support) := by
    intro x _
    rcases D.supportLocallyFiniteWithinDomain x (Set.mem_univ x) with
      ⟨V, hV, hfin⟩
    grind
  choose V hVnhds hVfin using hloc
  rcases hS.elim_nhds_subcover'
      (U := fun x hx ↦ V x hx)
      (hU := fun x hx ↦ hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      S ∩ D.support ⊆
        ⋃ x ∈ t, (V (x : ℂ) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyS, hyD⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : ℂ) x.2 := ht hyS
    simp_all
  have hfinite :
      Set.Finite (⋃ x ∈ t,
        (V (x : ℂ) x.2 ∩ D.support)) := by
    refine (t.finite_toSet).biUnion ?_
    simp_all
  exact hfinite.subset hsub

end NumberField.Odlyzko
