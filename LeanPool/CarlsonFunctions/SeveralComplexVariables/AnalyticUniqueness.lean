/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Analytic uniqueness from positive real parameters

This file records uniqueness principles for holomorphic functions whose values are known only
on the positive real locus.  They are useful for transporting certain identities proved using
real probability measures to their complex analytic continuations.
-/

open Complex Set Filter
open scoped Topology

@[expose] public noncomputable section AnalyticUniqueness

/-- Local one-variable uniqueness from agreement on a real germ.  This is the form useful when
the functions are only analytic on a connected continuation domain rather than entire. -/
theorem AnalyticOnNhd.eqOn_of_eventuallyEq_ofReal {U : Set ℂ} {F G : ℂ → ℂ}
    {x₀ : ℝ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hU : IsPreconnected U) (hx₀ : (x₀ : ℂ) ∈ U)
    (hEq : ∀ᶠ x : ℝ in 𝓝 x₀, F (x : ℂ) = G (x : ℂ)) : Set.EqOn F G U := by
  let wR : ℕ → ℝ := fun n ↦ x₀ + (n + 1 : ℝ)⁻¹
  let w : ℕ → ℂ := fun n ↦ (wR n : ℂ)
  have hwR : Tendsto wR atTop (𝓝 x₀) := by
    simpa [wR] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hw : Tendsto w atTop (𝓝 (x₀ : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hwR
  have hwne : ∀ n, w n ≠ (x₀ : ℂ) := by
    intro n h
    have hr : x₀ + (n + 1 : ℝ)⁻¹ = x₀ := Complex.ofReal_injective h
    have : (0 : ℝ) < (n + 1 : ℝ)⁻¹ := by positivity
    linarith
  have hwithin : Tendsto w atTop (𝓝[≠] (x₀ : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw, Eventually.of_forall hwne⟩
  have hagree : ∀ᶠ n : ℕ in atTop, F (w n) = G (w n) := by
    filter_upwards [hwR.eventually hEq] with n hn
    exact hn
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hU hx₀
    (hwithin.frequently hagree.frequently)

/-- Two entire functions of one complex variable which agree at every positive real number agree
everywhere. -/
theorem analyticOnNhd_eq_of_eqOn_posReal {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hEq : ∀ x : ℝ, 0 < x → F (x : ℂ) = G (x : ℂ)) : F = G := by
  have hEq' : ∀ᶠ x : ℝ in 𝓝 1, F (x : ℂ) = G (x : ℂ) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact hEq x hx
  have h := hF.eqOn_of_eventuallyEq_ofReal hG isPreconnected_univ (Set.mem_univ _) hEq'
  exact funext fun z => h (Set.mem_univ z)

/-- Two entire functions of finitely many complex variables which agree on all vectors of
strictly positive real parameters agree everywhere.  No complex-open agreement hypothesis is
needed. -/
theorem analyticOnNhd_eq_of_eqOn_posReal_pi {ι : Type*} [Fintype ι]
    {F G : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    (hG : AnalyticOnNhd ℂ G univ)
    (hEq : ∀ b : ι → ℝ, (∀ i, 0 < b i) →
      F (fun i ↦ (b i : ℂ)) = G (fun i ↦ (b i : ℂ))) : F = G := by
  classical
  have hstep : ∀ s : Finset ι, ∀ b : ι → ℂ,
      (∀ i, i ∉ s → ∃ x : ℝ, 0 < x ∧ b i = (x : ℂ)) → F b = G b := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro b hb
        choose r hr hbr using fun i ↦ hb i (by simp)
        have hb_eq : b = fun i ↦ (r i : ℂ) := by
          funext i
          exact hbr i
        rw [hb_eq]
        exact hEq r hr
    | @insert a s ha ih =>
        intro b hb
        let L : ℂ → (ι → ℂ) := fun w ↦ Function.update b a w
        have hL : AnalyticOnNhd ℂ L univ := by
          intro w _
          apply AnalyticAt.pi
          intro i
          by_cases hia : i = a
          · subst i
            have heq : (fun x : ℂ ↦ L x a) = id := by
              funext x
              simp [L]
            rw [heq]
            exact analyticAt_id
          · simpa [L, hia] using
              (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ b i) w)
        have hslices : (fun w ↦ F (L w)) = (fun w ↦ G (L w)) := by
          apply analyticOnNhd_eq_of_eqOn_posReal
          · intro w _
            exact (hF (L w) (mem_univ _)).comp_of_eq (hL w (mem_univ _)) rfl
          · intro w _
            exact (hG (L w) (mem_univ _)).comp_of_eq (hL w (mem_univ _)) rfl
          · intro x hx
            apply ih
            intro i his
            by_cases hia : i = a
            · subst i
              exact ⟨x, hx, by simp [L]⟩
            · simpa [L, hia] using hb i (by simp [his, hia])
        have := congrFun hslices (b a)
        simpa [L] using this
  funext b
  exact hstep Finset.univ b (by simp)

end AnalyticUniqueness
