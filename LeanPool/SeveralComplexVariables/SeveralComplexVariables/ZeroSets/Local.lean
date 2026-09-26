/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ZeroSets.Persistence

/-!
# Local structure of scalar zero sets

Nontrivial analytic germs have a nonzero derivative of finite order. Minimizing this order along
a zero set supplies an analytic function with nonzero derivative that vanishes on that set.
Persistence of zeros supplies the converse inclusion after straightening this auxiliary
function.

## Main results

`AnalyticAt.eventuallyEq_zero_of_iteratedFDeriv_eq_zero` is vanishing of a germ whose iterated
derivatives all vanish. `exists_analytic_zeroSet_superset_fderiv_ne_zero` produces an analytic
function with nonzero derivative vanishing on a given zero set.
`eventually_zeroSet_eq_linear_zeroSet` is the local graph description after straightening.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An analytic germ whose iterated derivatives all vanish is the zero germ. -/
theorem _root_.AnalyticAt.eventuallyEq_zero_of_iteratedFDeriv_eq_zero {f : E → ℂ} {a : E}
    (hf : AnalyticAt ℂ f a) (hzero : ∀ n, iteratedFDeriv ℂ n f a = 0) :
    f =ᶠ[𝓝 a] 0 := by
  obtain ⟨p, r, hp⟩ := hf
  filter_upwards [eball_mem_nhds a hp.r_pos] with y hy
  have hs := hp.hasSum_iteratedFDeriv (y := y - a) (by
    simpa only [mem_eball, edist_zero_right, edist_eq_enorm_sub, sub_zero] using hy)
  simpa [hzero] using hs.tsum_eq.symm

/-- A nonempty proper scalar zero set is contained in the zero set of an analytic function whose
derivative is nonzero at some point of the original zero set. Choose a derivative of minimal
order that does not vanish everywhere on the set. -/
theorem exists_analytic_zeroSet_superset_fderiv_ne_zero [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∃ b ∈ U, f b ≠ 0) (hz : ∃ a ∈ U, f a = 0) :
    ∃ (a : E) (g : E → ℂ), a ∈ U ∧ f a = 0 ∧ AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, f z = 0 → g z = 0) ∧ fderiv ℂ g a ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ a ∈ U, f a = 0 ∧ iteratedFDeriv ℂ n f a ≠ 0 := by
    by_contra! h
    obtain ⟨a, ha, hfa⟩ := hz
    have he := (hf a ha).eventuallyEq_zero_of_iteratedFDeriv_eq_zero (fun n => h n a ha hfa)
    obtain ⟨b, hb, hfb⟩ := hne
    exact hfb (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc ha he hb)
  obtain ⟨a, ha, hfa, hda⟩ := Nat.find_spec hex
  have hmin : ∀ n < Nat.find hex, ∀ z ∈ U, f z = 0 → iteratedFDeriv ℂ n f z = 0 := by
    intro n hn z hz hfz
    by_contra hd
    exact Nat.find_min hex hn ⟨z, hz, hfz, hd⟩
  generalize hn : Nat.find hex = n at hda hmin
  cases n with
  | zero =>
    exact (hda (by ext v; simpa only [iteratedFDeriv_zero_apply,
      zero_apply] using hfa)).elim
  | succ n =>
    obtain ⟨v, hv⟩ : ∃ v, iteratedFDeriv ℂ (n + 1) f a v ≠ 0 := by
      contrapose! hda
      ext v
      exact hda v
    let g : E → ℂ := fun z => iteratedFDeriv ℂ n f z (Fin.tail v)
    have hg : AnalyticOnNhd ℂ g U :=
      ((hf.iteratedFDeriv n).differentiableOn.continuousMultilinear_apply_const
        (Fin.tail v)).analyticOnNhd_of_finiteDimensional hU
    refine ⟨a, g, ha, hfa, hg, ?_, ?_⟩
    · intro z hz hfz
      simp [g, hmin n (Nat.lt_succ_self n) z hz hfz]
    · intro hd
      apply hv
      rw [((hf.iteratedFDeriv n) a ha).differentiableAt.iteratedFDeriv_succ_apply_left']
      change fderiv ℂ g a (v 0) = 0
      simp [hd]

/-- If the zeros of an analytic function lie in a hyperplane and include a point of that hyperplane,
then the two zero sets agree near that point. -/
theorem eventually_zeroSet_eq_linear_zeroSet {V : Set E} (hV : IsOpen V)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f V) {L : E →L[ℂ] ℂ}
    (hL : Function.Surjective L) {a : E} (ha : a ∈ V) (hfa : f a = 0) (hLa : L a = 0)
    (hsub : ∀ z ∈ V, f z = 0 → L z = 0) :
    ∀ᶠ z in 𝓝 a, f z = 0 ↔ L z = 0 := by
  obtain ⟨v, hv⟩ := hL 1
  let S : E × ℂ → E := fun p => p.1 + p.2 • v
  have hS : Continuous S := continuous_fst.add (continuous_snd.smul continuous_const)
  let W := S ⁻¹' V
  have hW : IsOpen W := hV.preimage hS
  have hline : Continuous (fun t : ℂ => a + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have h0 : (0 : ℂ) ∈ (fun t : ℂ => a + t • v) ⁻¹' V := by simpa using ha
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp ((hV.preimage hline).mem_nhds h0)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hdisc : ∀ t ∈ closedBall (0 : ℂ) r, (a, t) ∈ W := by
    intro t ht
    exact hεV ((closedBall_subset_ball (half_lt_self hε)) ht)
  have hboundary : ∀ t ∈ sphere (0 : ℂ) r, (f ∘ S) (a, t) ≠ 0 := by
    intro t ht hft
    have ht0 : t = 0 := by
      simpa [S, hLa, hv] using hsub (S (a, t)) (hdisc t (sphere_subset_closedBall ht)) hft
    subst t
    have : r = 0 := by simpa using ht.symm
    exact hr.ne' this
  have hroots := eventually_exists_zero_in_fiber hW
    (hf.continuousOn.comp hS.continuousOn (mapsTo_preimage _ _))
    (fun p hp => ((hf (S p) hp).differentiableAt.comp p.2
      ((differentiableAt_const p.1).add (differentiableAt_id.smul_const v))))
    hr hdisc (by simpa [S] using hfa) hboundary
  filter_upwards [hV.eventually_mem ha, hroots] with z hz hroot
  refine ⟨hsub z hz, fun hLz => ?_⟩
  obtain ⟨t, _, hzt, hft⟩ := hroot
  have ht0 : t = 0 := by simpa [S, hLz, hv] using hsub (S (z, t)) hzt hft
  simpa [S, ht0] using hft

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
