/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.FiniteSetAvoidance
public import Mathlib.Analysis.Complex.JensenFormula

/-!
# Zero Free Circle Selection

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace NumberField.Odlyzko

open Classical in
theorem AnalyticOnNhd.exists_zeroFree_sphere
    {f : ℂ → ℂ} {c : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hf : AnalyticOnNhd ℂ f (closedBall c b))
    (hc : f c ≠ 0) :
    ∃ R ∈ Ioo a b, ∀ z ∈ sphere c R, f z ≠ 0 := by
  let D := MeromorphicOn.divisor f (closedBall c b)
  have hDfin : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  have hb : 0 < b := ha.trans_lt hab
  have hcball : c ∈ closedBall c b := mem_closedBall_self hb.le
  have hmer : MeromorphicOn f (closedBall c b) := hf.meromorphicOn
  have hcord : meromorphicOrderAt f c ≠ ⊤ := by
    intro htop
    have hne : f =ᶠ[nhdsWithin c {c}ᶜ] 0 :=
      meromorphicOrderAt_eq_top_iff.mp htop
    have hnhds : f =ᶠ[𝓝 c] 0 :=
      ((hf c hcball).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        continuousAt_const).1 hne
    exact hc hnhds.eq_of_nhds
  have hord : ∀ z : closedBall c b, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    exact hmer.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c b).isPreconnected hcball z.property hcord
  let S : Finset ℝ := hDfin.toFinset.image fun z ↦ dist z c
  obtain ⟨R, hR, hsep⟩ :=
    exists_mem_Ioo_abs_sub_ge_finiteSetAvoidanceRadiusOnLength
      S a (sub_pos.mpr hab)
  refine ⟨R, by grind, ?_⟩
  intro z hz hzero
  have hzball : z ∈ closedBall c b := by
    rw [mem_sphere] at hz
    rw [mem_closedBall, hz]
    grind
  have hzSupport : z ∈ D.support := by
    apply Function.mem_support.mpr
    rw [MeromorphicOn.divisor_apply hmer hzball]
    intro horder
    have horder0 : meromorphicOrderAt f z = 0 :=
      (WithTop.untop₀_eq_zero.mp horder).resolve_right (hord ⟨z, hzball⟩)
    rw [(hf z hzball).meromorphicOrderAt_eq] at horder0
    have : analyticOrderAt f z = 0 := by simpa using horder0
    exact (hf z hzball).analyticOrderAt_ne_zero.mpr hzero this
  have hzS : dist z c ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨z, hDfin.mem_toFinset.mpr hzSupport, rfl⟩
  have hpositive :=
    finiteSetAvoidanceRadiusOnLength_pos (sub_pos.mpr hab) S
  rw [mem_sphere] at hz
  grind

end NumberField.Odlyzko
