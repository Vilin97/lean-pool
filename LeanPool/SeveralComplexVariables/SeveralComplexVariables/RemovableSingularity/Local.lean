/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Cauchy
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.Geometry
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.RemovableSingularity.OneVariable

/-!
# Local Riemann extension in finite-dimensional complex spaces

Translate a fixed small complex circle through nearby points and integrate the original function
along it. The circle avoids the defining zero set. One-variable removability identifies the
integral with the original function off the zero set; parameter-dependent integration proves
joint analyticity. The target is a complex Banach space, and no Weierstrass or Hartogs extension
theorem is used.

## Main results

`exists_local_extension_zeroSet_of_bounded` is local Riemann extension across a scalar zero set
for a locally bounded Banach-valued holomorphic map.
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A bounded analytic function off a scalar zero set admits a local analytic extension at every
point where the defining germ is nonzero. The neighborhood need not be connected. -/
theorem exists_local_extension_zeroSet_of_bounded
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : AnalyticOnNhd ℂ g U)
    {a : E} (ha : a ∈ U) (hne : ¬ g =ᶠ[𝓝 a] 0)
    {f : E → F} (hf : AnalyticOnNhd ℂ f (U \ g ⁻¹' {0}))
    {C : ℝ} (hb : ∀ z ∈ U \ g ⁻¹' {0}, ‖f z‖ ≤ C) :
    ∃ (V : Set E) (f' : E → F), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      AnalyticOnNhd ℂ f' V ∧ EqOn f' f (V \ g ⁻¹' {0}) := by
  obtain ⟨v, r, R, V, hr, hrR, hV, haV, hdisc, hcircle⟩ :=
    exists_translated_circle_avoiding_zeroSet hU hg ha hne
  have hR : 0 < R := hr.trans hrR
  have hVU : V ⊆ U := by
    intro z hz
    simpa using hdisc z hz 0 (mem_closedBall_self hR.le)
  let W : Set (E × ℂ) := {p | p.2 ≠ 0 ∧ p.1 + p.2 • v ∈ U ∧ g (p.1 + p.2 • v) ≠ 0}
  let H : E × ℂ → F := fun p => p.2⁻¹ • f (p.1 + p.2 • v)
  have hH : AnalyticOnNhd ℂ H W := by
    intro p hp
    have hA : AnalyticAt ℂ (fun q : E × ℂ => q.1 + q.2 • v) p :=
      analyticAt_fst.add (analyticAt_snd.smul analyticAt_const)
    exact (analyticAt_snd.inv hp.1).smul ((hf _ hp.2).comp_of_eq hA rfl)
  have hW : ∀ z ∈ V, ∀ t ∈ sphere (0 : ℂ) r, (z, t) ∈ W := by
    intro z hz t ht
    refine ⟨?_, hdisc z hz t (closedBall_subset_closedBall hrR.le (sphere_subset_closedBall ht)),
      hcircle z hz t ht⟩
    change t ≠ 0
    intro h
    have heq := mem_sphere.mp ht
    simp [h] at heq
    linarith
  let f' : E → F := fun z => (2 * Real.pi * I : ℂ)⁻¹ • ∮ t in C(0, r), H (z, t)
  have hfa : AnalyticOnNhd ℂ f' V :=
    (analyticOnNhd_circleIntegral_kernel hV hH hr.le hW).const_smul
  refine ⟨V, f', hV, haV, hVU, hfa, ?_⟩
  intro z hz
  have hsl : AnalyticOnNhd ℂ (fun t : ℂ => g (z + t • v)) (ball 0 R) := by
    intro t ht
    exact (hg _ (hdisc z hz.1 t (ball_subset_closedBall ht))).comp_of_eq
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) rfl
  have hfs : AnalyticOnNhd ℂ (fun t : ℂ => f (z + t • v))
      (ball 0 R \ (fun t : ℂ => g (z + t • v)) ⁻¹' {0}) := by
    intro t ht
    exact (hf _ ⟨hdisc z hz.1 t (ball_subset_closedBall ht.1), ht.2⟩).comp_of_eq
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) rfl
  have hsne : ∃ t ∈ ball (0 : ℂ) R, g (z + t • v) ≠ 0 :=
    ⟨0, mem_ball_self hR, by simpa using hz.2⟩
  obtain ⟨fsl, hfsl, heq⟩ := exists_analyticOnNhd_extension_zeroSet_oneVariable
    isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected hsl hsne hfs (by
      intro t ht _
      refine ⟨1, zero_lt_one, C, ?_⟩
      intro w hw
      exact hb _ ⟨hdisc z hz.1 w (ball_subset_closedBall hw.2.1), hw.2.2⟩)
  have hcauchy :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (f := fsl) countable_empty (mem_ball_self hr)
    (hfsl.continuousOn.mono (closedBall_subset_ball hrR))
    (fun w hw => (hfsl w (ball_subset_ball hrR.le hw.1)).differentiableAt)
  have hboundary : (∮ t in C(0, r), H (z, t)) = ∮ t in C(0, r), (t - 0)⁻¹ • fsl t := by
    apply circleIntegral.integral_congr hr.le
    intro t ht
    have htR : t ∈ ball (0 : ℂ) R := closedBall_subset_ball hrR (sphere_subset_closedBall ht)
    simp only [H, sub_zero, heq ⟨htR, hcircle z hz.1 t ht⟩]
  exact (congrArg (fun q => (2 * Real.pi * I : ℂ)⁻¹ • q) hboundary).trans
    (hcauchy.trans (by simpa using heq ⟨mem_ball_self hR, by simpa using hz.2⟩))

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
