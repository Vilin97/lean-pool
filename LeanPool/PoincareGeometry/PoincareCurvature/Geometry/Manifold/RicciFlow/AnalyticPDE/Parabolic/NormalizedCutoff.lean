/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ModelManifoldGaugeFlow
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LocalizedCoefficientScaling

/-!
# Quantitative smooth normalized cutoffs

The manifold bump-function construction is augmented with the three concrete
bounds used by normalized parabolic localization: `|χ| ≤ 1`, a global
Lipschitz constant, and a radius containing the support.
-/

@[expose] public section

noncomputable section
open Set
open scoped Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE

/-- Quantitative data attached to a smooth compactly supported cutoff on a
finite-dimensional real normed space. -/
structure NormalizedCutoffControl (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  cutoff : X → ℝ
  lipschitzBound : ℝ
  supportRadius : ℝ
  contDiff_three : ContDiff ℝ 3 cutoff
  compactSupport : HasCompactSupport cutoff
  lipschitzBound_nonneg : 0 ≤ lipschitzBound
  supportRadius_pos : 0 < supportRadius
  abs_le_one : ∀ x, |cutoff x| ≤ 1
  norm_sub_le : ∀ x y,
    ‖cutoff x - cutoff y‖ ≤ lipschitzBound * dist x y
  support_norm_le : ∀ x, cutoff x ≠ 0 → ‖x‖ ≤ supportRadius

namespace NormalizedCutoffControl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem supportRadius_nonneg (χ : NormalizedCutoffControl X) :
    0 ≤ χ.supportRadius := χ.supportRadius_pos.le

theorem abs_sub_le (χ : NormalizedCutoffControl X) (x y : X) :
    |χ.cutoff x - χ.cutoff y| ≤ χ.lipschitzBound * dist x y := by
  simpa [Real.norm_eq_abs] using χ.norm_sub_le x y

end NormalizedCutoffControl

/-- A compact set inside an open set admits a smooth normalized cutoff with
all quantitative constants required by coefficient scaling.  It equals one
on a neighborhood of the compact set and its support stays inside the given
open set. -/
theorem exists_normalizedCutoffControl_one_nhdsSet_of_isCompact
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : NormalizedCutoffControl X,
      tsupport χ.cutoff ⊆ U ∧
      (∀ᶠ x in nhdsSet K, χ.cutoff x = 1) ∧
      ∀ x, χ.cutoff x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hf, hfc, hfsupp, hfOne, hfIcc⟩ :=
    SmoothDependenceCk.exists_contDiff_cutoff_one_nhdsSet_of_isCompact
      (n := 3) hK hU hKU
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨L, hL0, hL⟩ :=
    exists_nonneg_lipschitz_bound_of_contDiff_one_hasCompactSupport hf1 hfc
  obtain ⟨R, hR, hRsupp⟩ :=
    exists_pos_support_radius_of_hasCompactSupport hfc
  let χ : NormalizedCutoffControl X :=
    { cutoff := f
      lipschitzBound := L
      supportRadius := R
      contDiff_three := hf
      compactSupport := hfc
      lipschitzBound_nonneg := hL0
      supportRadius_pos := hR
      abs_le_one := fun x => by
        rw [abs_of_nonneg (hfIcc x).1]
        exact (hfIcc x).2
      norm_sub_le := hL
      support_norm_le := hRsupp }
  exact ⟨χ, hfsupp, hfOne, hfIcc⟩

/-- A normalized cutoff adapted to the unit ball.  This is the cutoff needed
after centering and parabolically rescaling a local coordinate operator: it
is identically one on the normalized closed unit ball, independently of the
unscaled chart center. -/
theorem exists_normalizedCutoffControl_one_on_closedBall
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    ∃ χ : NormalizedCutoffControl X,
      (∀ x ∈ Metric.closedBall (0 : X) 1, χ.cutoff x = 1) ∧
      tsupport χ.cutoff ⊆ Metric.ball (0 : X) 2 := by
  have hcompact : IsCompact (Metric.closedBall (0 : X) 1) :=
    isCompact_closedBall (0 : X) 1
  have hopen : IsOpen (Metric.ball (0 : X) 2) := Metric.isOpen_ball
  have hsub : Metric.closedBall (0 : X) 1 ⊆ Metric.ball (0 : X) 2 := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hx (by norm_num)
  obtain ⟨χ, hχsupp, hχone, _⟩ :=
    exists_normalizedCutoffControl_one_nhdsSet_of_isCompact
      hcompact hopen hsub
  refine ⟨χ, ?_, hχsupp⟩
  intro x hx
  exact hχone.self_of_nhdsSet x hx

end AnalyticPDE
end RicciFlow
