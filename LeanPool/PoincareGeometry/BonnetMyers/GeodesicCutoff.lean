/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.Geodesic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Compactly supported coordinate-geodesic extensions

The chart geodesic equation is genuinely `C¹` only while its position remains
in the chosen extended-chart target.  For flow-dependence and inverse-function
arguments it is useful to replace that local right-hand side by a global,
compactly supported `C¹` field which agrees with it near one prescribed state.

This module proves exactly that localization step.  It does not claim a normal
neighbourhood or a minimizing-geodesic theorem; it supplies the analytic
extension those later arguments require.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

private theorem contDiff_and_hasCompactSupport_cutoff_smul
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set A} {f : A → V} {χ : A → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U)
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    ContDiff ℝ n (fun x ↦ χ x • f x) ∧
      HasCompactSupport (fun x ↦ χ x • f x) := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x ↦ ?_), ?_⟩
  · by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsub hx)))
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  · refine hχc.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun hχx ↦ hx (by rw [hχx, zero_smul])

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
  (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)

/-- Around any coordinate state whose position lies in the extended-chart
target, the genuine coordinate geodesic system agrees with a globally defined
compactly supported `C¹` vector field. -/
theorem exists_contDiff_compactSupport_coordinateGeodesic_extension
    {z₀ : E} (hz₀ : z₀ ∈ (extChartAt I x₀).target) (u₀ : E) :
    ∃ G : E × E → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z₀, u₀)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) := by
  let F : E × E → E × E :=
    fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q
  let U : Set (E × E) := (extChartAt I x₀).target ×ˢ Set.univ
  have hU : IsOpen U :=
    (isOpen_extChartAt_target x₀).prod isOpen_univ
  have hF : ContDiffOn ℝ 1 F U := by
    intro q hq
    exact (coordinateAcceleration_system_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
      hq.1 q.2).contDiffWithinAt
  let p : E × E := (z₀, u₀)
  have hp : p ∈ U := ⟨hz₀, Set.mem_univ _⟩
  obtain ⟨r, hrpos, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let χ : ContDiffBump p :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  have hχsub : tsupport (χ : E × E → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by dsimp [χ]; linarith)).trans hball
  let G : E × E → E × E := fun q ↦ χ q • F q
  obtain ⟨hG, hGcompact⟩ :=
    contDiff_and_hasCompactSupport_cutoff_smul hU hF χ.contDiff χ.hasCompactSupport hχsub
  refine ⟨G, ?_, ?_, ?_⟩
  · simpa only [G] using hG
  · simpa only [G] using hGcompact
  · filter_upwards [χ.eventuallyEq_one] with q hq
    change χ q • F q = F q
    simpa only [Pi.one_apply, one_smul] using
      congrArg (fun c : ℝ ↦ c • F q) hq

end LocalGeodesicData

end BonnetMyersEntry
