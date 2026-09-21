/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.GeodesicFlowRegularity

/-!
# Two-point coordinate geodesic neighbourhoods

The ordinary normal-neighbourhood inverse fixes the initial point.  For
continuation of a minimizing metric segment one needs one inverse-function
chart that works while both endpoints vary.  This module shrinks the
two-point endpoint equivalence from `GeodesicFlowRegularity` to a common
neighbourhood of the diagonal.

No metric-minimizing assertion is made here.  The output is a unique small
coordinate geodesic for each nearby ordered endpoint pair, with the entire
trajectory certified to solve the genuine coordinate equation.
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
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
  (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- An open neighbourhood of a diagonal point in a normed product contains
the square of one open neighbourhood of the underlying point. -/
theorem exists_open_self_prod_subset_of_mem_open
    {W : Set (E × E)} (hW : IsOpen W) {z : E} (hz : (z, z) ∈ W) :
    ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ×ˢ V ⊆ W := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ⟨Metric.ball z δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  have hp' : dist p z < δ := Metric.mem_ball.mp hp
  have hq' : dist q z < δ := Metric.mem_ball.mp hq
  have hmax : max (dist p z) (dist q z) < δ := max_lt hp' hq'
  exact lt_trans hmax (by dsimp [δ]; linarith)

/-- An open coordinate-state neighbourhood around `(x₀,0)` contains every
state based sufficiently near `x₀` whose intrinsic tangent norm is uniformly
small.  This is the bridge from geometric unit-speed bounds to membership in
the two-point inverse-function source. -/
theorem exists_open_base_neighborhood_small_tangent_coordinateState_mem
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type u)]
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hsource : (extChartAt I x₀ x₀, 0) ∈ R.source) :
    ∃ N : Set M, IsOpen N ∧ x₀ ∈ N ∧ ∃ δ > (0 : ℝ),
      ∀ p ∈ N, ∀ v : TangentSpace I p, ‖v‖ < δ →
        (extChartAt I x₀ p,
          (trivializationAt E (TangentSpace I : M → Type _) x₀)
            |>.continuousLinearMapAt ℝ p v) ∈ R.source := by
  let z : E := extChartAt I x₀ x₀
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (R.open_source.mem_nhds hsource)
  obtain ⟨C, hC, hCevent⟩ :=
    eventually_norm_trivializationAt_lt E (TangentSpace I : M → Type _) x₀
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcoord : {p : M | extChartAt I x₀ p ∈ Metric.ball z (ε / 2)} ∈ 𝓝 x₀ := by
    apply (continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds
    exact Metric.ball_mem_nhds z (by linarith)
  have hbase : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
    (isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source (I := I) x₀)
  have hcommon : (extChartAt I x₀).source ∩
      {p : M | extChartAt I x₀ p ∈ Metric.ball z (ε / 2)} ∩
      {p : M | ‖e.continuousLinearMapAt ℝ p‖ < C} ∈ 𝓝 x₀ :=
    inter_mem (inter_mem hbase hcoord) hCevent
  obtain ⟨N, hNsub, hNopen, hxN⟩ := mem_nhds_iff.mp hcommon
  refine ⟨N, hNopen, hxN, δ, hδ, ?_⟩
  intro p hp v hv
  have hpdata := hNsub hp
  have hpcoord : dist (extChartAt I x₀ p) z < ε / 2 :=
    Metric.mem_ball.mp hpdata.1.2
  have hop : ‖e.continuousLinearMapAt ℝ p‖ < C := hpdata.2
  have hread : ‖e.continuousLinearMapAt ℝ p v‖ < ε / 2 := by
    have hmul : ‖e.continuousLinearMapAt ℝ p‖ * ‖v‖ < C * δ := by
      nlinarith [norm_nonneg v, norm_nonneg (e.continuousLinearMapAt ℝ p), hδ, hC]
    calc
      ‖e.continuousLinearMapAt ℝ p v‖ ≤
          ‖e.continuousLinearMapAt ℝ p‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ < C * δ := hmul
      _ = ε / 2 := by
        dsimp [δ]
        field_simp
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  change max (dist (extChartAt I x₀ p) z)
    (dist (e.continuousLinearMapAt ℝ p v) 0) < ε
  apply max_lt
  · exact hpcoord.trans (by linarith)
  · exact (by simpa [dist_zero_right] using hread.trans (by linarith))

/-- Around a chart point there is one open coordinate neighbourhood `V` such
that every ordered pair in `V × V` lies in the target of a locally invertible
two-point geodesic endpoint map.  The inverse state is unique inside
`R.source`, and every source trajectory remains in the chart and solves the
actual coordinate geodesic system on `[-2,2]`. -/
theorem exists_twoPoint_coordinateGeodesic_neighborhood
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hzcenter : z = extChartAt I x₀ x₀) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ∃ R : OpenPartialHomeomorph (E × E) (E × E), ∃ V : Set E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝 (z, 0)]
        (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
      (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
      (∀ t, Φ (z, 0) t = (z, 0)) ∧
      ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
      (∀ q, R q = (q.1, (Φ q 1).1)) ∧
      (z, 0) ∈ R.source ∧ (z, z) ∈ R.target ∧
      (∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y) ∧
      (∀ q ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
        (Φ q t).1 ∈ (extChartAt I x₀).target ∧
          G (Φ q t) =
            secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ q t) ∧
          G =ᶠ[𝓝 (Φ q t)]
            (fun p ↦ secondOrderSystem
              (coordinateAcceleration cov x₀ b) p)) ∧
      (∀ q ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
        ∀ j : Fin (Module.finrank ℝ E),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
            𝓝 ((extChartAt I x₀).symm (Φ q t).1)]
            (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j) ∧
      (∀ q ∈ R.source,
        let qrev : E × E := ((Φ q 1).1, -(Φ q 1).2)
        qrev ∈ R.source ∧ Φ qrev 1 = (q.1, -q.2)) ∧
      IsOpen V ∧ z ∈ V ∧ V ×ˢ V ⊆ R.target ∧
      (∀ p ∈ V, ∀ q ∈ V,
        let s := R.symm (p, q)
        s ∈ R.source ∧ s.1 = p ∧ (Φ s 1).1 = q) ∧
      ∀ {p q : E} (s : E × E), s ∈ R.source →
        s.1 = p → (Φ s 1).1 = q → (p, q) ∈ R.target →
        s = R.symm (p, q) := by
  obtain ⟨G, Φ, R, hG, hGcompact, hGeq, hΦzero, hΦcurve, hfix, hΦsmooth,
    hR, hsource, htarget, hinverseSmooth, hactual, hframe, hreverse⟩ :=
    exists_reversalInvariant_twoPoint_coordinateGeodesic_localEquiv
      (I := I) (M := M) (E := E) cov x₀ b hz hzcenter
  obtain ⟨V, hVopen, hzV, hVV⟩ :=
    exists_open_self_prod_subset_of_mem_open
      (E := E) R.open_target htarget
  refine ⟨G, Φ, R, V, hG, hGcompact, hGeq, hΦzero, hΦcurve, hfix, hΦsmooth,
    hR, hsource, htarget, hinverseSmooth, hactual, hframe, hreverse,
    hVopen, hzV, hVV, ?_, ?_⟩
  · intro p hp q hq
    have hpqTarget : (p, q) ∈ R.target := hVV ⟨hp, hq⟩
    let s : E × E := R.symm (p, q)
    have hsSource : s ∈ R.source := R.map_target hpqTarget
    have hright : R s = (p, q) := R.right_inv hpqTarget
    rw [hR] at hright
    exact ⟨hsSource, congrArg Prod.fst hright, congrArg Prod.snd hright⟩
  · intro p q s hs hsp hsq hpq
    apply R.injOn hs (R.map_target hpq)
    rw [hR, R.right_inv hpq]
    exact Prod.ext hsp hsq

end LocalGeodesicData

end BonnetMyersEntry
