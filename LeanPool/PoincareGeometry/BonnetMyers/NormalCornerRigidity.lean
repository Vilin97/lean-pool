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

import LeanPool.PoincareGeometry.BonnetMyers.CornerRigidity

/-!
# Corner rigidity in normal coordinates

The explicit endpoint first-variation formula is applied to a one-sided
exact-distance curve.  Equality in the distance growth estimate forces the
outgoing coordinate tangent to continue in the terminal radial direction.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace BonnetMyersEntry.LocalGeodesicData

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [PseudoMetricSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- For an exact-distance outgoing coordinate curve, the endpoint first
variation formula forces its tangent to continue in the same direction as
the incoming normal geodesic's terminal radial tangent. -/
theorem normalCoordinate_sameDirection_of_exactDistance_right
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (V W : Set E) (z : E)
    (hVopen : IsOpen V) (hFWopen : IsOpen (F '' W))
    (hF : ContDiff ℝ 1 F) (hψ : ContDiffOn ℝ 1 ψ V)
    (hFWV : F '' W ⊆ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hFzero : F 0 = z)
    (hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖)
    {u : E} (huW : u ∈ W) (hFu : F u ≠ z) (hψFu : ψ (F u) = u)
    {sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ u}
    (hgauss : ∀ q : E,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u q) (LocalChartSecondOrderSolution.curve sol 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q x₀))
    (hspeed : inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀))
    (c : ℝ → E) (ξ : E) (hc : HasDerivAt c ξ 0) (hc0 : c 0 = F u)
    (heq : (fun s ↦ dist x₀ ((extChartAt I x₀).symm (c s))) =ᶠ[
      𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ dist x₀ ((extChartAt I x₀).symm (F u)) +
        s * ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b ξ
            (LocalChartSecondOrderSolution.curve sol 1)‖)) :
    let T := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)
    let Kξ := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b ξ
        (LocalChartSecondOrderSolution.curve sol 1)
    ‖Kξ‖ • T = ‖T‖ • Kξ := by
  let T := coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)
  let K : E →L[ℝ] TM (LocalChartSecondOrderSolution.curve sol 1) :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b
        (LocalChartSecondOrderSolution.curve sol 1)).toContinuousLinearMap
  dsimp only
  have hKapply (q : E) : K q =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q
        (LocalChartSecondOrderSolution.curve sol 1) := rfl
  have hy : F u ∈ (F '' W) \ {z} :=
    ⟨⟨u, huW, rfl⟩, by simpa using hFu⟩
  have hd := normalCoordinate_dist_hasFDerivAt
    (I := I) (M := M) x₀ b F ψ V W z hVopen hFWopen hψ hFWV
      hright hFzero hradial hy
  have hformula :
      fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u) ξ =
        inner ℝ T (K ξ) / ‖T‖ := by
    simpa only [T, hKapply] using
      normalCoordinate_dist_fderiv_apply_eq_endpoint_inner
        (I := I) (M := M) cov x₀ b F ψ V W z hVopen hFWopen hF hψ
          hFWV hright hFzero hradial huW hFu hψFu hgauss hspeed ξ
  have hT : T ≠ 0 := by
    have hnorm : ‖T‖ =
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hspeed
      nlinarith [norm_nonneg T,
        norm_nonneg (coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b u x₀)]
    intro hzero
    have hsourceZero :
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀ = 0 := by
      apply norm_eq_zero.mp
      rw [← hnorm, hzero, norm_zero]
    have hinj := CurveConnection.coordinateFrameLinear_injective_of_mem_source
      (I := I) (M := M) x₀ b (mem_extChartAt_source (I := I) x₀)
    have hframeZero :
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (0 : E) x₀ = 0 := by
      change (IntrinsicAcceleration.coordinateFrameLinear
        (I := I) (M := M) x₀ b x₀) 0 = 0
      exact map_zero _
    have hu0 : u = 0 := by
      apply hinj
      simpa [IntrinsicAcceleration.coordinateFrameVector, hframeZero] using hsourceZero
    exact hFu (hu0 ▸ hFzero)
  have halign := sameDirection_of_distance_firstVariation_right
    (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
    (fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u))
    c K (F u) ξ T hd.differentiableAt.hasFDerivAt hc hc0 hformula hT
    (by simpa only [T, hKapply] using heq)
  simpa only [T, hKapply] using halign

/-- For an exact-distance curve moving back toward the centre of the incoming
normal geodesic, the endpoint first variation forces the curve tangent to be
opposite to the terminal radial tangent. -/
theorem normalCoordinate_oppositeDirection_of_exactDistance_right
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (V W : Set E) (z : E)
    (hVopen : IsOpen V) (hFWopen : IsOpen (F '' W))
    (hF : ContDiff ℝ 1 F) (hψ : ContDiffOn ℝ 1 ψ V)
    (hFWV : F '' W ⊆ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hFzero : F 0 = z)
    (hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖)
    {u : E} (huW : u ∈ W) (hFu : F u ≠ z) (hψFu : ψ (F u) = u)
    {sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ u}
    (hgauss : ∀ q : E,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u q) (LocalChartSecondOrderSolution.curve sol 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q x₀))
    (hspeed : inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀))
    (c : ℝ → E) (ξ : E) (hc : HasDerivAt c ξ 0) (hc0 : c 0 = F u)
    (heq : (fun s ↦ dist x₀ ((extChartAt I x₀).symm (c s))) =ᶠ[
      𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ dist x₀ ((extChartAt I x₀).symm (F u)) -
        s * ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b ξ
            (LocalChartSecondOrderSolution.curve sol 1)‖)) :
    let T := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b
        (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)
    let Kξ := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b ξ
        (LocalChartSecondOrderSolution.curve sol 1)
    ‖Kξ‖ • T = -(‖T‖ • Kξ) := by
  let T := coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)
  let K : E →L[ℝ] TM (LocalChartSecondOrderSolution.curve sol 1) :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b
        (LocalChartSecondOrderSolution.curve sol 1)).toContinuousLinearMap
  dsimp only
  have hKapply (q : E) : K q =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q
        (LocalChartSecondOrderSolution.curve sol 1) := rfl
  have hy : F u ∈ (F '' W) \ {z} :=
    ⟨⟨u, huW, rfl⟩, by simpa using hFu⟩
  have hd := normalCoordinate_dist_hasFDerivAt
    (I := I) (M := M) x₀ b F ψ V W z hVopen hFWopen hψ hFWV
      hright hFzero hradial hy
  have hformula :
      fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u) ξ =
        inner ℝ T (K ξ) / ‖T‖ := by
    simpa only [T, hKapply] using
      normalCoordinate_dist_fderiv_apply_eq_endpoint_inner
        (I := I) (M := M) cov x₀ b F ψ V W z hVopen hFWopen hF hψ
          hFWV hright hFzero hradial huW hFu hψFu hgauss hspeed ξ
  have hT : T ≠ 0 := by
    have hnorm : ‖T‖ =
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hspeed
      nlinarith [norm_nonneg T,
        norm_nonneg (coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b u x₀)]
    intro hzero
    have hsourceZero :
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀ = 0 := by
      apply norm_eq_zero.mp
      rw [← hnorm, hzero, norm_zero]
    have hinj := CurveConnection.coordinateFrameLinear_injective_of_mem_source
      (I := I) (M := M) x₀ b (mem_extChartAt_source (I := I) x₀)
    have hframeZero :
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b (0 : E) x₀ = 0 := by
      change (IntrinsicAcceleration.coordinateFrameLinear
        (I := I) (M := M) x₀ b x₀) 0 = 0
      exact map_zero _
    have hu0 : u = 0 := by
      apply hinj
      simpa [IntrinsicAcceleration.coordinateFrameVector, hframeZero] using hsourceZero
    exact hFu (hu0 ▸ hFzero)
  have halign := oppositeDirection_of_distance_firstVariation_right
    (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
    (fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u))
    c K (F u) ξ T hd.differentiableAt.hasFDerivAt hc hc0 hformula hT
    (by simpa only [T, hKapply] using heq)
  simpa only [T, hKapply] using halign

/-- A manifold curve moving back toward the centre of an incoming normal
geodesic at full speed has tangent opposite to the terminal radial tangent.
This is the chart-independent form used to rule out a corner in an exact
metric segment. -/
theorem normalCoordinate_oppositeDirection_of_exactDistanceCurve_right
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (V W : Set E) (z : E)
    (hVopen : IsOpen V) (hFWopen : IsOpen (F '' W))
    (hF : ContDiff ℝ 1 F) (hψ : ContDiffOn ℝ 1 ψ V)
    (hFWV : F '' W ⊆ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hFzero : F 0 = z)
    (hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖)
    {u : E} (huW : u ∈ W) (hFu : F u ≠ z) (hψFu : ψ (F u) = u)
    {incoming : LocalChartSecondOrderSolution I
      (coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ u}
    (hgauss : ∀ q : E,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (incoming.velocity 1) (LocalChartSecondOrderSolution.curve incoming 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u q) (LocalChartSecondOrderSolution.curve incoming 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q x₀))
    (hspeed : inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (incoming.velocity 1) (LocalChartSecondOrderSolution.curve incoming 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (incoming.velocity 1) (LocalChartSecondOrderSolution.curve incoming 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀))
    {c : M} (hinCurve1 : LocalChartSecondOrderSolution.curve incoming 1 = c)
    (hendpointSource : c ∈ (extChartAt I x₀).source)
    (hendpointChart : extChartAt I x₀ c = F u)
    (β : ℝ → M) (v : TM c)
    (hβderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I β 0
      (CurveConnection.timeTangentMap (I := I) 0 v))
    (hβzero : β 0 = c)
    (hdecrease : (fun s ↦ dist x₀ (β s)) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ dist x₀ c - s * ‖v‖)) :
    let T := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b (incoming.velocity 1) c
    ‖v‖ • T = -(‖T‖ • v) := by
  subst c
  let c : M := LocalChartSecondOrderSolution.curve incoming 1
  let T : TM c := coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b (incoming.velocity 1) c
  dsimp only
  obtain ⟨ξ, hξ, hKξ⟩ :=
    CurveConnection.exists_chart_hasDerivAt_coordinateFrameCombination_eq
      (I := I) (M := M) x₀ b β hβderiv (by
        rw [hβzero]
        simpa only [c] using hendpointSource)
  have hKξc : coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b ξ c = v := by
    rw [hβzero] at hKξ
    simpa only [c] using hKξ
  have hchart0 : (fun s ↦ extChartAt I x₀ (β s)) 0 = F u := by
    simpa only [hβzero, c] using hendpointChart
  have hstay : ∀ᶠ s in 𝓝 (0 : ℝ), β s ∈ (extChartAt I x₀).source :=
    hβderiv.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x₀).mem_nhds (by
        rw [hβzero]
        simpa only [c] using hendpointSource))
  have heq :
      (fun s ↦ dist x₀ ((extChartAt I x₀).symm (extChartAt I x₀ (β s)))) =ᶠ[
        𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ dist x₀ ((extChartAt I x₀).symm (F u)) -
        s * ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b ξ c‖) := by
    filter_upwards [hstay.filter_mono inf_le_left, hdecrease] with s hs hdec
    have hend : (extChartAt I x₀).symm (F u) = c := by
      rw [← hendpointChart]
      exact (extChartAt I x₀).left_inv hendpointSource
    calc
      dist x₀ ((extChartAt I x₀).symm (extChartAt I x₀ (β s))) =
          dist x₀ (β s) := by rw [(extChartAt I x₀).left_inv hs]
      _ = dist x₀ c - s * ‖v‖ := hdec
      _ = dist x₀ ((extChartAt I x₀).symm (F u)) -
          s * ‖coordinateFrameCombination
            (I := I) (M := M) (x₀ := x₀) b ξ c‖ := by
        rw [hend, hKξc]
  have hopposite := normalCoordinate_oppositeDirection_of_exactDistance_right
    (I := I) (M := M) cov x₀ b F ψ V W z hVopen hFWopen hF hψ hFWV
      hright hFzero hradial huW hFu hψFu hgauss hspeed
      (fun s ↦ extChartAt I x₀ (β s)) ξ hξ hchart0
      (by simpa only [c] using heq)
  rw [hKξc] at hopposite
  simpa only [T, c] using hopposite

/-- A radial minimizer arriving at a corner and a radial minimizer leaving it
on the same exact metric segment have positively aligned tangent directions.
The outgoing curve is read in the incoming normal chart, while exact prefix
and suffix distances provide the one-sided distance derivative. -/
theorem normalCoordinate_sameDirection_of_exactMetricCorner
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (V W : Set E) (z : E)
    (hVopen : IsOpen V) (hFWopen : IsOpen (F '' W))
    (hF : ContDiff ℝ 1 F) (hψ : ContDiffOn ℝ 1 ψ V)
    (hFWV : F '' W ⊆ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hFzero : F 0 = z)
    (hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖)
    {u : E} (huW : u ∈ W) (hFu : F u ≠ z) (hψFu : ψ (F u) = u)
    {incoming : LocalChartSecondOrderSolution I
      (coordinateAcceleration (I := I) (M := M) cov x₀ b) x₀ u}
    (hgauss : ∀ q : E,
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (incoming.velocity 1) (LocalChartSecondOrderSolution.curve incoming 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (fderiv ℝ F u q) (LocalChartSecondOrderSolution.curve incoming 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q x₀))
    (hspeed : inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (incoming.velocity 1) (LocalChartSecondOrderSolution.curve incoming 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (incoming.velocity 1) (LocalChartSecondOrderSolution.curve incoming 1)) =
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u x₀))
    {c : M} (hinCurve1 : LocalChartSecondOrderSolution.curve incoming 1 = c)
    (hendpointSource : c ∈ (extChartAt I x₀).source)
    (hendpointChart : extChartAt I x₀
      c = F u)
    {uOut : E}
    (outgoing : LocalChartSecondOrderSolution I
      (coordinateAcceleration (I := I) (M := M) cov c b) c uOut)
    (houtRadius : outgoing.radius = 2)
    {d : M} (hout1 : LocalChartSecondOrderSolution.curve outgoing 1 = d)
    (houtDist : dist c d =
      ‖coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) b uOut c‖)
    (houtSubdist : ∀ s ∈ Ioo (0 : ℝ) 1,
      dist c (LocalChartSecondOrderSolution.curve outgoing s) =
        ‖coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) b uOut c‖ * s ∧
      dist (LocalChartSecondOrderSolution.curve outgoing s) d =
        ‖coordinateFrameCombination (I := I) (M := M)
          (x₀ := c) b uOut c‖ * (1 - s))
    (hchain : dist x₀ d =
      dist x₀ c + dist c d) :
    let TIn := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b
        (incoming.velocity 1) c
    let TOut := coordinateFrameCombination
      (I := I) (M := M) (x₀ := c) b uOut c
    ‖TOut‖ • TIn = ‖TIn‖ • TOut := by
  subst c
  let c : M := LocalChartSecondOrderSolution.curve incoming 1
  let TIn : TM c := coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b (incoming.velocity 1) c
  let TOut : TM c := coordinateFrameCombination
    (I := I) (M := M) (x₀ := c) b uOut c
  let TOut0 : TM (LocalChartSecondOrderSolution.curve outgoing 0) :=
    coordinateFrameCombination (I := I) (M := M) (x₀ := c) b
      (outgoing.velocity 0) (LocalChartSecondOrderSolution.curve outgoing 0)
  dsimp only
  have hzeroOut : (0 : ℝ) ∈ Ioo (-outgoing.radius) outgoing.radius := by
    rw [houtRadius]
    norm_num
  have houtDeriv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve outgoing) 0
      (CurveConnection.timeTangentMap (I := I) 0 TOut0) := by
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    exact curve_derivative_velocity
      (I := I) (M := M) (E := E) (H := H) cov c b outgoing hzeroOut
  obtain ⟨ξ, hξ, hKξ⟩ :=
    CurveConnection.exists_chart_hasDerivAt_coordinateFrameCombination_eq
      (I := I) (M := M) x₀ b (LocalChartSecondOrderSolution.curve outgoing)
        houtDeriv (by
          rw [LocalChartSecondOrderSolution.curve_initial]
          simpa only [c] using hendpointSource)
  have hKξc : coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b ξ c = TOut := by
    dsimp only [TOut0] at hKξ
    rw [outgoing.velocity_initial] at hKξ
    have hcurve0 : LocalChartSecondOrderSolution.curve outgoing 0 = c := by
      simpa only [c] using LocalChartSecondOrderSolution.curve_initial outgoing
    rw [hcurve0] at hKξ
    simpa only [TOut] using hKξ
  have hchart0 : (fun s ↦ extChartAt I x₀
      (LocalChartSecondOrderSolution.curve outgoing s)) 0 = F u := by
    simpa only [LocalChartSecondOrderSolution.curve_initial, c] using hendpointChart
  have hgrowth := distance_along_exact_metric_tail
    (a := x₀) (c := c) (d := d)
    (beta := LocalChartSecondOrderSolution.curve outgoing)
    (C := ‖TOut‖)
    (by simp only [c, LocalChartSecondOrderSolution.curve_initial]) hout1
    (by simpa only [c] using hchain)
    (by simpa only [c, TOut] using houtDist)
    (by simpa only [c, TOut] using houtSubdist)
  have houtContinuous : ContinuousAt
      (LocalChartSecondOrderSolution.curve outgoing) 0 := houtDeriv.continuousAt
  have hstay : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve outgoing s ∈ (extChartAt I x₀).source :=
    houtContinuous.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x₀).mem_nhds (by
        simpa only [c, LocalChartSecondOrderSolution.curve_initial] using
          hendpointSource))
  have hlt : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
  have hlt' : ∀ᶠ s in 𝓝 (0 : ℝ), s < 1 := hlt
  have heq :
      (fun s ↦ dist x₀ ((extChartAt I x₀).symm
        (extChartAt I x₀ (LocalChartSecondOrderSolution.curve outgoing s)))) =ᶠ[
        𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ dist x₀ ((extChartAt I x₀).symm (F u)) +
        s * ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b ξ c‖) := by
    filter_upwards [hstay.filter_mono inf_le_left,
      hlt'.filter_mono inf_le_left, self_mem_nhdsWithin] with s hsSource hslt hs0
    rw [(extChartAt I x₀).left_inv hsSource,
      hgrowth s ⟨hs0, hslt.le⟩]
    have hcenter : (extChartAt I x₀).symm (F u) = c := by
      rw [← hendpointChart]
      exact (extChartAt I x₀).left_inv hendpointSource
    rw [hcenter]
    have hnorm :
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b ξ c‖ =
          ‖TOut‖ := by
      exact congrArg norm hKξc
    rw [hnorm]
    ring
  have halign := normalCoordinate_sameDirection_of_exactDistance_right
    (I := I) (M := M) cov x₀ b F ψ V W z hVopen hFWopen hF hψ hFWV
      hright hFzero hradial huW hFu hψFu hgauss hspeed
      (fun s ↦ extChartAt I x₀ (LocalChartSecondOrderSolution.curve outgoing s))
      ξ hξ hchart0 heq
  simpa only [TIn, c, hKξc] using halign

end BonnetMyersEntry.LocalGeodesicData
