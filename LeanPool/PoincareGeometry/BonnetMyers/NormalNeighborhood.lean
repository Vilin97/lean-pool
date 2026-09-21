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

import LeanPool.PoincareGeometry.BonnetMyers.GeodesicFlowRegularity
import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicGeodesic
import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicAcceleration
import LeanPool.PoincareGeometry.BonnetMyers.GeodesicLength

/-!
# A local geodesic endpoint neighbourhood

The localized coordinate-flow inverse theorem supplies a coordinate geodesic
to each sufficiently nearby chart point.  This module transports that result
back to the manifold and packages the resulting path as an intrinsic local
geodesic.  It deliberately proves endpoint reachability only: local metric
minimization still requires the Gauss-lemma/length comparison bridge.
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

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
  (x₀ : M)

/-- A stationary cutoff flow based at the chart centre stays, for all
sufficiently small initial velocities and all unit times, in a common chart
neighbourhood where the canonical smooth frame agrees as a germ with the
coordinate frame.  The germ statement, rather than pointwise equality alone,
is what metric-compatibility differentiation consumes. -/
theorem eventually_flow_curve_has_smoothFrame_germ
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (G : E × E → E × E) (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (Φ : (E × E) → ℝ → E × E) (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hfix : ∀ t, Φ (extChartAt I x₀ x₀, 0) t = (extChartAt I x₀ x₀, 0)) :
    ∀ᶠ u in 𝓝 (0 : E), ∀ t ∈ Icc (-1 : ℝ) 1,
      let p := (Φ (extChartAt I x₀ x₀, u) t).1
      let y := (extChartAt I x₀).symm p
      p ∈ (extChartAt I x₀).target ∧
        y ∈ IntrinsicAcceleration.smoothFrameAgreementSet
          (I := I) (M := M) x₀ b ∧
        ∀ j : Fin (Module.finrank ℝ E),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[𝓝 y]
            (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j := by
  let z : E := extChartAt I x₀ x₀
  let A : Set M := IntrinsicAcceleration.smoothFrameAgreementSet
    (I := I) (M := M) x₀ b
  have hcentre : (extChartAt I x₀).symm z = x₀ := by
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have hAcoord : {p : E | (extChartAt I x₀).symm p ∈ A} ∈ 𝓝 z := by
    apply (continuousAt_extChartAt_symm (I := I) x₀).preimage_mem_nhds
    rw [hcentre]
    exact IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
      (I := I) (M := M) x₀ b
  have hcoord : (extChartAt I x₀).target ∩
      {p : E | (extChartAt I x₀).symm p ∈ A} ∈ 𝓝 z :=
    inter_mem ((isOpen_extChartAt_target (I := I) x₀).mem_nhds
      (mem_extChartAt_target x₀)) hAcoord
  obtain ⟨N, hNsub, hNopen, hzN⟩ := mem_nhds_iff.mp hcoord
  let S : Set (E × E) := N ×ˢ Set.univ
  have hS : S ∈ 𝓝 (z, 0) :=
    (hNopen.prod isOpen_univ).mem_nhds ⟨hzN, Set.mem_univ _⟩
  have hstay := eventually_forall_flow_mem_of_stationary
    (G := G) hG hGcompact hΦzero hΦcurve (z := z) (by simpa only [z] using hfix)
    hS (T := (1 : ℝ))
  filter_upwards [hstay] with u hu
  intro t ht
  let p : E := (Φ (z, u) t).1
  let y : M := (extChartAt I x₀).symm p
  have hpN : p ∈ N := (hu t ht).1
  have hpdata : p ∈ (extChartAt I x₀).target ∧
      (extChartAt I x₀).symm p ∈ A := hNsub hpN
  have hySource : y ∈ (extChartAt I x₀).source := by
    exact (extChartAt I x₀).map_target hpdata.1
  have hyagree : y ∈ A := hpdata.2
  refine ⟨hpdata.1, hyagree, ?_⟩
  intro j
  have hcoordN : {q : M | extChartAt I x₀ q ∈ N} ∈ 𝓝 y := by
    apply (continuousAt_extChartAt' (I := I) hySource).preimage_mem_nhds
    have hpy : extChartAt I x₀ y = p := (extChartAt I x₀).right_inv hpdata.1
    rw [hpy]
    exact hNopen.mem_nhds hpN
  have hsource : (extChartAt I x₀).source ∈ 𝓝 y :=
    (isOpen_extChartAt_source (I := I) x₀).mem_nhds hySource
  filter_upwards [hcoordN, hsource] with q hqN hqSource
  have hqagree : (extChartAt I x₀).symm (extChartAt I x₀ q) ∈ A :=
    (hNsub hqN).2
  rw [(extChartAt I x₀).left_inv hqSource] at hqagree
  exact hqagree.2 j

/-- Around zero initial velocity there is one open set on which the radial
flow law, the actual coordinate geodesic equation, transverse first
variations, and agreement with one smooth tangent frame all hold uniformly.
This is the common-domain package needed for a coordinate proof of the Gauss
lemma. -/
theorem exists_open_velocity_neighborhood_actual_firstVariation_smoothFrame :
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E, ∃ U : Set E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        IsOpen U ∧ 0 ∈ U ∧
        (∀ u ∈ U, ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (z, a • u) t =
            ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) ∧
        (∀ u ∈ U, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t) ∧
            G =ᶠ[𝓝 (Φ (z, u) t)]
              (fun q ↦ secondOrderSystem
                (coordinateAcceleration cov x₀ b) q)) ∧
        (∀ u ∈ U, ∀ t ∈ Icc (-1 : ℝ) 1,
          ∀ j : Fin (Module.finrank ℝ E),
            smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
              𝓝 ((extChartAt I x₀).symm (Φ (z, u) t).1)]
              (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j) ∧
        ∀ u ∈ U, ∀ w : E,
          ∃ K : NNReal, ∃ A : ℝ → ((E × E) →L[ℝ] (E × E)), ∃ W : ℝ → E × E,
            (∀ t, ‖A t‖₊ ≤ K) ∧
            (∀ t, A t = fderiv ℝ G (Φ (z, u) t)) ∧
            (∀ t ∈ Icc (-2 : ℝ) 2,
              A t = fderiv ℝ
                (fun q ↦ secondOrderSystem
                  (coordinateAcceleration cov x₀ b) q) (Φ (z, u) t)) ∧
            W 0 = (0, w) ∧
            (∀ t, HasDerivAt W (A t (W t)) t) ∧
            (∀ t ∈ Icc (-2 : ℝ) 2,
              HasDerivAt (fun s ↦ (W s).1) (W t).2 t) ∧
            (∀ t, 0 ≤ t →
              HasDerivAt (fun s : ℝ ↦ Φ (z, u + s • w) t) (W t) 0) ∧
            (∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (-2 : ℝ) 2,
              (Φ (z, u + s • w) t).1 ∈ (extChartAt I x₀).target ∧
                G (Φ (z, u + s • w) t) =
                  secondOrderSystem (coordinateAcceleration cov x₀ b)
                    (Φ (z, u + s • w) t)) := by
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  have hz : z ∈ (extChartAt I x₀).target := mem_extChartAt_target x₀
  obtain ⟨G, Φ, U, hG, hGcompact, hΦzero, hΦcurve, hΦsmooth, hend, hfix,
    hUopen, hzeroU, hradial, hactual, hvariation⟩ :=
    exists_open_velocity_neighborhood_actual_firstVariation
      (I := I) (M := M) (E := E) cov x₀ b hz
  have hframeRaw := eventually_flow_curve_has_smoothFrame_germ
      (I := I) (M := M) (E := E) (x₀ := x₀) b G hG hGcompact Φ hΦzero
        hΦcurve (by simpa only [z] using hfix)
  have hframe : ∀ᶠ u in 𝓝 (0 : E), ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ (z, u) t).1)]
          (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j := by
    filter_upwards [hframeRaw] with u hu
    intro t ht j
    exact (hu t ht).2.2 j
  have hcommon : ∀ᶠ u in 𝓝 (0 : E), u ∈ U ∧
      ∀ t ∈ Icc (-1 : ℝ) 1,
        ∀ j : Fin (Module.finrank ℝ E),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
            𝓝 ((extChartAt I x₀).symm (Φ (z, u) t).1)]
            (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j := by
    filter_upwards [hUopen.mem_nhds hzeroU, hframe] with u huU huframe
    exact ⟨huU, huframe⟩
  obtain ⟨U', hU'sub, hU'open, hzeroU'⟩ := mem_nhds_iff.mp hcommon
  refine ⟨G, Φ, U', hG, hGcompact, hΦzero, hΦcurve, hΦsmooth, hend, hfix,
    hU'open, hzeroU', ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hradial u (hU'sub hu).1
  · intro u hu
    exact hactual u (hU'sub hu).1
  · intro u hu
    exact (hU'sub hu).2
  · intro u hu w
    exact hvariation u (hU'sub hu).1 w

/-- Every point in a neighbourhood of `x₀` is the time-one endpoint of a
genuine intrinsic local geodesic issuing from `x₀`.  The returned radius is
two, so the whole segment `[-2, 2]` stays inside the coordinate chart and
satisfies the actual coordinate geodesic equation. -/
theorem exists_eventually_localGeodesic_endpoint :
    ∀ᶠ y in 𝓝 x₀, ∃ v : TangentSpace I x₀,
      ∃ γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v,
        γ.solution.radius = 2 ∧ IntrinsicGeodesic.LocalGeodesic.curve γ 1 = y := by
  obtain ⟨ψ, hψ⟩ := exists_eventually_localChartSecondOrderSolution_endpoint
    (I := I) (M := M) (E := E) cov x₀
      (IntrinsicGeodesic.canonicalBasis (E := E))
  have hcoords : ∀ᶠ y in 𝓝 x₀,
      ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))) x₀
            (ψ (extChartAt I x₀ y)),
        sol.radius = 2 ∧ sol.coordinate 1 = extChartAt I x₀ y :=
    (continuousAt_extChartAt (I := I) x₀).tendsto.eventually hψ
  filter_upwards [hcoords, extChartAt_source_mem_nhds (I := I) x₀] with y hy hsource
  obtain ⟨sol, hradius, hend⟩ := hy
  let u : E := ψ (extChartAt I x₀ y)
  let v : TangentSpace I x₀ :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x₀ u
  have hvel : coordinateVelocity (I := I) (M := M) (E := E) x₀ v = u := by
    dsimp [v, u, coordinateVelocity]
    exact (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt_symmL
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀) _
  let sol' : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))) x₀
        (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) :=
    IntrinsicGeodesic.LocalChartSecondOrderSolution.castInitialVelocity hvel sol
  let γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v :=
    ⟨sol', local_solution_isCoordinateGeodesic
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀)
        (b := IntrinsicGeodesic.canonicalBasis (E := E)) sol'⟩
  refine ⟨v, γ, ?_, ?_⟩
  · change sol'.radius = 2
    dsimp [sol']
    rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.radius_castInitialVelocity]
    exact hradius
  · change LocalChartSecondOrderSolution.curve γ.solution 1 = y
    change (extChartAt I x₀).symm (sol'.coordinate 1) = y
    dsimp [sol']
    rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.coordinate_castInitialVelocity]
    rw [hend]
    exact (extChartAt I x₀).left_inv hsource

/-- A normal-endpoint neighbourhood with its radial coordinate identity made
explicit on the manifold curve.  The same local inverse `ψ` recovers the
scaled initial coordinate velocity at every point of the returned geodesic
segment.

This is the radial normal-coordinate input for a Gauss-lemma proof; it does
not by itself establish that the segment minimizes Riemannian distance. -/
theorem exists_eventually_localGeodesic_endpoint_radial :
    ∃ ψ : E → E, ∃ V : Set E,
      IsOpen V ∧ extChartAt I x₀ x₀ ∈ V ∧ ContDiffOn ℝ 1 ψ V ∧
      (∀ y ∈ V, Function.Bijective (fderiv ℝ ψ y)) ∧
      ContDiffAt ℝ 1 ψ (extChartAt I x₀ x₀) ∧
      HasStrictFDerivAt ψ (ContinuousLinearMap.id ℝ E) (extChartAt I x₀ x₀) ∧
      ψ (extChartAt I x₀ x₀) = 0 ∧
      ∀ᶠ y in 𝓝 x₀, extChartAt I x₀ y ∈ V ∧ ∃ v : TangentSpace I x₀,
      ∃ γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v,
        γ.solution.radius = 2 ∧ IntrinsicGeodesic.LocalGeodesic.curve γ 1 = y ∧
          (∀ a ∈ Icc (0 : ℝ) 1,
            extChartAt I x₀ (IntrinsicGeodesic.LocalGeodesic.curve γ a) ∈ V ∧
            ψ (extChartAt I x₀ (IntrinsicGeodesic.LocalGeodesic.curve γ a)) =
              a • coordinateVelocity (I := I) (M := M) (E := E) x₀ v) ∧
          ∀ a ∈ Ioo (0 : ℝ) 1,
            fderiv ℝ ψ
              (extChartAt I x₀ (IntrinsicGeodesic.LocalGeodesic.curve γ a))
              (γ.solution.velocity a) =
                coordinateVelocity (I := I) (M := M) (E := E) x₀ v := by
  obtain ⟨ψ, V, hVopen, hzV, hψon, hψbij, hψsmooth, hψstrict, hψzero, hψ⟩ :=
    exists_eventually_localChartSecondOrderSolution_endpoint_radial
    (I := I) (M := M) (E := E) cov x₀
      (IntrinsicGeodesic.canonicalBasis (E := E))
  have hcoords : ∀ᶠ y in 𝓝 x₀,
      extChartAt I x₀ y ∈ V ∧ ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))) x₀
            (ψ (extChartAt I x₀ y)),
        sol.radius = 2 ∧ sol.coordinate 1 = extChartAt I x₀ y ∧
          (∀ a ∈ Icc (0 : ℝ) 1, sol.coordinate a ∈ V) ∧
          (∀ a ∈ Icc (0 : ℝ) 1, ψ (sol.coordinate a) =
            a • ψ (extChartAt I x₀ y)) ∧
          ∀ a ∈ Ioo (0 : ℝ) 1,
            fderiv ℝ ψ (sol.coordinate a) (sol.velocity a) =
              ψ (extChartAt I x₀ y) :=
    (continuousAt_extChartAt (I := I) x₀).tendsto.eventually hψ
  refine ⟨ψ, V, hVopen, hzV, hψon, hψbij, hψsmooth, hψstrict, hψzero, ?_⟩
  filter_upwards [hcoords, extChartAt_source_mem_nhds (I := I) x₀] with y hy hsource
  obtain ⟨hyV, sol, hradius, hend, hVpath, hradial, hderiv⟩ := hy
  let u : E := ψ (extChartAt I x₀ y)
  let v : TangentSpace I x₀ :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x₀ u
  have hvel : coordinateVelocity (I := I) (M := M) (E := E) x₀ v = u := by
    dsimp [v, u, coordinateVelocity]
    exact (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt_symmL
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀) _
  let sol' : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))) x₀
        (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) :=
    IntrinsicGeodesic.LocalChartSecondOrderSolution.castInitialVelocity hvel sol
  let γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v :=
    ⟨sol', local_solution_isCoordinateGeodesic
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀)
        (b := IntrinsicGeodesic.canonicalBasis (E := E)) sol'⟩
  refine ⟨hyV, v, γ, ?_, ?_, ?_, ?_⟩
  · change sol'.radius = 2
    dsimp [sol']
    rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.radius_castInitialVelocity]
    exact hradius
  · change LocalChartSecondOrderSolution.curve γ.solution 1 = y
    change (extChartAt I x₀).symm (sol'.coordinate 1) = y
    dsimp [sol']
    rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.coordinate_castInitialVelocity]
    rw [hend]
    exact (extChartAt I x₀).left_inv hsource
  · intro a ha
    have hradius' : sol'.radius = 2 := by
      dsimp [sol']
      rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.radius_castInitialVelocity]
      exact hradius
    have haint : a ∈ Ioo (-sol'.radius) sol'.radius := by
      rw [hradius']
      constructor <;> linarith [ha.1, ha.2]
    constructor
    · change extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol' a) ∈ V
      rw [LocalChartSecondOrderSolution.curve_eq_chart sol' haint]
      dsimp [sol']
      rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.coordinate_castInitialVelocity]
      exact hVpath a ha
    · change ψ (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol' a)) =
        a • coordinateVelocity (I := I) (M := M) (E := E) x₀ v
      rw [LocalChartSecondOrderSolution.curve_eq_chart sol' haint]
      dsimp [sol']
      rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.coordinate_castInitialVelocity]
      rw [hvel]
      exact hradial a ha
  · intro a ha
    have hradius' : sol'.radius = 2 := by
      dsimp [sol']
      rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.radius_castInitialVelocity]
      exact hradius
    have haint : a ∈ Ioo (-sol'.radius) sol'.radius := by
      rw [hradius']
      constructor <;> linarith [ha.1, ha.2]
    change fderiv ℝ ψ
      (extChartAt I x₀ (LocalChartSecondOrderSolution.curve sol' a))
      (sol'.velocity a) = coordinateVelocity (I := I) (M := M) (E := E) x₀ v
    rw [LocalChartSecondOrderSolution.curve_eq_chart sol' haint]
    dsimp [sol']
    rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.coordinate_castInitialVelocity]
    rw [IntrinsicGeodesic.LocalChartSecondOrderSolution.velocity_castInitialVelocity]
    rw [hvel]
    exact hderiv a ha

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- The radial normal-coordinate identity differentiates to the initial
coordinate velocity on the open unit segment.  This conclusion is obtained
from the exact radial identity itself, so no unproved regularity of the local
inverse is being assumed. -/
theorem hasDerivAt_coordinateInverse_along_radial
    (ψ : E → E) {v : TangentSpace I x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v)
    (hradial : ∀ a ∈ Icc (0 : ℝ) 1,
      ψ (extChartAt I x₀ (IntrinsicGeodesic.LocalGeodesic.curve γ a)) =
        a • coordinateVelocity (I := I) (M := M) (E := E) x₀ v)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s ↦ ψ (extChartAt I x₀ (IntrinsicGeodesic.LocalGeodesic.curve γ s)))
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) a := by
  have hlinear : HasDerivAt
      (fun s : ℝ ↦ s • coordinateVelocity (I := I) (M := M) (E := E) x₀ v)
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) a := by
    simpa using (hasDerivAt_id' a).smul_const
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v)
  apply hlinear.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with s hs
  exact hradial s ⟨le_of_lt hs.1, le_of_lt hs.2⟩

omit [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- A local geodesic whose coordinate radius exceeds one is a genuine `C¹`
manifold path on the closed unit interval. -/
theorem localGeodesic_contMDiffOn_curve_Icc_zero_one
    {v : TangentSpace I x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v)
    (hradius : 1 < γ.solution.radius) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I 1
      (IntrinsicGeodesic.LocalGeodesic.curve γ) (Icc (0 : ℝ) 1) := by
  change ContMDiffOn (𝓘(ℝ, ℝ)) I 1
    (LocalChartSecondOrderSolution.curve γ.solution) (Icc (0 : ℝ) 1)
  exact localChartSecondOrderSolution_contMDiffOn_curve (I := I) γ.solution
    (by linarith) hradius (by norm_num)

omit [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- The local endpoint geodesics above are valid competitors for Riemannian
distance on `[0,1]`.  This is an upper bound only; it intentionally does not
assert the missing local minimizing property. -/
theorem localGeodesic_riemannianEDist_le_pathELength_Icc_zero_one
    {v : TangentSpace I x₀}
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v)
    (hradius : 1 < γ.solution.radius) :
    riemannianEDist I (IntrinsicGeodesic.LocalGeodesic.curve γ 0)
        (IntrinsicGeodesic.LocalGeodesic.curve γ 1) ≤
      pathELength I (IntrinsicGeodesic.LocalGeodesic.curve γ) 0 1 := by
  exact riemannianEDist_le_pathELength
    (localGeodesic_contMDiffOn_curve_Icc_zero_one (I := I) (M := M)
      cov x₀ γ hradius)
    rfl rfl (by norm_num)

/-- The nearby endpoint construction returns an actual smooth geodesic path
and its ordinary Riemannian-distance upper bound, in addition to endpoint
reachability. -/
theorem exists_eventually_smooth_localGeodesic_endpoint :
    ∀ᶠ y in 𝓝 x₀, ∃ v : TangentSpace I x₀,
      ∃ γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v,
        IntrinsicGeodesic.LocalGeodesic.curve γ 1 = y ∧
        ContMDiffOn (𝓘(ℝ, ℝ)) I 1
          (IntrinsicGeodesic.LocalGeodesic.curve γ) (Icc (0 : ℝ) 1) ∧
        riemannianEDist I (IntrinsicGeodesic.LocalGeodesic.curve γ 0)
            (IntrinsicGeodesic.LocalGeodesic.curve γ 1) ≤
          pathELength I (IntrinsicGeodesic.LocalGeodesic.curve γ) 0 1 := by
  filter_upwards [exists_eventually_localGeodesic_endpoint
      (I := I) (M := M) (E := E) cov x₀] with y hy
  obtain ⟨v, γ, hradius, hend⟩ := hy
  have hlarge : 1 < γ.solution.radius := by linarith
  exact ⟨v, γ, hend,
    localGeodesic_contMDiffOn_curve_Icc_zero_one (I := I) (M := M)
      cov x₀ γ hlarge,
    localGeodesic_riemannianEDist_le_pathELength_Icc_zero_one (I := I) (M := M)
      cov x₀ γ hlarge⟩

/-- A genuinely open normal-endpoint neighbourhood.  Each of its points is
reached by a smooth coordinate-geodesic segment from the centre.  The result
does not call those segments minimizing; that remains the separate
Gauss-lemma step. -/
theorem exists_open_localGeodesic_endpoint_neighborhood :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∀ y ∈ U, ∃ v : TangentSpace I x₀,
        ∃ γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v,
          γ.solution.radius = 2 ∧
          IntrinsicGeodesic.LocalGeodesic.curve γ 1 = y ∧
          ContMDiffOn (𝓘(ℝ, ℝ)) I 1
            (IntrinsicGeodesic.LocalGeodesic.curve γ) (Icc (0 : ℝ) 1) := by
  obtain ⟨U, hsub, hUopen, hxU⟩ := mem_nhds_iff.mp
    (exists_eventually_localGeodesic_endpoint (I := I) (M := M) (E := E) cov x₀)
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  obtain ⟨v, γ, hradius, hend⟩ := hsub hy
  have hlarge : 1 < γ.solution.radius := by linarith
  exact ⟨v, γ, hradius, hend,
    localGeodesic_contMDiffOn_curve_Icc_zero_one (I := I) (M := M)
      cov x₀ γ hlarge⟩

end LocalGeodesicData

end BonnetMyersEntry
