/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentLog
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Regularity of distance in normal coordinates

On the punctured image of a sufficiently small normal coordinate chart, the
finite intrinsic distance from the centre is exactly the norm of the smooth
logarithm coordinate.  This module records the resulting `C¹` regularity,
which is the differentiable input for the remaining corner-rigidity step.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

/-- In a real inner-product space, the derivative of the norm of a nonzero
smooth vector-valued map is the normalized inner product with that vector. -/
theorem hasFDerivAt_norm_comp_inner
    {G F : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : G → F} {f' : G →L[ℝ] F} {x : G}
    (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => ‖f y‖)
      ((1 / ‖f x‖) • (innerSL ℝ (f x)).comp f') x := by
  have hs := hf.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  rw [show (fun y => ‖f y‖) = (fun y => Real.sqrt (‖f y‖ ^ 2)) by
    funext y
    exact (Real.sqrt_sq (norm_nonneg _)).symm]
  convert hs using 1
  ext y
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Real.sqrt_sq (norm_nonneg _), two_smul, add_apply]
  field_simp
  ring

/-- The differentials of two `C¹` local inverses compose to the identity at
every point of the open target. -/
theorem fderiv_comp_fderiv_eq_id_of_rightInverseOn
    {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (F : F₁ → F₂) (ψ : F₂ → F₁) (V : Set F₂)
    (hVopen : IsOpen V) (hF : ContDiff ℝ 1 F)
    (hψ : ContDiffOn ℝ 1 ψ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    {y : F₂} (hy : y ∈ V) :
    (fderiv ℝ F (ψ y)).comp (fderiv ℝ ψ y) =
      ContinuousLinearMap.id ℝ F₂ := by
  have hψat : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
    (hψ.contDiffAt (hVopen.mem_nhds hy)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hFat : HasFDerivAt F (fderiv ℝ F (ψ y)) (ψ y) :=
    (hF.differentiable one_ne_zero (ψ y)).hasFDerivAt
  have hcomp : HasFDerivAt (fun x ↦ F (ψ x))
      ((fderiv ℝ F (ψ y)).comp (fderiv ℝ ψ y)) y :=
    hFat.comp y hψat
  have heq : (fun x : F₂ ↦ x) =ᶠ[𝓝 y] (fun x ↦ F (ψ x)) := by
    filter_upwards [hVopen.mem_nhds hy] with x hx
    exact (hright x hx).symm
  have hid : HasFDerivAt (fun x : F₂ ↦ x)
      ((fderiv ℝ F (ψ y)).comp (fderiv ℝ ψ y)) y :=
    hcomp.congr_of_eventuallyEq heq
  exact hid.unique (hasFDerivAt_id y)

/-- Algebraic endpoint form of the first variation formula.  An inverse
differential and the Gauss pairing convert the normalized radial covector at
the initial point into normalized pairing with terminal radial velocity. -/
theorem endpoint_distance_differential_eq_inner
    {E X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (L : E →L[ℝ] X) (K : E →L[ℝ] Y)
    (DF Dψ : E →L[ℝ] E) (u : E) (T : Y)
    (hinverse : DF.comp Dψ = ContinuousLinearMap.id ℝ E)
    (hgauss : ∀ w : E, inner ℝ T (K (DF w)) = inner ℝ (L u) (L w))
    (hspeed : inner ℝ T T = inner ℝ (L u) (L u))
    (hu : L u ≠ 0) (ξ : E) :
    (((1 / ‖L u‖) • (innerSL ℝ (L u)).comp (L.comp Dψ)) ξ) =
      inner ℝ T (K ξ) / ‖T‖ := by
  have hnorm : ‖T‖ = ‖L u‖ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hspeed
    nlinarith [norm_nonneg T, norm_nonneg (L u)]
  have hinverse_apply : DF (Dψ ξ) = ξ := by
    have h := congrArg (fun A : E →L[ℝ] E ↦ A ξ) hinverse
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  have hg := hgauss (Dψ ξ)
  rw [hinverse_apply] at hg
  rw [hg, hnorm]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  field_simp

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [PseudoMetricSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- If normal coordinates identify distance from the centre with the norm of
the logarithm vector, that distance function is `C¹` off the centre. -/
theorem normalCoordinate_dist_contDiffOn_punctured
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (V W : Set E) (z : E)
    (hψ : ContDiffOn ℝ 1 ψ V)
    (hFWV : F '' W ⊆ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hFzero : F 0 = z)
    (hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖) :
    ContDiffOn ℝ 1 (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
      ((F '' W) \ {z}) := by
  let L : E →L[ℝ] TM x₀ :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
  have hψ' : ContDiffOn ℝ 1 ψ ((F '' W) \ {z}) :=
    hψ.mono (fun _ hy ↦ hFWV hy.1)
  have hLψ : ContDiffOn ℝ 1 (fun y ↦ L (ψ y)) ((F '' W) \ {z}) :=
    L.contDiff.comp_contDiffOn hψ'
  have hnonzero : ∀ y ∈ (F '' W) \ {z}, L (ψ y) ≠ 0 := by
    intro y hy hzero
    have hinjL : Function.Injective L := by
      exact CurveConnection.coordinateFrameLinear_injective_of_mem_source
        (I := I) (M := M) x₀ b (mem_extChartAt_source (I := I) x₀)
    have hψzero : ψ y = 0 := by
      apply hinjL
      simpa using hzero
    have hyz : y = z := by
      calc
        y = F (ψ y) := (hright y (hFWV hy.1)).symm
        _ = F 0 := by rw [hψzero]
        _ = z := hFzero
    exact hy.2 (by simpa using hyz)
  have hsmooth : ContDiffOn ℝ 1 (fun y ↦ ‖L (ψ y)‖) ((F '' W) \ {z}) :=
    hLψ.norm ℝ hnonzero
  apply hsmooth.congr
  intro y hy
  rw [hradial y hy.1]
  rfl

/-- The explicit derivative of normal-coordinate distance away from the
centre: normalized radial pairing, transported through the logarithm map. -/
theorem normalCoordinate_dist_hasFDerivAt
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F ψ : E → E) (V W : Set E) (z : E)
    (hVopen : IsOpen V)
    (hFWopen : IsOpen (F '' W))
    (hψ : ContDiffOn ℝ 1 ψ V)
    (hFWV : F '' W ⊆ V)
    (hright : ∀ y ∈ V, F (ψ y) = y)
    (hFzero : F 0 = z)
    (hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖)
    {y : E} (hy : y ∈ (F '' W) \ {z}) :
    let L : E →L[ℝ] TM x₀ :=
      (IntrinsicAcceleration.coordinateFrameLinear
        (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
    HasFDerivAt (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
      ((1 / ‖L (ψ y)‖) •
        (innerSL ℝ (L (ψ y))).comp (L.comp (fderiv ℝ ψ y))) y := by
  let L : E →L[ℝ] TM x₀ :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
  dsimp only
  have hinjL : Function.Injective L := by
    exact CurveConnection.coordinateFrameLinear_injective_of_mem_source
      (I := I) (M := M) x₀ b (mem_extChartAt_source (I := I) x₀)
  have hnonzero : L (ψ y) ≠ 0 := by
    intro hzero
    have hψzero : ψ y = 0 := by
      apply hinjL
      simpa using hzero
    have hyz : y = z := by
      calc
        y = F (ψ y) := (hright y (hFWV hy.1)).symm
        _ = F 0 := by rw [hψzero]
        _ = z := hFzero
    exact hy.2 (by simpa using hyz)
  have hψat : HasFDerivAt ψ (fderiv ℝ ψ y) y := by
    exact (hψ.contDiffAt (hVopen.mem_nhds (hFWV hy.1))).differentiableAt
      one_ne_zero |>.hasFDerivAt
  have hLψ : HasFDerivAt (fun y ↦ L (ψ y))
      (L.comp (fderiv ℝ ψ y)) y :=
    L.hasFDerivAt.comp y hψat
  have hnorm := hasFDerivAt_norm_comp_inner hLψ hnonzero
  apply hnorm.congr_of_eventuallyEq
  filter_upwards [hFWopen.mem_nhds hy.1] with y' hy'
  exact hradial y' hy'

/-- Endpoint first variation formula in chart coordinates.  The differential
of distance from the centre pairs an arbitrary endpoint direction with the
terminal radial velocity and divides by radial speed. -/
theorem normalCoordinate_dist_fderiv_apply_eq_endpoint_inner
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
    (ξ : E) :
    fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u) ξ =
      inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ξ (LocalChartSecondOrderSolution.curve sol 1)) /
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)‖ := by
  let L : E →L[ℝ] TM x₀ :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
  let K : E →L[ℝ] TM (LocalChartSecondOrderSolution.curve sol 1) :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b
        (LocalChartSecondOrderSolution.curve sol 1)).toContinuousLinearMap
  have hLapply (q : E) : L q =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q x₀ := rfl
  have hKapply (q : E) : K q =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b q
        (LocalChartSecondOrderSolution.curve sol 1) := rfl
  have hy : F u ∈ (F '' W) \ {z} :=
    ⟨⟨u, huW, rfl⟩, by simpa using hFu⟩
  have hd := normalCoordinate_dist_hasFDerivAt
    (I := I) (M := M) x₀ b F ψ V W z hVopen hFWopen hψ hFWV
      hright hFzero hradial hy
  have hd_apply := congrArg (fun A : E →L[ℝ] ℝ ↦ A ξ) hd.fderiv
  have hinverse : (fderiv ℝ F u).comp (fderiv ℝ ψ (F u)) =
      ContinuousLinearMap.id ℝ E := by
    simpa only [hψFu] using fderiv_comp_fderiv_eq_id_of_rightInverseOn
      F ψ V hVopen hF hψ hright (hFWV hy.1)
  have hLu : L u ≠ 0 := by
    have hinj := CurveConnection.coordinateFrameLinear_injective_of_mem_source
      (I := I) (M := M) x₀ b (mem_extChartAt_source (I := I) x₀)
    intro hzero
    have hu0 : u = 0 := by
      apply hinj
      change L u = L 0
      simpa using hzero
    exact hFu (hu0 ▸ hFzero)
  have halgebra := endpoint_distance_differential_eq_inner L K
    (fderiv ℝ F u) (fderiv ℝ ψ (F u)) u
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
      (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
    hinverse (by simpa only [hLapply, hKapply] using hgauss)
    (by simpa only [hLapply] using hspeed) hLu ξ
  rw [hψFu] at hd_apply
  change fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u) ξ =
    (((1 / ‖L u‖) •
      (innerSL ℝ (L u)).comp (L.comp (fderiv ℝ ψ (F u)))) ξ) at hd_apply
  exact hd_apply.trans (by simpa only [hKapply] using halgebra)

end LocalGeodesicData

section

variable [T3Space M] [ConnectedSpace M]
/-- A smooth Riemannian metric admits normal coordinates in which the finite
metric distance from the centre is the norm of the logarithm coordinate; in
particular this distance is `C¹` away from the centre. -/
theorem exists_normalCoordinate_dist_contDiffOn_punctured
    (g : ContMDiffRiemannianMetric I ∞ E TM) (x₀ : M) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F ψ : E → E, ∃ V W : Set E,
      IsOpen V ∧ IsOpen W ∧ IsOpen (F '' W) ∧
      z ∈ F '' W ∧ F '' W ⊆ V ∧
      ContDiff ℝ 1 F ∧ ContDiffOn ℝ 1 ψ V ∧ F 0 = z ∧
      (∀ y ∈ V, F (ψ y) = y) ∧
      (∀ y ∈ V,
        (fderiv ℝ F (ψ y)).comp (fderiv ℝ ψ y) =
          ContinuousLinearMap.id ℝ E) ∧
      (∀ y ∈ F '' W,
        dist x₀ ((extChartAt I x₀).symm y) =
          ‖LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖) ∧
      ContDiffOn ℝ 1 (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
        ((F '' W) \ {z}) ∧
      (∀ y ∈ (F '' W) \ {z},
        let L : E →L[ℝ] TM x₀ :=
          (IntrinsicAcceleration.coordinateFrameLinear
            (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
        HasFDerivAt (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
          ((1 / ‖L (ψ y)‖) •
            (innerSL ℝ (L (ψ y))).comp (L.comp (fderiv ℝ ψ y))) y) ∧
      (∀ u ∈ W, F u ≠ z →
        ∃ sol : LocalChartSecondOrderSolution I
          (LocalGeodesicData.coordinateAcceleration
            (leviCivita (I := I) (M := M) g) x₀ b) x₀ u,
          sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
          ∀ ξ : E,
            fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u) ξ =
              inner ℝ
                  (LocalGeodesicData.coordinateFrameCombination
                    (I := I) (M := M) (x₀ := x₀) b
                      (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
                  (LocalGeodesicData.coordinateFrameCombination
                    (I := I) (M := M) (x₀ := x₀) b ξ
                      (LocalChartSecondOrderSolution.curve sol 1)) /
                ‖LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b
                    (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)‖) := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  dsimp only
  obtain ⟨F, ψ, U, V, W, r, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hWopen, hzeroW,
    hWsubset, hFWopen, hzFW, hr, hball, hgeodesic⟩ :=
      exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
        (I := I) (M := M) g x₀
  have hFWV : F '' W ⊆ V := by
    rintro y ⟨u, huW, rfl⟩
    exact hFmemV u (hWsubset huW)
  have hradial : ∀ y ∈ F '' W,
      dist x₀ ((extChartAt I x₀).symm y) =
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := x₀) b (ψ y) x₀‖ := by
    intro y hy
    obtain ⟨u, huW, rfl⟩ := hy
    obtain ⟨sol, hradius, hcoordinate, hlength, _hgauss, _hspeed,
      _hspeedAll, hdistRiem, hdistMetric, _hsubdist, hmin⟩ := hgeodesic u huW
    simpa only [hleft u (hWsubset huW)] using hdistMetric
  have hsmooth := LocalGeodesicData.normalCoordinate_dist_contDiffOn_punctured
    (I := I) (M := M) x₀ b F ψ V W z hψ hFWV hright hFzero hradial
  have hderiv : ∀ y ∈ (F '' W) \ {z},
      let L : E →L[ℝ] TM x₀ :=
        (IntrinsicAcceleration.coordinateFrameLinear
          (I := I) (M := M) x₀ b x₀).toContinuousLinearMap
      HasFDerivAt (fun y ↦ dist x₀ ((extChartAt I x₀).symm y))
        ((1 / ‖L (ψ y)‖) •
          (innerSL ℝ (L (ψ y))).comp (L.comp (fderiv ℝ ψ y))) y := by
    intro y hy
    exact LocalGeodesicData.normalCoordinate_dist_hasFDerivAt
      (I := I) (M := M) x₀ b F ψ V W z hVopen hFWopen hψ hFWV
        hright hFzero hradial hy
  have hinverseDeriv : ∀ y ∈ V,
      (fderiv ℝ F (ψ y)).comp (fderiv ℝ ψ y) =
        ContinuousLinearMap.id ℝ E := by
    intro y hy
    exact fderiv_comp_fderiv_eq_id_of_rightInverseOn
      F ψ V hVopen hF hψ hright hy
  have hfirstVariation : ∀ u ∈ W, F u ≠ z →
      ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration
          (leviCivita (I := I) (M := M) g) x₀ b) x₀ u,
        sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
        ∀ ξ : E,
          fderiv ℝ (fun y ↦ dist x₀ ((extChartAt I x₀).symm y)) (F u) ξ =
            inner ℝ
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b
                    (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b ξ
                    (LocalChartSecondOrderSolution.curve sol 1)) /
              ‖LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := x₀) b
                  (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)‖ := by
    intro u huW hFu
    obtain ⟨sol, hradius, hcoordinate, _hlength, hgauss, hspeed,
      _hspeedAll, _hdistRiem, _hdistMetric, _hsubdist, _hmin⟩ := hgeodesic u huW
    refine ⟨sol, hradius, hcoordinate, ?_⟩
    intro ξ
    exact LocalGeodesicData.normalCoordinate_dist_fderiv_apply_eq_endpoint_inner
      (I := I) (M := M) (leviCivita (I := I) (M := M) g) x₀ b
        F ψ V W z hVopen hFWopen hF hψ hFWV hright hFzero hradial
        huW hFu (hleft u (hWsubset huW)) hgauss hspeed ξ
  exact ⟨F, ψ, V, W, hVopen, hWopen, hFWopen, hzFW, hFWV, hF, hψ,
    hFzero, hright, hinverseDeriv, hradial, hsmooth, hderiv, hfirstVariation⟩

end
end BonnetMyersEntry
