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

public import LeanPool.PoincareGeometry.BonnetMyers.GaussLemma
public import LeanPool.PoincareGeometry.BonnetMyers.MetricBridge

/-!
# Local distance realization by normal geodesics

The integrated Gauss lemma first gives length minimization among competitors
that remain in a normal neighbourhood.  This module removes that restriction:
a path shorter than a sufficiently small radial geodesic cannot leave a
metric ball contained in the normal neighbourhood.  Consequently every point
has an open neighbourhood whose points are joined to the centre by smooth
normal geodesics realizing the intrinsic Riemannian distance.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

local notation "TM" => (TangentSpace I : M → Type _)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- A `C¹` path whose total length is smaller than a metric-ball radius never
leaves that ball, provided the metric distance agrees with Riemannian
edistance. -/
theorem contMDiffOn_mem_ball_of_pathELength_lt
    [PseudoMetricSpace M] [RiemannianBundle TM]
    {x : M} {r : ℝ} (hr : 0 < r) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1))
    (hγ0 : γ 0 = x)
    (hedist : ∀ y : M, riemannianEDist I x y = ENNReal.ofReal (dist x y))
    (hlength : pathELength I γ 0 1 < ENNReal.ofReal r) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Metric.ball x r := by
  intro t ht
  rw [Metric.mem_ball]
  have hpref : riemannianEDist I x (γ t) ≤ pathELength I γ 0 t := by
    apply riemannianEDist_le_pathELength
    · exact hγ.mono (Icc_subset_Icc_right ht.2)
    · exact hγ0
    · rfl
    · exact ht.1
  have hpref_le : pathELength I γ 0 t ≤ pathELength I γ 0 1 :=
    pathELength_mono le_rfl ht.2
  have hdist : ENNReal.ofReal (dist x (γ t)) < ENNReal.ofReal r := by
    rw [← hedist]
    exact lt_of_le_of_lt (hpref.trans hpref_le) hlength
  simpa [dist_comm] using (ENNReal.ofReal_lt_ofReal_iff hr).mp hdist

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- A length comparison valid for paths staying in a neighbourhood becomes
unrestricted below the radius of a metric ball contained in that
neighbourhood. -/
theorem pathELength_le_of_local_ball
    [PseudoMetricSpace M] [RiemannianBundle TM]
    {x y : M} {r : ℝ} (hr : 0 < r) {N : Set M}
    (hball : Metric.ball x r ⊆ N)
    (hedist : ∀ z : M, riemannianEDist I x z = ENNReal.ofReal (dist x z))
    {L : ℝ≥0∞} (hLr : L < ENNReal.ofReal r)
    (hlocal : ∀ γ : ℝ → M,
      γ 0 = x → γ 1 = y →
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N) →
      ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
      L ≤ pathELength I γ 0 1) :
    ∀ γ : ℝ → M,
      γ 0 = x → γ 1 = y →
      ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
      L ≤ pathELength I γ 0 1 := by
  intro γ hγ0 hγ1 hγ
  by_contra hnot
  have hshort : pathELength I γ 0 1 < L := lt_of_not_ge hnot
  have hstayBall := contMDiffOn_mem_ball_of_pathELength_lt
    (I := I) (M := M) hr γ hγ hγ0 hedist (hshort.trans hLr)
  exact (not_lt_of_ge (hlocal γ hγ0 hγ1
    (fun t ht ↦ hball (hstayBall t ht)) hγ)) hshort

section

variable [CompleteSpace E] [I.Boundaryless]
  [T2Space M] [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [IsManifold I ∞ M]
/-- For a smooth Riemannian metric, normal radial geodesics of sufficiently
small radial norm minimize length among all `C¹` competitors, without an
assumption that the competitor remains in the normal neighbourhood. -/
theorem exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
    (g : ContMDiffRiemannianMetric I ∞ E TM) (x₀ : M) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    let z := extChartAt I x₀ x₀
    ∃ F ψ : E → E, ∃ U V W : Set E, ∃ r : ℝ,
      IsOpen U ∧ 0 ∈ U ∧ IsOpen V ∧ z ∈ V ∧
      ContDiff ℝ 1 F ∧ ContDiffOn ℝ 1 ψ V ∧ F 0 = z ∧
      (∀ u ∈ U, ψ (F u) = u) ∧ (∀ y ∈ V, F (ψ y) = y) ∧
      (∀ u ∈ U, F u ∈ V) ∧ (∀ y ∈ V, ψ y ∈ U) ∧
      (∀ u ∈ U, F u ∈ (extChartAt I x₀).target) ∧
      IsOpen W ∧ 0 ∈ W ∧ W ⊆ U ∧
      IsOpen (F '' W) ∧ z ∈ F '' W ∧
      0 < r ∧
      Metric.ball x₀ r ⊆
        (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' V ∧
      ∀ u ∈ W,
        ∃ sol : LocalChartSecondOrderSolution I
          (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u,
          sol.radius = 2 ∧ sol.coordinate 1 = F u ∧
          pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
            ENNReal.ofReal
              ‖LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
          (∀ w : E,
            inner ℝ
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b
                    (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b
                    (fderiv ℝ F u w) (LocalChartSecondOrderSolution.curve sol 1)) =
              inner ℝ
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b u x₀)
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b w x₀)) ∧
          inner ℝ
              (LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := x₀) b
                  (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1))
              (LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := x₀) b
                  (sol.velocity 1) (LocalChartSecondOrderSolution.curve sol 1)) =
            inner ℝ
              (LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := x₀) b u x₀)
              (LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := x₀) b u x₀) ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            inner ℝ
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b
                    (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t))
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b
                    (sol.velocity t) (LocalChartSecondOrderSolution.curve sol t)) =
              inner ℝ
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b u x₀)
                (LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b u x₀)) ∧
          riemannianEDist I x₀ ((extChartAt I x₀).symm (F u)) =
            pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ∧
          dist x₀ ((extChartAt I x₀).symm (F u)) =
            ‖LocalGeodesicData.coordinateFrameCombination
              (I := I) (M := M) (x₀ := x₀) b u x₀‖ ∧
          (∀ s ∈ Ioo (0 : ℝ) 1,
            dist x₀ (LocalChartSecondOrderSolution.curve sol s) =
                ‖LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b u x₀‖ * s ∧
            dist (LocalChartSecondOrderSolution.curve sol s)
                ((extChartAt I x₀).symm (F u)) =
              ‖LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := x₀) b u x₀‖ * (1 - s)) ∧
          ∀ γ : ℝ → M,
            γ 0 = x₀ → γ 1 = (extChartAt I x₀).symm (F u) →
            ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
            pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ≤
              pathELength I γ 0 1 := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  have hcov : CovariantDerivative.IsLeviCivita cov := by
    simpa [cov] using (leviCivita_isLeviCivita (I := I) (M := M) g)
  obtain ⟨F, ψ, U, V, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hgeodesic⟩ :=
      LocalGeodesicData.exists_normalCoordinate_locally_lengthMinimizing_geodesic
        (I := I) (M := M) (E := E) cov x₀ hcov.2 hcov.1
  let N : Set M :=
    (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' V
  have hNopen : IsOpen N := by
    exact isOpen_extChartAt_preimage' (I := I) x₀ hVopen
  have hxN : x₀ ∈ N := by
    refine ⟨mem_extChartAt_source (I := I) x₀, ?_⟩
    simpa [z] using hzV
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hNopen.mem_nhds hxN)
  let L : E →ₗ[ℝ] TangentSpace I x₀ :=
    IntrinsicAcceleration.coordinateFrameLinear (I := I) (M := M) x₀ b x₀
  let W : Set E := U ∩ L ⁻¹' Metric.ball 0 r
  have hWopen : IsOpen W := by
    exact hUopen.inter (Metric.isOpen_ball.preimage L.continuous_of_finiteDimensional)
  have hzeroW : (0 : E) ∈ W := by
    refine ⟨hzeroU, ?_⟩
    change L 0 ∈ Metric.ball 0 r
    rw [LinearMap.map_zero]
    exact Metric.mem_ball_self hr
  have hWsubset : W ⊆ U := inter_subset_left
  have hFW : F '' W = V ∩ ψ ⁻¹' W := by
    ext y
    constructor
    · rintro ⟨u, huW, rfl⟩
      exact ⟨hFmemV u (hWsubset huW), by
        change ψ (F u) ∈ W
        rwa [hleft u (hWsubset huW)]⟩
    · intro hy
      exact ⟨ψ y, hy.2, hright y hy.1⟩
  have hFWopen : IsOpen (F '' W) := by
    rw [hFW]
    exact ContinuousOn.isOpen_inter_preimage hψ.continuousOn hVopen hWopen
  have hzFW : z ∈ F '' W := by
    exact ⟨0, hzeroW, hFzero⟩
  refine ⟨F, ψ, U, V, W, r, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hWopen, hzeroW,
    hWsubset, hFWopen, hzFW, hr, hball, ?_⟩
  intro u huW
  have hu : u ∈ U := hWsubset huW
  have hnorm :
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b u x₀‖ < r := by
    simpa [W, L, IntrinsicAcceleration.coordinateFrameLinear_apply,
      IntrinsicAcceleration.coordinateFrameVector] using huW.2
  obtain ⟨sol, hradius, hcoordinate, hlength, hgauss, hspeed, hspeedAll,
    hlocal⟩ := hgeodesic u hu
  have hmin : ∀ γ : ℝ → M,
      γ 0 = x₀ → γ 1 = (extChartAt I x₀).symm (F u) →
      ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
      pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ≤
        pathELength I γ 0 1 := by
    apply pathELength_le_of_local_ball (I := I) (M := M) hr hball
      (fun y ↦ finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
        (I := I) (M := M) g x₀ y)
    · rw [hlength]
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hnorm
    · intro γ hγ0 hγ1 hγN hγ
      exact hlocal γ hγ0 hγ1
        (fun t ht ↦ (hγN t ht).1) (fun t ht ↦ (hγN t ht).2) hγ
  have hcurve1 : LocalChartSecondOrderSolution.curve sol 1 =
      (extChartAt I x₀).symm (F u) := by
    change (extChartAt I x₀).symm (sol.coordinate 1) =
      (extChartAt I x₀).symm (F u)
    rw [hcoordinate]
  have hdist_le : riemannianEDist I x₀ ((extChartAt I x₀).symm (F u)) ≤
      pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 := by
    have h :=
      LocalGeodesicData.riemannianEDist_le_localChartSecondOrderSolution_pathELength
        (I := I) (M := M) sol (a := 0) (c := 1) (by rw [hradius]; norm_num)
          (by rw [hradius]; norm_num) (by norm_num)
    simpa only [LocalChartSecondOrderSolution.curve_initial, hcurve1] using h
  have hdist_ge : pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ≤
      riemannianEDist I x₀ ((extChartAt I x₀).symm (F u)) := by
    by_contra hnot
    have hdist_lt : riemannianEDist I x₀ ((extChartAt I x₀).symm (F u)) <
        pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 :=
      lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγ, hγlength⟩ :=
      exists_lt_of_riemannianEDist_lt hdist_lt
    exact (not_lt_of_ge (hmin γ hγ0 hγ1 hγ)) hγlength
  have hdistRiem := le_antisymm hdist_le hdist_ge
  have hdistMetric : dist x₀ ((extChartAt I x₀).symm (F u)) =
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b u x₀‖ := by
    rw [finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
      (I := I) (M := M) g, hdistRiem, hlength]
    exact ENNReal.toReal_ofReal (norm_nonneg _)
  have hsubdist : ∀ s ∈ Ioo (0 : ℝ) 1,
      dist x₀ (LocalChartSecondOrderSolution.curve sol s) =
          ‖LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := x₀) b u x₀‖ * s ∧
      dist (LocalChartSecondOrderSolution.curve sol s)
          ((extChartAt I x₀).symm (F u)) =
        ‖LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := x₀) b u x₀‖ * (1 - s) := by
    intro s hs
    let C : ℝ := ‖LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b u x₀‖
    have hprefixLength :=
      LocalGeodesicData.local_geodesic_pathELength_eq_initial_speed_mul_of_inner_eq
        (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hradius hspeedAll
          (a := 0) (c := s) (by norm_num) hs.1 hs.2.le
    have htailLength :=
      LocalGeodesicData.local_geodesic_pathELength_eq_initial_speed_mul_of_inner_eq
        (I := I) (M := M) (E := E) (H := H) cov x₀ b sol hradius hspeedAll
          (a := s) (c := 1) hs.1.le hs.2 (by norm_num)
    have hprefixEDist :=
      LocalGeodesicData.riemannianEDist_le_localChartSecondOrderSolution_pathELength
        (I := I) (M := M) sol (a := 0) (c := s)
          (by rw [hradius]; norm_num)
          (lt_trans hs.2 (by rw [hradius]; norm_num)) hs.1
    have htailEDist :=
      LocalGeodesicData.riemannianEDist_le_localChartSecondOrderSolution_pathELength
        (I := I) (M := M) sol (a := s) (c := 1)
          (by calc
            -sol.radius = -2 := by rw [hradius]
            _ < 0 := by norm_num
            _ < s := hs.1)
          (by rw [hradius]; norm_num) hs.2
    have hprefix : dist x₀ (LocalChartSecondOrderSolution.curve sol s) ≤ C * s := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) hs.1.le)).mp
      rw [← finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
        (I := I) (M := M) g]
      calc
        riemannianEDist I x₀ (LocalChartSecondOrderSolution.curve sol s) ≤
            pathELength I (LocalChartSecondOrderSolution.curve sol) 0 s := by
          simpa only [LocalChartSecondOrderSolution.curve_initial] using hprefixEDist
        _ = ENNReal.ofReal C * ENNReal.ofReal (s - 0) := by
          simpa only [C] using hprefixLength
        _ = ENNReal.ofReal (C * s) := by
          simpa using (ENNReal.ofReal_mul (by
            dsimp only [C]
            exact norm_nonneg _)).symm
    have htail : dist (LocalChartSecondOrderSolution.curve sol s)
        ((extChartAt I x₀).symm (F u)) ≤ C * (1 - s) := by
      apply (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hs.2.le))).mp
      rw [← finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
        (I := I) (M := M) g]
      calc
        riemannianEDist I (LocalChartSecondOrderSolution.curve sol s)
            ((extChartAt I x₀).symm (F u)) =
            riemannianEDist I (LocalChartSecondOrderSolution.curve sol s)
              (LocalChartSecondOrderSolution.curve sol 1) := by rw [hcurve1]
        _ ≤ pathELength I (LocalChartSecondOrderSolution.curve sol) s 1 := htailEDist
        _ = ENNReal.ofReal C * ENNReal.ofReal (1 - s) := by
          simpa only [C] using htailLength
        _ = ENNReal.ofReal (C * (1 - s)) := by
          exact (ENNReal.ofReal_mul (by
            dsimp only [C]
            exact norm_nonneg _)).symm
    have htriangle : C ≤ dist x₀ (LocalChartSecondOrderSolution.curve sol s) +
        dist (LocalChartSecondOrderSolution.curve sol s)
          ((extChartAt I x₀).symm (F u)) := by
      dsimp only [C]
      rw [← hdistMetric]
      exact dist_triangle _ _ _
    have hsumUpper : dist x₀ (LocalChartSecondOrderSolution.curve sol s) +
        dist (LocalChartSecondOrderSolution.curve sol s)
          ((extChartAt I x₀).symm (F u)) ≤ C := by
      calc
        _ ≤ C * s + C * (1 - s) := add_le_add hprefix htail
        _ = C := by ring
    have hsum := le_antisymm hsumUpper htriangle
    constructor
    · change dist x₀ (LocalChartSecondOrderSolution.curve sol s) = C * s
      apply le_antisymm hprefix
      linarith
    · change dist (LocalChartSecondOrderSolution.curve sol s)
          ((extChartAt I x₀).symm (F u)) = C * (1 - s)
      apply le_antisymm htail
      linarith
  exact ⟨sol, hradius, hcoordinate, hlength, hgauss, hspeed, hspeedAll,
    hdistRiem, hdistMetric, hsubdist, hmin⟩
/-- Every point has an open neighbourhood in which it is joined to each
point by a smooth radial geodesic that realizes the intrinsic Riemannian
distance and minimizes against every `C¹` competitor. -/
theorem exists_open_geodesically_distanceRealizing_neighborhood
    (g : ContMDiffRiemannianMetric I ∞ E TM) (x₀ : M) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    ∃ N : Set M, IsOpen N ∧ x₀ ∈ N ∧
      ∀ y ∈ N, ∃ u : E, ∃ sol : LocalChartSecondOrderSolution I
        (LocalGeodesicData.coordinateAcceleration cov x₀ b) x₀ u,
        sol.radius = 2 ∧
        LocalChartSecondOrderSolution.curve sol 0 = x₀ ∧
        LocalChartSecondOrderSolution.curve sol 1 = y ∧
        pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 =
          riemannianEDist I x₀ y ∧
        ∀ γ : ℝ → M,
          γ 0 = x₀ → γ 1 = y →
          ContMDiffOn (𝓘(ℝ, ℝ)) I 1 γ (Icc (0 : ℝ) 1) →
          pathELength I (LocalChartSecondOrderSolution.curve sol) 0 1 ≤
            pathELength I γ 0 1 := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  let b := IntrinsicGeodesic.canonicalBasis (E := E)
  let z : E := extChartAt I x₀ x₀
  obtain ⟨F, ψ, U, V, W, r, hUopen, hzeroU, hVopen, hzV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hWopen, hzeroW,
    hWsubset, hFWopen, hzFW, hr, hball, hgeodesic⟩ :=
      exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
        (I := I) (M := M) g x₀
  let N : Set M :=
    (extChartAt I x₀).source ∩ (extChartAt I x₀) ⁻¹' (F '' W)
  have hNopen : IsOpen N :=
    isOpen_extChartAt_preimage' (I := I) x₀ hFWopen
  have hxN : x₀ ∈ N := by
    refine ⟨mem_extChartAt_source (I := I) x₀, ?_⟩
    simpa [z] using hzFW
  refine ⟨N, hNopen, hxN, ?_⟩
  intro y hyN
  obtain ⟨u, huW, hFu⟩ := hyN.2
  obtain ⟨sol, hradius, hcoordinate, _hlength, _hgauss, _hspeed,
    _hspeedAll, hdist, _hdistMetric, _hsubdist, hmin⟩ :=
    hgeodesic u huW
  have hendpoint : (extChartAt I x₀).symm (F u) = y := by
    rw [hFu]
    exact (extChartAt I x₀).left_inv hyN.1
  have hcurve1 : LocalChartSecondOrderSolution.curve sol 1 = y := by
    change (extChartAt I x₀).symm (sol.coordinate 1) = y
    rw [hcoordinate]
    exact hendpoint
  refine ⟨u, sol, hradius, LocalChartSecondOrderSolution.curve_initial sol,
    hcurve1, ?_, ?_⟩
  · simpa only [hendpoint] using hdist.symm
  · intro γ hγ0 hγ1 hγ
    exact hmin γ hγ0 (hγ1.trans hendpoint.symm) hγ

end

end BonnetMyersEntry
