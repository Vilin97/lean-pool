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

public import LeanPool.PoincareGeometry.BonnetMyers.NormalCornerRigidity
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentLog

/-!
# Corner alignment along exact Riemannian metric segments

An incoming normal neighbourhood based at one segment point is retained while
the next segment point varies.  From every later point in that neighbourhood,
a sufficiently short outgoing normal connector has tangent direction aligned
with the incoming connector.  This is the local compatibility statement needed
to replace a continuous metric segment by one smooth geodesic.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- Fix an earlier parameter `r` of an exact metric segment.  There is an open
normal neighbourhood of `γ r` such that, whenever `t > r` lies in it, the
normal connector from `γ r` to `γ t` aligns with every sufficiently short
outgoing normal connector from `γ t` along the segment. -/
theorem riemannian_metric_segment_exists_normal_corner_alignment
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    let b := IntrinsicGeodesic.canonicalBasis (E := E)
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ p q, riemannianEDist I (γ p) (γ q) =
        ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
      ∀ r : MetricHopfRinow.SegmentParameter x z,
        ∃ N : Set M, IsOpen N ∧ γ r ∈ N ∧
          ∀ t : MetricHopfRinow.SegmentParameter x z, γ t ∈ N →
            (r : ℝ) < (t : ℝ) →
            ∃ uIn : E, ∃ incoming : LocalChartSecondOrderSolution I
              (LocalGeodesicData.coordinateAcceleration cov (γ r) b) (γ r) uIn,
              incoming.radius = 2 ∧
              LocalChartSecondOrderSolution.curve incoming 0 = γ r ∧
              LocalChartSecondOrderSolution.curve incoming 1 = γ t ∧
              ‖LocalGeodesicData.coordinateFrameCombination
                (I := I) (M := M) (x₀ := γ r) b
                  (incoming.velocity 1) (γ t)‖ =
                (t : ℝ) - (r : ℝ) ∧
              (∀ (β : ℝ → M) (v : TM (γ t)),
                HasMFDerivAt (𝓘(ℝ, ℝ)) I β 0
                    (CurveConnection.timeTangentMap (I := I) 0 v) →
                β 0 = γ t →
                (fun s ↦ dist (γ r) (β s)) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
                    (fun s ↦ dist (γ r) (γ t) - s * ‖v‖) →
                let TIn := LocalGeodesicData.coordinateFrameCombination
                  (I := I) (M := M) (x₀ := γ r) b
                    (incoming.velocity 1) (γ t)
                ‖v‖ • TIn = -(‖TIn‖ • v)) ∧
              ∃ ε > (0 : ℝ),
                ∀ s : MetricHopfRinow.SegmentParameter x z,
                  (t : ℝ) < (s : ℝ) → (s : ℝ) - (t : ℝ) < ε →
                  ∃ uOut : E, ∃ outgoing : LocalChartSecondOrderSolution I
                    (LocalGeodesicData.coordinateAcceleration cov (γ t) b) (γ t) uOut,
                    outgoing.radius = 2 ∧
                    LocalChartSecondOrderSolution.curve outgoing 0 = γ t ∧
                    LocalChartSecondOrderSolution.curve outgoing 1 = γ s ∧
                    let TIn := LocalGeodesicData.coordinateFrameCombination
                      (I := I) (M := M) (x₀ := γ r) b
                        (incoming.velocity 1) (γ t)
                    let TOut := LocalGeodesicData.coordinateFrameCombination
                      (I := I) (M := M) (x₀ := γ t) b uOut (γ t)
                    ‖TIn‖ = (t : ℝ) - (r : ℝ) ∧
                    ‖TOut‖ = (s : ℝ) - (t : ℝ) ∧
                    ‖TOut‖ • TIn = ‖TIn‖ • TOut ∧
                    ((t : ℝ) - (r : ℝ))⁻¹ • TIn =
                      ((s : ℝ) - (t : ℝ))⁻¹ • TOut := by
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
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  dsimp only
  intro x z γ hγ hsegment r
  have hdist (p q : MetricHopfRinow.SegmentParameter x z) :
      dist (γ p) (γ q) = |(q : ℝ) - (p : ℝ)| := by
    rw [finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
      (I := I) (M := M) g, hsegment p q,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  let zr : E := extChartAt I (γ r) (γ r)
  obtain ⟨F, ψ, U, V, W, radius, hUopen, hzeroU, hVopen, hzrV, hF, hψ,
    hFzero, hleft, hright, hFmemV, hψmemU, hFtarget, hWopen, hzeroW,
    hWsubset, hFWopen, hzrFW, hradiusPos, hball, hgeodesic⟩ :=
      exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
        (I := I) (M := M) g (γ r)
  let N : Set M :=
    (extChartAt I (γ r)).source ∩
      (extChartAt I (γ r)) ⁻¹' (F '' W)
  have hNopen : IsOpen N :=
    isOpen_extChartAt_preimage' (I := I) (γ r) hFWopen
  have hrN : γ r ∈ N := by
    refine ⟨mem_extChartAt_source (I := I) (γ r), ?_⟩
    change extChartAt I (γ r) (γ r) ∈ F '' W
    simpa only [zr] using hzrFW
  refine ⟨N, hNopen, hrN, ?_⟩
  intro t htN hrt
  obtain ⟨uIn, huInW, hFuIn⟩ := htN.2
  obtain ⟨incoming, hinRadius, hinCoordinate, _hinLength, hinGauss,
    hinSpeed, _hinSpeedAll, _hinDistRiem, hinDist, _hinSubdist, _hinMin⟩ :=
      hgeodesic uIn huInW
  have hinEndpoint : (extChartAt I (γ r)).symm (F uIn) = γ t := by
    rw [hFuIn]
    exact (extChartAt I (γ r)).left_inv htN.1
  have hinCurve1 : LocalChartSecondOrderSolution.curve incoming 1 = γ t := by
    change (extChartAt I (γ r)).symm (incoming.coordinate 1) = γ t
    rw [hinCoordinate]
    exact hinEndpoint
  have hFuInNe : F uIn ≠ zr := by
    intro heq
    have hpoints : γ t = γ r := by
      calc
        γ t = (extChartAt I (γ r)).symm (F uIn) := hinEndpoint.symm
        _ = (extChartAt I (γ r)).symm zr := by rw [heq]
        _ = γ r := (extChartAt I (γ r)).left_inv
          (mem_extChartAt_source (I := I) (γ r))
    have hzero : dist (γ r) (γ t) = 0 := by rw [hpoints, dist_self]
    rw [hdist r t, abs_of_pos (sub_pos.mpr hrt)] at hzero
    linarith
  have hFWV : F '' W ⊆ V := by
    rintro y ⟨u, huW, rfl⟩
    exact hFmemV u (hWsubset huW)
  have hradial : ∀ y ∈ F '' W,
      dist (γ r) ((extChartAt I (γ r)).symm y) =
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b (ψ y) (γ r)‖ := by
    intro y hy
    obtain ⟨u, huW, rfl⟩ := hy
    obtain ⟨sol, _hsolRadius, _hsolCoordinate, _hsolLength, _hsolGauss,
      _hsolSpeed, _hsolSpeedAll, _hsolDistRiem, hsolDist,
      _hsolSubdist, _hsolMin⟩ := hgeodesic u huW
    simpa only [hleft u (hWsubset huW)] using hsolDist
  have hTinNorm :
      ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1) (γ t)‖ =
        (t : ℝ) - (r : ℝ) := by
    have hnormEq :
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1)
            (LocalChartSecondOrderSolution.curve incoming 1)‖ =
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b uIn (γ r)‖ := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinSpeed
      nlinarith [norm_nonneg (LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1)
          (LocalChartSecondOrderSolution.curve incoming 1)),
        norm_nonneg (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b uIn (γ r))]
    calc
      ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1) (γ t)‖ =
          ‖LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1)
              (LocalChartSecondOrderSolution.curve incoming 1)‖ := by rw [hinCurve1]
      _ = ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b uIn (γ r)‖ := hnormEq
      _ = dist (γ r) ((extChartAt I (γ r)).symm (F uIn)) := hinDist.symm
      _ = dist (γ r) (γ t) := by rw [hinEndpoint]
      _ = |(t : ℝ) - (r : ℝ)| := hdist r t
      _ = (t : ℝ) - (r : ℝ) := abs_of_pos (sub_pos.mpr hrt)
  have hinOpposite :
      ∀ (β : ℝ → M) (v : TM (γ t)),
        HasMFDerivAt (𝓘(ℝ, ℝ)) I β 0
            (CurveConnection.timeTangentMap (I := I) 0 v) →
        β 0 = γ t →
        (fun s ↦ dist (γ r) (β s)) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
            (fun s ↦ dist (γ r) (γ t) - s * ‖v‖) →
        let TIn := LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b
            (incoming.velocity 1) (γ t)
        ‖v‖ • TIn = -(‖TIn‖ • v) := by
    intro β v hβderiv hβzero hdecrease
    exact LocalGeodesicData.normalCoordinate_oppositeDirection_of_exactDistanceCurve_right
      (I := I) (M := M) cov (γ r) b F ψ V W zr hVopen hFWopen hF hψ
        hFWV hright hFzero hradial huInW hFuInNe
        (hleft uIn (hWsubset huInW)) hinGauss hinSpeed hinCurve1 htN.1
        hFuIn.symm β v hβderiv hβzero hdecrease
  let zt : E := extChartAt I (γ t) (γ t)
  obtain ⟨Fout, ψout, Uout, Vout, Wout, radiusOut, hUoutOpen, hzeroUout,
    hVoutOpen, hztVout, hFout, hψout, hFoutZero, hleftOut, hrightOut,
    hFoutMemVout, hψoutMemUout, hFoutTarget, hWoutOpen, hzeroWout,
    hWoutSubset, hFoutWoutOpen, hztFoutWout, hradiusOutPos, hballOut,
    hgeodesicOut⟩ := exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
      (I := I) (M := M) g (γ t)
  let Nout : Set M :=
    (extChartAt I (γ t)).source ∩
      (extChartAt I (γ t)) ⁻¹' (Fout '' Wout)
  have hNoutOpen : IsOpen Nout :=
    isOpen_extChartAt_preimage' (I := I) (γ t) hFoutWoutOpen
  have htNout : γ t ∈ Nout := by
    refine ⟨mem_extChartAt_source (I := I) (γ t), ?_⟩
    change extChartAt I (γ t) (γ t) ∈ Fout '' Wout
    simpa only [zt] using hztFoutWout
  have hnear : γ ⁻¹' Nout ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds (hNoutOpen.mem_nhds htNout)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨uIn, incoming, hinRadius,
    LocalChartSecondOrderSolution.curve_initial incoming, hinCurve1,
    hTinNorm, hinOpposite, ε, hε, ?_⟩
  intro s hts hst
  have hsNout : γ s ∈ Nout := hεN (by
    change |(s : ℝ) - (t : ℝ)| < ε
    rw [abs_of_pos (sub_pos.mpr hts)]
    exact hst)
  obtain ⟨uOut, huOutW, hFoutU⟩ := hsNout.2
  obtain ⟨outgoing, houtRadius, houtCoordinate, _houtLength, _houtGauss,
    _houtSpeed, _houtSpeedAll, _houtDistRiem, houtDist,
    houtSubdist, _houtMin⟩ := hgeodesicOut uOut huOutW
  have houtEndpoint : (extChartAt I (γ t)).symm (Fout uOut) = γ s := by
    rw [hFoutU]
    exact (extChartAt I (γ t)).left_inv hsNout.1
  have houtCurve1 : LocalChartSecondOrderSolution.curve outgoing 1 = γ s := by
    change (extChartAt I (γ t)).symm (outgoing.coordinate 1) = γ s
    rw [houtCoordinate]
    exact houtEndpoint
  have hinEndpointSource : γ t ∈ (extChartAt I (γ r)).source := htN.1
  have hinEndpointChart : extChartAt I (γ r) (γ t) = F uIn := hFuIn.symm
  have houtDist' : dist (γ t) (γ s) =
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := γ t) b uOut (γ t)‖ := by
    simpa only [b, houtEndpoint] using houtDist
  have houtSubdist' : ∀ q ∈ Ioo (0 : ℝ) 1,
      dist (γ t) (LocalChartSecondOrderSolution.curve outgoing q) =
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ t) b uOut (γ t)‖ * q ∧
      dist (LocalChartSecondOrderSolution.curve outgoing q) (γ s) =
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ t) b uOut (γ t)‖ * (1 - q) := by
    simpa only [b, houtEndpoint] using houtSubdist
  have hchain : dist (γ r) (γ s) =
      dist (γ r) (γ t) + dist (γ t) (γ s) := by
    rw [hdist r s, hdist r t, hdist t s,
      abs_of_pos (sub_pos.mpr hrt), abs_of_pos (sub_pos.mpr hts),
      abs_of_pos (sub_pos.mpr (hrt.trans hts))]
    ring
  have halign :=
    LocalGeodesicData.normalCoordinate_sameDirection_of_exactMetricCorner
      (I := I) (M := M) cov (γ r) b F ψ V W zr hVopen hFWopen hF hψ
        hFWV hright hFzero hradial huInW hFuInNe
        (hleft uIn (hWsubset huInW)) hinGauss hinSpeed hinCurve1 hinEndpointSource
        hinEndpointChart outgoing houtRadius houtCurve1 houtDist' houtSubdist' hchain
  have hToutNorm :
      ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ t) b uOut (γ t)‖ =
        (s : ℝ) - (t : ℝ) := by
    calc
      ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ t) b uOut (γ t)‖ =
          dist (γ t) ((extChartAt I (γ t)).symm (Fout uOut)) := houtDist.symm
      _ = dist (γ t) (γ s) := by rw [houtEndpoint]
      _ = |(s : ℝ) - (t : ℝ)| := hdist t s
      _ = (s : ℝ) - (t : ℝ) := abs_of_pos (sub_pos.mpr hts)
  have halign' :
      ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ t) b uOut (γ t)‖ •
          LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1) (γ t) =
        ‖LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1) (γ t)‖ •
          LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := γ t) b uOut (γ t) := by
    simpa only [hinCurve1, b] using halign
  have hnormalized := inv_smul_eq_inv_smul_of_norm_smul_eq
    (sub_pos.mpr hrt) (sub_pos.mpr hts) hTinNorm hToutNorm halign'
  exact ⟨uOut, outgoing, houtRadius,
    LocalChartSecondOrderSolution.curve_initial outgoing, houtCurve1,
    hTinNorm, hToutNorm, halign', hnormalized⟩

end BonnetMyersEntry
