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

public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentDense
public import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentBoundary

/-! # Metric Segment Smooth -/

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

def IsLocallyGeodesicAt
    [PseudoMetricSpace M]
    [RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M)
    (t : MetricHopfRinow.SegmentParameter x z) : Prop :=
  ∃ c : M, ∃ v : TM c,
    ∃ β : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov c v,
      ‖v‖ = 1 ∧
      IntrinsicGeodesic.LocalGeodesic.curve β 0 = γ t ∧
      ∃ ρ > (0 : ℝ),
        ∀ s : MetricHopfRinow.SegmentParameter x z,
          |(s : ℝ) - (t : ℝ)| < ρ →
          IntrinsicGeodesic.LocalGeodesic.curve β
            ((s : ℝ) - (t : ℝ)) = γ s
/-- Every nondegenerate exact Riemannian metric segment has an interior point
at which one unit-speed intrinsic local geodesic represents the segment on
both sides.  The proof combines density of backward geodesic pieces with
normal-coordinate first variation and local ODE uniqueness. -/
theorem riemannian_metric_segment_exists_interior_locally_geodesic
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ p q, riemannianEDist I (γ p) (γ q) =
        ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
      0 < dist x z →
      ∃ t : MetricHopfRinow.SegmentParameter x z,
        0 < (t : ℝ) ∧ (t : ℝ) < dist x z ∧
        IsLocallyGeodesicAt (I := I) (M := M) cov γ t := by
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
  intro x z γ hγ hsegment hD
  have hdist (p q : MetricHopfRinow.SegmentParameter x z) :
      dist (γ p) (γ q) = |(q : ℝ) - (p : ℝ)| := by
    rw [finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
      (I := I) (M := M) g, hsegment p q,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  let r : MetricHopfRinow.SegmentParameter x z :=
    ⟨0, le_rfl, dist_nonneg⟩
  obtain ⟨N, hNopen, hrN, hcorner⟩ :=
    riemannian_metric_segment_exists_normal_corner_alignment
      (I := I) (M := M) g γ hγ hsegment r
  have hpreN : γ ⁻¹' N ∈ 𝓝 r :=
    hγ.continuousAt.preimage_mem_nhds (hNopen.mem_nhds hrN)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpreN
  let e : ℝ := min (δ / 2) (dist x z / 2)
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have heD : e < dist x z := by
    have hle : e ≤ dist x z / 2 := min_le_right _ _
    linarith
  let q₀ : MetricHopfRinow.SegmentParameter x z :=
    ⟨e, he.le, heD.le⟩
  have hq₀ball : q₀ ∈ Metric.ball r δ := by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    change |e - 0| < δ
    rw [sub_zero, abs_of_pos he]
    have hle : e ≤ δ / 2 := min_le_left _ _
    linarith
  have hq₀N : γ q₀ ∈ N := hball hq₀ball
  let J : Set (MetricHopfRinow.SegmentParameter x z) :=
    γ ⁻¹' N ∩ {t | 0 < (t : ℝ)} ∩ {t | (t : ℝ) < dist x z}
  have hJopen : IsOpen J := by
    apply IsOpen.inter
    · exact (hNopen.preimage hγ).inter
        (isOpen_Ioi.preimage continuous_subtype_val)
    · exact isOpen_Iio.preimage continuous_subtype_val
  have hJnonempty : J.Nonempty := by
    exact ⟨q₀, ⟨hq₀N, he⟩, heD⟩
  have hDense := riemannian_metric_segment_dense_local_geodesic_left
    (I := I) (M := M) g γ hγ hsegment
  obtain ⟨q, hqLeft, hqJ⟩ := hDense.exists_mem_open hJopen hJnonempty
  have hqN : γ q ∈ N := hqJ.1.1
  have hqpos : 0 < (q : ℝ) := hqJ.1.2
  have hqD : (q : ℝ) < dist x z := hqJ.2
  have hrq : (r : ℝ) < (q : ℝ) := by simpa [r] using hqpos
  obtain ⟨cL, vL, βL, hvLOr, hβLzero, ρL, hρL, hβL⟩ := hqLeft
  have hvL : ‖vL‖ = 1 := hvLOr.resolve_right (ne_of_gt hqpos)
  have hcL : cL = γ q := by
    rw [← hβLzero]
    exact (IntrinsicGeodesic.LocalGeodesic.curve_initial βL).symm
  subst cL
  obtain ⟨uIn, incoming, hinRadius, _hinZero, hinEnd, hinNorm,
    hinOpposite, ε, hε, hout⟩ := hcorner q hqN hrq
  let a : ℝ := (q : ℝ) - (r : ℝ)
  have ha : 0 < a := sub_pos.mpr hrq
  have haEq : a = (q : ℝ) := by simp [a, r]
  have hsmall : Iio (min ρL (q : ℝ)) ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds (lt_min hρL hqpos)
  have hsmallWithin : Iio (min ρL (q : ℝ)) ∈ 𝓝[Ici (0 : ℝ)] 0 :=
    Filter.Eventually.filter_mono inf_le_left hsmall
  have hdecrease :
      (fun s ↦ dist (γ r) (IntrinsicGeodesic.LocalGeodesic.curve βL s)) =ᶠ[
        𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ dist (γ r) (γ q) - s * ‖vL‖) := by
    filter_upwards [hsmallWithin, self_mem_nhdsWithin] with s hs hs0
    by_cases hsZero : s = 0
    · subst s
      simp only [hβLzero, zero_mul, sub_zero]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZero)
      have hsρ : s < ρL := lt_of_lt_of_le hs (min_le_left _ _)
      have hsq : s < (q : ℝ) := lt_of_lt_of_le hs (min_le_right _ _)
      let p : MetricHopfRinow.SegmentParameter x z :=
        ⟨(q : ℝ) - s, by linarith, by linarith [q.2.2]⟩
      have hpq : (p : ℝ) < (q : ℝ) := by dsimp [p]; linarith
      have hgap : (q : ℝ) - (p : ℝ) < ρL := by simpa [p] using hsρ
      have hcurve := hβL p hpq hgap
      have hcurve' : IntrinsicGeodesic.LocalGeodesic.curve βL s = γ p := by
        simpa [p] using hcurve
      rw [hcurve', hdist r p, hdist r q, hvL]
      change |((q : ℝ) - s) - 0| = |(q : ℝ) - 0| - s * 1
      rw [abs_of_nonneg (by linarith)]
      simp only [sub_zero, abs_of_pos hqpos]
      ring
  let TIn : TM (γ q) := LocalGeodesicData.coordinateFrameCombination
    (I := I) (M := M) (x₀ := γ r) b
      (incoming.velocity 1) (γ q)
  have hTInNorm : ‖TIn‖ = a := by
    simpa only [TIn, b, a] using hinNorm
  have hβLderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (IntrinsicGeodesic.LocalGeodesic.curve βL) 0
      (CurveConnection.timeTangentMap (I := I) 0 vL) := by
    have hraw := IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve βL
      (t := (0 : ℝ)) (by
        constructor
        · linarith [βL.solution.radius_pos]
        · exact βL.solution.radius_pos)
    have hraw' : HasMFDerivAt (𝓘(ℝ, ℝ)) I
        (IntrinsicGeodesic.LocalGeodesic.curve βL) 0
        (ContinuousLinearMap.toSpanSingleton ℝ vL) := by
      simpa only [hβLzero,
        IntrinsicGeodesic.LocalGeodesic.velocity_initial] using hraw
    have hmap : CurveConnection.timeTangentMap (I := I) 0 vL =
        ContinuousLinearMap.toSpanSingleton ℝ vL :=
      CurveConnection.timeTangentMap_eq_toSpanSingleton (I := I) 0 vL
    exact hmap.symm ▸ hraw'
  have hopposite := hinOpposite
    (IntrinsicGeodesic.LocalGeodesic.curve βL) vL hβLderiv hβLzero hdecrease
  have hopposite' : TIn = -(a • vL) := by
    change ‖vL‖ • TIn = -(‖TIn‖ • vL) at hopposite
    rw [hvL, one_smul, hTInNorm] at hopposite
    exact hopposite
  have hnormalizedBack : a⁻¹ • TIn = -vL := by
    calc
      a⁻¹ • TIn = a⁻¹ • (-(a • vL)) := congrArg (fun w : TM (γ q) ↦ a⁻¹ • w) hopposite'
      _ = -(a⁻¹ • (a • vL)) := by rw [smul_neg]
      _ = -vL := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  let αIn₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) incoming
  let αIn := IntrinsicGeodesic.LocalGeodesic.rescale αIn₀ a⁻¹ (inv_pos.mpr ha)
  let scaleState (k : ℝ) : Bundle.TotalSpace E TM → Bundle.TotalSpace E TM :=
    fun p ↦ ⟨p.proj, k • p.snd⟩
  have hOne : (1 : ℝ) ∈ Ioo (-incoming.radius) incoming.radius := by
    rw [hinRadius]
    norm_num
  have hcurveIn : IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1 = γ q := by
    exact (congrFun (IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve incoming) 1).trans hinEnd
  have hstateIn₀ : IntrinsicGeodesic.localState αIn₀ 1 =
      (⟨γ q, TIn⟩ : Bundle.TotalSpace E TM) := by
    have hframe := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
      (I := I) (M := M) (E := E) cov (γ r) b αIn₀.solution
        αIn₀.solution.velocity (t := 1) (by simpa [αIn₀, b] using hOne)
    have hstateFrame : IntrinsicGeodesic.localState αIn₀ 1 =
        (⟨IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1,
          LocalGeodesicData.coordinateFrameCombination
            (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1)
              (IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1)⟩ :
          Bundle.TotalSpace E TM) := by
      refine Bundle.TotalSpace.ext (by rfl) ?_
      change HEq
        (LocalGeodesicData.tangentField cov (γ r) b αIn₀.solution
          αIn₀.solution.velocity 1)
        (LocalGeodesicData.coordinateFrameCombination
          (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1)
            (αIn₀.solution.curve 1))
      simpa [αIn₀, b] using (heq_of_eq hframe)
    exact hstateFrame.trans (congrArg (fun y : M ↦
      (⟨y, LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := γ r) b (incoming.velocity 1) y⟩ :
        Bundle.TotalSpace E TM)) hcurveIn)
  have hInTime : a⁻¹ * a ∈ Ioo (-αIn₀.solution.radius) αIn₀.solution.radius := by
    simpa [αIn₀, inv_mul_cancel₀ (ne_of_gt ha)] using hOne
  have hvIn := IntrinsicGeodesic.LocalGeodesic.rescale_actual_velocity
    αIn₀ a⁻¹ (inv_pos.mpr ha) hInTime
  have hstateResIn : IntrinsicGeodesic.localState αIn a =
      scaleState a⁻¹ (IntrinsicGeodesic.localState αIn₀ 1) := by
    have hbaseRes : IntrinsicGeodesic.LocalGeodesic.curve αIn a =
        IntrinsicGeodesic.LocalGeodesic.curve αIn₀ 1 := by
      simpa [αIn, inv_mul_cancel₀ (ne_of_gt ha)] using
        IntrinsicGeodesic.LocalGeodesic.rescale_curve αIn₀ a⁻¹ (inv_pos.mpr ha) a
    refine Bundle.TotalSpace.ext hbaseRes ?_
    rw [inv_mul_cancel₀ (ne_of_gt ha)] at hvIn
    exact (heq_of_eq hvIn).trans (by rfl)
  let β := IntrinsicGeodesic.LocalGeodesic.reverse βL
  have hstateβ : IntrinsicGeodesic.localState β 0 =
      (⟨γ q, -vL⟩ : Bundle.TotalSpace E TM) := by
    apply Bundle.TotalSpace.ext
      (IntrinsicGeodesic.LocalGeodesic.curve_initial β)
    exact heq_of_eq (IntrinsicGeodesic.LocalGeodesic.velocity_initial β)
  have hstateIn : IntrinsicGeodesic.localState αIn a =
      (⟨γ q, -vL⟩ : Bundle.TotalSpace E TM) := by
    calc
      IntrinsicGeodesic.localState αIn a =
          scaleState a⁻¹ (IntrinsicGeodesic.localState αIn₀ 1) := hstateResIn
      _ = scaleState a⁻¹ (⟨γ q, TIn⟩ : Bundle.TotalSpace E TM) :=
        congrArg (scaleState a⁻¹) hstateIn₀
      _ = (⟨γ q, -vL⟩ : Bundle.TotalSpace E TM) := by
        apply Bundle.TotalSpace.ext (by rfl)
        exact heq_of_eq hnormalizedBack
  have hstateβIn : IntrinsicGeodesic.localState β 0 =
      IntrinsicGeodesic.localState αIn a := hstateβ.trans hstateIn.symm
  let ρ : ℝ := min ρL (min ε β.solution.radius)
  have hρ : 0 < ρ := lt_min hρL (lt_min hε β.solution.radius_pos)
  refine ⟨q, hqpos, hqD, γ q, -vL, β, ?_, ?_, ρ, hρ, ?_⟩
  · simp [hvL]
  · exact IntrinsicGeodesic.LocalGeodesic.curve_initial β
  · intro s hs
    rcases lt_trichotomy (s : ℝ) (q : ℝ) with hsq | hsq | hqs
    · have hgapPos : 0 < (q : ℝ) - (s : ℝ) := sub_pos.mpr hsq
      have hgapρ : (q : ℝ) - (s : ℝ) < ρ := by
        rw [abs_of_neg (sub_neg.mpr hsq)] at hs
        simpa only [neg_sub] using hs
      have hgapρL : (q : ℝ) - (s : ℝ) < ρL :=
        lt_of_lt_of_le hgapρ (min_le_left _ _)
      rw [IntrinsicGeodesic.LocalGeodesic.reverse_curve]
      have hneg : -((s : ℝ) - (q : ℝ)) = (q : ℝ) - (s : ℝ) := by ring
      rw [hneg]
      exact hβL s hsq hgapρL
    · have hsqEq : s = q := Subtype.ext hsq
      subst s
      simpa using IntrinsicGeodesic.LocalGeodesic.curve_initial β
    · have hd : 0 < (s : ℝ) - (q : ℝ) := sub_pos.mpr hqs
      have hdρ : (s : ℝ) - (q : ℝ) < ρ := by
        simpa [abs_of_pos hd] using hs
      have hdε : (s : ℝ) - (q : ℝ) < ε :=
        lt_of_lt_of_le hdρ (le_trans (min_le_right _ _) (min_le_left _ _))
      have hdβ : (s : ℝ) - (q : ℝ) < β.solution.radius :=
        lt_of_lt_of_le hdρ (le_trans (min_le_right _ _) (min_le_right _ _))
      obtain ⟨uOut, outgoing, houtRadius, _houtZero, houtEnd,
        _hInNorm, _hOutNorm, _halign, hnormalized⟩ := hout s hqs hdε
      let d : ℝ := (s : ℝ) - (q : ℝ)
      let αOut₀ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
        (I := I) (M := M) outgoing
      let αOut := IntrinsicGeodesic.LocalGeodesic.rescale αOut₀ d⁻¹
        (inv_pos.mpr hd)
      have hstateInOut : IntrinsicGeodesic.localState αIn a =
          IntrinsicGeodesic.localState αOut 0 := by
        simpa only [a, d, αIn₀, αIn, αOut₀, αOut] using
          (rescaled_normal_connectors_state_eq
            (I := I) (M := M) cov (γ r) (γ q) uIn uOut incoming outgoing
              hinRadius hinEnd ha hd hnormalized)
      have hstateβOut : IntrinsicGeodesic.localState β 0 =
          IntrinsicGeodesic.localState αOut 0 := hstateβIn.trans hstateInOut
      have heq :=
        IntrinsicGeodesic.LocalGeodesic.curve_eqOn_common_interval_of_initial_state_eq
          β αOut hstateβOut
      have hαOutRadius : αOut.solution.radius = 2 * d := by
        simp only [αOut, IntrinsicGeodesic.LocalGeodesic.rescale_radius,
          αOut₀, IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_radius,
          houtRadius]
        field_simp
      have hdInterval : d ∈ Ioo
          (-(min β.solution.radius αOut.solution.radius))
          (min β.solution.radius αOut.solution.radius) := by
        rw [hαOutRadius]
        constructor
        · have hminPos : 0 < min β.solution.radius (2 * d) :=
            lt_min β.solution.radius_pos (by positivity)
          linarith
        · apply lt_min
          · simpa only [d] using hdβ
          · linarith
      calc
        IntrinsicGeodesic.LocalGeodesic.curve β ((s : ℝ) - (q : ℝ)) =
            IntrinsicGeodesic.LocalGeodesic.curve αOut d := heq hdInterval
        _ = IntrinsicGeodesic.LocalGeodesic.curve αOut₀ (d⁻¹ * d) :=
          IntrinsicGeodesic.LocalGeodesic.rescale_curve αOut₀ d⁻¹
            (inv_pos.mpr hd) d
        _ = IntrinsicGeodesic.LocalGeodesic.curve αOut₀ 1 := by
          rw [inv_mul_cancel₀ (ne_of_gt hd)]
        _ = LocalChartSecondOrderSolution.curve outgoing 1 := by
          rw [IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve]
        _ = γ s := houtEnd
/-- A complete unit-speed geodesic which agrees with an exact metric segment
on some right neighbourhood of an interior parameter agrees all the way to
the segment's right endpoint. -/
theorem riemannian_metric_segment_globalGeodesic_agrees_right
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
      Continuous γ →
      (∀ p q, riemannianEDist I (γ p) (γ q) =
        ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
      ∀ {c : M} {v₀ : TM c}
        (α : IntrinsicGeodesic.GlobalGeodesic (I := I) (M := M) cov c v₀),
        ‖v₀‖ = 1 →
        ∀ τ : MetricHopfRinow.SegmentParameter x z,
          (τ : ℝ) < dist x z →
          (∃ ε > (0 : ℝ),
            ∀ s : MetricHopfRinow.SegmentParameter x z,
              (τ : ℝ) ≤ (s : ℝ) → (s : ℝ) - (τ : ℝ) < ε →
              IntrinsicGeodesic.GlobalGeodesic.curve α
                ((s : ℝ) - (τ : ℝ)) = γ s) →
          ∀ s : MetricHopfRinow.SegmentParameter x z,
            (τ : ℝ) ≤ (s : ℝ) →
            IntrinsicGeodesic.GlobalGeodesic.curve α
              ((s : ℝ) - (τ : ℝ)) = γ s := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  dsimp only
  intro x z γ hγ hsegment c v₀ α hv₀ τ hτD hseed s hs
  obtain ⟨ε₀, hε₀, hseed⟩ := hseed
  let e₀ : ℝ := min (ε₀ / 2) ((dist x z - (τ : ℝ)) / 2)
  have he₀ : 0 < e₀ := by
    dsimp [e₀]
    exact lt_min (by linarith) (by linarith)
  have he₀ε : e₀ < ε₀ := by
    have hle : e₀ ≤ ε₀ / 2 := min_le_left _ _
    linarith
  have he₀D : (τ : ℝ) + e₀ < dist x z := by
    have hle : e₀ ≤ (dist x z - (τ : ℝ)) / 2 := min_le_right _ _
    linarith
  let S : Set ℝ := {b | (τ : ℝ) ≤ b ∧ b ≤ dist x z ∧
    ∀ r : MetricHopfRinow.SegmentParameter x z,
      (τ : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ b →
      IntrinsicGeodesic.GlobalGeodesic.curve α
        ((r : ℝ) - (τ : ℝ)) = γ r}
  have hseedS : (τ : ℝ) + e₀ ∈ S := by
    refine ⟨by linarith, he₀D.le, ?_⟩
    intro r hτr hr
    apply hseed r hτr
    have hgap : (r : ℝ) - (τ : ℝ) ≤ e₀ := by linarith
    exact lt_of_le_of_lt hgap he₀ε
  have hSnonempty : S.Nonempty := ⟨(τ : ℝ) + e₀, hseedS⟩
  have hSbounded : BddAbove S := ⟨dist x z, fun _ h ↦ h.2.1⟩
  let B : ℝ := sSup S
  have hseedB : (τ : ℝ) + e₀ ≤ B := by
    dsimp only [B]
    exact le_csSup hSbounded hseedS
  have hτB : (τ : ℝ) < B := lt_of_lt_of_le (by linarith) hseedB
  have hBD : B ≤ dist x z := by
    dsimp only [B]
    exact csSup_le hSnonempty (fun _ h ↦ h.2.1)
  let bB : MetricHopfRinow.SegmentParameter x z :=
    ⟨B, le_trans τ.2.1 hτB.le, hBD⟩
  let Q : Set (MetricHopfRinow.SegmentParameter x z) :=
    {r | IntrinsicGeodesic.GlobalGeodesic.curve α
      ((r : ℝ) - (τ : ℝ)) = γ r}
  have hαcont : Continuous (IntrinsicGeodesic.GlobalGeodesic.curve α) :=
    continuous_iff_continuousAt.mpr (fun t ↦
      (IntrinsicGeodesic.GlobalGeodesic.contMDiffAt_curve
        (I := I) (M := M) α t).continuousAt)
  have hQclosed : IsClosed Q := by
    apply isClosed_eq
    · exact hαcont.comp (continuous_subtype_val.sub continuous_const)
    · exact hγ
  have hbBclosure : bB ∈ closure Q := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hbefore : B - ε < sSup S := by dsimp only [B]; linarith
    obtain ⟨a, haS, ha⟩ := exists_lt_of_lt_csSup hSnonempty hbefore
    have haB : a ≤ B := by
      dsimp only [B]
      exact le_csSup hSbounded haS
    let r : MetricHopfRinow.SegmentParameter x z :=
      ⟨a, le_trans τ.2.1 haS.1, haS.2.1⟩
    refine ⟨r, ?_, ?_⟩
    · exact haS.2.2 r haS.1 le_rfl
    · rw [Subtype.dist_eq, Real.dist_eq]
      change |B - a| < ε
      rw [abs_of_nonneg (sub_nonneg.mpr haB)]
      linarith
  have hbBQ : bB ∈ Q := by
    rw [← hQclosed.closure_eq]
    exact hbBclosure
  have hBS : B ∈ S := by
    refine ⟨hτB.le, hBD, ?_⟩
    intro r hτr hrB
    rcases lt_or_eq_of_le hrB with hrB | hrB
    · obtain ⟨a, haS, hra⟩ := exists_lt_of_lt_csSup hSnonempty (by
        simpa only [B] using hrB)
      exact haS.2.2 r hτr hra.le
    · have hr : r = bB := Subtype.ext hrB
      subst r
      exact hbBQ
  have hBD' : dist x z ≤ B := by
    by_contra hnot
    have hBltD : B < dist x z := lt_of_not_ge hnot
    obtain ⟨ε, hε, hext⟩ :=
      riemannian_metric_segment_globalGeodesic_extend_right
        (I := I) (M := M) g γ hγ hsegment α hv₀ τ bB
          (by simpa only [bB] using hτB)
          (by simpa only [bB] using hBltD) (by
            intro r hτr hr
            exact hBS.2.2 r hτr (by simpa only [bB] using hr))
    let e : ℝ := min (ε / 2) ((dist x z - B) / 2)
    have he : 0 < e := by
      dsimp [e]
      exact lt_min (by linarith) (by linarith)
    have heε : e < ε := by
      have hle : e ≤ ε / 2 := min_le_left _ _
      linarith
    have heD : B + e < dist x z := by
      have hle : e ≤ (dist x z - B) / 2 := min_le_right _ _
      linarith
    let r : MetricHopfRinow.SegmentParameter x z :=
      ⟨B + e, by linarith [τ.2.1], heD.le⟩
    have hrS : B + e ∈ S := by
      refine ⟨by linarith [hτB], heD.le, ?_⟩
      intro u hτu hu
      by_cases huB : (u : ℝ) ≤ B
      · exact hBS.2.2 u hτu huB
      · apply hext u (lt_of_not_ge huB)
        have : (u : ℝ) - B ≤ e := by linarith
        exact lt_of_le_of_lt this heε
    have hrB : B + e ≤ B := by
      dsimp only [B]
      exact le_csSup hSbounded hrS
    linarith
  have hB : B = dist x z := le_antisymm hBD hBD'
  exact hBS.2.2 s hs (by rw [hB]; exact s.2.2)
/-- On a complete finite-dimensional Riemannian manifold, every nondegenerate
exact metric segment is the restriction of one complete unit-speed intrinsic
geodesic.  The time origin is the interior parameter at which the initial
local smooth germ is constructed. -/
theorem riemannian_metric_segment_eq_global_unitGeodesic
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
    let cov := leviCivita (I := I) (M := M) g
    ∀ (_hcomplete : @CompleteSpace M
        (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace),
      ∀ {x z : M} (γ : MetricHopfRinow.SegmentParameter x z → M),
        Continuous γ →
        (∀ p q, riemannianEDist I (γ p) (γ q) =
          ENNReal.ofReal |(q : ℝ) - (p : ℝ)|) →
        0 < dist x z →
        ∃ τ : MetricHopfRinow.SegmentParameter x z,
          ∃ c : M, ∃ v₀ : TM c,
            ∃ α : IntrinsicGeodesic.GlobalGeodesic
              (I := I) (M := M) cov c v₀,
              0 < (τ : ℝ) ∧ (τ : ℝ) < dist x z ∧ ‖v₀‖ = 1 ∧
              ∀ s : MetricHopfRinow.SegmentParameter x z,
                IntrinsicGeodesic.GlobalGeodesic.curve α
                  ((s : ℝ) - (τ : ℝ)) = γ s := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := by infer_instance
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := finiteRiemannianMetricSpace (I := I) (M := M) g
  let cov := leviCivita (I := I) (M := M) g
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  have hcov : CovariantDerivative.IsLeviCivita cov := by
    simpa [cov] using (leviCivita_isLeviCivita (I := I) (M := M) g)
  dsimp only
  intro hcomplete x z γ hγ hsegment hD
  obtain ⟨τ, hτpos, hτD, hlocal⟩ :=
    riemannian_metric_segment_exists_interior_locally_geodesic
      (I := I) (M := M) g γ hγ hsegment hD
  obtain ⟨c, v₀, β, hv₀, hβ0, ρ, hρ, hβ⟩ := hlocal
  obtain ⟨α, _hunique⟩ :=
    IntrinsicGeodesic.GlobalGeodesic.exists_and_unique_of_complete
      (I := I) (M := M) (cov := cov) (x₀ := c) (v₀ := v₀)
        hcov.2 hcomplete
  have hαβ := IntrinsicGeodesic.GlobalGeodesic.agrees_locally α β
  obtain ⟨η, hη, hαβball⟩ := Metric.mem_nhds_iff.mp hαβ
  let ε : ℝ := min ρ η
  have hε : 0 < ε := lt_min hρ hη
  have hseedBoth : ∀ s : MetricHopfRinow.SegmentParameter x z,
      |(s : ℝ) - (τ : ℝ)| < ε →
      IntrinsicGeodesic.GlobalGeodesic.curve α
        ((s : ℝ) - (τ : ℝ)) = γ s := by
    intro s hs
    have hsρ : |(s : ℝ) - (τ : ℝ)| < ρ :=
      lt_of_lt_of_le hs (min_le_left _ _)
    have hsη : |(s : ℝ) - (τ : ℝ)| < η :=
      lt_of_lt_of_le hs (min_le_right _ _)
    have hstate := hαβball (show (s : ℝ) - (τ : ℝ) ∈
        Metric.ball (0 : ℝ) η by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact hsη)
    have hcurve := congrArg Bundle.TotalSpace.proj hstate
    change IntrinsicGeodesic.GlobalGeodesic.curve α
      ((s : ℝ) - (τ : ℝ)) =
        IntrinsicGeodesic.LocalGeodesic.curve β
          ((s : ℝ) - (τ : ℝ)) at hcurve
    exact hcurve.trans (hβ s hsρ)
  have hright : ∀ s : MetricHopfRinow.SegmentParameter x z,
      (τ : ℝ) ≤ (s : ℝ) →
      IntrinsicGeodesic.GlobalGeodesic.curve α
        ((s : ℝ) - (τ : ℝ)) = γ s := by
    apply riemannian_metric_segment_globalGeodesic_agrees_right
      (I := I) (M := M) g γ hγ hsegment α hv₀ τ hτD
    refine ⟨ε, hε, ?_⟩
    intro s hτs hs
    apply hseedBoth s
    rw [abs_of_nonneg (sub_nonneg.mpr hτs)]
    exact hs
  let τR : MetricHopfRinow.SegmentParameter x z :=
    MetricHopfRinow.reverseSegmentParameter τ
  let γR : MetricHopfRinow.SegmentParameter x z → M :=
    fun s ↦ γ (MetricHopfRinow.reverseSegmentParameter s)
  let αR := IntrinsicGeodesic.GlobalGeodesic.reverse α
  have hrevContinuous : Continuous
      (fun s : MetricHopfRinow.SegmentParameter x z ↦
        MetricHopfRinow.reverseSegmentParameter s) :=
    MetricHopfRinow.continuous_reverseSegmentParameter
  have hγR : Continuous γR := hγ.comp hrevContinuous
  have hsegmentR : ∀ p q, riemannianEDist I (γR p) (γR q) =
      ENNReal.ofReal |(q : ℝ) - (p : ℝ)| := by
    intro p q
    rw [show γR p = γ (MetricHopfRinow.reverseSegmentParameter p) by rfl,
      show γR q = γ (MetricHopfRinow.reverseSegmentParameter q) by rfl,
      hsegment]
    congr 1
    simp only [MetricHopfRinow.coe_reverseSegmentParameter]
    rw [show (dist x z - (q : ℝ)) - (dist x z - (p : ℝ)) =
      (p : ℝ) - (q : ℝ) by ring, abs_sub_comm]
  have hv₀R : ‖-v₀‖ = 1 := by simpa only [norm_neg] using hv₀
  have hτRD : (τR : ℝ) < dist x z := by
    simp only [τR, MetricHopfRinow.coe_reverseSegmentParameter]
    linarith
  have hseedR : ∃ δ > (0 : ℝ),
      ∀ s : MetricHopfRinow.SegmentParameter x z,
        (τR : ℝ) ≤ (s : ℝ) → (s : ℝ) - (τR : ℝ) < δ →
        IntrinsicGeodesic.GlobalGeodesic.curve αR
          ((s : ℝ) - (τR : ℝ)) = γR s := by
    refine ⟨ε, hε, ?_⟩
    intro s hτs hs
    let r : MetricHopfRinow.SegmentParameter x z :=
      MetricHopfRinow.reverseSegmentParameter s
    have htime : -((s : ℝ) - (τR : ℝ)) =
        (r : ℝ) - (τ : ℝ) := by
      simp only [τR, r, MetricHopfRinow.coe_reverseSegmentParameter]
      ring
    have hclose : |(r : ℝ) - (τ : ℝ)| < ε := by
      rw [← htime, abs_neg, abs_of_nonneg (sub_nonneg.mpr hτs)]
      exact hs
    calc
      IntrinsicGeodesic.GlobalGeodesic.curve αR
          ((s : ℝ) - (τR : ℝ)) =
          IntrinsicGeodesic.GlobalGeodesic.curve α
            (-((s : ℝ) - (τR : ℝ))) := by
        exact IntrinsicGeodesic.GlobalGeodesic.reverse_curve α _
      _ = IntrinsicGeodesic.GlobalGeodesic.curve α
          ((r : ℝ) - (τ : ℝ)) := congrArg _ htime
      _ = γ r := hseedBoth r hclose
      _ = γR s := rfl
  have hleftR : ∀ s : MetricHopfRinow.SegmentParameter x z,
      (τR : ℝ) ≤ (s : ℝ) →
      IntrinsicGeodesic.GlobalGeodesic.curve αR
        ((s : ℝ) - (τR : ℝ)) = γR s := by
    exact riemannian_metric_segment_globalGeodesic_agrees_right
      (I := I) (M := M) g γR hγR hsegmentR αR hv₀R τR hτRD hseedR
  refine ⟨τ, c, v₀, α, hτpos, hτD, hv₀, ?_⟩
  intro s
  rcases le_total (τ : ℝ) (s : ℝ) with hτs | hsτ
  · exact hright s hτs
  · let r : MetricHopfRinow.SegmentParameter x z :=
      MetricHopfRinow.reverseSegmentParameter s
    have hτRr : (τR : ℝ) ≤ (r : ℝ) := by
      simp only [τR, r, MetricHopfRinow.coe_reverseSegmentParameter]
      linarith
    have hr := hleftR r hτRr
    calc
      IntrinsicGeodesic.GlobalGeodesic.curve α
          ((s : ℝ) - (τ : ℝ)) =
          IntrinsicGeodesic.GlobalGeodesic.curve αR
            ((r : ℝ) - (τR : ℝ)) := by
        rw [IntrinsicGeodesic.GlobalGeodesic.reverse_curve]
        congr 2
        simp only [τR, r, MetricHopfRinow.coe_reverseSegmentParameter]
        ring
      _ = γR r := hr
      _ = γ s := by
        simp only [γR, r,
          MetricHopfRinow.reverseSegmentParameter_involutive]

end BonnetMyersEntry
