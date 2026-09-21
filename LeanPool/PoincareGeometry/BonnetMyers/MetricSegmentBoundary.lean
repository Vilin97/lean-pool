/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.TwoPointCornerRigidity
import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentRegularity
import LeanPool.PoincareGeometry.BonnetMyers.MetricSegmentGluing

/-!
# Uniform continuation of a smooth piece of an exact metric segment

The two-point connector energy removes the non-uniformity of normal
neighbourhoods whose centre moves toward a putative endpoint.  If a complete
unit-speed geodesic already represents an exact metric segment up to an
interior parameter, one strong two-point neighbourhood at that parameter
identifies its final short piece with the incoming connector.  First
variation then aligns every sufficiently short outgoing minimizing connector,
and local ODE uniqueness continues the original complete geodesic across the
endpoint.
-/

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

private theorem tangent_norm_eq_of_heq
    [IsManifold I 1 M] [RiemannianBundle TM]
    {a b : M} {v : TM a} {w : TM b} (hab : a = b) (h : HEq v w) :
    ‖v‖ = ‖w‖ := by
  subst b
  exact congrArg norm (eq_of_heq h)

private theorem tangent_smul_heq_of_heq
    [IsManifold I 1 M] [RiemannianBundle TM]
    {a b : M} {v : TM a} {w : TM b} (c : ℝ) (h : HEq v w) :
    HEq (c • v) (c • w) := by
  cases h
  rfl

private theorem sameDirection_of_tangent_heq
    [IsManifold I 1 M] [RiemannianBundle TM]
    {a b : M} {v T : TM a} {v' T' : TM b}
    (hab : a = b) (hv : HEq v v') (hT : HEq T T')
    (h : ‖v‖ • T = ‖T‖ • v) :
    ‖v'‖ • T' = ‖T'‖ • v' := by
  subst b
  simpa only [eq_of_heq hv, eq_of_heq hT] using h
/-- A complete unit-speed geodesic which represents an exact metric segment
on a nontrivial closed interval continues to represent it on a uniform right
neighbourhood of the interval's right endpoint. -/
theorem riemannian_metric_segment_globalGeodesic_extend_right
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
        ∀ τ b : MetricHopfRinow.SegmentParameter x z,
          (τ : ℝ) < (b : ℝ) → (b : ℝ) < dist x z →
          (∀ r : MetricHopfRinow.SegmentParameter x z,
            (τ : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ (b : ℝ) →
            IntrinsicGeodesic.GlobalGeodesic.curve α
              ((r : ℝ) - (τ : ℝ)) = γ r) →
          ∃ ε > (0 : ℝ),
            ∀ s : MetricHopfRinow.SegmentParameter x z,
              (b : ℝ) < (s : ℝ) → (s : ℝ) - (b : ℝ) < ε →
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
  let basis := IntrinsicGeodesic.canonicalBasis (E := E)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  have hcov : CovariantDerivative.IsLeviCivita cov := by
    simpa [cov] using (leviCivita_isLeviCivita (I := I) (M := M) g)
  dsimp only
  intro x z γ hγ hsegment c v₀ α hv₀ τ b hτb hbD hagree
  have hdist (p q : MetricHopfRinow.SegmentParameter x z) :
      dist (γ p) (γ q) = |(q : ℝ) - (p : ℝ)| := by
    rw [finiteRiemannianMetricSpace_dist_eq_riemannianEDist_toReal
      (I := I) (M := M) g, hsegment p q,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  let tb : ℝ := (b : ℝ) - (τ : ℝ)
  have hαb : IntrinsicGeodesic.GlobalGeodesic.curve α tb = γ b := by
    exact hagree b hτb.le le_rfl
  let xb : M := γ b
  let zb : E := extChartAt I xb xb
  have hyb : (extChartAt I xb).symm zb = xb := by
    dsimp only [zb]
    exact (extChartAt I xb).left_inv (mem_extChartAt_source (I := I) xb)
  obtain ⟨G, Φ, R, V, hG, hGcompact, _hGeq, hΦzero, hΦcurve, _hfix,
      hΦsmooth, hR, hsource, _htarget, hinverseSmooth, hactual, hframe,
      _hreverse, hVopen, hzbV, hVV, _hendpoint, hunique⟩ :=
    LocalGeodesicData.exists_twoPoint_coordinateGeodesic_neighborhood
      (I := I) (M := M) cov xb basis
        (mem_extChartAt_target (I := I) xb) rfl
  obtain ⟨Nstate, hNstateOpen, hxbNstate, δ, hδ,
      hsmallState⟩ :=
    LocalGeodesicData.exists_open_base_neighborhood_small_tangent_coordinateState_mem
      (I := I) (M := M) (x₀ := xb) R hsource
  obtain ⟨Uframe, hUframeSub, hUframeOpen, hxbUframe⟩ :=
    mem_nhds_iff.mp
      (IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
        (I := I) (M := M) xb basis)
  let P : Set M :=
    (extChartAt I xb).source ∩ (extChartAt I xb) ⁻¹' V
  have hPopen : IsOpen P :=
    isOpen_extChartAt_preimage' (I := I) xb hVopen
  have hxbP : xb ∈ P := by
    refine ⟨mem_extChartAt_source (I := I) xb, ?_⟩
    change extChartAt I xb xb ∈ V
    simpa only [zb] using hzbV
  obtain ⟨Fout, ψout, Uout, Vout, Wout, radiusOut, hUoutOpen,
      hzeroUout, hVoutOpen, hzbVout, hFout, hψout, hFoutZero,
      hleftOut, hrightOut, hFoutMemVout, hψoutMemUout, hFoutTarget,
      hWoutOpen, hzeroWout, hWoutSubset, hFoutWoutOpen, hzbFoutWout,
      hradiusOutPos, hballOut, hgeodesicOut⟩ :=
    exists_normalCoordinate_unrestricted_lengthMinimizing_geodesic
      (I := I) (M := M) g xb
  let Nout : Set M :=
    (extChartAt I xb).source ∩ (extChartAt I xb) ⁻¹' (Fout '' Wout)
  have hNoutOpen : IsOpen Nout :=
    isOpen_extChartAt_preimage' (I := I) xb hFoutWoutOpen
  have hxbNout : xb ∈ Nout := by
    refine ⟨mem_extChartAt_source (I := I) xb, ?_⟩
    change extChartAt I xb xb ∈ Fout '' Wout
    simpa only [zb] using hzbFoutWout
  let O : Set M := Uframe ∩ Nstate ∩ Nout ∩ P
  have hOopen : IsOpen O :=
    ((hUframeOpen.inter hNstateOpen).inter hNoutOpen).inter hPopen
  have hxbO : xb ∈ O :=
    ⟨⟨⟨hxbUframe, hxbNstate⟩, hxbNout⟩, hxbP⟩
  have hαO :
      (IntrinsicGeodesic.GlobalGeodesic.curve α) ⁻¹' O ∈ 𝓝 tb := by
    apply (IntrinsicGeodesic.GlobalGeodesic.contMDiffAt_curve
      (I := I) (M := M) α tb).continuousAt.preimage_mem_nhds
    simpa only [hαb, xb] using hOopen.mem_nhds hxbO
  obtain ⟨ρα, hρα, hαball⟩ := Metric.mem_nhds_iff.mp hαO
  have hγO : γ ⁻¹' O ∈ 𝓝 b :=
    hγ.continuousAt.preimage_mem_nhds (hOopen.mem_nhds hxbO)
  obtain ⟨ργ, hργ, hγball⟩ := Metric.mem_nhds_iff.mp hγO
  have hPnhds : P ∈ 𝓝 xb := hPopen.mem_nhds hxbP
  obtain ⟨rV, hrV, hballV⟩ := Metric.mem_nhds_iff.mp hPnhds
  let d : ℝ := min (ρα / 4) (min (δ / 2) (((b : ℝ) - (τ : ℝ)) / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hdρα : 2 * d < ρα := by
    have hle : d ≤ ρα / 4 := min_le_left _ _
    linarith
  have hdδ : d < δ := by
    have hle : d ≤ δ / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hdτb : d < (b : ℝ) - (τ : ℝ) := by
    have hle : d ≤ ((b : ℝ) - (τ : ℝ)) / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  let q : MetricHopfRinow.SegmentParameter x z :=
    ⟨(b : ℝ) - d, by linarith [τ.2.1], by linarith [b.2.2]⟩
  have hτq : (τ : ℝ) < (q : ℝ) := by dsimp [q]; linarith
  have hqb : (q : ℝ) < (b : ℝ) := by dsimp [q]; linarith
  let tq : ℝ := (q : ℝ) - (τ : ℝ)
  have htqdist : dist tq tb < ρα := by
    rw [Real.dist_eq]
    dsimp [tq, tb, q]
    rw [show ((b : ℝ) - d - (τ : ℝ)) - ((b : ℝ) - (τ : ℝ)) = -d by ring,
      abs_neg, abs_of_pos hd]
    linarith [hdρα]
  have hαqO : IntrinsicGeodesic.GlobalGeodesic.curve α tq ∈ O :=
    hαball (Metric.mem_ball.mpr htqdist)
  have hαq : IntrinsicGeodesic.GlobalGeodesic.curve α tq = γ q :=
    hagree q hτq.le hqb.le
  let β := IntrinsicGeodesic.GlobalGeodesic.rescale
    (IntrinsicGeodesic.GlobalGeodesic.shift α tq) d hd
  have hβzero : IntrinsicGeodesic.GlobalGeodesic.curve β 0 = γ q := by
    simpa only [β, IntrinsicGeodesic.GlobalGeodesic.rescale_curve,
      IntrinsicGeodesic.GlobalGeodesic.shift_curve, mul_zero, add_zero] using hαq
  have htqd : tq + d = tb := by
    dsimp [tq, tb, q]
    ring
  have hβone : IntrinsicGeodesic.GlobalGeodesic.curve β 1 = γ b := by
    simp only [β, IntrinsicGeodesic.GlobalGeodesic.rescale_curve,
      IntrinsicGeodesic.GlobalGeodesic.shift_curve, mul_one, htqd]
    exact hαb
  have hspeedα (t : ℝ) :
      ‖IntrinsicGeodesic.GlobalGeodesic.velocity α t‖ = 1 := by
    exact (IntrinsicGeodesic.GlobalGeodesic.norm_velocity_eq_initial
      (I := I) (M := M) α hcov.2 t).trans hv₀
  let A : TM xb := by
    change TM (γ b)
    exact hαb ▸ IntrinsicGeodesic.GlobalGeodesic.velocity α tb
  have hAheq : HEq A (IntrinsicGeodesic.GlobalGeodesic.velocity α tb) := by
    dsimp only [A]
    exact eqRec_heq hαb (IntrinsicGeodesic.GlobalGeodesic.velocity α tb)
  have hAnorm : ‖A‖ = 1 := by
    exact (tangent_norm_eq_of_heq hαb.symm hAheq).trans (hspeedα tb)
  have hβspeed0 : ‖IntrinsicGeodesic.GlobalGeodesic.velocity β 0‖ = d := by
    calc
      ‖IntrinsicGeodesic.GlobalGeodesic.velocity β 0‖ =
          ‖d • IntrinsicGeodesic.GlobalGeodesic.velocity α tq‖ :=
        IntrinsicGeodesic.GlobalGeodesic.norm_velocity_eq_initial
          (I := I) (M := M) β hcov.2 0
      _ = d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, hspeedα, mul_one]
  let s₀ : E × E :=
    (extChartAt I xb (IntrinsicGeodesic.GlobalGeodesic.curve β 0),
      (trivializationAt E TM xb).continuousLinearMapAt ℝ
        (IntrinsicGeodesic.GlobalGeodesic.curve β 0)
        (IntrinsicGeodesic.GlobalGeodesic.velocity β 0))
  have hs₀source : s₀ ∈ R.source := by
    apply hsmallState (IntrinsicGeodesic.GlobalGeodesic.curve β 0)
    · rw [hβzero, ← hαq]
      exact hαqO.1.1.2
    · rw [hβspeed0]
      exact hdδ
  have hβframe : ∀ t ∈ Ioo (-1 : ℝ) 2,
      IntrinsicAcceleration.smoothFrameAgreementSet
        (I := I) (M := M) xb basis ∈
          𝓝 (IntrinsicGeodesic.GlobalGeodesic.curve β t) := by
    intro t ht
    have htime : dist (tq + d * t) tb < ρα := by
      rw [Real.dist_eq]
      have htbound : |t - 1| < 2 := by
        rw [abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      have hcalc : tq + d * t - tb = d * (t - 1) := by rw [← htqd]; ring
      rw [hcalc, abs_mul, abs_of_pos hd]
      nlinarith [hdρα]
    have hmemO : IntrinsicGeodesic.GlobalGeodesic.curve β t ∈ O := by
      rw [show IntrinsicGeodesic.GlobalGeodesic.curve β t =
        IntrinsicGeodesic.GlobalGeodesic.curve α (tq + d * t) by
          simp only [β, IntrinsicGeodesic.GlobalGeodesic.rescale_curve,
            IntrinsicGeodesic.GlobalGeodesic.shift_curve]]
      exact hαball (Metric.mem_ball.mpr htime)
    exact mem_of_superset (hUframeOpen.mem_nhds hmemO.1.1.1) hUframeSub
  have hflow :=
    LocalGeodesicData.coordinateFlow_eq_globalGeodesic_fixedChartState
      (I := I) (M := M) cov xb basis hcov.2 G Φ hΦzero hΦcurve
        (hactual s₀ hs₀source) β (s := s₀) rfl hβframe
  have hflowOne := hflow (show (1 : ℝ) ∈ Ioo (-1 : ℝ) 2 by norm_num)
  let p : E := extChartAt I xb (γ q)
  have hpV : p ∈ V := by
    change extChartAt I xb (γ q) ∈ V
    rw [← hαq]
    exact hαqO.2.2
  have hpqTarget : (p, zb) ∈ R.target := hVV ⟨hpV, hzbV⟩
  have hs₀fst : s₀.1 = p := by simp only [s₀, p, hβzero]
  have hs₀end : (Φ s₀ 1).1 = zb := by
    have h := congrArg Prod.fst hflowOne
    simpa only [hβone, zb] using h
  have hs₀eq : s₀ = R.symm (p, zb) :=
    hunique s₀ hs₀source hs₀fst hs₀end hpqTarget
  let T : TM xb := LocalGeodesicData.coordinateFrameCombination
    (I := I) (M := M) (x₀ := xb) basis
      (Φ (R.symm (p, zb)) 1).2 xb
  have hT : T = IntrinsicGeodesic.GlobalGeodesic.velocity β 1 := by
    have hsecond := congrArg Prod.snd hflowOne
    rw [hs₀eq] at hsecond
    change (Φ (R.symm (p, zb)) 1).2 =
      (trivializationAt E TM xb).continuousLinearMapAt ℝ
        (IntrinsicGeodesic.GlobalGeodesic.curve β 1)
        (IntrinsicGeodesic.GlobalGeodesic.velocity β 1) at hsecond
    rw [hβone] at hsecond
    change LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := xb) basis
        (Φ (R.symm (p, zb)) 1).2 xb = _
    rw [hsecond,
      LocalGeodesicData.coordinateFrameCombination_eq_symmL
        (I := I) (M := M) (x₀ := xb) basis (mem_chart_source H xb)]
    exact (trivializationAt E TM xb).symmL_continuousLinearMapAt
      (mem_baseSet_trivializationAt E TM xb)
        (IntrinsicGeodesic.GlobalGeodesic.velocity β 1)
  have hβvelOne : IntrinsicGeodesic.GlobalGeodesic.velocity β 1 =
      d • IntrinsicGeodesic.GlobalGeodesic.velocity α tb := by
    rw [IntrinsicGeodesic.GlobalGeodesic.rescale_velocity,
      IntrinsicGeodesic.GlobalGeodesic.shift_velocity]
    rw [show tq + d * 1 = tb by simpa using htqd]
    rfl
  have hTscaled : T = d • IntrinsicGeodesic.GlobalGeodesic.velocity α tb :=
    hT.trans hβvelOne
  have hTscaledA : T = d • A := by
    apply eq_of_heq
    exact (heq_of_eq hTscaled).trans
      (tangent_smul_heq_of_heq d hAheq).symm
  have hTnorm : ‖T‖ = d := by
    rw [hTscaledA, norm_smul_of_nonneg hd.le, hAnorm, mul_one]
  have hqSource : γ q ∈ (extChartAt I xb).source := by
    rw [← hαq]
    exact hαqO.2.1
  have hxp : (extChartAt I xb).symm p = γ q := by
    exact (extChartAt I xb).left_inv hqSource
  have hincomingDistance : dist ((extChartAt I xb).symm p)
      ((extChartAt I xb).symm zb) = ‖T‖ := by
    rw [hxp, show (extChartAt I xb).symm zb = γ b by simpa only [xb] using hyb,
      hdist q b, abs_of_pos (sub_pos.mpr hqb), hTnorm]
    dsimp [q]
    ring
  let βg := Classical.choose (α.local_germ tb)
  have hβgerm : (fun u ↦ α.state (tb + u)) =ᶠ[𝓝 (0 : ℝ)]
      IntrinsicGeodesic.localState βg :=
    Classical.choose_spec (α.local_germ tb)
  -- The displayed choice above is definitionally the same germ; from here
  -- onward use its own metric neighbourhood radius.
  obtain ⟨ρg, hρg, hgball⟩ := Metric.mem_nhds_iff.mp hβgerm
  let ε : ℝ := min (ργ / 2)
    (min (rV / 2) (min (ρg / 2) (βg.solution.radius / 2)))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by linarith) (by linarith [βg.solution.radius_pos])))
  refine ⟨ε, hε, ?_⟩
  intro s hbs hsbε
  let e : ℝ := (s : ℝ) - (b : ℝ)
  have he : 0 < e := sub_pos.mpr hbs
  have heργ : e < ργ := by
    have hle : ε ≤ ργ / 2 := min_le_left _ _
    linarith
  have herV : e < rV := by
    have hle : ε ≤ rV / 2 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have heρg : e < ρg := by
    have hle : ε ≤ ρg / 2 :=
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith
  have heβg : e < βg.solution.radius := by
    have hle : ε ≤ βg.solution.radius / 2 :=
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  have hsball : s ∈ Metric.ball b ργ := by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    rw [abs_of_pos he]
    exact heργ
  have hsO : γ s ∈ O := hγball hsball
  obtain ⟨uOut, huOutW, hFoutU⟩ := hsO.1.2.2
  obtain ⟨outgoing, houtRadius, houtCoordinate, _houtLength, _houtGauss,
      _houtSpeed, _houtSpeedAll, _houtDistRiem, houtDist, houtSubdist,
      _houtMin⟩ := hgeodesicOut uOut huOutW
  have houtEndpoint : (extChartAt I xb).symm (Fout uOut) = γ s := by
    rw [hFoutU]
    exact (extChartAt I xb).left_inv hsO.1.2.1
  have houtCurveZero : LocalChartSecondOrderSolution.curve outgoing 0 = xb :=
    LocalChartSecondOrderSolution.curve_initial outgoing
  have houtCurveOne : LocalChartSecondOrderSolution.curve outgoing 1 = γ s := by
    change (extChartAt I xb).symm (outgoing.coordinate 1) = γ s
    rw [houtCoordinate]
    exact houtEndpoint
  let vOut : TM xb :=
    (trivializationAt E TM xb).symmL ℝ xb uOut
  have hvOutFrame : LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := xb) basis uOut xb = vOut := by
    exact LocalGeodesicData.coordinateFrameCombination_eq_symmL
      (I := I) (M := M) (x₀ := xb) basis (mem_chart_source H xb) uOut
  have hvOutNorm : ‖vOut‖ = e := by
    rw [← hvOutFrame, ← houtDist, houtEndpoint, hdist b s,
      abs_of_pos (sub_pos.mpr hbs)]
  have hframeNorm :
      ‖LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := xb) basis uOut xb‖ = e :=
    (congrArg norm hvOutFrame).trans hvOutNorm
  have houtSubdist' : ∀ t ∈ Ioo (0 : ℝ) 1,
      dist xb (LocalChartSecondOrderSolution.curve outgoing t) = e * t ∧
      dist (LocalChartSecondOrderSolution.curve outgoing t) (γ s) =
        e * (1 - t) := by
    intro t ht
    constructor
    · calc
        dist xb (LocalChartSecondOrderSolution.curve outgoing t) =
            ‖LocalGeodesicData.coordinateFrameCombination
              (I := I) (M := M) (x₀ := xb) basis uOut xb‖ * t :=
          (houtSubdist t ht).1
        _ = e * t := by rw [hframeNorm]
    · calc
        dist (LocalChartSecondOrderSolution.curve outgoing t) (γ s) =
            ‖LocalGeodesicData.coordinateFrameCombination
              (I := I) (M := M) (x₀ := xb) basis uOut xb‖ * (1 - t) := by
          rw [← houtEndpoint]
          exact (houtSubdist t ht).2
        _ = e * (1 - t) := by rw [hframeNorm]
  have hchain : dist (γ q) (γ s) =
      dist (γ q) xb + dist xb (γ s) := by
    change dist (γ q) (γ s) = dist (γ q) (γ b) + dist (γ b) (γ s)
    rw [hdist q s, hdist q b, hdist b s,
      abs_of_pos (sub_pos.mpr (hqb.trans hbs)),
      abs_of_pos (sub_pos.mpr hqb), abs_of_pos (sub_pos.mpr hbs)]
    ring
  have hβsource : ∀ t ∈ Icc (0 : ℝ) 1,
      LocalChartSecondOrderSolution.curve outgoing t ∈
        (extChartAt I xb).source := by
    intro t ht
    exact (extChartAt I xb).map_target
      (outgoing.coordinate_mem_target t (by
        rw [houtRadius]
        constructor <;> linarith [ht.1, ht.2]))
  have hβtarget : ∀ t ∈ Icc (0 : ℝ) 1,
      (p, extChartAt I xb
        (LocalChartSecondOrderSolution.curve outgoing t)) ∈ R.target := by
    intro t ht
    apply hVV
    refine ⟨hpV, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      simpa only [houtCurveZero, zb] using hzbV
    by_cases ht1 : t = 1
    · subst t
      rw [houtCurveOne]
      exact hsO.2.2
    have htIoo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    have hcurveBall : LocalChartSecondOrderSolution.curve outgoing t ∈
        Metric.ball xb rV := by
      rw [Metric.mem_ball, dist_comm, houtSubdist' t htIoo |>.1]
      nlinarith [htIoo.1, htIoo.2]
    exact (hballV hcurveBall).2
  let αOut := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution
    (I := I) (M := M) outgoing
  have hαOutCurve : IntrinsicGeodesic.LocalGeodesic.curve αOut =
      LocalChartSecondOrderSolution.curve outgoing :=
    IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_curve outgoing
  have hαOutZero : IntrinsicGeodesic.LocalGeodesic.curve αOut 0 = xb := by
    rw [hαOutCurve]
    exact houtCurveZero
  have hαOutOne : IntrinsicGeodesic.LocalGeodesic.curve αOut 1 = γ s := by
    rw [hαOutCurve]
    exact houtCurveOne
  let KY : TM ((extChartAt I xb).symm zb) :=
    LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := xb) basis uOut ((extChartAt I xb).symm zb)
  have hKYheq : HEq KY vOut := by
    dsimp only [KY]
    rw [hyb, hvOutFrame]
  have hKYnorm : ‖KY‖ = e :=
    (tangent_norm_eq_of_heq hyb hKYheq).trans hvOutNorm
  let TY : TM ((extChartAt I xb).symm zb) :=
    LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := xb) basis
        (Φ (R.symm (p, zb)) 1).2 ((extChartAt I xb).symm zb)
  have hTYheq : HEq TY T := by
    dsimp only [TY, T]
    rw [hyb]
  have hTYnorm : ‖TY‖ = ‖T‖ := tangent_norm_eq_of_heq hyb hTYheq
  have hcoordDeriv : HasDerivAt outgoing.coordinate uOut 0 := by
    have hzero : (0 : ℝ) ∈ Ioo (-outgoing.radius) outgoing.radius := by
      rw [houtRadius]
      norm_num
    have hraw := outgoing.coordinate_hasDeriv 0 hzero
    rw [outgoing.velocity_initial] at hraw
    exact hraw
  have hcoordZero : outgoing.coordinate 0 = zb := by
    simpa only [zb] using outgoing.coordinate_initial
  have hcoordTarget : ∀ t ∈ Icc (0 : ℝ) 1,
      (p, outgoing.coordinate t) ∈ R.target := by
    intro t ht
    have htime : t ∈ Ioo (-outgoing.radius) outgoing.radius := by
      rw [houtRadius]
      constructor <;> linarith [ht.1, ht.2]
    simpa only [LocalChartSecondOrderSolution.curve_eq_chart outgoing htime] using
      hβtarget t ht
  have htail := distance_along_exact_metric_tail
    (a := (extChartAt I xb).symm p)
    (c := (extChartAt I xb).symm zb) (d := γ s)
    (beta := LocalChartSecondOrderSolution.curve outgoing) (C := e)
    (houtCurveZero.trans hyb.symm) houtCurveOne
    (by simpa only [hxp, hyb] using hchain)
    (by
      rw [hyb]
      change dist (γ b) (γ s) = e
      rw [hdist b s, abs_of_pos (sub_pos.mpr hbs)])
    (by simpa only [hyb] using houtSubdist')
  have hcoordDistance : ∀ t ∈ Icc (0 : ℝ) 1,
      dist ((extChartAt I xb).symm p)
          ((extChartAt I xb).symm (outgoing.coordinate t)) =
        dist ((extChartAt I xb).symm p) ((extChartAt I xb).symm zb) +
          t * ‖KY‖ := by
    intro t ht
    calc
      dist ((extChartAt I xb).symm p)
          ((extChartAt I xb).symm (outgoing.coordinate t)) =
          dist ((extChartAt I xb).symm p) (outgoing.curve t) := rfl
      _ = dist ((extChartAt I xb).symm p) ((extChartAt I xb).symm zb) +
          e * t := htail t ht
      _ = dist ((extChartAt I xb).symm p) ((extChartAt I xb).symm zb) +
          t * ‖KY‖ := by rw [hKYnorm]; ring
  have halign :=
    LocalGeodesicData.twoPointConnector_sameDirection_of_exactDistanceCurve_right
      (I := I) (M := M) cov xb basis hcov.2 hcov.1 G Φ R hG hGcompact
        hΦzero hΦcurve hΦsmooth hR hinverseSmooth hactual hframe
        (fun a c ↦ finiteRiemannianMetricSpace_riemannianEDist_eq_ofReal_dist
          (I := I) (M := M) g a c)
        hpqTarget outgoing.coordinate uOut hcoordDeriv hcoordZero hcoordTarget
        hcoordDistance
        (by simpa only [TY] using hincomingDistance.trans hTYnorm.symm)
  have halign' : ‖vOut‖ • T = ‖T‖ • vOut := by
    exact sameDirection_of_tangent_heq hyb hKYheq hTYheq (by
      simpa only [TY, KY] using halign)
  have hnormalized := inv_smul_eq_inv_smul_of_norm_smul_eq
    hd he hTnorm hvOutNorm halign'
  have hleftNorm : d⁻¹ • T = A := by
    calc
      d⁻¹ • T = d⁻¹ • (d • A) :=
        congrArg (fun v : TM xb ↦ d⁻¹ • v) hTscaledA
      _ = A := by
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hd), one_smul]
  have hvOutNormalized : e⁻¹ • vOut = A := by
    rw [hleftNorm] at hnormalized
    exact hnormalized.symm
  let αOutUnit := IntrinsicGeodesic.LocalGeodesic.rescale
    αOut e⁻¹ (inv_pos.mpr he)
  have hstateLocal : IntrinsicGeodesic.localState βg 0 =
      IntrinsicGeodesic.localState αOutUnit 0 := by
    have hgzero := hβgerm.self_of_nhds
    have hgzero' : α.state tb = IntrinsicGeodesic.localState βg 0 := by
      simpa only [add_zero] using hgzero
    apply Bundle.TotalSpace.ext
    · calc
        (IntrinsicGeodesic.localState βg 0).proj =
            (IntrinsicGeodesic.GlobalGeodesic.curve α tb) := by
              rw [← hgzero']
              rfl
        _ = xb := hαb
        _ = (IntrinsicGeodesic.localState αOutUnit 0).proj := by
          change xb = IntrinsicGeodesic.LocalGeodesic.curve αOutUnit 0
          rw [IntrinsicGeodesic.LocalGeodesic.curve_initial]
    · have hleft : HEq (IntrinsicGeodesic.localState βg 0).snd
          (IntrinsicGeodesic.GlobalGeodesic.velocity α tb) := by
          rw [← hgzero']
          change HEq (IntrinsicGeodesic.GlobalGeodesic.velocity α tb)
            (IntrinsicGeodesic.GlobalGeodesic.velocity α tb)
          rfl
      have hleftA : HEq (IntrinsicGeodesic.localState βg 0).snd A :=
        hleft.trans hAheq.symm
      have hright : (IntrinsicGeodesic.localState αOutUnit 0).snd =
          e⁻¹ • vOut := by
        exact IntrinsicGeodesic.LocalGeodesic.velocity_initial αOutUnit
      exact hleftA.trans (heq_of_eq (hvOutNormalized.symm.trans hright.symm))
  have hlocalEq :=
    IntrinsicGeodesic.LocalGeodesic.curve_eqOn_common_interval_of_initial_state_eq
      βg αOutUnit hstateLocal
  have hαOutUnitRadius : αOutUnit.solution.radius = 2 * e := by
    simp only [αOutUnit, IntrinsicGeodesic.LocalGeodesic.rescale_radius,
      αOut, IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_radius,
      houtRadius]
    field_simp
  have heInterval : e ∈ Ioo
      (-(min βg.solution.radius αOutUnit.solution.radius))
      (min βg.solution.radius αOutUnit.solution.radius) := by
    rw [hαOutUnitRadius]
    constructor
    · have hminPos : 0 < min βg.solution.radius (2 * e) :=
        lt_min βg.solution.radius_pos (by positivity)
      linarith
    · exact lt_min heβg (by linarith)
  have hglobalGerm : α.state (tb + e) =
      IntrinsicGeodesic.localState βg e := by
    apply hgball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos he]
    exact heρg
  have hcurveGlobal : IntrinsicGeodesic.GlobalGeodesic.curve α (tb + e) =
      IntrinsicGeodesic.LocalGeodesic.curve βg e :=
    congrArg Bundle.TotalSpace.proj hglobalGerm
  calc
    IntrinsicGeodesic.GlobalGeodesic.curve α ((s : ℝ) - (τ : ℝ)) =
        IntrinsicGeodesic.GlobalGeodesic.curve α (tb + e) := by
          congr 2
          dsimp [tb, e]
          ring
    _ = IntrinsicGeodesic.LocalGeodesic.curve βg e := hcurveGlobal
    _ = IntrinsicGeodesic.LocalGeodesic.curve αOutUnit e :=
      hlocalEq heInterval
    _ = IntrinsicGeodesic.LocalGeodesic.curve αOut (e⁻¹ * e) :=
      IntrinsicGeodesic.LocalGeodesic.rescale_curve
        αOut e⁻¹ (inv_pos.mpr he) e
    _ = IntrinsicGeodesic.LocalGeodesic.curve αOut 1 := by
      rw [inv_mul_cancel₀ (ne_of_gt he)]
    _ = γ s := hαOutOne

end BonnetMyersEntry
