/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisHolomorphicJoint
public import LeanPool.NavierStokesAndEuler.NavierStokes.HolomorphicFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReferenceJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.StressActivation
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Algebra.Group.EvenFunction

@[expose] public section

/-!
# A common holomorphic parameter neighborhood through initial activation

All continuations below are explicit integrals of the actual natural slopes.
The complex neighborhood is obtained from compactness and real positivity.
-/

noncomputable section

namespace NavierStokes.ActivationHolomorphic

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff


abbrev CPoint := ℝ × ℂ
abbrev CField := CPoint → ℂ

def radial (F : CField) (p : CPoint) : ℂ := deriv (fun x => F (x, p.2)) p.1

/-- Joint real smoothness and actual holomorphic parameter slices. -/
structure Regular (S : Set ℝ) (Ω : Set ℂ) (F : CField) : Prop where
  smooth : ContDiffOn ℝ ∞ F (S ×ˢ Ω)
  holomorphic : ∀ x ∈ S, DifferentiableOn ℂ (fun z => F (x, z)) Ω

theorem radial_smooth {S : Set ℝ} {Ω : Set ℂ} (hS : IsOpen S) (hΩ : IsOpen Ω)
    {F : CField} (hF : ContDiffOn ℝ ∞ F (S ×ˢ Ω)) :
    ContDiffOn ℝ ∞ (radial F) (S ×ˢ Ω) := by
  intro p hp
  have hbase := hF.contDiffAt ((hS.prod hΩ).mem_nhds hp)
  have hG : ContDiffAt ℝ ∞ (fun w : CPoint × ℝ => F (w.2, w.1.2)) (p, p.1) :=
    hbase.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact ((hG.fderiv contDiffAt_fst (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

/-- Radial differentiation preserves holomorphy on an arbitrary open radial
domain. The difference quotients converge uniformly on each compact disk. -/
theorem radial_holomorphic {S : Set ℝ} {Ω : Set ℂ} (hS : IsOpen S) (hΩ : IsOpen Ω)
    {F : CField} (hF : ContDiffOn ℝ ∞ F (S ×ˢ Ω))
    (hhol : ∀ r ∈ S, DifferentiableOn ℂ (fun z => F (r, z)) Ω)
    {r : ℝ} (hr : r ∈ S) : DifferentiableOn ℂ (fun z => radial F (r, z)) Ω := by
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  let σ := ε / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hDisk : closedBall z σ ⊆ Ω :=
    (closedBall_subset_ball (by dsimp [σ]; linarith : σ < ε)).trans hεsub
  let V : ℝ → C(CauchyRestriction.Disk z σ, ℂ) :=
    CompactSmoothFamily.family (closedBall z σ) F
  have hV : ContDiffOn ℝ ∞ V S :=
    CompactSmoothFamily.contDiffOn_family_of_joint (closedBall z σ) S Ω
      hS hΩ hDisk F hF
  have hval (s : ℝ) (hs : s ∈ S) (w : CauchyRestriction.Disk z σ) : V s w = F (s, w) :=
    CompactSmoothFamily.family_apply_of_joint (closedBall z σ) hDisk F hF.continuousOn hs w
  have hd : HasDerivAt V (deriv V r) r :=
    (hV.contDiffAt (hS.mem_nhds hr)).differentiableAt (by simp) |>.hasDerivAt
  have hderiv (w : CauchyRestriction.Disk z σ) : deriv V r w = radial F (r, w) := by
    have he := (ContinuousMap.evalCLM ℝ w).hasFDerivAt.comp_hasDerivAt r hd
    have heq : (fun s => V s w) =ᶠ[𝓝 r] (fun s => F (s, w)) := by
      filter_upwards [hS.mem_nhds hr] with s hs
      exact hval s hs w
    exact (he.congr_of_eventuallyEq heq.symm).deriv.symm
  let Q : ℝ → ℂ → ℂ := fun t w => t⁻¹ • (F (r + t, w) - F (r, w))
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), r + t ∈ S := by
    exact
      (continuousAt_const.fun_add continuousAt_id : ContinuousAt (fun t : ℝ => r + t) 0).eventually
        (hS.mem_nhds (by simpa only [add_zero] using hr))
  have hlim : TendstoUniformlyOn Q (fun w => radial F (r, w)) (𝓝[≠] (0 : ℝ)) (ball z σ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have ht := Metric.tendsto_nhds.mp hd.tendsto_slope_zero δ hδ
    filter_upwards [ht, hnear.filter_mono nhdsWithin_le_nhds] with t ht htr
    intro w hw
    let w' : CauchyRestriction.Disk z σ := ⟨w, ball_subset_closedBall hw⟩
    have hb := (deriv V r - t⁻¹ • (V (r + t) - V r)).norm_coe_le_norm w'
    have hn : ‖radial F (r, w) - Q t w‖ ≤
        ‖deriv V r - t⁻¹ • (V (r + t) - V r)‖ := by
      simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, hderiv,
        hval (r + t) htr, hval r hr, Q, w'] using hb
    rw [dist_eq_norm]
    apply hn.trans_lt
    simpa only [dist_eq_norm, norm_sub_rev] using ht
  have hQ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), DifferentiableOn ℂ (Q t) (ball z σ) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with t ht
    exact (((hhol (r + t) ht).sub (hhol r hr)).const_smul t⁻¹).mono
      (ball_subset_closedBall.trans hDisk)
  have hdiff := hlim.tendstoLocallyUniformlyOn.differentiableOn hQ isOpen_ball
  exact (hdiff.differentiableAt (Metric.ball_mem_nhds z hσ)).differentiableWithinAt

theorem Regular.radial {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω) : Regular S Ω (radial F) :=
  ⟨radial_smooth hS hΩ hF.smooth, fun _ hr => radial_holomorphic hS hΩ hF.smooth hF.holomorphic hr⟩

theorem Regular.mono {S S' : Set ℝ} {Ω Ω' : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : S' ⊆ S) (hΩ : Ω' ⊆ Ω) : Regular S' Ω' F :=
  ⟨hF.smooth.mono (Set.prod_mono hS hΩ), fun _ hx => (hF.holomorphic _ (hS hx)).mono hΩ⟩

theorem regular_const (S : Set ℝ) (Ω : Set ℂ) (c : ℂ) : Regular S Ω (fun _ => c) :=
  ⟨contDiffOn_const, fun _ _ => differentiableOn_const c⟩

theorem Regular.add {S : Set ℝ} {Ω : Set ℂ} {F G : CField}
    (hF : Regular S Ω F) (hG : Regular S Ω G) : Regular S Ω (fun p => F p + G p) :=
  ⟨hF.smooth.add hG.smooth, fun x hx => (hF.holomorphic x hx).add (hG.holomorphic x hx)⟩

theorem Regular.mul {S : Set ℝ} {Ω : Set ℂ} {F G : CField}
    (hF : Regular S Ω F) (hG : Regular S Ω G) : Regular S Ω (fun p => F p * G p) :=
  ⟨hF.smooth.mul hG.smooth, fun x hx => (hF.holomorphic x hx).mul (hG.holomorphic x hx)⟩

theorem Regular.cexp {S : Set ℝ} {Ω : Set ℂ} {F : CField} (hF : Regular S Ω F) :
    Regular S Ω (fun p => Complex.exp (F p)) :=
  ⟨((Complex.contDiff_exp : ContDiff ℂ ∞ Complex.exp).restrict_scalars ℝ).comp_contDiffOn hF.smooth,
    fun x hx => (hF.holomorphic x hx).cexp⟩

theorem Regular.clog {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hne : ∀ p ∈ S ×ˢ Ω, F p ∈ Complex.slitPlane) :
    Regular S Ω (fun p => Complex.log (F p)) := by
  constructor
  · intro p hp
    exact ((Complex.contDiffAt_log (hne p hp)).restrict_scalars ℝ |>.comp_contDiffWithinAt p
      (hF.smooth p hp))
  · intro x hx z hz
    exact ((hF.holomorphic x hx z hz).clog (hne (x,z) ⟨hx,hz⟩))

theorem regular_parameter {S : Set ℝ} {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Ω) : Regular S Ω (fun p => g p.2) :=
  ⟨(hg.contDiffOn_of_completeSpace.restrict_scalars ℝ).comp contDiffOn_snd (fun _ hp => hp.2),
    fun _ _ => hg.differentiableOn⟩

theorem regular_radius {S : Set ℝ} {Ω : Set ℂ} {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g S) :
    Regular S Ω (fun p => (g p.1 : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn (hg.comp contDiffOn_fst (fun _ hp => hp.1)),
    fun x _ => by
      change DifferentiableOn ℂ (fun _ : ℂ => (g x : ℂ)) Ω
      exact differentiableOn_const _⟩

section CompactIntegral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {s : Set H} {G : H × ℝ → ℂ}

theorem compact_integral_smooth (hs : IsOpen s)
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ G (p,t)) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, G (p,t)) s := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hs zero_le_one
  · intro t ht p hp
    exact ((hG p hp t ht).comp p (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro k
    rintro ⟨p,t⟩ ⟨hp,ht⟩
    have hflip : ContDiffAt ℝ ∞ (Function.uncurry (fun t p => G (p,t))) (t,p) :=
      (hG p hp t ht).comp (t,p) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hd := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv (fun t p => G (p,t)) k t p
      hflip
    exact ((hd.comp (p,t) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt).continuousWithinAt

end CompactIntegral

abbrev Segment := ↥(Icc (0 : ℝ) 1)

def segmentExtend (f : C(Segment, ℂ)) (t : ℝ) : ℂ :=
  f (projIcc 0 1 zero_le_one t)

theorem segmentExtend_continuous (f : C(Segment, ℂ)) : Continuous (segmentExtend f) :=
  f.continuous.comp continuous_projIcc

theorem segmentIntegral_norm (f : C(Segment, ℂ)) :
    ‖∫ t in (0 : ℝ)..1, segmentExtend f t‖ ≤ 1 * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := segmentExtend f)
    (fun t _ => f.norm_coe_le_norm (projIcc 0 1 zero_le_one t))
  simpa only [sub_zero, abs_one, mul_one, one_mul] using h

noncomputable def segmentIntegral : C(Segment, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous {
    toFun f := ∫ t in (0 : ℝ)..1, segmentExtend f t
    map_add' := by
      intro f g
      exact intervalIntegral.integral_add
        ((segmentExtend_continuous f).intervalIntegrable 0 1)
        ((segmentExtend_continuous g).intervalIntegrable 0 1)
    map_smul' := by
      intro c f
      exact intervalIntegral.integral_smul c (segmentExtend f)
  } 1 segmentIntegral_norm

/-- Holomorphic integration only requires smoothness near the actual compact
integration segment, with no assumptions outside that segment. -/
theorem compact_integral_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : ℂ × ℝ → ℂ}
    (hG : ∀ z ∈ Ω, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ G (z,t))
    (hhol : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => G (z,t)) Ω) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, G (z,t)) Ω := by
  let K : Set ℝ := Icc 0 1
  let D : ℂ × ℝ → ℂ →L[ℝ] ℂ := fun p => fderiv ℝ (fun z => G (z,p.2)) p.1
  have hGc : ContinuousOn G (Ω ×ˢ K) := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    exact (hG z hz t ht).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Ω ×ˢ K) := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    have hdup : ContDiffAt ℝ ∞ (fun w : (ℂ × ℝ) × ℂ => G (w.2,w.1.2)) ((z,t),z) :=
      (hG z hz t ht).comp ((z,t),z) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
    have hD : ContDiffAt ℝ ∞ D (z,t) := hdup.fderiv contDiffAt_fst (by simp)
    exact hD.continuousAt.continuousWithinAt
  have hf : DifferentiableOn ℂ (CompactSmoothFamily.family K G) Ω := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply HolomorphicFamily.differentiableAt_of_evaluations (CompactSmoothFamily.family K G)
    · exact (CompactSmoothFamily.hasFDerivAt_family K hΩ G D hGc hDc
        (fun z hz t => ((hG z hz t t.2).comp z
          (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp) |>.hasFDerivAt)
            hz).differentiableAt
    · intro t
      apply ((hhol t t.2).differentiableAt (hΩ.mem_nhds hz)).congr_of_eventuallyEq
      filter_upwards [hΩ.mem_nhds hz] with w hw
      exact CompactSmoothFamily.family_apply K G w
        (CompactSmoothFamily.slice_continuous hGc hw) t
  have hi := (segmentIntegral : C(Segment, ℂ) →L[ℂ] ℂ).differentiable.comp_differentiableOn hf
  apply hi.congr
  intro z hz
  change (∫ t in (0 : ℝ)..1, G (z,t)) = ∫ t in (0 : ℝ)..1,
    segmentExtend (CompactSmoothFamily.family K G z) t
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ K := by simpa only [K,uIcc_of_le zero_le_one] using ht
  rw [segmentExtend,projIcc_of_mem zero_le_one ht']
  exact (CompactSmoothFamily.family_apply K G z
    (CompactSmoothFamily.slice_continuous hGc hz) ⟨t,ht'⟩).symm

def average (F : CField) (p : CPoint) : ℂ := ∫ t in (0 : ℝ)..1, F (t*p.1,p.2)
def primitive (F : CField) (p : CPoint) : ℂ := ∫ x in (0 : ℝ)..p.1, F (x,p.2)

theorem primitive_eq_mul_average (F : CField) (p : CPoint) :
    primitive F p = (p.1 : ℂ) * average F p := by
  have he := intervalIntegral.smul_integral_comp_mul_left (fun x => F (x,p.2)) p.1 (a := 0) (b := 1)
  simpa only [primitive,average,mul_zero,mul_one,Complex.real_smul,mul_comm] using he.symm

theorem Regular.average {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω)
    (hscale : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, t*x ∈ S) : Regular S Ω (average F) := by
  constructor
  · unfold ActivationHolomorphic.average
    apply compact_integral_smooth (G := fun q : CPoint × ℝ => F (q.2*q.1.1,q.1.2)) (hS.prod hΩ)
    intro p hp t ht
    have hb : ContDiffAt ℝ ∞ F (t*p.1,p.2) :=
      hF.smooth.contDiffAt ((hS.prod hΩ).mem_nhds ⟨hscale p.1 hp.1 t ht,hp.2⟩)
    exact hb.comp (p,t) ((contDiffAt_snd.mul contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  · intro x hx
    unfold ActivationHolomorphic.average
    apply compact_integral_holomorphic (G := fun q : ℂ × ℝ => F (q.2*x,q.1)) hΩ
    · intro z hz t ht
      have hb : ContDiffAt ℝ ∞ F (t*x,z) :=
        hF.smooth.contDiffAt ((hS.prod hΩ).mem_nhds ⟨hscale x hx t ht,hz⟩)
      exact hb.comp (z,t) ((contDiffAt_snd.mul contDiffAt_const).prodMk contDiffAt_fst)
    · intro t ht
      exact hF.holomorphic (t*x) (hscale x hx t ht)

theorem Regular.primitive {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω)
    (hscale : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, t*x ∈ S) : Regular S Ω (primitive F) := by
  have hb := (regular_radius (Ω := Ω) (contDiffOn_id : ContDiffOn ℝ ∞ id S)).mul (hF.average hS hΩ
    hscale)
  have he : ActivationHolomorphic.primitive F =
      (fun p => (p.1 : ℂ) * ActivationHolomorphic.average F p) := funext (primitive_eq_mul_average
        F)
  rw [he]
  exact hb

theorem radial_hasDerivAt {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hS : IsOpen S) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F (S ×ˢ Ω))
    {p : CPoint} (hp : p ∈ S ×ˢ Ω) :
    HasDerivAt (fun x => F (x,p.2)) (radial F p) p.1 :=
  (((hF.contDiffAt ((hS.prod hΩ).mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasDerivAt

theorem slice_continuous {Ω : Set ℂ} {F : CField} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ω)) {z : ℂ} (hz : z ∈ Ω) :
    Continuous (fun x => F (x,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((hF.contDiffAt ((isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _,hz⟩)).comp x
    (contDiffAt_id.prodMk contDiffAt_const)).continuousAt

theorem primitive_hasDerivAt {Ω : Set ℂ} {F : CField} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ Ω)) {p : CPoint} (hp : p.2 ∈ Ω) :
    HasDerivAt (fun x => primitive F (x,p.2)) (F p) p.1 := by
  have hc := slice_continuous hΩ hF hp
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 p.1)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

def dampedSlope (δ : ℝ) (G : CField) (p : CPoint) : ℂ :=
  (ReferencePath.slopeCutoff δ p.1 : ℂ) * radial G p

def continuation (δ : ℝ) (G : CField) (p : CPoint) : ℂ :=
  G (0,p.2) + primitive (dampedSlope δ G) p

theorem regular_dampedSlope {T δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G) :
    Regular univ Ω (dampedSlope δ G) := by
  have hD := hG.radial isOpen_Iio hΩ
  constructor
  · intro p hp
    by_cases ht : p.1 < T
    · exact (((Complex.ofRealCLM.contDiff.comp (ReferencePath.slopeCutoff_smooth δ)).comp
        contDiff_fst).contDiffAt.mul
          (hD.smooth.contDiffAt ((isOpen_Iio.prod hΩ).mem_nhds ⟨ht,hp.2⟩))).contDiffWithinAt
    · have hfar : 2*δ < p.1 := hδT.trans_le (le_of_not_gt ht)
      have heq : dampedSlope δ G =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hfar)] with q hq
        simp only [dampedSlope,ReferencePath.slopeCutoff_zero hδ hq.le,Complex.ofReal_zero,zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro x _
    by_cases ht : x < T
    · change DifferentiableOn ℂ (fun z => (ReferencePath.slopeCutoff δ x : ℂ) * radial G (x,z)) Ω
      exact (differentiableOn_const _).mul (hD.holomorphic x ht)
    · have hzero : (fun z => dampedSlope δ G (x,z)) = (fun _ => 0) := by
        funext z
        simp [dampedSlope,ReferencePath.slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt ht))]
      rw [hzero]
      exact differentiableOn_const _

theorem regular_continuation {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2*δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G) :
    Regular univ Ω (continuation δ G) := by
  have hi := (regular_dampedSlope hδ hδT hΩ hG).primitive isOpen_univ hΩ (by intros; trivial)
  have hzero : Regular univ Ω (fun p => G (0,p.2)) := by
    constructor
    · exact hG.smooth.comp (contDiff_const.prodMk contDiff_snd).contDiffOn
        (fun _ hp => ⟨hT,hp.2⟩)
    · intro _ _
      exact hG.holomorphic 0 hT
  exact hzero.add hi

theorem continuation_hasDerivAt {T δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G)
    {p : CPoint} (hp : p.2 ∈ Ω) :
    HasDerivAt (fun x => continuation δ G (x,p.2)) (dampedSlope δ G p) p.1 := by
  unfold continuation
  simpa only [zero_add] using (hasDerivAt_const p.1 (G (0,p.2))).fun_add
    (primitive_hasDerivAt hΩ (regular_dampedSlope hδ hδT hΩ hG).smooth hp)

theorem continuation_eq_initial {T δ : ℝ} (_ : 0 < T) (hδ : 0 < δ) (hδT : 2*δ < T)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {G : CField} (hG : Regular (Iio T) Ω G)
    {p : CPoint} (hp : p.2 ∈ Ω) (hx : p.1 ≤ δ) : continuation δ G p = G p := by
  have hd : ∀ t ∈ uIcc 0 p.1,
      HasDerivAt (fun x => G (x,p.2)) (dampedSlope δ G (t,p.2)) t := by
    intro t ht
    have htδ : t ≤ δ := (mem_uIcc.mp ht).elim (fun h => h.2.trans hx) (fun h => h.2.trans hδ.le)
    have htT : t < T := by linarith
    simpa only [dampedSlope,ReferencePath.slopeCutoff_one hδ htδ,Complex.ofReal_one,one_mul] using
      radial_hasDerivAt isOpen_Iio hΩ hG.smooth (p := (t,p.2)) ⟨htT,hp⟩
  have hc := slice_continuous hΩ (regular_dampedSlope hδ hδT hΩ hG).smooth hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 p.1)
  change G (0,p.2) + _ = _
  rw [show primitive (dampedSlope δ G) p = G p-G (0,p.2) from hi]
  ring

def controlled (T κ : ℝ) (G : CField) (p : CPoint) : ℂ :=
  G (0,p.2) + primitive (fun q => (StressActivation.damping T κ q.1 : ℂ) * radial G q) p

theorem regular_controlled (T κ : ℝ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {G : CField} (hG : Regular univ Ω G) : Regular univ Ω (controlled T κ G) := by
  have hD := (regular_radius (StressActivation.damping_smooth T κ).contDiffOn).mul
    (hG.radial isOpen_univ hΩ)
  have hi := hD.primitive isOpen_univ hΩ (by intros; trivial)
  have hzero : Regular univ Ω (fun p => G (0,p.2)) := by
    constructor
    · exact hG.smooth.comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun _ hp =>
      ⟨trivial,hp.2⟩)
    · intro _ _
      exact hG.holomorphic 0 (mem_univ _)
  exact hzero.add hi

theorem controlled_eq_initial {T : ℝ} (hT : 0 < T) (κ : ℝ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {G : CField} (hG : Regular univ Ω G) {p : CPoint} (hp : p.2 ∈ Ω) (hx : p.1 ≤ 0) :
    controlled T κ G p = G p := by
  have hd : ∀ t ∈ uIcc 0 p.1, HasDerivAt (fun x => G (x,p.2))
      ((StressActivation.damping T κ t : ℂ) * radial G (t,p.2)) t := by
    intro t ht
    have ht0 : t ≤ 0 := (show t ∈ Icc p.1 0 by simpa only [uIcc_of_ge hx] using ht).2
    simpa only [StressActivation.damping,StressActivation.activation_zero hT κ ht0,sub_zero,
      Complex.ofReal_one,one_mul] using
      radial_hasDerivAt isOpen_univ hΩ hG.smooth (p := (t,p.2)) ⟨trivial,hp⟩
  have hD := (regular_radius (StressActivation.damping_smooth T κ).contDiffOn).mul
    (hG.radial isOpen_univ hΩ)
  have hc := slice_continuous hΩ hD.smooth hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 p.1)
  change G (0,p.2) + _ = _
  unfold primitive
  rw [hi]
  ring

theorem radial_ofReal {S : Set ℝ} (hS : IsOpen S) {G : CField} {g : ProfileHistories.Field}
    {x η : ℝ} (hx : x ∈ S) (hg : ContDiffAt ℝ ∞ g (x,η))
    (heq : ∀ y ∈ S, G (y,(η : ℂ)) = (g (y,η) : ℂ)) :
    radial G (x,(η : ℂ)) = (ProfileHistories.radialPartial g (x,η) : ℂ) := by
  have he : (fun y => G (y,(η : ℂ))) =ᶠ[𝓝 x] (fun y => (g (y,η) : ℂ)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact heq y hy
  exact he.deriv_eq.trans (ReferenceJetBounds.radial_deriv hg).ofReal_comp.deriv

theorem continuation_ofReal {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2*δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : CField} {g : ProfileHistories.Field}
    (hg : ContDiffOn ℝ ∞ g (Iio T ×ˢ J))
    (heq : ∀ x < T, ∀ η ∈ J, G (x,(η : ℂ)) = (g (x,η) : ℂ))
    (x : ℝ) {η : ℝ} (hη : η ∈ J) :
    continuation δ G (x,(η : ℂ)) = (ReferencePath.continuation δ g (x,η) : ℂ) := by
  have hD (y : ℝ) : dampedSlope δ G (y,(η : ℂ)) = (ReferencePath.dampedSlope δ g (y,η) : ℂ) := by
    by_cases hy : y < T
    · have hd := radial_ofReal isOpen_Iio hy
        (hg.contDiffAt ((isOpen_Iio.prod hJ).mem_nhds ⟨hy,hη⟩)) (fun z hz => heq z hz η hη)
      simp only [dampedSlope,ReferencePath.dampedSlope,hd,Complex.ofReal_mul]
    · have hz := ReferencePath.slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt hy))
      simp only [dampedSlope,ReferencePath.dampedSlope,hz,Complex.ofReal_zero,zero_mul]
  simp only [continuation,ReferencePath.continuation,primitive,ProfileHistories.primitive,Complex.ofReal_add]
  rw [heq 0 hT η hη]
  congr 1
  calc
    _ = ∫ y in (0 : ℝ)..x, (ReferencePath.dampedSlope δ g (y,η) : ℂ) :=
      intervalIntegral.integral_congr (fun y _ => hD y)
    _ = _ := intervalIntegral.integral_ofReal

theorem controlled_ofReal (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J)
    {G : CField} {g : ProfileHistories.Field} (hg : ContDiffOn ℝ ∞ g (univ ×ˢ J))
    (heq : ∀ x η : ℝ, η ∈ J → G (x,(η : ℂ)) = (g (x,η) : ℂ))
    (x : ℝ) {η : ℝ} (hη : η ∈ J) :
    controlled T κ G (x,(η : ℂ)) = (StressActivation.controlled T κ g (x,η) : ℂ) := by
  have hD (y : ℝ) : radial G (y,(η : ℂ)) = (ProfileHistories.radialPartial g (y,η) : ℂ) :=
    radial_ofReal isOpen_univ (mem_univ _)
      (hg.contDiffAt ((isOpen_univ.prod hJ).mem_nhds ⟨mem_univ _,hη⟩)) (fun z _ => heq z η hη)
  simp only [controlled,StressActivation.controlled,primitive,ProfileHistories.primitive,Complex.ofReal_add]
  rw [heq 0 η hη]
  congr 1
  calc
    _ = ∫ y in (0 : ℝ)..x,
        ((StressActivation.damping T κ y * ProfileHistories.radialPartial g (y,η) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro y _
      change (StressActivation.damping T κ y : ℂ) * radial G (y,(η : ℂ)) =
        ((StressActivation.damping T κ y * ProfileHistories.radialPartial g (y,η) : ℝ) : ℂ)
      rw [hD y,Complex.ofReal_mul]
    _ = _ := intervalIntegral.integral_ofReal

def logPoint (N : ReferencePath.Input) (p : CPoint) : CPoint := (N.logTime p.1,p.2)
def expPoint (N : ReferencePath.Input) (p : CPoint) : CPoint := (N.endpoint*Real.exp p.1,p.2)

theorem logPoint_smoothAt (N : ReferencePath.Input) {p : CPoint} (hp : 0 < p.1) :
    ContDiffAt ℝ ∞ (logPoint N) p := by
  have hd : ContDiffAt ℝ ∞ (fun q : CPoint => q.1 / N.endpoint) p :=
    contDiffAt_fst.div_const _
  exact (hd.log (div_pos hp N.endpoint_pos).ne').prodMk contDiffAt_snd

theorem expPoint_smooth (N : ReferencePath.Input) : ContDiff ℝ ∞ (expPoint N) :=
  (contDiff_const.mul contDiff_fst.exp).prodMk contDiff_snd

theorem expPoint_logPoint (N : ReferencePath.Input) {p : CPoint} (hp : 0 < p.1) :
    expPoint N (logPoint N p) = p := by
  apply Prod.ext
  · change N.endpoint * Real.exp (Real.log (p.1/N.endpoint)) = p.1
    rw [Real.exp_log (div_pos hp N.endpoint_pos),mul_div_cancel₀ _ N.endpoint_pos.ne']
  · rfl

def attach (N : ReferencePath.Input) (F G : CField) (p : CPoint) : ℂ :=
  if p.1 ≤ N.endpoint then F p else G (logPoint N p)

theorem attach_logPoint (N : ReferencePath.Input) {F G : CField} {Ω : Set ℂ}
    (heq : ∀ p : CPoint, 0 < p.1 → p.1 ≤ N.endpoint → p.2 ∈ Ω → G (logPoint N p) = F p)
    {p : CPoint} (hp : 0 < p.1) (hz : p.2 ∈ Ω) : attach N F G p = G (logPoint N p) := by
  by_cases hx : p.1 ≤ N.endpoint
  · exact (ite_eq_left hx).trans (heq p hp hx hz).symm
  · exact ite_eq_right hx

theorem regular_attach (N : ReferencePath.Input) {R : ℝ} (hR : 0 < R) (hXR : N.endpoint < R)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F G : CField}
    (hF : Regular (Ioo (-R) R) Ω F) (hG : Regular univ Ω G)
    (heq : ∀ p : CPoint, 0 < p.1 → p.1 ≤ N.endpoint → p.2 ∈ Ω → G (logPoint N p) = F p) :
    Regular (Ioi (-R)) Ω (attach N F G) := by
  constructor
  · intro p hp
    by_cases hx : 0 < p.1
    · have hb : ContDiffAt ℝ ∞ G (logPoint N p) :=
        hG.smooth.contDiffAt ((isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _,hp.2⟩)
      have hs := hb.comp p (logPoint_smoothAt N hx)
      have hlocal : attach N F G =ᶠ[𝓝 p] (fun q => G (logPoint N q)) := by
        filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hx),
          continuousAt_snd.eventually (hΩ.mem_nhds hp.2)] with q hq hz
        exact attach_logPoint N heq hq hz
      exact (hs.congr_of_eventuallyEq hlocal).contDiffWithinAt
    · have hbefore : p.1 < N.endpoint := (le_of_not_gt hx).trans_lt N.endpoint_pos
      have hFp : ContDiffAt ℝ ∞ F p := hF.smooth.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds
        ⟨⟨hp.1,lt_of_le_of_lt (le_of_not_gt hx) hR⟩,hp.2⟩)
      have hlocal : attach N F G =ᶠ[𝓝 p] F := by
        filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
        exact ite_eq_left hq.le
      exact (hFp.congr_of_eventuallyEq hlocal).contDiffWithinAt
  · intro x hx
    by_cases hxe : x ≤ N.endpoint
    · have hf := hF.holomorphic x ⟨hx,hxe.trans_lt hXR⟩
      simpa only [attach,ite_eq_left hxe] using hf
    · have hg := hG.holomorphic (N.logTime x) (mem_univ _)
      simpa only [attach,ite_eq_right hxe,logPoint] using hg

/-- An explicit natural extension, including the positivity neighborhood
needed by the logarithm. It is constructed from the coefficient series below. -/
structure NaturalExtension (N : ReferencePath.Input) (Ω : Set ℂ) (R : ℝ) where
  radius_pos : 0 < R
  endpoint_lt : N.endpoint < R
  f : CField
  U : CField
  f_regular : Regular (Ioo (-R) R) Ω f
  U_regular : Regular (Ioo (-R) R) Ω U
  f_real : ∀ x η : ℝ, f (x,(η : ℂ)) = (N.f (x,η) : ℂ)
  U_real : ∀ x η : ℝ, U (x,(η : ℂ)) = (N.U (x,η) : ℂ)
  exp_mem : ∀ t < ReferencePath.rampLimit, N.endpoint*Real.exp t ∈ Ioo (-R) R
  right_half : ∀ t < ReferencePath.rampLimit, ∀ z ∈ Ω, 0 < (f (N.endpoint*Real.exp t,z)).re
  initial_half : ∀ x ∈ Icc (0 : ℝ) N.endpoint, ∀ z ∈ Ω, 0 < (f (x,z)).re

namespace NaturalExtension

variable {N : ReferencePath.Input} {Ω : Set ℂ} {R : ℝ} (E : NaturalExtension N Ω R)

def logF : CField := fun p => Complex.log (E.f (expPoint N p))
def logU : CField := fun p => E.U (expPoint N p)

theorem logF_regular : Regular (Iio ReferencePath.rampLimit) Ω E.logF := by
  have hb : Regular (Iio ReferencePath.rampLimit) Ω (fun p => E.f (expPoint N p)) := by
    constructor
    · exact E.f_regular.smooth.comp (expPoint_smooth N).contDiffOn
        (fun p hp => ⟨E.exp_mem p.1 hp.1,hp.2⟩)
    · intro t ht
      exact E.f_regular.holomorphic _ (E.exp_mem t ht)
  exact hb.clog (fun p hp => Or.inl (E.right_half p.1 hp.1 p.2 hp.2))

theorem logU_regular : Regular (Iio ReferencePath.rampLimit) Ω E.logU := by
  constructor
  · exact E.U_regular.smooth.comp (expPoint_smooth N).contDiffOn
      (fun p hp => ⟨E.exp_mem p.1 hp.1,hp.2⟩)
  · intro t ht
    exact E.U_regular.holomorphic _ (E.exp_mem t ht)

theorem logF_real {t η : ℝ} (ht : t < ReferencePath.rampLimit)
    (hη : η ∈ ReferencePath.parameterInterval) :
    E.logF (t,(η : ℂ)) = (N.logF (t,η) : ℂ) := by
  change Complex.log (E.f (N.endpoint*Real.exp t,(η : ℂ))) = _
  rw [E.f_real]
  exact (Complex.ofReal_log (N.fromLog_f_pos (p := (t,η)) ⟨ht,hη⟩).le).symm

theorem logU_real (t η : ℝ) : E.logU (t,(η : ℂ)) = (N.logU (t,η) : ℂ) := E.U_real _ _

def refLog (δ : ℝ) : CField := continuation δ E.logF
def refAxial (δ : ℝ) : CField := continuation δ E.logU
def refF (δ : ℝ) : CField := attach N E.f (fun p => Complex.exp (E.refLog δ p))
def refU (δ : ℝ) : CField := attach N E.U (E.refAxial δ)
def actLog (T κ δ : ℝ) : CField := controlled T κ (E.refLog δ)
def actAxial (T κ δ : ℝ) : CField := controlled T κ (E.refAxial δ)
def actF (T κ δ : ℝ) : CField := attach N E.f (fun p => Complex.exp (E.actLog T κ δ p))
def actU (T κ δ : ℝ) : CField := attach N E.U (E.actAxial T κ δ)

theorem refLog_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit) :
    Regular univ Ω (E.refLog δ) :=
  regular_continuation ReferencePath.rampLimit_pos hδ hδT hΩ E.logF_regular

theorem refAxial_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
  :
    Regular univ Ω (E.refAxial δ) :=
  regular_continuation ReferencePath.rampLimit_pos hδ hδT hΩ E.logU_regular

theorem refLog_initial (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    {p : CPoint} (hp : p.2 ∈ Ω) (ht : p.1 ≤ 0) : E.refLog δ p = E.logF p :=
  continuation_eq_initial ReferencePath.rampLimit_pos hδ hδT hΩ E.logF_regular hp (ht.trans hδ.le)

theorem refAxial_initial (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    {p : CPoint} (hp : p.2 ∈ Ω) (ht : p.1 ≤ 0) : E.refAxial δ p = E.logU p :=
  continuation_eq_initial ReferencePath.rampLimit_pos hδ hδT hΩ E.logU_regular hp (ht.trans hδ.le)

theorem angular_attach_regular (hΩ : IsOpen Ω) {G : CField} (hG : Regular univ Ω G)
    (hinit : ∀ p : CPoint, p.2 ∈ Ω → p.1 ≤ 0 → G p = E.logF p) :
    Regular (Ioi (-R)) Ω (attach N E.f (fun p => Complex.exp (G p))) := by
  apply regular_attach N E.radius_pos E.endpoint_lt hΩ E.f_regular hG.cexp
  intro p hp hxe hz
  have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hp).2 (by simpa only [Real.exp_zero,mul_one]
    using hxe)
  rw [hinit (logPoint N p) hz ht]
  change Complex.exp (Complex.log (E.f (expPoint N (logPoint N p)))) = E.f p
  rw [expPoint_logPoint N hp]
  apply Complex.exp_log
  have hpos := E.right_half (N.logTime p.1) (ht.trans_lt ReferencePath.rampLimit_pos) p.2 hz
  have he : (N.endpoint*Real.exp (N.logTime p.1),p.2) = p := expPoint_logPoint N hp
  rw [he] at hpos
  intro hn
  simp only [hn,Complex.zero_re,lt_self_iff_false] at hpos

theorem axial_attach_regular (hΩ : IsOpen Ω) {G : CField} (hG : Regular univ Ω G)
    (hinit : ∀ p : CPoint, p.2 ∈ Ω → p.1 ≤ 0 → G p = E.logU p) :
    Regular (Ioi (-R)) Ω (attach N E.U G) := by
  apply regular_attach N E.radius_pos E.endpoint_lt hΩ E.U_regular hG
  intro p hp hxe hz
  have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hp).2 (by simpa only [Real.exp_zero,mul_one]
    using hxe)
  rw [hinit (logPoint N p) hz ht]
  change E.U (expPoint N (logPoint N p)) = E.U p
  rw [expPoint_logPoint N hp]

theorem refF_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit) :
    Regular (Ioi (-R)) Ω (E.refF δ) :=
  E.angular_attach_regular hΩ (E.refLog_regular hΩ hδ hδT)
    (fun _ hp ht => E.refLog_initial hΩ hδ hδT hp ht)

theorem refU_regular (hΩ : IsOpen Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit) :
    Regular (Ioi (-R)) Ω (E.refU δ) :=
  E.axial_attach_regular hΩ (E.refAxial_regular hΩ hδ hδT)
    (fun _ hp ht => E.refAxial_initial hΩ hδ hδT hp ht)

theorem actF_regular (hΩ : IsOpen Ω) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) : Regular (Ioi (-R)) Ω (E.actF T κ δ) := by
  apply E.angular_attach_regular hΩ (regular_controlled T κ hΩ (E.refLog_regular hΩ hδ hδT))
  intro p hp ht
  exact (controlled_eq_initial hT κ hΩ (E.refLog_regular hΩ hδ hδT) hp ht).trans
    (E.refLog_initial hΩ hδ hδT hp ht)

theorem actU_regular (hΩ : IsOpen Ω) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) : Regular (Ioi (-R)) Ω (E.actU T κ δ) := by
  apply E.axial_attach_regular hΩ (regular_controlled T κ hΩ (E.refAxial_regular hΩ hδ hδT))
  intro p hp ht
  exact (controlled_eq_initial hT κ hΩ (E.refAxial_regular hΩ hδ hδT) hp ht).trans
    (E.refAxial_initial hΩ hδ hδT hp ht)

theorem refLog_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refLog δ (x,(η : ℂ)) = (StressActivation.FromReference.refLog N δ (x,η) : ℂ) :=
  continuation_ofReal ReferencePath.rampLimit_pos hδ hδT ReferencePath.parameterInterval_open
    N.logF_smooth (fun _ ht _ hη => E.logF_real ht hη) x hη

theorem refAxial_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refAxial δ (x,(η : ℂ)) = (StressActivation.FromReference.refAxial N δ (x,η) : ℂ) :=
  continuation_ofReal ReferencePath.rampLimit_pos hδ hδT ReferencePath.parameterInterval_open
    N.logU_smooth (fun _ _ _ _ => E.logU_real _ _) x hη

theorem actLog_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actLog T κ δ (x,(η : ℂ)) =
      (StressActivation.controlled T κ (StressActivation.FromReference.refLog N δ) (x,η) : ℂ) :=
  controlled_ofReal T κ ReferencePath.parameterInterval_open
    (StressActivation.FromReference.refLog_smooth N hδ hδT)
    (fun x _ hη => E.refLog_real hδ hδT x hη) x hη

theorem actAxial_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actAxial T κ δ (x,(η : ℂ)) =
      (StressActivation.controlled T κ (StressActivation.FromReference.refAxial N δ) (x,η) : ℂ) :=
  controlled_ofReal T κ ReferencePath.parameterInterval_open
    (StressActivation.FromReference.refAxial_smooth N hδ hδT)
    (fun x _ hη => E.refAxial_real hδ hδT x hη) x hη

theorem refF_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refF δ (x,(η : ℂ)) = (N.refF δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [refF,attach,ite_eq_left hx,ReferencePath.Input.refF,E.f_real]
  · simp only [refF,attach,ite_eq_right hx,ReferencePath.Input.refF,logPoint]
    rw [E.refLog_real hδ hδT _ hη,Complex.ofReal_exp]
    rfl

theorem refU_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.refU δ (x,(η : ℂ)) = (N.refU δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [refU,attach,ite_eq_left hx,ReferencePath.Input.refU,E.U_real]
  · simp only [refU,attach,ite_eq_right hx,ReferencePath.Input.refU,logPoint]
    exact E.refAxial_real hδ hδT _ hη

theorem actF_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actF T κ δ (x,(η : ℂ)) = (StressActivation.FromReference.f N T κ δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [actF,attach,ite_eq_left
    hx,StressActivation.FromReference.f,ReferencePath.Input.refF,E.f_real]
  · simp only [actF,attach,ite_eq_right
    hx,StressActivation.FromReference.f,logPoint,StressActivation.activatedAngular]
    rw [E.actLog_real hδ hδT T κ _ hη,Complex.ofReal_exp]

theorem actU_real {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (T κ x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    E.actU T κ δ (x,(η : ℂ)) = (StressActivation.FromReference.U N T κ δ (x,η) : ℂ) := by
  by_cases hx : x ≤ N.endpoint
  · simp only [actU,attach,ite_eq_left
    hx,StressActivation.FromReference.U,ReferencePath.Input.refU,E.U_real]
  · simp only [actU,attach,ite_eq_right hx,StressActivation.FromReference.U,logPoint]
    exact E.actAxial_real hδ hδT T κ _ hη

theorem actF_ne_zero (T κ δ : ℝ) {p : CPoint} (hx : 0 ≤ p.1) (hz : p.2 ∈ Ω) :
    E.actF T κ δ p ≠ 0 := by
  by_cases he : p.1 ≤ N.endpoint
  · have hp := E.initial_half p.1 ⟨hx,he⟩ p.2 hz
    rw [actF,attach,ite_eq_left he]
    intro hn
    simp only [hn,Complex.zero_re,lt_self_iff_false] at hp
  · simp only [actF,attach,ite_eq_right he]
    exact Complex.exp_ne_zero _

end NaturalExtension

open NaturalAxisCoefficients NaturalEntrance

def parameterWindow : AxisCoefficientSpace.Window where
  left := -21/20
  right := 21/20
  nondegenerate := by norm_num

theorem parameterWindow_subset {η : ℝ} (hη : η ∈ parameterWindow.interval) :
    η ∈ window.interval ∧ η ∈ ReferencePath.parameterInterval := by
  change -21/20 ≤ η ∧ η ≤ 21/20 at hη
  change (-11/10 ≤ η ∧ η ≤ 11/10) ∧ (-11/10 < η ∧ η < 11/10)
  constructor <;> constructor <;> linarith [hη.1,hη.2]

theorem closed_parameter_subset {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    η ∈ parameterWindow.interval := by
  change -21/20 ≤ η ∧ η ≤ 21/20
  constructor <;> linarith [hη.1,hη.2]

theorem parameterTube_open (J : AxisCoefficientSpace.Window) (δ : ℝ) :
    IsOpen (AxisHolomorphic.parameterTube J δ) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨η,hη,hz⟩
  apply Filter.mem_of_superset (isOpen_ball.mem_nhds hz)
  intro w hw
  exact ⟨η,hη,hw⟩

section NaturalConstruction

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (F : CoefficientProfile d Λ C)

def naturalF (p : CPoint) : ℂ :=
  (Complex.exp ((Λ : ℂ) * axisPhase h j σ p.2) / (C : ℂ)) *
    AxisHolomorphic.complexProfile window d.coefficients.epsilon F.coefficients.1 0 (Λ*p.1) p.2

def naturalU (p : CPoint) : ℂ :=
  complexU j p.2 + (1/(Λ : ℂ)) *
    AxisHolomorphic.complexProfile window d.coefficients.epsilon F.coefficients.2 0 (Λ*p.1) p.2

theorem naturalF_real (x η : ℝ) : naturalF F (x,(η : ℂ)) = (F.family.f (x,η) : ℂ) := by
  rw [F.f_eq]
  simp only [naturalF,axisPhase_ofReal,AxisHolomorphic.complexProfile_zero_ofReal]
  change _ = ((realAmplitude h j σ Λ C η *
    AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.1 (Λ*x,η) : ℝ) : ℂ)
  simp only [realAmplitude,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_exp]

theorem naturalU_real (x η : ℝ) : naturalU F (x,(η : ℂ)) = (F.family.U (x,η) : ℂ) := by
  rw [F.U_eq]
  simp only [naturalU,AxisHolomorphic.complexProfile_zero_ofReal]
  change _ = ((NaturalAxisData.U j η + (1/Λ) *
    AxisEvaluation.profile window d.coefficients.epsilon F.coefficients.2 (Λ*x,η) : ℝ) : ℂ)
  simp only [complexU,NaturalAxisData.U,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat]

theorem scaled_radius_mem (hΛ : 0 < Λ) {x : ℝ} (hx : x ∈ Ioo (-(5/Λ)) (5/Λ)) :
    Λ*x ∈ Ioo (-5 : ℝ) 5 := by
  constructor
  · have ht := (mul_lt_mul_of_pos_left hx.1 hΛ)
    have he : Λ * (-(5/Λ)) = -5 := by field_simp
    rwa [he] at ht
  · have ht := (mul_lt_mul_of_pos_left hx.2 hΛ)
    simpa only [mul_div_cancel₀ 5 hΛ.ne'] using ht

theorem coefficient_regular (hΛ : 0 < Λ) {Ω : Set ℂ}
    (hΩ : Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 : ℝ))))
    (A : AxisCoefficientSpace.AxisSpace window d.coefficients.epsilon) :
    Regular (Ioo (-(5/Λ)) (5/Λ)) Ω
      (fun p => AxisHolomorphic.complexProfile window d.coefficients.epsilon A 0 (Λ*p.1) p.2) := by
  constructor
  · have hb : ContDiffOn ℝ ∞
        (fun p : CPoint => AxisHolomorphic.complexProfile window d.coefficients.epsilon A 0 p.1 p.2)
        (Ioo (-5 : ℝ) 5 ×ˢ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 :
          ℝ)))) :=
      AxisHolomorphicJoint.complexProfile_joint_smooth window d.coefficients.epsilon_pos
      (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (5 : ℝ)/20 < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) A 0
    have hm : ContDiffOn ℝ ∞ (fun p : CPoint => (Λ*p.1,p.2))
        (Ioo (-(5/Λ)) (5/Λ) ×ˢ Ω) :=
      ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
    have hout := hb.comp hm (fun p hp => ⟨scaled_radius_mem hΛ hp.1,hΩ hp.2⟩)
    simpa only [Function.comp_def] using hout
  · intro x hx
    exact ((AxisHolomorphic.complexProfile_analytic window d.coefficients.epsilon_pos
      (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (5 : ℝ)/20 < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) A 0 (abs_lt.mpr (scaled_radius_mem hΛ hx)).le).mono
        hΩ).differentiableOn

theorem naturalF_regular (hΛ : 0 < Λ) {Ω : Set ℂ}
    (hstrip : Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 : ℝ))))
    (hphase : Ω ⊆ d.compactSet) : Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalF F) := by
  have hA : AnalyticOnNhd ℂ (fun z => Complex.exp ((Λ : ℂ)*axisPhase h j σ z)/(C : ℂ)) Ω := by
    intro z hz
    have hp : AnalyticAt ℂ (fun w => (Λ : ℂ)*axisPhase h j σ w) z :=
      analyticAt_const.mul (d.phase_analytic z (hphase hz))
    simpa only [div_eq_mul_inv, Function.comp_def] using hp.cexp.fun_mul (analyticAt_const (v := (C
      : ℂ)⁻¹))
  exact (regular_parameter hA).mul (coefficient_regular hΛ hstrip F.coefficients.1)

theorem naturalU_regular (hΛ : 0 < Λ) {Ω : Set ℂ}
    (hstrip : Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 : ℝ)))) :
    Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalU F) := by
  have hbase : AnalyticOnNhd ℂ (complexU j) Ω := by
    intro z _
    unfold complexU
    fun_prop
  exact (regular_parameter hbase).add
    ((regular_const _ _ (1/(Λ : ℂ))).mul (coefficient_regular hΛ hstrip F.coefficients.2))

theorem exists_preliminary_tube (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧
      (∀ η ∈ parameterWindow.interval, (η : ℂ) ∈ Ω) ∧
      Ω ⊆ AxisHolomorphic.parameterStrip window (d.coefficients.epsilon*(1-(1/2 : ℝ))) ∧
      Ω ⊆ d.compactSet ∧ Ω ⊆ regularSet h j σ := by
  obtain ⟨δ,hδ,hsub⟩ := AxisHolomorphic.exists_parameterTube_subset window parameterWindow
    (by norm_num [window,parameterWindow]) (by norm_num [window,parameterWindow])
      (mul_pos d.coefficients.epsilon_pos (by norm_num : 0 < 1-(1/2 : ℝ)))
  let r := min δ d.radius
  have hr : 0 < r := lt_min hδ d.radius_pos
  refine ⟨AxisHolomorphic.parameterTube parameterWindow r ∩ regularSet h j σ,
    (parameterTube_open _ _).inter (regularSet_open _ _ _), ?_, ?_, ?_, inter_subset_right⟩
  · intro η hη
    exact ⟨AxisHolomorphic.parameterTube_contains_real parameterWindow hr hη,
      real_mem_regularSet hsmall hσ (parameterWindow_subset hη).1⟩
  · rintro z ⟨⟨η,hη,hz⟩,_⟩
    exact hsub ⟨η,hη,hz.trans_le (min_le_left _ _)⟩
  · rintro z ⟨⟨η,hη,hz⟩,_⟩
    exact d.covers η (parameterWindow_subset hη).1 (hz.le.trans (min_le_right _ _))

/-- Compact real positivity produces a single complex tube, uniformly over
the whole natural radial interval used by REF. -/
theorem exists_positive_natural_tube (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) :
    ∃ δ : ℝ, 0 < δ ∧
      let Ω := AxisHolomorphic.parameterTube parameterWindow δ
      IsOpen Ω ∧ Ω ⊆ regularSet h j σ ∧
      Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalF F) ∧
      Regular (Ioo (-(5/Λ)) (5/Λ)) Ω (naturalU F) ∧
      ∀ x ∈ Icc (0 : ℝ) ((41/10)/Λ), ∀ z ∈ Ω, 0 < (naturalF F (x,z)).re := by
  obtain ⟨Ω,hΩ,hreal,hstrip,hphase,hreg⟩ := exists_preliminary_tube (d := d) hsmall hσ
  have hf := naturalF_regular F hΛ hstrip hphase
  have hu := naturalU_regular F hΛ hstrip
  let S : Set ℝ := Ioo (-(5/Λ)) (5/Λ)
  let O : Set CPoint := {p | p ∈ S ×ˢ Ω ∧ 0 < (naturalF F p).re}
  have hopen : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hdom := (isOpen_Ioo.prod hΩ).mem_nhds hp.1
    have hpos := (Complex.continuous_re.continuousAt.comp (hf.smooth.contDiffAt
      hdom).continuousAt).eventually
      (Ioi_mem_nhds hp.2)
    filter_upwards [hdom,hpos] with q hq hqpos
    exact ⟨hq,hqpos⟩
  let K : Set CPoint := Icc (0 : ℝ) ((41/10)/Λ) ×ˢ (Complex.ofReal '' parameterWindow.interval)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.image Complex.continuous_ofReal)
  have hKS : ∀ x ∈ Icc (0 : ℝ) ((41/10)/Λ), x ∈ S := by
    intro x hx
    constructor
    · exact lt_of_lt_of_le (neg_neg_of_pos (div_pos (by norm_num) hΛ)) hx.1
    · exact hx.2.trans_lt ((div_lt_div_iff_of_pos_right hΛ).2 (by norm_num))
  have hKO : K ⊆ O := by
    rintro ⟨x,z⟩ ⟨hx,η,hη,rfl⟩
    refine ⟨⟨hKS x hx,hreal η hη⟩,?_⟩
    rw [naturalF_real,Complex.ofReal_re]
    have hY0 : 0 ≤ Λ*x := mul_nonneg hΛ.le hx.1
    have hY1 : Λ*x ≤ 41/10 := by
      have hh := mul_le_mul_of_nonneg_left hx.2 hΛ.le
      simpa only [mul_div_cancel₀ (41/10) hΛ.ne'] using hh
    have hdom : (x,η) ∈ NaturalProfile.domain Λ := by
      change (-20 < Λ*x ∧ Λ*x < 20) ∧ η ∈ ReferencePath.parameterInterval
      exact ⟨⟨by linarith,by linarith⟩,(parameterWindow_subset hη).2⟩
    exact F.family.positive (x,η) hdom hY0 hY1
  obtain ⟨δ,hδ,hδO⟩ := hK.exists_cthickening_subset_open hopen hKO
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) ((41/10)/Λ))
      {z : ℂ} (hz : z ∈ AxisHolomorphic.parameterTube parameterWindow δ) : (x,z) ∈ O := by
    rcases hz with ⟨η,hη,hz⟩
    apply hδO
    apply closedBall_subset_cthickening
      (show (x,(η : ℂ)) ∈ K from ⟨hx,mem_image_of_mem Complex.ofReal hη⟩) δ
    change dist (x,z) (x,(η : ℂ)) ≤ δ
    simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)] using hz.le
  have hsub : AxisHolomorphic.parameterTube parameterWindow δ ⊆ Ω := by
    intro z hz
    exact (hpos 0 ⟨le_rfl,by positivity⟩ hz).1.2
  refine ⟨δ,hδ,parameterTube_open _ _,hsub.trans hreg,hf.mono Subset.rfl hsub,
    hu.mono Subset.rfl hsub,?_⟩
  intro x hx z hz
  exact (hpos x hx hz).2

theorem natural_log_radius (hΛ : 0 < Λ) {t : ℝ} (ht : t < ReferencePath.rampLimit) :
    0 < (4/Λ)*Real.exp t ∧ (4/Λ)*Real.exp t < (41/10)/Λ := by
  have he : Real.exp t < 41/40 := by
    simpa only [ReferencePath.rampLimit,Real.exp_log (by norm_num : (0 : ℝ) < 41/40)] using
      Real.exp_lt_exp.mpr ht
  constructor
  · positivity
  · rw [div_mul_eq_mul_div]
    exact (div_lt_div_iff_of_pos_right hΛ).2 (by nlinarith)

/-- Construction from the actual coefficient witness. In particular the
natural extension and its common positive neighborhood are not assumptions. -/
theorem exists_natural_extension (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ _ : NaturalExtension (ReferenceJetBounds.referenceInput F hΛ)
      (AxisHolomorphic.parameterTube parameterWindow ρ) (5/Λ),
      AxisHolomorphic.parameterTube parameterWindow ρ ⊆ regularSet h j σ := by
  obtain ⟨ρ,hρ,hopen,hreg,hf,hu,hpos⟩ := exists_positive_natural_tube F hΛ hsmall hσ
  refine ⟨ρ,hρ,{
    radius_pos := div_pos (by norm_num) hΛ
    endpoint_lt := ?_
    f := naturalF F
    U := naturalU F
    f_regular := hf
    U_regular := hu
    f_real := naturalF_real F
    U_real := naturalU_real F
    exp_mem := ?_
    right_half := ?_
    initial_half := ?_ },hreg⟩
  · change 4/Λ < 5/Λ
    exact (div_lt_div_iff_of_pos_right hΛ).2 (by norm_num)
  · intro t ht
    have hb := natural_log_radius hΛ ht
    change -(5/Λ) < (4/Λ)*Real.exp t ∧ (4/Λ)*Real.exp t < 5/Λ
    constructor
    · exact (neg_neg_of_pos (div_pos (by norm_num) hΛ)).trans hb.1
    · exact hb.2.trans ((div_lt_div_iff_of_pos_right hΛ).2 (by norm_num))
  · intro t ht z hz
    exact hpos _ ⟨(natural_log_radius hΛ ht).1.le,(natural_log_radius hΛ ht).2.le⟩ z hz
  · intro x hx z hz
    have he : (ReferenceJetBounds.referenceInput F hΛ).endpoint ≤ (41/10)/Λ := by
      change 4/Λ ≤ (41/10)/Λ
      exact (div_le_div_iff_of_pos_right hΛ).2 (by norm_num)
    exact hpos x ⟨hx.1,hx.2.trans he⟩ z hz

end NaturalConstruction

def radialJet (F : CField) (k : ℕ) (p : CPoint) : ℂ :=
  iteratedDeriv k (fun x => F (x,p.2)) p.1

theorem radialJet_succ (F : CField) (k : ℕ) : radialJet F (k+1) = radial (radialJet F k) := by
  funext p
  simp only [radialJet,radial,iteratedDeriv_succ]

theorem Regular.radialJet {S : Set ℝ} {Ω : Set ℂ} {F : CField}
    (hF : Regular S Ω F) (hS : IsOpen S) (hΩ : IsOpen Ω) (k : ℕ) :
    Regular S Ω (radialJet F k) := by
  induction k with
  | zero =>
    unfold ActivationHolomorphic.radialJet
    simpa only [iteratedDeriv_zero,Prod.eta] using hF
  | succ k ih => rw [radialJet_succ]; exact ih.radial hS hΩ

theorem scale_half_interval {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Ioi (-R))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t*x ∈ Ioi (-R) := by
  rcases le_total x 0 with hn | hp
  · have hb : x ≤ t*x := by simpa only [one_mul] using mul_le_mul_of_nonpos_right ht.2 hn
    exact hx.trans_le hb
  · exact (neg_neg_of_pos hR).trans_le (mul_nonneg ht.1 hp)

theorem Regular.pow {S : Set ℝ} {Ω : Set ℂ} {F : CField} (hF : Regular S Ω F) (n : ℕ) :
    Regular S Ω (fun p => F p ^ n) :=
  ⟨hF.smooth.pow n,fun x hx => (hF.holomorphic x hx).pow n⟩

def pressure (P0 : ℂ → ℂ) (f : CField) (p : CPoint) : ℂ :=
  P0 p.2 + primitive (fun q => f q ^ 2) p

theorem regular_pressure {R : ℝ} (hR : 0 < R) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : CField} (hf : Regular (Ioi (-R)) Ω f) {P0 : ℂ → ℂ}
    (hP0 : AnalyticOnNhd ℂ P0 Ω) : Regular (Ioi (-R)) Ω (pressure P0 f) :=
  (regular_parameter hP0).add ((hf.pow 2).primitive isOpen_Ioi hΩ
    (fun _ hx _ ht => scale_half_interval hR hx ht))

theorem average_ofReal {F : CField} {g : ProfileHistories.Field} {η : ℝ}
    (heq : ∀ x : ℝ, F (x,(η : ℂ)) = (g (x,η) : ℂ)) (x : ℝ) :
    average F (x,(η : ℂ)) = (ProfileHistories.average g (x,η) : ℂ) := by
  unfold average ProfileHistories.average
  calc
    _ = ∫ t in (0 : ℝ)..1, (g (t*x,η) : ℂ) := intervalIntegral.integral_congr (fun t _ => heq (t*x))
    _ = _ := intervalIntegral.integral_ofReal

theorem primitive_ofReal {F : CField} {g : ProfileHistories.Field} {η : ℝ}
    (heq : ∀ x : ℝ, F (x,(η : ℂ)) = (g (x,η) : ℂ)) (x : ℝ) :
    primitive F (x,(η : ℂ)) = (ProfileHistories.primitive g (x,η) : ℂ) := by
  unfold primitive ProfileHistories.primitive
  calc
    _ = ∫ t in (0 : ℝ)..x, (g (t,η) : ℂ) := intervalIntegral.integral_congr (fun t _ => heq t)
    _ = _ := intervalIntegral.integral_ofReal

theorem pressure_ofReal {F : CField} {g : ProfileHistories.Field} {η : ℝ}
    (heq : ∀ x : ℝ, F (x,(η : ℂ)) = (g (x,η) : ℂ))
    {P0 : ℂ → ℂ} {p0 : ℝ → ℝ} (hP0 : P0 (η : ℂ) = (p0 η : ℂ)) (x : ℝ) :
    pressure P0 F (x,(η : ℂ)) =
      ((p0 η + ProfileHistories.primitive (fun p => g p ^ 2) (x,η) : ℝ) : ℂ) := by
  rw [pressure,hP0,Complex.ofReal_add]
  congr 1
  apply primitive_ofReal
  intro y
  simp only [heq,Complex.ofReal_pow]

def signedSquare (F : CField) (p : CPoint) : ℂ := F (p.1^2,p.2)

theorem Regular.signedSquare {R : ℝ} (hR : 0 < R) {Ω : Set ℂ} {F : CField}
    (hF : Regular (Ioi (-R)) Ω F) : Regular univ Ω (signedSquare F) := by
  constructor
  · exact hF.smooth.comp ((contDiff_fst.pow 2).prodMk contDiff_snd).contDiffOn
      (fun p hp => ⟨(neg_neg_of_pos hR).trans_le (sq_nonneg p.1),hp.2⟩)
  · intro r _
    exact hF.holomorphic (r^2) ((neg_neg_of_pos hR).trans_le (sq_nonneg r))

theorem signedSquare_even (F : CField) (z : ℂ) : Function.Even (fun r => signedSquare F (r,z)) := by
  intro r
  simp only [signedSquare,neg_sq]

/-- The actual base data on one common complex tube. The constructor below
supplies the pressure extension from its proved defining integral. -/
structure InitialTube (N : ReferencePath.Input) (h : ℝ) (P0 : ℝ → ℝ)
    (R : ℝ) (Ω : Set ℂ) where
  natural : NaturalExtension N Ω R
  isOpen : IsOpen Ω
  real_mem : ∀ η ∈ Icc (-1 : ℝ) 1, (η : ℂ) ∈ Ω
  elliptic_ne_zero : ∀ z ∈ Ω, complexL h z ≠ 0
  pressure0 : ℂ → ℂ
  pressure0_analytic : AnalyticOnNhd ℂ pressure0 Ω
  pressure0_real : ∀ η : ℝ, pressure0 (η : ℂ) = (P0 η : ℂ)

namespace InitialTube

variable {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
variable (E : InitialTube N h P0 R Ω)

def f (T κ δ : ℝ) : CField := E.natural.actF T κ δ
def U (T κ δ : ℝ) : CField := E.natural.actU T κ δ
def Ubar (T κ δ : ℝ) : CField := average (E.U T κ δ)
def Pi (T κ δ : ℝ) : CField := pressure E.pressure0 (E.f T κ δ)

theorem regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) :
    Regular (Ioi (-R)) Ω (E.f T κ δ) ∧
    Regular (Ioi (-R)) Ω (E.U T κ δ) ∧
    Regular (Ioi (-R)) Ω (E.Ubar T κ δ) ∧
    Regular (Ioi (-R)) Ω (E.Pi T κ δ) := by
  have hf := E.natural.actF_regular E.isOpen hT hδ hδT κ
  have hu := E.natural.actU_regular E.isOpen hT hδ hδT κ
  exact ⟨hf,hu,hu.average isOpen_Ioi E.isOpen
    (fun _ hx _ ht => scale_half_interval E.natural.radius_pos hx ht),
      regular_pressure E.natural.radius_pos E.isOpen hf E.pressure0_analytic⟩

/-- The width of the holomorphic domain is unchanged at every fixed radial
derivative order. These are actual iterated derivatives of the functions. -/
theorem all_radial_jets {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) (k : ℕ) :
    Regular (Ioi (-R)) Ω (radialJet (E.f T κ δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.U T κ δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.Ubar T κ δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.Pi T κ δ) k) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.regular hT hδ hδT κ
  exact ⟨hf.radialJet isOpen_Ioi E.isOpen k,hu.radialJet isOpen_Ioi E.isOpen k,
    hv.radialJet isOpen_Ioi E.isOpen k,hp.radialJet isOpen_Ioi E.isOpen k⟩

/-- The signed-square pullbacks are smooth and holomorphic through the axis,
and are even in the signed radius. -/
theorem signed_regular {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) :
    Regular univ Ω (signedSquare (E.f T κ δ)) ∧
    Regular univ Ω (signedSquare (E.U T κ δ)) ∧
    Regular univ Ω (signedSquare (E.Ubar T κ δ)) ∧
    Regular univ Ω (signedSquare (E.Pi T κ δ)) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.regular hT hδ hδT κ
  exact ⟨hf.signedSquare E.natural.radius_pos,hu.signedSquare E.natural.radius_pos,
    hv.signedSquare E.natural.radius_pos,hp.signedSquare E.natural.radius_pos⟩

theorem f_ne_zero (T κ δ : ℝ) {x : ℝ} (hx : 0 ≤ x) {z : ℂ} (hz : z ∈ Ω) :
    E.f T κ δ (x,z) ≠ 0 := E.natural.actF_ne_zero T κ δ hx hz

/-- Agreement includes the literal axis-to-radius average and pressure,
with no independently prescribed moment data. -/
theorem real_profiles {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    E.f T κ δ (x,(η : ℂ)) = (P.f (x,η) : ℂ) ∧
    E.U T κ δ (x,(η : ℂ)) = (P.U (x,η) : ℂ) ∧
    E.Ubar T κ δ (x,(η : ℂ)) = (P.Ubar (x,η) : ℂ) ∧
    E.Pi T κ δ (x,(η : ℂ)) = (P.pressure (x,η) : ℂ) := by
  refine ⟨E.natural.actF_real hδ hδT T κ x hη,
    E.natural.actU_real hδ hδT T κ x hη,?_,?_⟩
  · exact average_ofReal (fun y => E.natural.actU_real hδ hδT T κ y hη) x
  · exact pressure_ofReal (fun y => E.natural.actF_real hδ hδT T κ y hη) (E.pressure0_real η) x

theorem reference_regular {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit) :
    Regular (Ioi (-R)) Ω (E.natural.refF δ) ∧
    Regular (Ioi (-R)) Ω (E.natural.refU δ) ∧
    Regular (Ioi (-R)) Ω (average (E.natural.refU δ)) ∧
    Regular (Ioi (-R)) Ω (pressure E.pressure0 (E.natural.refF δ)) := by
  have hf := E.natural.refF_regular E.isOpen hδ hδT
  have hu := E.natural.refU_regular E.isOpen hδ hδT
  exact ⟨hf,hu,hu.average isOpen_Ioi E.isOpen
    (fun _ hx _ ht => scale_half_interval E.natural.radius_pos hx ht),
      regular_pressure E.natural.radius_pos E.isOpen hf E.pressure0_analytic⟩

theorem reference_real_profiles {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) (x : ℝ) {η : ℝ} (hη : η ∈ ReferencePath.parameterInterval) :
    let P := N.histories hδ hδT P0 hP0
    E.natural.refF δ (x,(η : ℂ)) = (P.f (x,η) : ℂ) ∧
    E.natural.refU δ (x,(η : ℂ)) = (P.U (x,η) : ℂ) ∧
    average (E.natural.refU δ) (x,(η : ℂ)) = (P.Ubar (x,η) : ℂ) ∧
    pressure E.pressure0 (E.natural.refF δ) (x,(η : ℂ)) = (P.pressure (x,η) : ℂ) := by
  refine ⟨E.natural.refF_real hδ hδT x hη,E.natural.refU_real hδ hδT x hη,?_,?_⟩
  · exact average_ofReal (fun y => E.natural.refU_real hδ hδT y hη) x
  · exact pressure_ofReal (fun y => E.natural.refF_real hδ hδT y hη) (E.pressure0_real η) x

end InitialTube

/-- Actual coefficient profiles and the actual pressure datum construct the
common tube. The width is chosen before the REF and ACT cutoff lengths. -/
theorem exists_initialTube {h j σ Λ C : ℝ} {g a : ℝ → ℝ} {cap : ℝ}
    (hp : PressureDatum.Admissible g a cap)
    {d : AnalyticInputs h j σ (PressureDatum.pressure g a)}
    (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ)
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) :
    ∃ ρ : ℝ, 0 < ρ ∧ Nonempty (InitialTube (ReferenceJetBounds.referenceInput F hΛ) h
      (PressureDatum.pressure g a) (5/Λ) (AxisHolomorphic.parameterTube parameterWindow ρ)) := by
  obtain ⟨ρ,hρ,E,hreg⟩ := exists_natural_extension F hΛ hsmall hσ
  refine ⟨ρ,hρ,⟨{
    natural := E
    isOpen := parameterTube_open _ _
    real_mem := fun η hη => AxisHolomorphic.parameterTube_contains_real parameterWindow hρ
      (closed_parameter_subset hη)
    elliptic_ne_zero := fun z hz => (hreg hz).1.2
    pressure0 := PressureDatum.complexPressure g a
    pressure0_analytic := (PressureDatum.complexPressure_analytic hp).mono (fun z hz => (hreg
      hz).1.1)
    pressure0_real := PressureDatum.complexPressure_ofReal g a
  }⟩⟩

theorem natural_average_identity {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ProfileHistories.Field} (hs : NaturalProfile.IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) : ProfileHistories.average U p
      = V p := by
  by_cases hx : p.1 = 0
  · have he : p = (0,p.2) := Prod.ext hx rfl
    rw [he,ProfileHistories.average_at_axis,hs.U_axis p.2 hp.2,hs.average_axis p.2 hp.2]
  · rw [ProfileHistories.average_eq_quotient U hx]
    change (∫ X in (0 : ℝ)..p.1, U (X,p.2)) / p.1 = V p
    rw [← hs.average_integral p hp,mul_div_cancel_left₀ _ hx]

/-- The natural average recovered by complex integration is the original
natural profile's actual average, including the regular value at the axis. -/
theorem natural_Ubar_real {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : CoefficientProfile d Λ C) {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) :
    average (naturalU F) (p.1,(p.2 : ℂ)) = (F.family.Ubar p : ℂ) := by
  rw [average_ofReal (fun x => naturalU_real F x p.2) p.1]
  exact congrArg Complex.ofReal (natural_average_identity F.family.natural hp)

theorem natural_Pi_real {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : CoefficientProfile d Λ C) {P : ℂ → ℂ} (hP : ∀ η : ℝ, P (η : ℂ) = (P0 η : ℂ))
    {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) :
    pressure P (naturalF F) (p.1,(p.2 : ℂ)) = (F.family.Pi p : ℂ) := by
  rw [pressure_ofReal (fun x => naturalF_real F x p.2) (hP p.2) p.1]
  congr 1
  have he := F.family.natural.pressure_integral p hp
  change F.family.Pi p - P0 p.2 = ProfileHistories.primitive (fun q => F.family.f q ^ 2) p at he
  linarith

theorem iteratedDeriv_smooth {S : Set ℝ} (hS : IsOpen S) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S) (k : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv k g) S := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hS (by simp)

theorem iteratedDeriv_ofReal {S : Set ℝ} (hS : IsOpen S) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g S) (k : ℕ) {x : ℝ} (hx : x ∈ S) :
    iteratedDeriv k (fun y => (g y : ℂ)) x = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun y => (g y : ℂ)) =ᶠ[𝓝 x]
        (fun y => ((iteratedDeriv k g y : ℝ) : ℂ)) := by
      filter_upwards [hS.mem_nhds hx] with y hy
      exact ih hy
    rw [heq.deriv_eq]
    exact (((iteratedDeriv_smooth hS hg k).contDiffAt (hS.mem_nhds hx)).differentiableAt
      (by simp)).hasDerivAt.ofReal_comp.deriv

/-- The holomorphic radial jets extend the actual real radial derivatives,
including at the axis; agreement is derived from equality of the functions. -/
theorem radialJet_real {S : Set ℝ} {Ω : Set ℂ} (hS : IsOpen S) (_ : IsOpen Ω)
    {F : CField} (hF : Regular S Ω F) {g : ℝ → ℝ} {η : ℝ} (hη : (η : ℂ) ∈ Ω)
    (heq : ∀ x ∈ S, F (x,(η : ℂ)) = (g x : ℂ)) (k : ℕ) {x : ℝ} (hx : x ∈ S) :
    radialJet F k (x,(η : ℂ)) = ((iteratedDeriv k g x : ℝ) : ℂ) := by
  have hs : ContDiffOn ℝ ∞ (fun x => F (x,(η : ℂ))) S :=
    hF.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨hx,hη⟩)
  have hgr : ContDiffOn ℝ ∞ g S := by
    apply (Complex.reCLM.contDiff.comp_contDiffOn hs).congr
    intro y hy
    change g y = (F (y,(η : ℂ))).re
    rw [heq y hy,Complex.ofReal_re]
  have he : (fun y => F (y,(η : ℂ))) =ᶠ[𝓝 x] (fun y => (g y : ℂ)) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact heq y hy
  exact (he.iteratedDeriv_eq k).trans (iteratedDeriv_ofReal hS hgr k hx)

theorem InitialTube.real_radial_jets {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
    (E : InitialTube N h P0 R Ω) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2*δ < ReferencePath.rampLimit) (κ : ℝ) (hP0 : ContDiff ℝ ∞ P0)
    (k : ℕ) {x η : ℝ} (hx : x ∈ Ioi (-R)) (hη : η ∈ Icc (-1 : ℝ) 1) :
    let P := StressActivation.FromReference.histories N hT hδ hδT κ P0 hP0
    radialJet (E.f T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.f (y,η)) x : ℝ) : ℂ) ∧
    radialJet (E.U T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.U (y,η)) x : ℝ) : ℂ) ∧
    radialJet (E.Ubar T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.Ubar (y,η)) x : ℝ) : ℂ) ∧
    radialJet (E.Pi T κ δ) k (x,(η : ℂ)) = ((iteratedDeriv k (fun y => P.pressure (y,η)) x : ℝ) :
      ℂ) := by
  have hη' := NaturalAxisCoefficients.original_interval_interior hη
  obtain ⟨hf,hu,hv,hp⟩ := E.regular hT hδ hδT κ
  refine ⟨radialJet_real isOpen_Ioi E.isOpen hf (E.real_mem η hη) ?_ k hx,
    radialJet_real isOpen_Ioi E.isOpen hu (E.real_mem η hη) ?_ k hx,
    radialJet_real isOpen_Ioi E.isOpen hv (E.real_mem η hη) ?_ k hx,
    radialJet_real isOpen_Ioi E.isOpen hp (E.real_mem η hη) ?_ k hx⟩
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').1
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').2.1
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').2.2.1
  · intro y _
    exact (E.real_profiles hT hδ hδT κ hP0 y hη').2.2.2

theorem scale_symmetric_interval {R x t : ℝ} (hx : x ∈ Ioo (-R) R) (ht : t ∈ Icc (0 : ℝ) 1) :
    t*x ∈ Ioo (-R) R := by
  apply abs_lt.mp
  calc
    |t*x| = t*|x| := by rw [abs_mul,abs_of_nonneg ht.1]
    _ ≤ |x| := mul_le_of_le_one_left (abs_nonneg x) ht.2
    _ < R := abs_lt.mpr hx

theorem InitialTube.natural_regular {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω : Set ℂ}
    (E : InitialTube N h P0 R Ω) :
    Regular (Ioo (-R) R) Ω E.natural.f ∧
    Regular (Ioo (-R) R) Ω E.natural.U ∧
    Regular (Ioo (-R) R) Ω (average E.natural.U) ∧
    Regular (Ioo (-R) R) Ω (pressure E.pressure0 E.natural.f) := by
  refine ⟨E.natural.f_regular,E.natural.U_regular,?_,?_⟩
  · exact E.natural.U_regular.average isOpen_Ioo E.isOpen
      (fun _ hx _ ht => scale_symmetric_interval hx ht)
  · exact (regular_parameter E.pressure0_analytic).add
      ((E.natural.f_regular.pow 2).primitive isOpen_Ioo E.isOpen
        (fun _ hx _ ht => scale_symmetric_interval hx ht))

theorem InitialTube.natural_all_radial_jets {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω :
  Set ℂ}
    (E : InitialTube N h P0 R Ω) (k : ℕ) :
    Regular (Ioo (-R) R) Ω (radialJet E.natural.f k) ∧
    Regular (Ioo (-R) R) Ω (radialJet E.natural.U k) ∧
    Regular (Ioo (-R) R) Ω (radialJet (average E.natural.U) k) ∧
    Regular (Ioo (-R) R) Ω (radialJet (pressure E.pressure0 E.natural.f) k) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.natural_regular
  exact ⟨hf.radialJet isOpen_Ioo E.isOpen k,hu.radialJet isOpen_Ioo E.isOpen k,
    hv.radialJet isOpen_Ioo E.isOpen k,hp.radialJet isOpen_Ioo E.isOpen k⟩

theorem InitialTube.reference_all_radial_jets {N : ReferencePath.Input} {h R : ℝ} {P0 : ℝ → ℝ} {Ω :
  Set ℂ}
    (E : InitialTube N h P0 R Ω) {δ : ℝ} (hδ : 0 < δ) (hδT : 2*δ < ReferencePath.rampLimit) (k : ℕ)
      :
    Regular (Ioi (-R)) Ω (radialJet (E.natural.refF δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (E.natural.refU δ) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (average (E.natural.refU δ)) k) ∧
    Regular (Ioi (-R)) Ω (radialJet (pressure E.pressure0 (E.natural.refF δ)) k) := by
  obtain ⟨hf,hu,hv,hp⟩ := E.reference_regular hδ hδT
  exact ⟨hf.radialJet isOpen_Ioi E.isOpen k,hu.radialJet isOpen_Ioi E.isOpen k,
    hv.radialJet isOpen_Ioi E.isOpen k,hp.radialJet isOpen_Ioi E.isOpen k⟩

theorem InitialTube.natural_real_profiles {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C) (hΛ : 0 < Λ)
    {R : ℝ} {Ω : Set ℂ} (E : InitialTube (ReferenceJetBounds.referenceInput F hΛ) h P0 R Ω)
    {p : ProfileHistories.Point} (hp : p ∈ NaturalProfile.domain Λ) :
    E.natural.f (p.1,(p.2 : ℂ)) = (F.family.f p : ℂ) ∧
    E.natural.U (p.1,(p.2 : ℂ)) = (F.family.U p : ℂ) ∧
    average E.natural.U (p.1,(p.2 : ℂ)) = (F.family.Ubar p : ℂ) ∧
    pressure E.pressure0 E.natural.f (p.1,(p.2 : ℂ)) = (F.family.Pi p : ℂ) := by
  refine ⟨E.natural.f_real _ _,E.natural.U_real _ _,?_,?_⟩
  · rw [average_ofReal (fun x => E.natural.U_real x p.2) p.1]
    exact congrArg Complex.ofReal (natural_average_identity F.family.natural hp)
  · rw [pressure_ofReal (fun x => E.natural.f_real x p.2) (E.pressure0_real p.2) p.1]
    congr 1
    change P0 p.2 + ProfileHistories.primitive (fun q => F.family.f q ^ 2) p = F.family.Pi p
    have he := F.family.natural.pressure_integral p hp
    change F.family.Pi p - P0 p.2 = ProfileHistories.primitive (fun q => F.family.f q ^ 2) p at he
    linarith

end NavierStokes.ActivationHolomorphic

end
