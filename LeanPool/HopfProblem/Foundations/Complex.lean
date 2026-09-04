/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1

/-!
# Hopf problem: foundations · complex

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def TriangleRiemannNormalization.discCoordinate {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ℂ :=
  e x

private theorem
    TriangleRiemannNormalization.discCoordinate_injective {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) : Function.Injective (discCoordinate e) := by
  intro x y he
  exact e.injective (Subtype.ext he)

private theorem TriangleRiemannNormalization.discCoordinate_ne {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) {x y : K} (hxy : x ≠ y) :
    discCoordinate e x ≠ discCoordinate e y := fun he => hxy (discCoordinate_injective e he)

private theorem TriangleRiemannNormalization.discCoordinate_norm_le {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (x : K) : ‖discCoordinate e x‖ ≤ 1 := by
  simpa only [discCoordinate, Metric.mem_closedBall, dist_zero_right] using (e x).property

private def TriangleRiemannNormalization.punctureMap {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) (x : {x : K | x ≠ pinf}) :
    RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) :=
  ⟨discCoordinate e x, discCoordinate_norm_le e x, discCoordinate_ne e x.property⟩

private theorem
    TriangleRiemannNormalization.punctureMap_isEmbedding {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Topology.IsEmbedding (punctureMap e pinf) := by
  have hs :
    Topology.IsEmbedding
      (Subtype.val : RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) → ℂ) :=
    Topology.IsEmbedding.subtypeVal
  have he : Topology.IsEmbedding (fun x : {x : K | x ≠ pinf} => e (x : K)) :=
    e.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hv : Topology.IsEmbedding (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) :=
    Topology.IsEmbedding.subtypeVal
  have hcomp : Topology.IsEmbedding (fun x : {x : K | x ≠ pinf} => (e (x : K) : ℂ)) := hv.comp he
  exact hs.of_comp_iff.mp hcomp

private theorem TriangleRiemannNormalization.punctureMap_surjective {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    Function.Surjective (punctureMap e pinf) := by
  intro z
  let y : Metric.closedBall (0 : ℂ) 1 :=
    ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1⟩
  have hx : e.symm y ≠ pinf := by
    intro he
    apply z.property.2
    have h := congrArg (discCoordinate e) he
    simpa only [discCoordinate, Homeomorph.apply_symm_apply] using h
  refine ⟨⟨e.symm y, hx⟩, ?_⟩
  apply Subtype.ext
  exact congrArg (fun w : Metric.closedBall (0 : ℂ) 1 => (w : ℂ)) (e.apply_symm_apply y)

private def TriangleRiemannNormalization.punctureHomeomorph {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (pinf : K) :
    {x : K | x ≠ pinf} ≃ₜ RiemannSphere.closedDiscWithoutPole (discCoordinate e pinf) :=
  (punctureMap_isEmbedding e pinf).toHomeomorphOfSurjective (punctureMap_surjective e pinf)

private def TriangleRiemannNormalization.normalizationHomeomorph {K : Type*} [TopologicalSpace K]
    (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1) (h0inf : p0 ≠ pinf)
    (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1) (h1 : ‖discCoordinate e p1‖ = 1)
    (hinf : ‖discCoordinate e pinf‖ = 1) :
    {x : K | x ≠ pinf} ≃ₜ
      RiemannSphere.closedOrientedHalfPlane
        (RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
          (discCoordinate e pinf)) :=
  (punctureHomeomorph e pinf).trans
    (RiemannSphere.closedDiscHalfPlaneHomeomorph (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf)

@[simp]
private theorem TriangleRiemannNormalization.normalizationHomeomorph_apply {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1)
    (x : {x : K | x ≠ pinf}) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ) =
      RiemannSphere.MobiusCircle.crossRatio (discCoordinate e p0) (discCoordinate e p1)
        (discCoordinate e pinf) (discCoordinate e x) := by
  exact
    RiemannSphere.closedDiscHalfPlaneHomeomorph_apply (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

private theorem TriangleRiemannNormalization.normalizationHomeomorph_first {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p0, h0inf⟩ : ℂ) = 0 := by
  rw [normalizationHomeomorph_apply]
  exact RiemannSphere.MobiusCircle.crossRatio_at_zero _ _ _

private theorem TriangleRiemannNormalization.normalizationHomeomorph_second {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf ⟨p1, h1inf⟩ : ℂ) = 1 := by
  rw [normalizationHomeomorph_apply]
  exact
    RiemannSphere.MobiusCircle.crossRatio_at_one (discCoordinate_ne e h01.symm)
      (discCoordinate_ne e h1inf)

private theorem TriangleRiemannNormalization.normalizationHomeomorph_strict_iff {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1)
    (x : {x : K | x ≠ pinf}) :
    0 <
        RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
            (discCoordinate e pinf) *
          (normalizationHomeomorph e p0 p1 pinf h01 h0inf h1inf h0 h1 hinf x : ℂ).im ↔
      ‖discCoordinate e x‖ < 1 := by
  exact
    RiemannSphere.closedDiscHalfPlaneHomeomorph_strict_iff (discCoordinate_ne e h01)
      (discCoordinate_ne e h0inf) (discCoordinate_ne e h1inf) h0 h1 hinf
      (punctureHomeomorph e pinf x)

private theorem TriangleRiemannNormalization.normalization_orientation_ne_zero {K : Type*}
    [TopologicalSpace K] (e : K ≃ₜ Metric.closedBall (0 : ℂ) 1) (p0 p1 pinf : K) (h01 : p0 ≠ p1)
    (h0inf : p0 ≠ pinf) (h1inf : p1 ≠ pinf) (h0 : ‖discCoordinate e p0‖ = 1)
    (h1 : ‖discCoordinate e p1‖ = 1) (hinf : ‖discCoordinate e pinf‖ = 1) :
    RiemannSphere.MobiusCircle.orientation (discCoordinate e p0) (discCoordinate e p1)
        (discCoordinate e pinf) ≠
      0 :=
  RiemannSphere.MobiusCircle.orientation_ne_zero h0 h1 hinf (discCoordinate_ne e h01.symm)
    (discCoordinate_ne e h1inf) (discCoordinate_ne e h0inf)

private theorem _root_.AnalyticOnNhd.exists_finset_eq_prod_smul_nonzero {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {s : Set 𝕜}
    (hfs : AnalyticOnNhd 𝕜 f s) (hs_comp : IsCompact s) (hs_conn : IsPreconnected s)
    (hf₀ : ¬Set.EqOn f 0 s) :
    ∃ (t : Finset 𝕜),
      (∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0) ∧
        ∃ (g : 𝕜 → E),
          AnalyticOnNhd 𝕜 g s ∧
            (f = fun z ↦ (∏ x ∈ t, (z - x) ^ analyticOrderNatAt f x) • g z) ∧
              (∀ z ∈ s, g z ≠ 0) := by
  have hf_top :
    ∀ {f : 𝕜 → E}, AnalyticOnNhd 𝕜 f s → ¬Set.EqOn f 0 s → ∀ x ∈ s, analyticOrderAt f x ≠ ⊤ := by
    intro f hfs hf₀ x hx hfx
    rw [analyticOrderAt_eq_top] at hfx
    exact hf₀ <| hfs.eqOn_zero_of_preconnected_of_eventuallyEq_zero hs_conn hx hfx
  obtain ⟨t, hts⟩ : ∃ t : Finset 𝕜, ∀ x, x ∈ t ↔ x ∈ s ∧ f x = 0 := by
    use
      hs_comp.finite_sdiff_of_mem_codiscreteWithin
          hfs.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top |>.toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq, not_or,
      analyticOrderAt_eq_zero, and_congr_right_iff]
    push Not
    intro x hx
    simp [hfs _ hx, hf_top hfs hf₀ x hx]
  use t, hts
  induction t using Finset.cons_induction generalizing f with
  | empty =>
    use f, hfs
    simpa using hts
  | cons a t hat iht =>
    simp only [Finset.mem_cons] at hts
    have has : a ∈ s := (hts a).mp (.inl rfl) |>.1
    obtain ⟨g, hga, hg₀, hfg⟩ :
      ∃ g, AnalyticOnNhd 𝕜 g s ∧ g a ≠ 0 ∧ f = fun z ↦ (z - a) ^ analyticOrderNatAt f a • g z := by
      classical
      rcases hfs a has |>.analyticOrderAt_ne_top |>.mp (hf_top hfs hf₀ a has) with
        ⟨g, hga, hg₀, hfg⟩
      set g' := Function.update (fun z ↦ (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z) a (g a)
      have hgg' : g =ᶠ[𝓝 a] g' := by
        refine hfg.mono fun z hz ↦ ?_
        rcases eq_or_ne z a with rfl | hza
        · simp [g']
        · simp [g', hza, hz, sub_eq_zero]
      refine ⟨g', ?_, ?_, ?_⟩
      · intro z hz
        rcases eq_or_ne z a with rfl | hza
        · exact hga.congr hgg'
        · have : g' =ᶠ[𝓝 z] fun z ↦ (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z :=
            eventually_ne_nhds hza |>.mono fun w hw ↦ by simp [g', hw]
          rw [analyticAt_congr this]
          refine .smul (.zpow ?_ (by rwa [sub_ne_zero])) (hfs z hz)
          fun_prop
      · simp [g', hg₀]
      · ext z
        rcases eq_or_ne z a with rfl | hza
        · simpa [g'] using hfg.self_of_nhds
        · simp [g', hza, sub_eq_zero]
    have hgt : ∀ z, z ∈ t ↔ z ∈ s ∧ g z = 0 := by
      rw [hfg] at hts
      intro z
      rcases eq_or_ne z a with rfl | hza
      · simp [hg₀, hat]
      · simpa [hza, sub_eq_zero] using hts z
    have hgs₀ : ¬Set.EqOn g 0 s := by
      intro hgs₀
      exact hg₀ <| hgs₀ has
    rcases iht hga hgs₀ hgt with ⟨g', hg's, hgg', hg'₀⟩
    use g', hg's, ?_, hg'₀
    ext z
    rw [congrFun hfg, congrFun hgg', Finset.prod_cons, SemigroupAction.mul_smul]
    congr 2
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    congr 1
    conv_rhs => rw [hfg, analyticOrderNatAt]
    rw [← Pi.smul_def', analyticOrderAt_smul]
    · suffices analyticOrderAt (fun z ↦ (z - a) ^ analyticOrderNatAt f a) x = 0 by
        rw [this]
        simp [analyticOrderNatAt]
      rw [analyticOrderAt_eq_zero]
      right
      simp [sub_eq_zero, ne_of_mem_of_not_mem hx hat]
    · fun_prop
    · exact hga _ <| ((hts _).mp <| .inr hx).1

private theorem
    _root_.Complex.circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd {f : ℂ → ℂ} {c : ℂ}
    {R : ℝ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hf₀ : ∀ z ∈ Metric.sphere c R, f z ≠ 0) (hR : 0 ≤ R) :
    ∮ z in C(c, R), logDeriv f z =
      (2 * (Real.pi) * Complex.I) * ∑ᶠ z ∈ Metric.ball c R, analyticOrderNatAt f z := by
  rcases
    hf.exists_finset_eq_prod_smul_nonzero (ProperSpace.isCompact_closedBall _ _)
      Metric.isPreconnected_closedBall
      (fun hf₀' ↦
        ((NormedSpace.sphere_nonempty (x := c)).mpr hR).elim fun x hx ↦
          hf₀ x hx <| hf₀' <| Metric.sphere_subset_closedBall hx) with
    ⟨t, htR, g, hgR, hfg, hg₀⟩
  have hne : ∀ z ∈ Metric.sphere c R, ∀ w ∈ t, z - w ≠ 0 := by
    intro z hz w hw
    rw [sub_ne_zero]
    rintro rfl
    rw [htR] at hw
    exact hf₀ _ hz hw.2
  have ht_sub : ↑t ⊆ Metric.ball c R := by
    intro w hw
    rw [Finset.mem_coe, htR, ← Metric.sphere_union_ball, Set.mem_union] at hw
    exact hw.1.resolve_left fun hw' ↦ hf₀ w hw' hw.2
  have hleft :
    Set.EqOn (logDeriv f) (fun z ↦ (∑ w ∈ t, analyticOrderNatAt f w / (z - w)) + logDeriv g z)
      (Metric.sphere c R) := by
    intro z hz
    conv_lhs => rw [hfg]
    simp only [smul_eq_mul]
    rw [logDeriv_mul, logDeriv_prod]
    · congr 1
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv, Pi.div_apply, deriv_sub_const, deriv_id'']
      simp [div_eq_mul_inv]
    · intro w hw
      apply pow_ne_zero
      exact hne z hz w hw
    · intros
      fun_prop
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw ↦ pow_ne_zero _ (hne z hz w hw)
    · exact hg₀ z (Metric.sphere_subset_closedBall hz)
    · fun_prop
    · exact hgR _ (Metric.sphere_subset_closedBall hz) |>.differentiableAt
  rw [finsum_mem_eq_sum_of_subset (t := t), circleIntegral.integral_congr hR hleft]
  · have hdg : AnalyticOnNhd ℂ (logDeriv g) (Metric.closedBall c R) := hgR.deriv.div hgR hg₀
    have hi : ∀ w ∈ t, CircleIntegrable (fun z ↦ analyticOrderNatAt f w / (z - w)) c R := by
      intro w hw
      simp only [div_eq_mul_inv]
      refine .const_mul (circleIntegrable_sub_inv_iff.mpr <| .inr fun hw' ↦ ?_) _
      rw [abs_of_nonneg hR] at hw'
      exact hne w hw' w hw (sub_self _)
    rw [circleIntegral.integral_add, circleIntegral.integral_fun_sum,
      DiffContOnCl.circleIntegral_eq_zero hR, add_zero, Nat.cast_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [Complex.circleIntegral_div_sub_of_differentiable_on_off_countable Set.countable_empty]
      · exact ht_sub hw
      · fun_prop
      · intros; fun_prop
    · exact hdg.differentiableOn.diffContOnCl_ball subset_rfl
    · exact hi
    · exact .fun_sum _ hi
    · exact hdg.continuousOn.mono Metric.sphere_subset_closedBall |>.circleIntegrable hR
  · rintro z ⟨hzc, hz⟩
    rw [Function.mem_support, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or,
      analyticOrderAt_eq_zero, not_or, Classical.not_not, ne_eq, Classical.not_not] at hz
    replace hz := hz.1.2
    rw [hfg, smul_eq_zero, Finset.prod_eq_zero_iff] at hz
    rcases hz.resolve_right (hg₀ z <| Metric.ball_subset_closedBall hzc) with ⟨w, hwt, hzw⟩
    exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzw)).symm ▸ hwt
  · exact ht_sub

private theorem _root_.Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn {ι : Type*}
    {U : Set ℂ} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, ∀ x ∈ U, F i x ≠ 0)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    Set.EqOn f 0 U ∨ ∀ x ∈ U, f x ≠ 0 := by
  have hfd : DifferentiableOn ℂ f U := hf.differentiableOn hFd hUo
  rw [Classical.or_iff_not_imp_left]
  intro hf₀ c hc hfc
  rcases hfd.analyticAt (hUo.mem_nhds hc) |>.eventually_eq_zero_or_eventually_ne_zero with hfc₀ |
    hfc₀
  · exact
      hf₀ <| hfd.analyticOnNhd hUo |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hc hfc₀
  · obtain ⟨R, hR₀, hRU, hfR⟩ :
      ∃ R > 0, Metric.closedBall c R ⊆ U ∧ ∀ w ∈ Metric.sphere c R, f w ≠ 0 := by
      rw [eventually_nhdsWithin_iff] at hfc₀
      rcases
        Metric.nhds_basis_closedBall.eventually_iff.mp (hfc₀.and <| hUo.eventually_mem hc) with
        ⟨R, hR₀, hR⟩
      refine
        ⟨R, hR₀, fun w hw => (hR hw).2, fun w hw =>
          (hR <| Metric.sphere_subset_closedBall hw).1 ?_⟩
      exact Metric.ne_of_mem_sphere hw hR₀.ne'
    have hRU' : Metric.sphere c R ⊆ U := Metric.sphere_subset_closedBall.trans hRU
    have hlogDeriv :
      TendstoUniformlyOn (fun i => logDeriv (F i)) (logDeriv f) l (Metric.sphere c R) := by
      simp only [logDeriv]
      have h := (hf.deriv hFd hUo).mono hRU'
      rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere c R)]
      refine h.fun_div₀ (hf.mono hRU') ?_ ?_ ?_
      · exact hfd.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU'
      · exact hfd.continuousOn.mono hRU'
      · exact hfR
    have hcirc :
      Filter.Tendsto (fun i => ∮ z in C(c, R), logDeriv (F i) z) l
        (𝓝 (∮ z in C(c, R), logDeriv f z)) := by
      apply hlogDeriv.tendsto_circleIntegral_of_continuousOn hR₀.le
      filter_upwards [hF, hFd] with i hi₀ hiD
      refine .div ?_ (hiD.continuousOn.mono hRU') ?_
      · exact hiD.analyticOnNhd hUo |>.deriv |>.continuousOn |>.mono hRU'
      · exact fun x hx => hi₀ x (hRU' hx)
    have H₀ : ∀ᶠ i in l, ∮ (z : ℂ) in C(c, R), logDeriv (F i) z = 0 := by
      filter_upwards [hF, hFd] with i hi hid
      apply DiffContOnCl.circleIntegral_eq_zero hR₀.le
      exact (hid.deriv hUo).div hid hi |>.diffContOnCl_ball hRU
    have hzero := hcirc.congr' H₀
    rw [tendsto_const_nhds_iff, eq_comm,
      Complex.circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd, mul_eq_zero] at hzero
    · replace hzero := hzero.resolve_left (by simp)
      norm_cast at hzero
      refine ne_of_gt ?_ hzero
      apply finsum_cond_pos
      · simp
      · use c
        suffices ∃ᶠ (x : ℂ) in 𝓝 c, f x ≠ 0 by
          simpa [pos_iff_ne_zero, analyticOrderNatAt, analyticOrderAt_eq_zero, hfc,
            analyticOrderAt_eq_top, hfd.analyticAt (hUo.mem_nhds hc), hR₀]
        rw [eventually_nhdsWithin_iff] at hfc₀
        refine Filter.Frequently.mp ?_ hfc₀
        rw [Filter.frequently_iff_neBot, Set.ofPred_mem_eq, ← nhdsWithin]
        infer_instance
      · have hanalytic := (hfd.analyticOnNhd hUo).mono hRU
        have hfinite :=
          (ProperSpace.isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin
            hanalytic.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top
        refine hfinite.subset ?_
        simp +contextual [Set.subset_def, analyticOrderNatAt, le_of_lt]
    · exact hfd.analyticOnNhd hUo |>.mono hRU
    · exact hfR
    · exact hR₀.le

private theorem
    _root_.Complex.eqOn_const_or_injOn_of_tendstoLocallyUniformlyOn {ι : Type*} {U : Set ℂ}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hF : ∀ᶠ i in l, Set.InjOn (F i) U)
    (hFd : ∀ᶠ i in l, DifferentiableOn ℂ (F i) U) (hf : TendstoLocallyUniformlyOn F f l U) :
    (∃ C, ∀ x ∈ U, f x = C) ∨ Set.InjOn f U := by
  rw [Classical.or_iff_not_imp_left]
  intro hfU x hx y hy hxy
  by_contra! hne
  obtain ⟨r, hr₀, hrU, hry⟩ : ∃ r > 0, Metric.ball x r ⊆ U ∧ y ∉ Metric.ball x r := by
    simp_rw [← Set.subset_compl_singleton_iff, ← Set.subset_inter_iff, ← Metric.mem_nhds_iff]
    simp [hUo.mem_nhds hx, hne]
  have hf_sub :
    TendstoLocallyUniformlyOn (fun i z => F i z - F i y) (f · - f y) l (Metric.ball x r) := by
    refine
      (hf.mono hrU).fun_sub <|
        (Filter.Tendsto.tendstoUniformly_const ?_).tendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact hf.tendsto_at hy
  refine
    Complex.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn Metric.isOpen_ball
        Metric.isPreconnected_ball (hF.mono fun i hi z hz => ?_) ?_ hf_sub |>.resolve_left
      ?_ x (by simpa) (by rwa [sub_eq_zero])
  · rw [sub_ne_zero, hi.ne_iff (hrU hz) hy]
    exact ne_of_mem_of_not_mem hz hry
  · exact hFd.mono fun i hi => hi.mono hrU |>.sub_const _
  · intro heq
    refine hfU ⟨f y, ?_⟩
    refine
      hf.differentiableOn hFd hUo |>.analyticOnNhd hUo |>.eqOn_of_preconnected_of_eventuallyEq
        analyticOnNhd_const hUc hx ?_
    exact
      heq.eventuallyEq_of_mem (Metric.ball_mem_nhds _ hr₀) |>.mono fun z hz => sub_eq_zero.mp hz

private theorem
    _root_.Complex.exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ, Function.Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [Set.ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize
      this (hUo.vadd (-a)) (by simpa) (by simp [hU])
        (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← Set.image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (Set.mapsTo_image _ _ hz)
  rcases
    Complex.exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [Set.image_id])
      two_ne_zero with
    ⟨f, hfc, hf_inv⟩
  replace hf_inv : Function.LeftInverse (· ^ 2) f := hf_inv
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  · simp only [Dense, Classical.not_forall, mem_closure_iff_frequently, Filter.not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩
    use -f x
    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx
    rw [nhds_neg, Filter.eventually_neg]
    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

private lemma _root_.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) :
    ∃ f : ℂ → ℂ, Set.MapsTo f U (Metric.ball 0 1) ∧ Set.InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  rcases Complex.exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with
    ⟨f, hf_inj, hfd, hdf⟩
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < Dist.dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)
  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

private lemma _root_.Complex.UnitDisc.shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (Star.star z * w).one_add_coe_ne_zero

private theorem _root_.Complex.UnitDisc.norm_shiftFun_le_mo1973_19129 (z w : 𝔻) :
    ‖(z + w : ℂ) / (1 + conj ↑z * w)‖ ≤ (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  have hz := z.sq_norm_lt_one
  have hw := w.sq_norm_lt_one
  have hzw : z.re * w.re + z.im * w.im ≤ ‖(z : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def, ← Real.sqrt_mul, Complex.normSq_apply,
      Complex.normSq_apply]
    · apply Real.le_sqrt_of_sq_le
      linear_combination (norm :=
        { apply le_of_eq; simp; ring
        })
        sq_nonneg (z.re * w.im - z.im * w.re)
    · apply Complex.normSq_nonneg
  rw [norm_div, div_le_div_iff₀, ← sq_le_sq₀]
  · rw [← sub_nonneg] at hzw
    simp [mul_pow, RCLike.norm_sq_eq_def, add_sq] at hz hw ⊢
    linear_combination 2 * mul_nonneg hzw (mul_nonneg (sub_nonneg.2 hz.le) (sub_nonneg.2 hw.le))
  any_goals positivity
  simpa using Complex.UnitDisc.shift_den_ne_zero z w

private def _root_.Complex.UnitDisc.shiftFun_mo1973_19130 (z w : 𝔻) : 𝔻 :=
  Complex.UnitDisc.mk ((z + w : ℂ) / (1 + conj ↑z * w)) <|
    by
    refine (Complex.UnitDisc.norm_shiftFun_le_mo1973_19129 _ _).trans_lt ?_
    rw [div_lt_one (by positivity)]
    nlinarith only [z.norm_lt_one, w.norm_lt_one]

private theorem _root_.Complex.UnitDisc.coe_shiftFun_mo1973_19131 (z w : 𝔻) :
    (Complex.UnitDisc.shiftFun_mo1973_19130 z w : ℂ) = (z + w) / (1 + conj ↑z * w) :=
  rfl

private theorem _root_.Complex.UnitDisc.shiftFun_eq_iff_mo1973_19132 {z w u : 𝔻} :
    Complex.UnitDisc.shiftFun_mo1973_19130 z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← Complex.UnitDisc.coe_inj, Complex.UnitDisc.coe_shiftFun_mo1973_19131,
    div_eq_iff (Complex.UnitDisc.shift_den_ne_zero _ _)]
  ring_nf

private theorem _root_.Complex.UnitDisc.shiftFun_neg_apply_shiftFun_mo1973_19133 (z w : 𝔻) :
    Complex.UnitDisc.shiftFun_mo1973_19130 (-z) (Complex.UnitDisc.shiftFun_mo1973_19130 z w) =
      w := by
  rw [Complex.UnitDisc.shiftFun_eq_iff_mo1973_19132, Complex.UnitDisc.coe_shiftFun_mo1973_19131,
    add_div_eq_mul_add_div, ← mul_div_assoc, add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact Complex.UnitDisc.shift_den_ne_zero z w

private def _root_.Complex.UnitDisc.shift (z : 𝔻) : 𝔻 ≃ 𝔻
    where
  toFun := Complex.UnitDisc.shiftFun_mo1973_19130 z
  invFun := Complex.UnitDisc.shiftFun_mo1973_19130 (-z)
  left_inv := Complex.UnitDisc.shiftFun_neg_apply_shiftFun_mo1973_19133 _
  right_inv := by
    intro w
    simpa using Complex.UnitDisc.shiftFun_neg_apply_shiftFun_mo1973_19133 (-z) w

private theorem _root_.Complex.UnitDisc.coe_shift (z w : 𝔻) :
    (Complex.UnitDisc.shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := by rfl

private theorem _root_.Complex.UnitDisc.shift_eq_iff {z w u : 𝔻} :
    Complex.UnitDisc.shift z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w :=
  Complex.UnitDisc.shiftFun_eq_iff_mo1973_19132

private theorem _root_.Complex.UnitDisc.symm_shift (z : 𝔻) :
    (Complex.UnitDisc.shift z).symm = Complex.UnitDisc.shift (-z) := by
  ext1
  rfl

@[simp]
private theorem
    _root_.Complex.UnitDisc.shift_apply_zero (z : 𝔻) : Complex.UnitDisc.shift z 0 = z := by
  simp [Complex.UnitDisc.shift_eq_iff]

@[simp]
private theorem _root_.Complex.UnitDisc.shift_eq_zero_iff {z w : 𝔻} :
    Complex.UnitDisc.shift z w = 0 ↔ w = -z := by
  rw [← Equiv.eq_symm_apply, Complex.UnitDisc.symm_shift, Complex.UnitDisc.shift_apply_zero]

@[simp]
private theorem _root_.Complex.UnitDisc.shift_neg_apply_self (z : 𝔻) :
    Complex.UnitDisc.shift (-z) z = 0 := by simp

@[simp]
private theorem _root_.Complex.UnitDisc.shift_neg_apply_shift (z w : 𝔻) :
    Complex.UnitDisc.shift (-z) (Complex.UnitDisc.shift z w) = w := by
  rw [← Complex.UnitDisc.symm_shift, Equiv.symm_apply_apply]

@[fun_prop]
private theorem _root_.Complex.UnitDisc.continuous_shift (z : 𝔻) :
    Continuous (Complex.UnitDisc.shift z) := by
  rw [Complex.UnitDisc.isEmbedding_coe.continuous_iff]
  change Continuous (fun w : 𝔻 ↦ (Complex.UnitDisc.shift z w : ℂ))
  simp only [Complex.UnitDisc.coe_shift]
  exact
    (continuous_const.add Complex.UnitDisc.continuous_coe).div
      (continuous_const.add (continuous_const.mul Complex.UnitDisc.continuous_coe))
      (Complex.UnitDisc.shift_den_ne_zero z)

private theorem
    _root_.Complex.UnitDisc.hasDerivWithinAt_shift_comp {f : ℂ → Complex.UnitDisc} {z f' : ℂ}
    {s : Set ℂ} (w : Complex.UnitDisc) (hf : HasDerivWithinAt (fun x ↦ ↑(f x)) f' s z) :
    HasDerivWithinAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') s z := by
  simp only [Complex.UnitDisc.coe_shift]
  refine
    ((hf.const_add (w : ℂ)).fun_div ((hf.const_mul (conj (w : ℂ))).const_add 1)
          (Complex.UnitDisc.shift_den_ne_zero w (f z))).congr_deriv
      ?_
  rw [← Complex.mul_conj']
  ring

private theorem _root_.Complex.UnitDisc.hasDerivAt_shift_comp {f : ℂ → Complex.UnitDisc} {z f' : ℂ}
    (w : Complex.UnitDisc) (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z :=
  (Complex.UnitDisc.hasDerivWithinAt_shift_comp w hf.hasDerivWithinAt).hasDerivAt Filter.univ_mem

@[simp]
private theorem
    _root_.Complex.UnitDisc.differentiableWithinAt_shift_comp_iff {f : ℂ → Complex.UnitDisc}
    {z : ℂ} {s : Set ℂ} (w : Complex.UnitDisc) :
    DifferentiableWithinAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s z ↔
      DifferentiableWithinAt ℂ (f · : ℂ → ℂ) s z := by
  refine
    ⟨fun h ↦ ?_, fun h ↦
      (Complex.UnitDisc.hasDerivWithinAt_shift_comp w h.hasDerivWithinAt).differentiableWithinAt⟩
  simpa using
    (Complex.UnitDisc.hasDerivWithinAt_shift_comp (-w) h.hasDerivWithinAt).differentiableWithinAt

@[simp]
private theorem _root_.Complex.UnitDisc.differentiableOn_shift_comp_iff {f : ℂ → Complex.UnitDisc}
    {s : Set ℂ} (w : Complex.UnitDisc) :
    DifferentiableOn ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s ↔ DifferentiableOn ℂ (f · : ℂ → ℂ) s := by
  simp [DifferentiableOn]

@[simp]
private theorem
    _root_.Complex.UnitDisc.differentiableAt_shift_comp_iff {f : ℂ → Complex.UnitDisc} {z : ℂ}
    (w : Complex.UnitDisc) :
    DifferentiableAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) z ↔ DifferentiableAt ℂ (f · : ℂ → ℂ) z := by
  refine
    ⟨fun h ↦ ?_, fun h ↦ (Complex.UnitDisc.hasDerivAt_shift_comp w h.hasDerivAt).differentiableAt⟩
  simpa using (Complex.UnitDisc.hasDerivAt_shift_comp (-w) h.hasDerivAt).differentiableAt

@[simp]
private theorem _root_.Complex.UnitDisc.deriv_shift_comp (f : ℂ → Complex.UnitDisc) (z : ℂ)
    (w : Complex.UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z =
      (1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * deriv (f · : ℂ → ℂ) z := by
  by_cases hfd : DifferentiableAt ℂ (f · : ℂ → ℂ) z
  · exact (Complex.UnitDisc.hasDerivAt_shift_comp w hfd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hfd, deriv_zero_of_not_differentiableAt,
      MulZeroClass.mul_zero]
    simpa using hfd

private theorem _root_.Complex.UnitDisc.deriv_shift_comp_eq_zero (f : ℂ → Complex.UnitDisc) (z : ℂ)
    (w : Complex.UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z = 0 ↔ deriv (f · : ℂ → ℂ) z = 0 := by
  simp only [Complex.UnitDisc.deriv_shift_comp, mul_eq_zero, div_eq_zero_iff,
    pow_eq_zero_iff two_ne_zero, Complex.UnitDisc.shift_den_ne_zero, or_false]
  apply or_iff_right
  exact mod_cast sub_ne_zero.mpr w.sq_norm_lt_one.ne'

private theorem _root_.Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀ {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) (x : ℂ) :
    ∃ f : ℂ → Complex.UnitDisc,
      f x = 0 ∧ Set.InjOn f U ∧ (∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ f) z ≠ 0) := by
  classical
  obtain ⟨f, hf_inj, hf_deriv⟩ :
    ∃ f : ℂ → Complex.UnitDisc, Set.InjOn f U ∧ ∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ f) z ≠ 0 :=
    by
    rcases Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero hUo hUc hU with
      ⟨f, hfU, hf_inj, hdf⟩
    use fun z ↦ if hz : z ∈ U then .mk (f z) (by simpa using hfU hz) else 0
    constructor
    · simp +contextual [Set.InjOn, Complex.UnitDisc.mk_inj, hf_inj.eq_iff]
    · intro z hz
      convert hdf z hz using 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hUo.mem_nhds hz] with w hw
      simp [hw]
  use fun z ↦ (-f x).shift (f z)
  refine ⟨?_, (-f x).shift.injective.comp_injOn hf_inj, ?_⟩
  · simp
  · simpa only [Function.comp_def, ne_eq, Complex.UnitDisc.deriv_shift_comp_eq_zero]

private theorem _root_.Complex.exist_map_unitDisc_injOn_norm_deriv_gt_preserves_nonzero
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ)
    {x : ℂ} (hx : x ∈ U) {f : ℂ → Complex.UnitDisc}
    (hdf : DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ f) U) (hf₀ : f x = 0) (hf_inj : Set.InjOn f U)
    (hsurj : ¬Set.SurjOn f U Set.univ) :
    ∃ g : ℂ → Complex.UnitDisc, g x = 0 ∧ Set.InjOn g U ∧
      DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ g) U ∧
      ‖deriv (Complex.UnitDisc.coe ∘ f) x‖ < ‖deriv (Complex.UnitDisc.coe ∘ g) x‖ ∧
      ((∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ f) z ≠ 0) →
        ∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ g) z ≠ 0) := by
  by_cases hdf₀ : deriv (Complex.UnitDisc.coe ∘ f) x = 0
  · rcases Complex.exists_map_unitDisc_injOn_deriv_ne_zero₀ hUo hUc hU x with ⟨g, hg₀, hg_inj, hdg⟩
    refine ⟨g, hg₀, hg_inj, fun z hz ↦ ?_, ?_, fun _ => hdg⟩
    · exact (differentiableAt_of_deriv_ne_zero (hdg z hz)).differentiableWithinAt
    · simpa [hdf₀] using hdg x hx
  obtain ⟨c, hc⟩ : ∃ c, ∀ z ∈ U, f z ≠ c := by
    simpa [Set.SurjOn, Set.eq_univ_iff_forall] using hsurj
  have hcf : ContinuousOn f U := by
    rw [Complex.UnitDisc.isEmbedding_coe.continuousOn_iff]
    exact hdf.continuousOn
  rcases Complex.UnitDisc.exists_continuousOn_pow_eq hUc hUo
    ((-c).continuous_shift.comp_continuousOn hcf) (by simpa) 2 with ⟨g, hgc, hgf⟩
  have hg₀ : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    suffices g z ^ (2 : ℕ+) ≠ 0 by simpa using this
    simp [hgf, hc z hz]
  have hdg : ∀ z ∈ U, HasDerivAt (g · : ℂ → ℂ)
      ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) *
        deriv (f · : ℂ → ℂ) z) z := by
    intro z hz
    refine ((hasDerivAt_pow 2 _).of_comp_left
      (Complex.UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hUo.mem_nhds hz)
      (Complex.UnitDisc.hasDerivAt_shift_comp _ <| (hdf.hasDerivAt <| hUo.mem_nhds hz))
      (by simp [hg₀ z hz])
      (.of_forall fun a ↦ congr(Complex.UnitDisc.coe $(hgf a)))).congr_deriv ?_
    simp [Function.comp_def, field]
    ring
  have hg_sq_norm (z : ℂ) : ‖(g z : ℂ)‖ ^ 2 = ‖((-c).shift (f z) : ℂ)‖ := by
    rw [← norm_pow, ← PNat.val_ofNat, ← Complex.UnitDisc.coe_pow, hgf, Function.comp_apply]
  have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = (Real.sqrt) ‖((-c).shift (f z) : ℂ)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg _), hg_sq_norm]
  refine ⟨(-g x).shift ∘ g, ?map_x, ?injOn, ?deriv, ?norm_deriv, ?preserve⟩
  case map_x => simp
  case injOn =>
    refine (-g x).shift.injective.comp_injOn fun z hz w hw hzw ↦ ?_
    simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
  case deriv =>
    exact (-g x).differentiableOn_shift_comp_iff.mpr fun z hz ↦
      (hdg z hz).differentiableAt.differentiableWithinAt
  case norm_deriv =>
    have hkey : ‖deriv (Complex.UnitDisc.coe ∘ ⇑(-g x).shift ∘ g) x‖ =
        ‖deriv (f · : ℂ → ℂ) x‖ * ((Real.sqrt) ‖(c : ℂ)‖ + (Real.sqrt) ‖(c⁻¹ : ℂ)‖) / 2 := by
      have hgx : ‖(g x : ℂ)‖ = (Real.sqrt) ‖(c : ℂ)‖ := by simp [hg_norm, hf₀]
      simp only [Function.comp_def, Complex.UnitDisc.deriv_shift_comp, (hdg x hx).deriv,
        norm_mul, norm_div, ← mul_assoc, Complex.conj_mul',
        Complex.UnitDisc.coe_neg, map_neg, neg_mul]
      conv_rhs => rw [mul_comm, mul_div_right_comm]
      congr 1
      norm_cast
      have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
      have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
      simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]
      ring
    rw [hkey, mul_div_assoc]
    apply lt_mul_of_one_lt_right
    · simpa using hdf₀
    · have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf₀] using (hc x hx).symm
      suffices (Real.sqrt) ‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
      have : (Real.sqrt) ‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
      rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt] at this
      · linear_combination this
      · apply norm_nonneg
  case preserve =>
    intro hnonzero z hz
    change deriv (fun a => ((-g x).shift (g a) : ℂ)) z ≠ 0
    rw [ne_eq, Complex.UnitDisc.deriv_shift_comp_eq_zero, (hdg z hz).deriv]
    apply mul_ne_zero
    · apply div_ne_zero
      · exact mod_cast sub_ne_zero.mpr c.sq_norm_lt_one.ne'
      · refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (pow_ne_zero _ ?_)
        · simpa using hg₀ z hz
        · simpa only [Complex.UnitDisc.coe_neg, map_neg, neg_mul, ← sub_eq_add_neg] using
            Complex.UnitDisc.shift_den_ne_zero (-c) (f z)
    · exact hnonzero z hz

private theorem _root_.Complex.exist_map_unitDisc_injOn_deriv_ne_zero_norm_deriv_gt {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ Set.univ) {x : ℂ} (hx : x ∈ U)
    {f : ℂ → Complex.UnitDisc} (hdf : DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ f) U)
    (hf₀ : f x = 0) (hf_inj : Set.InjOn f U) (hsurj : ¬Set.SurjOn f U Set.univ)
    (hnonzero : ∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ f) z ≠ 0) :
    ∃ g : ℂ → Complex.UnitDisc,
      g x = 0 ∧
        Set.InjOn g U ∧
          DifferentiableOn ℂ (Complex.UnitDisc.coe ∘ g) U ∧
            (∀ z ∈ U, deriv (Complex.UnitDisc.coe ∘ g) z ≠ 0) ∧
              ‖deriv (Complex.UnitDisc.coe ∘ f) x‖ < ‖deriv (Complex.UnitDisc.coe ∘ g) x‖ := by
  obtain ⟨g, hg₀, hgi, hgd, hgt, hpres⟩ :=
    Complex.exist_map_unitDisc_injOn_norm_deriv_gt_preserves_nonzero hUo hUc hU hx hdf hf₀ hf_inj
      hsurj
  exact ⟨g, hg₀, hgi, hgd, hpres hnonzero, hgt⟩

private def SchwarzReflection.rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

private theorem SchwarzReflection.rectangleIntegral_eq_wedges (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w = Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f := by
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  rfl

private theorem SchwarzReflection.horizontal_line_mem_rectangle {z w : ℂ} {x y : ℝ}
    (hx : x ∈ [[z.re, w.re]]) (hy : y ∈ [[z.im, w.im]]) :
    (x : ℂ) + y * Complex.I ∈ Complex.Rectangle z w := by
  simpa only [Complex.Rectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
    zero_add] using And.intro hx hy

private theorem SchwarzReflection.continuousOn_vertical_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Complex.Rectangle z w)) {x : ℝ} (hx : x ∈ [[z.re, w.re]]) {a b : ℝ}
    (hab : [[a, b]] ⊆ [[z.im, w.im]]) :
    IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.MeasureSpace.volume a
      b := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop)
  intro y hy
  exact horizontal_line_mem_rectangle hx (hab hy)

private theorem SchwarzReflection.rectangleIntegral_split {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Complex.Rectangle z w)) {a : ℝ} (ha : a ∈ [[z.im, w.im]]) :
    rectangleIntegral f z w =
      rectangleIntegral f z (w.re + a * Complex.I) +
        rectangleIntegral f (z.re + a * Complex.I) w := by
  have hz : [[z.im, a]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc (Set.left_mem_uIcc) ha
  have hw : [[a, w.im]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc ha (Set.right_mem_uIcc)
  have hright :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuousOn_vertical_integrable hf (Set.right_mem_uIcc) hz)
      (continuousOn_vertical_integrable hf (Set.right_mem_uIcc) hw)
  have hleft :=
    intervalIntegral.integral_add_adjacent_intervals
      (continuousOn_vertical_integrable hf (Set.left_mem_uIcc) hz)
      (continuousOn_vertical_integrable hf (Set.left_mem_uIcc) hw)
  simp only [rectangleIntegral, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rw [← hright, ← hleft]
  ring

private theorem SchwarzReflection.rectangle_split_lower_subset {z w : ℂ} {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    Complex.Rectangle z (w.re + a * Complex.I) ⊆ Complex.Rectangle z w := by
  have hsub : [[z.im, a]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc Set.left_mem_uIcc ha
  intro x hx
  simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hx ⊢
  exact ⟨hx.1, hsub hx.2⟩

private theorem SchwarzReflection.rectangle_split_upper_subset {z w : ℂ} {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    Complex.Rectangle (z.re + a * Complex.I) w ⊆ Complex.Rectangle z w := by
  have hsub : [[a, w.im]] ⊆ [[z.im, w.im]] := Set.uIcc_subset_uIcc ha Set.right_mem_uIcc
  intro x hx
  simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, MulZeroClass.mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hx ⊢
  exact ⟨hx.1, hsub hx.2⟩

private theorem
    SchwarzReflection.rectangleIntegral_eq_zero_of_axis_not_interior {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Complex.Rectangle z w))
    (hd : ∀ x ∈ Complex.Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x)
    (haxis : (0 : ℝ) ∉ Set.Ioo (Min.min z.im w.im) (Max.max z.im w.im)) :
    rectangleIntegral f z w = 0 := by
  apply
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅
      Set.countable_empty hf
  intro x hx
  have hx' := hx.1
  simp only [Complex.mem_reProdIm, Set.mem_Ioo] at hx'
  apply hd x
  · exact ⟨⟨hx'.1.1.le, hx'.1.2.le⟩, ⟨hx'.2.1.le, hx'.2.2.le⟩⟩
  · intro hzero
    apply haxis
    simpa only [hzero, Set.mem_Ioo] using hx'.2

private theorem SchwarzReflection.zero_not_mem_open_interval_to_zero (a : ℝ) :
    (0 : ℝ) ∉ Set.Ioo (Min.min a 0) (Max.max a 0) := by
  rcases le_total a 0 with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h]

public
theorem SchwarzReflection.differentiableOn_of_continuousOn_off_real {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hf⟩
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, ← rectangleIntegral_eq_wedges]
  have hc := hf.mono hzw
  have hd' : ∀ x ∈ Complex.Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x := fun x hx =>
    hd x (hzw hx)
  by_cases haxis : (0 : ℝ) ∈ Set.Ioo (Min.min z.im w.im) (Max.max z.im w.im)
  · have haxis' : (0 : ℝ) ∈ [[z.im, w.im]] := ⟨haxis.1.le, haxis.2.le⟩
    rw [rectangleIntegral_split hc haxis']
    have hlow := rectangle_split_lower_subset (z := z) (w := w) haxis'
    have hhigh := rectangle_split_upper_subset (z := z) (w := w) haxis'
    have h₁ : rectangleIntegral f z (w.re + (0 : ℝ) * Complex.I) = 0 := by
      apply
        rectangleIntegral_eq_zero_of_axis_not_interior (hc.mono hlow)
          (fun x hx => hd' x (hlow hx))
      simpa using zero_not_mem_open_interval_to_zero z.im
    have h₂ : rectangleIntegral f (z.re + (0 : ℝ) * Complex.I) w = 0 := by
      apply
        rectangleIntegral_eq_zero_of_axis_not_interior (hc.mono hhigh)
          (fun x hx => hd' x (hhigh hx))
      simpa [min_comm, max_comm] using zero_not_mem_open_interval_to_zero w.im
    rw [h₁, h₂, add_zero]
  · exact rectangleIntegral_eq_zero_of_axis_not_interior hc hd' haxis

private theorem SchwarzReflection.analyticOnNhd_of_continuousOn_off_real {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    AnalyticOnNhd ℂ f U :=
  (differentiableOn_of_continuousOn_off_real hU hf hd).analyticOnNhd hU

private def SchwarzReflection.pasteUpper (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then f z else g z

@[simp]
private theorem SchwarzReflection.pasteUpper_of_nonneg (f g : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    pasteUpper f g z = f z :=
  ite_eq_left hz

@[simp]
private theorem SchwarzReflection.pasteUpper_of_neg (f g : ℂ → ℂ) {z : ℂ} (hz : z.im < 0) :
    pasteUpper f g z = g z :=
  ite_eq_right (not_le.mpr hz)

private theorem SchwarzReflection.continuousOn_pasteUpper {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : ContinuousOn f (U ∩ {z | 0 ≤ z.im})) (hg : ContinuousOn g (U ∩ {z | z.im ≤ 0}))
    (hfg : ∀ z ∈ U, z.im = 0 → f z = g z) : ContinuousOn (pasteUpper f g) U := by
  change ContinuousOn (fun z => if 0 ≤ z.im then f z else g z) U
  apply ContinuousOn.if
  · intro z hz
    exact hfg z hz.1 ((frontier_le_subset_eq continuous_const Complex.continuous_im hz.2).symm)
  · simpa only [closure_le_eq continuous_const Complex.continuous_im] using hf
  · apply hg.mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    apply closure_lt_subset_le Complex.continuous_im continuous_const
    simpa only [not_le] using hz.2

private theorem SchwarzReflection.analyticOnNhd_pasteUpper {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hfc : ContinuousOn f (U ∩ {z | 0 ≤ z.im})) (hgc : ContinuousOn g (U ∩ {z | z.im ≤ 0}))
    (hfd : ∀ z ∈ U, 0 < z.im → DifferentiableAt ℂ f z)
    (hgd : ∀ z ∈ U, z.im < 0 → DifferentiableAt ℂ g z) (hfg : ∀ z ∈ U, z.im = 0 → f z = g z) :
    AnalyticOnNhd ℂ (pasteUpper f g) U := by
  apply analyticOnNhd_of_continuousOn_off_real hU (continuousOn_pasteUpper hfc hgc hfg)
  intro z hz hn
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · apply (hgd z hz hneg).congr_of_eventuallyEq
    filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const hneg] with
      w hw
    exact pasteUpper_of_neg f g hw
  · apply (hfd z hz hpos).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hpos] with
      w hw
    exact pasteUpper_of_nonneg f g hw.le

end Mathoverflow1973

end
