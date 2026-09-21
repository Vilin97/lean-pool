/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialFlowFamily
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Continuity of the radial endpoint maps -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold Filter
open scoped Manifold ContDiff Topology ENNReal

namespace LichnerowiczObata

/-- A vanishing uniform distance bound identifies a continuous limit map. -/
theorem continuousOn_of_uniform_edist_bound {X Y : Type*} [TopologicalSpace X]
    [PseudoEMetricSpace Y] {s : Set X} {η : X × ℝ → Y} {P : X → Y}
    {l : Filter ℝ} [NeBot l] {b : ℝ → ℝ≥0∞}
    (hc : ∀ᶠ t in l, ContinuousOn (fun x => η (x, t)) s)
    (hb : ∀ᶠ t in l, ∀ x ∈ s, edist (P x) (η (x, t)) ≤ b t)
    (ht : Tendsto b l (𝓝 0)) : ContinuousOn P s := by
  have hu : TendstoUniformlyOn (fun t x => η (x, t)) P l s := by
    rw [EMetric.tendstoUniformlyOn_iff]
    intro ε hε
    have he : ∀ᶠ t in l, b t < ε := ht.eventually (gt_mem_nhds hε)
    filter_upwards [he, hb] with t het hbt
    intro x hx
    exact lt_of_le_of_lt (hbt x hx) het
  exact hu.continuousOn hc.frequently

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local instance poleMapsSmoothMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance poleMapsContinuousMetric : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The endpoint maps of a continuous family of actual radial gradient
curves are continuous: the endpoint error is uniformly bounded by radial time. -/
theorem continuousOn_radial_endpoint_maps [T3Space M]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {s : Set M} {η : M × ℝ → M} {P Q : M → M}
    (hc : ContinuousOn η (s ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hi : ∀ x ∈ s, IsMIntegralCurveOn (fun r => η (x, r))
      (gradient (I := I) (obataRadial K a f)) (Ioo 0 (Real.pi / Real.sqrt K)))
    (hs : ∀ x ∈ s, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      -a < f (η (x, r)) ∧ f (η (x, r)) < a)
    (hp : ∀ x ∈ s, Tendsto (fun r => η (x, r)) (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 (P x)))
    (hq : ∀ x ∈ s, Tendsto (fun r => η (x, r))
      (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 (Q x))) :
    ContinuousOn P s ∧ ContinuousOn Q s := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  have : NeBot (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ioo hL.ne]; exact ⟨le_rfl, hL.le⟩)
  have : NeBot (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ioo hL.ne]; exact ⟨hL.le, le_rfl⟩)
  have hc' (r : ℝ) (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
      ContinuousOn (fun x => η (x, r)) s :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, hr⟩)
  have hb (x : M) (hx : x ∈ s) (r : ℝ) (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) :=
    obataRadial_endpoint_distance hK ha hf hn (hi x hx) (hs x hx) (hp x hx) (hq x hx) hr
  constructor
  · apply continuousOn_of_uniform_edist_bound (η := η) (b := ENNReal.ofReal)
      (l := 𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact hc' r hr
    · filter_upwards [self_mem_nhdsWithin] with r hr
      intro x hx
      change riemannianEDist I (P x) (η (x, r)) ≤ ENNReal.ofReal r
      rw [riemannianEDist_comm]
      exact (hb x hx r hr).1
    · simpa only [ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · apply continuousOn_of_uniform_edist_bound (η := η)
      (b := fun r => ENNReal.ofReal (Real.pi / Real.sqrt K - r))
      (l := 𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact hc' r hr
    · filter_upwards [self_mem_nhdsWithin] with r hr
      intro x hx
      change riemannianEDist I (Q x) (η (x, r)) ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - r)
      rw [riemannianEDist_comm]
      exact (hb x hx r hr).2
    · have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (Real.pi / Real.sqrt K - r)) :=
        ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)
      simpa only [sub_self, ENNReal.ofReal_zero] using
        (hcont.tendsto (Real.pi / Real.sqrt K)).mono_left nhdsWithin_le_nhds

/-- The Obata equation constructs continuous maximum and minimum endpoint
maps on the regular region, with their intrinsic distance bounds. These
maps have not yet been proved constant. -/
theorem exists_continuous_obata_pole_maps [CompactSpace M] [T2Space M]
    [Nonempty M] [PreconnectedSpace M] {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) ∧
      ∃ P Q : M → M,
        ContinuousOn P {x | -a < f x ∧ f x < a} ∧
        ContinuousOn Q {x | -a < f x ∧ f x < a} ∧
        ∀ x : M, -a < f x ∧ f x < a →
          f (P x) = a ∧ f (Q x) = -a ∧
          riemannianEDist I x (P x) ≤ ENNReal.ofReal (obataRadial K a f x) ∧
          riemannianEDist I x (Q x) ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x) := by
  classical
  obtain ⟨a, ha, hb, hn, η, hηc, hη⟩ := exists_continuous_obata_radial_family hK hf hnon hH
  have he : ∀ x : M, ∃ p q : M, -a < f x ∧ f x < a →
      Tendsto (fun r => η (x, r)) (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
      Tendsto (fun r => η (x, r))
        (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) ∧
      f p = a ∧ f q = -a := by
    intro x
    by_cases hx : -a < f x ∧ f x < a
    · obtain ⟨p, q, hpq⟩ := (hη x hx).2.2.2
      exact ⟨p, q, fun _ => hpq⟩
    · exact ⟨x, x, fun h => False.elim (hx h)⟩
  choose P Q hPQ using he
  have hs : ∀ x : M, -a < f x ∧ f x < a →
      ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (η (x, r)) ∧ f (η (x, r)) < a := by
    intro x hx r hr
    have he := obataRadial_cos hK ha (η (x, r)) (hb _)
    rw [((hη x hx).2.2.1 r hr).1] at he
    rw [← he]
    exact obata_cos_level_mem hK ha hr
  have hc := continuousOn_radial_endpoint_maps hK ha hf hn hηc
    (fun x hx => (hη x hx).2.1) hs
    (fun x hx => (hPQ x hx).1) (fun x hx => (hPQ x hx).2.1)
  refine ⟨a, ha, hb, hn, P, Q, hc.1, hc.2, ?_⟩
  intro x hx
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  have hxr : obataRadial K a f x ∈ Ioo 0 (Real.pi / Real.sqrt K) :=
    ⟨div_pos (Real.arccos_pos.mpr hp) (Real.sqrt_pos.mpr hK),
      (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr hK)).mpr (Real.arccos_lt_pi.mpr hm)⟩
  have hd := obataRadial_endpoint_distance hK ha hf hn (hη x hx).2.1 (hs x hx)
    (hPQ x hx).1 (hPQ x hx).2.1 hxr
  rw [(hη x hx).1] at hd
  exact ⟨(hPQ x hx).2.2.1, (hPQ x hx).2.2.2, hd⟩

end LichnerowiczObata
