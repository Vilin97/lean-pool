/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialEndpoints

/-! # Intrinsic distance bounds up to the radial endpoints -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur MeasureTheory Manifold Filter
open scoped Manifold ContDiff Topology ENNReal

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The intrinsic Lipschitz estimate persists when one parameter tends to
a point of the closure of the domain. -/
theorem riemannianEDist_le_of_curve_tendsto [T3Space M]
    {γ : ℝ → M} {s : Set ℝ}
    (hb : ∀ u ∈ s, ∀ w ∈ s,
      riemannianEDist I (γ u) (γ w) ≤ ENNReal.ofReal |u - w|)
    {x r : ℝ} (hx : x ∈ closure s) (hr : r ∈ s) {p : M}
    (hp : Tendsto γ (𝓝[s] x) (𝓝 p)) :
    riemannianEDist I (γ r) p ≤ ENNReal.ofReal |r - x| := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have : NeBot (𝓝[s] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hd : Tendsto (fun t => riemannianEDist I (γ r) (γ t)) (𝓝[s] x)
      (𝓝 (riemannianEDist I (γ r) p)) := tendsto_const_nhds.edist hp
  have hc : Continuous (fun t : ℝ => ENNReal.ofReal |r - t|) :=
    ENNReal.continuous_ofReal.comp ((continuous_const.sub continuous_id).abs)
  apply le_of_tendsto_of_tendsto hd (hc.continuousAt.continuousWithinAt.tendsto)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hb r hr t ht

/-- Each point of a radial curve is within its remaining radial time of
the corresponding endpoint. This is an upper bound, not yet minimality. -/
theorem obataRadial_endpoint_distance [T3Space M]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {γ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hs : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ t) ∧ f (γ t) < a)
    {p q : M}
    (hp : Tendsto γ (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p))
    (hq : Tendsto γ (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q))
    {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    riemannianEDist I (γ r) p ≤ ENNReal.ofReal r ∧
      riemannianEDist I (γ r) q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - r) := by
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  have hb := riemannianEDist_obataRadial_curve_le_abs hK ha hf hn hγ hs
  constructor
  · have hd := riemannianEDist_le_of_curve_tendsto hb
      (show (0 : ℝ) ∈ closure (Ioo 0 (Real.pi / Real.sqrt K)) by
        rw [closure_Ioo hL.ne]; exact ⟨le_rfl, hL.le⟩) hr hp
    simpa only [sub_zero, abs_of_pos hr.1] using hd
  · have hd := riemannianEDist_le_of_curve_tendsto hb
      (show Real.pi / Real.sqrt K ∈ closure (Ioo 0 (Real.pi / Real.sqrt K)) by
        rw [closure_Ioo hL.ne]; exact ⟨hL.le, le_rfl⟩) hr hq
    simpa only [abs_of_neg (sub_neg.mpr hr.2), neg_sub] using hd

/-- Every regular point has extremal endpoints at the predicted upper
distance bounds, derived directly from the Obata equation. -/
theorem exists_obata_extrema_distance_bounds [CompactSpace M] [Nonempty M]
    [PreconnectedSpace M] [T2Space M] {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ x : M, -a < f x ∧ f x < a → ∃ p q : M,
        f p = a ∧ f q = -a ∧
        riemannianEDist I x p ≤ ENNReal.ofReal (obataRadial K a f x) ∧
        riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x) := by
  obtain ⟨a, ha, hb, hn, hcurves⟩ := exists_obata_radial_curves_with_endpoints hK hf hnon hH
  refine ⟨a, ha, hb, ?_⟩
  intro x hx
  obtain ⟨η, p, q, hηx, hi, hr, hp, hq, hfp, hfq⟩ := hcurves x hx
  have hs : ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (η r) ∧ f (η r) < a := by
    intro r hri
    have he := obataRadial_cos hK ha (η r) (hb _)
    rw [(hr r hri).1] at he
    rw [← he]
    exact obata_cos_level_mem hK ha hri
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hlt : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  have hxr : obataRadial K a f x ∈ Ioo 0 (Real.pi / Real.sqrt K) := by
    exact ⟨div_pos (Real.arccos_pos.mpr hlt) (Real.sqrt_pos.mpr hK),
      (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr hK)).mpr (Real.arccos_lt_pi.mpr hm)⟩
  have hd := obataRadial_endpoint_distance hK ha hf hn hi hs hp hq hxr
  rw [hηx] at hd
  exact ⟨p, q, hfp, hfq, hd⟩

end LichnerowiczObata
