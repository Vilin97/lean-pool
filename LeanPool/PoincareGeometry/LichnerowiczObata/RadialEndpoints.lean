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

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.UnitCurveDistance
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Completion of radial curves at finite endpoints -/

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

/-- Intrinsic Lipschitz control on a compact Riemannian manifold supplies
a limit at every point of the closure of the parameter domain. -/
theorem exists_tendsto_of_riemannianEDist_le [CompactSpace M] [T2Space M]
    {γ : ℝ → M} {s : Set ℝ}
    (hb : ∀ u ∈ s, ∀ w ∈ s,
      riemannianEDist I (γ u) (γ w) ≤ ENNReal.ofReal |u - w|)
    {x : ℝ} (hx : x ∈ closure s) :
    ∃ p : M, Tendsto γ (𝓝[s] x) (𝓝 p) := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hl : LipschitzOnWith 1 γ s := by
    intro u hu w hw
    change riemannianEDist I (γ u) (γ w) ≤ (1 : ℝ≥0∞) * edist u w
    simpa only [one_mul, edist_dist, Real.dist_eq] using hb u hu w hw
  have : NeBot (𝓝[s] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact cauchy_map_iff_exists_tendsto.mp
    ((cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hl.uniformContinuousOn
      inf_le_right)

/-- Two-sided intrinsic Lipschitz control of the full radial curve. -/
theorem riemannianEDist_obataRadial_curve_le_abs [T2Space M]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {γ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hs : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ t) ∧ f (γ t) < a) :
    ∀ u ∈ Ioo 0 (Real.pi / Real.sqrt K),
      ∀ w ∈ Ioo 0 (Real.pi / Real.sqrt K),
      riemannianEDist I (γ u) (γ w) ≤ ENNReal.ofReal |u - w| := by
    intro u hu w hw
    rcases le_total u w with huw | hwu
    · rw [abs_of_nonpos (sub_nonpos.mpr huw), neg_sub]
      exact riemannianEDist_le_obataRadial_curve hK ha hf hn isOpen_Ioo hγ hs huw
        (fun t ht => ⟨lt_of_lt_of_le hu.1 ht.1, lt_of_le_of_lt ht.2 hw.2⟩)
    · rw [riemannianEDist_comm, abs_of_nonneg (sub_nonneg.mpr hwu)]
      exact riemannianEDist_le_obataRadial_curve hK ha hf hn isOpen_Ioo hγ hs hwu
        (fun t ht => ⟨lt_of_lt_of_le hw.1 ht.1, lt_of_le_of_lt ht.2 hu.2⟩)

/-- Every regular radial gradient curve on the full finite radial interval
converges at both endpoints on a compact manifold. -/
theorem exists_obataRadial_curve_endpoints [CompactSpace M] [T2Space M]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {γ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hs : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ t) ∧ f (γ t) < a) :
    ∃ p q : M,
      Tendsto γ (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
      Tendsto γ (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) := by
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  have hb := riemannianEDist_obataRadial_curve_le_abs hK ha hf hn hγ hs
  obtain ⟨p, hp⟩ := exists_tendsto_of_riemannianEDist_le hb
    (show (0 : ℝ) ∈ closure (Ioo 0 (Real.pi / Real.sqrt K)) by
      rw [closure_Ioo hL.ne]; exact ⟨le_rfl, hL.le⟩)
  obtain ⟨q, hq⟩ := exists_tendsto_of_riemannianEDist_le hb
    (show Real.pi / Real.sqrt K ∈ closure (Ioo 0 (Real.pi / Real.sqrt K)) by
      rw [closure_Ioo hL.ne]; exact ⟨hL.le, le_rfl⟩)
  exact ⟨p, q, hp, hq⟩

/-- The cosine level identity identifies the two limits as extremal points. -/
theorem obataRadial_endpoint_values [T2Space M]
    {K a : ℝ} (hK : 0 < K) {f : M → ℝ} (hf : Continuous f)
    {γ : ℝ → M} {p q : M}
    (hc : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K),
      f (γ t) = a * Real.cos (Real.sqrt K * t))
    (hp : Tendsto γ (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p))
    (hq : Tendsto γ (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q)) :
    f p = a ∧ f q = -a := by
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  have hcont : Continuous (fun t : ℝ => a * Real.cos (Real.sqrt K * t)) := by fun_prop
  have he (x : ℝ) : (fun t => f (γ t)) =ᶠ[𝓝[Ioo 0 (Real.pi / Real.sqrt K)] x]
      (fun t => a * Real.cos (Real.sqrt K * t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hc t ht
  have : NeBot (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ioo hL.ne]; exact ⟨le_rfl, hL.le⟩)
  have : NeBot (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_Ioo hL.ne]; exact ⟨hL.le, le_rfl⟩)
  constructor
  · have ht : Tendsto (fun t : ℝ => a * Real.cos (Real.sqrt K * t))
        (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 a) := by
      simpa using (hcont.continuousAt.continuousWithinAt (s := Ioo 0 (Real.pi / Real.sqrt K))
        (x := 0)).tendsto
    exact tendsto_nhds_unique (hf.continuousAt.tendsto.comp hp) (ht.congr' (he 0).symm)
  · have ht : Tendsto (fun t : ℝ => a * Real.cos (Real.sqrt K * t))
        (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 (-a)) := by
      have hangle : Real.sqrt K * (Real.pi / Real.sqrt K) = Real.pi := by
        field_simp [(Real.sqrt_pos.mpr hK).ne']
      simpa only [hangle, Real.cos_pi, mul_neg_one] using
        (hcont.continuousAt.continuousWithinAt (s := Ioo 0 (Real.pi / Real.sqrt K))
          (x := Real.pi / Real.sqrt K)).tendsto
    exact tendsto_nhds_unique (hf.continuousAt.tendsto.comp hq) (ht.congr' (he _).symm)

/-- The Obata equation constructs full unit radial curves through every
regular point, with convergent extremal endpoints. The poles are not yet
asserted to be independent of the chosen regular point. -/
theorem exists_obata_radial_curves_with_endpoints [CompactSpace M] [Nonempty M]
    [PreconnectedSpace M] [T2Space M] {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) ∧
      ∀ x : M, -a < f x ∧ f x < a → ∃ (η : ℝ → M) (p q : M),
        η (obataRadial K a f x) = x ∧
        IsMIntegralCurveOn η (gradient (I := I) (obataRadial K a f))
          (Ioo 0 (Real.pi / Real.sqrt K)) ∧
        (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (η r) = r ∧ ‖mfderiv 𝓘(ℝ, ℝ) I η r 1‖ = 1) ∧
        Tendsto η (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
        Tendsto η (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) ∧
        f p = a ∧ f q = -a := by
  obtain ⟨p₀, q₀, hp₀, hq₀, hgp₀, hgq₀, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p₀, hp₀, hb, hn, ?_⟩
  intro x hx
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_gradient_curve hf x
  have h0 : gradient (I := I) f (γ 0) ≠ 0 := by
    rw [hγ0]
    intro hz
    have he := hn x
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hs : 0 < f p₀ ^ 2 - f x ^ 2 := by nlinarith [hx.1, hx.2]
    have := mul_pos hK hs
    linarith
  have hm := strictMono_gradient_curve hf hγ h0
  have hs : ∀ t, -f p₀ < f (γ t) ∧ f (γ t) < f p₀ := by
    intro t
    exact ⟨lt_of_le_of_lt (hb (γ (t - 1))).1 (hm (by linarith : t - 1 < t)),
      lt_of_lt_of_le (hm (by linarith : t < t + 1)) (hb (γ (t + 1))).2⟩
  have hd : ∀ t, HasDerivAt (f ∘ γ) (K * (f p₀ ^ 2 - f (γ t) ^ 2)) t := by
    intro t
    have hd := hasDerivAt_comp_integralCurve
      ((hf (γ t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) (hγ.isMIntegralCurveAt t)
    rw [← inner_gradient, real_inner_self_eq_norm_sq, hn] at hd
    exact hd
  let η := γ ∘ obataRadialTime K (f p₀) (f (γ 0))
  have hi := isMIntegralCurveOn_obataRadial_timeChange hK hp₀ hf hγ hs hd
  obtain ⟨p, q, hp, hq⟩ := exists_obataRadial_curve_endpoints hK hp₀ hf hn hi
    (fun t _ => hs _)
  have hc : ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      f (η r) = f p₀ * Real.cos (Real.sqrt K * r) := by
    intro r hr
    exact obataClock_inverse_level hK hp₀ hs hd (obata_cos_level_mem hK hp₀ hr)
  obtain ⟨hfp, hfq⟩ := obataRadial_endpoint_values hK hf.continuous hc hp hq
  refine ⟨η, p, q, ?_, hi, ?_, hp, hq, hfp, hfq⟩
  · have ht0 : obataRadialTime K (f p₀) (f x) (obataRadial K (f p₀) f x) = 0 := by
      unfold obataRadialTime
      rw [obataRadial_cos hK hp₀ x (hb x), sub_self]
    simp only [η, Function.comp_apply, hγ0, ht0]
  · intro r hr
    exact ⟨obata_radial_time_identity hK hp₀ hs hd hr,
      norm_velocity_obataRadial_timeChange hK hp₀ hf hn hγ hs hd hr⟩

end LichnerowiczObata
