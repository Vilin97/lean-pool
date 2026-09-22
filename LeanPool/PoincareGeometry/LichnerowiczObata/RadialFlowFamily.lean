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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ContinuousGlobalFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialEndpointDistance

/-! # A jointly continuous family of full radial curves -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold Filter
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

/-- The explicit radial time change of a family of gradient curves. -/
def obataRadialFamily {X : Type*} (K a : ℝ) (f : X → ℝ) (G : X → ℝ → X)
    (z : X × ℝ) : X := G z.1 (obataRadialTime K a (f z.1) z.2)

/-- The explicit clock preserves joint continuity on regular initial
points and the open radial interval. -/
theorem continuousOn_obataRadialFamily {X : Type*} [TopologicalSpace X]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : X → ℝ} (hf : Continuous f)
    {G : X → ℝ → X} (hG : Continuous (fun z : X × ℝ => G z.1 z.2)) :
    ContinuousOn (obataRadialFamily K a f G)
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) := by
  intro z hz
  have hc : ContinuousAt (fun w : X × ℝ => obataClock K a (f w.1)) z :=
    (hasDerivAt_obataClock hK ha hz.1).continuousAt.comp' (f := fun w : X × ℝ => f w.1)
      (hf.comp continuous_fst).continuousAt
  have hcos : Continuous (fun w : X × ℝ => a * Real.cos (Real.sqrt K * w.2)) := by fun_prop
  have ht : ContinuousAt (fun w : X × ℝ => obataClock K a (a * Real.cos (Real.sqrt K * w.2))) z :=
    (hasDerivAt_obataClock hK ha (obata_cos_level_mem hK ha hz.2)).continuousAt.comp'
      (f := fun w : X × ℝ => a * Real.cos (Real.sqrt K * w.2))
      hcos.continuousAt
  have htime : ContinuousAt (fun w : X × ℝ => obataRadialTime K a (f w.1) w.2) z := ht.sub hc
  exact (hG.continuousAt.comp' (f := fun w : X × ℝ => (w.1, obataRadialTime K a (f w.1) w.2))
    (continuousAt_fst.prodMk htime)).continuousWithinAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [CompactSpace M] [T2Space M]

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The actual gradient of a C2 function has a jointly continuous complete
flow on a compact manifold. -/
theorem exists_continuous_global_gradient_flow {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
    ∃ G : M → ℝ → M, Continuous (fun z : M × ℝ => G z.1 z.2) ∧
      (∀ x, G x 0 = x) ∧ ∀ x, IsMIntegralCurve (G x) (gradient (I := I) f) := by
  let : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  exact exists_continuous_global_manifold_flow (contMDiff_gradient 1 hf)
/-- The Obata equation supplies a single jointly continuous family of full
unit radial curves through all regular points, with extremal endpoints.
No continuous dependence or endpoint existence is assumed. -/
theorem exists_continuous_obata_radial_family [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) ∧
      ∃ η : M × ℝ → M,
        ContinuousOn η ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) ∧
        ∀ x : M, -a < f x ∧ f x < a →
          η (x, obataRadial K a f x) = x ∧
          IsMIntegralCurveOn (fun r => η (x, r)) (gradient (I := I) (obataRadial K a f))
            (Ioo 0 (Real.pi / Real.sqrt K)) ∧
          (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            obataRadial K a f (η (x, r)) = r ∧
              ‖mfderiv 𝓘(ℝ, ℝ) I (fun t => η (x, t)) r 1‖ = 1) ∧
          ∃ p q : M,
            Tendsto (fun r => η (x, r)) (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] 0) (𝓝 p) ∧
            Tendsto (fun r => η (x, r))
              (𝓝[Ioo 0 (Real.pi / Real.sqrt K)] (Real.pi / Real.sqrt K)) (𝓝 q) ∧
            f p = a ∧ f q = -a := by
  obtain ⟨p₀, q₀, hp₀, hq₀, hgp₀, hgq₀, hb, hn⟩ := obata_extrema hK hf hnon hH
  obtain ⟨G, hGc, hG0, hG⟩ := exists_continuous_global_gradient_flow hf
  let η := obataRadialFamily K (f p₀) f G
  refine ⟨f p₀, hp₀, hb, hn, η, continuousOn_obataRadialFamily hK hp₀ hf.continuous hGc, ?_⟩
  intro x hx
  have h0 : gradient (I := I) f (G x 0) ≠ 0 := by
    rw [hG0]
    intro hz
    have he := hn x
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hs : 0 < f p₀ ^ 2 - f x ^ 2 := by nlinarith [hx.1, hx.2]
    have := mul_pos hK hs
    linarith
  have hm := strictMono_gradient_curve hf (hG x) h0
  have hs : ∀ t, -f p₀ < f (G x t) ∧ f (G x t) < f p₀ := by
    intro t
    exact ⟨lt_of_le_of_lt (hb (G x (t - 1))).1 (hm (by linarith : t - 1 < t)),
      lt_of_lt_of_le (hm (by linarith : t < t + 1)) (hb (G x (t + 1))).2⟩
  have hd : ∀ t, HasDerivAt (f ∘ G x) (K * (f p₀ ^ 2 - f (G x t) ^ 2)) t := by
    intro t
    have hd := hasDerivAt_comp_integralCurve
      ((hf (G x t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) ((hG x).isMIntegralCurveAt t)
    rw [← inner_gradient, real_inner_self_eq_norm_sq, hn] at hd
    exact hd
  have hη : (fun r => η (x, r)) = G x ∘ obataRadialTime K (f p₀) (f (G x 0)) := by
    funext r
    simp only [η, obataRadialFamily, hG0, Function.comp_apply]
  have hi := isMIntegralCurveOn_obataRadial_timeChange hK hp₀ hf (hG x) hs hd
  rw [← hη] at hi
  obtain ⟨p, q, hp, hq⟩ := exists_obataRadial_curve_endpoints hK hp₀ hf hn hi
    (fun r _ => hs _)
  have hc : ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      f (η (x, r)) = f p₀ * Real.cos (Real.sqrt K * r) := by
    intro r hr
    have he := obataClock_inverse_level hK hp₀ hs hd (obata_cos_level_mem hK hp₀ hr)
    simpa only [η, obataRadialFamily, obataRadialTime, hG0] using he
  obtain ⟨hfp, hfq⟩ := obataRadial_endpoint_values hK hf.continuous hc hp hq
  refine ⟨?_, hi, ?_, p, q, hp, hq, hfp, hfq⟩
  · have ht0 : obataRadialTime K (f p₀) (f x) (obataRadial K (f p₀) f x) = 0 := by
      unfold obataRadialTime
      rw [obataRadial_cos hK hp₀ x (hb x), sub_self]
    simp only [η, obataRadialFamily, ht0, hG0]
  · intro r hr
    have hpoint : η (x, r) = G x (obataRadialTime K (f p₀) (f (G x 0)) r) := congrFun hη r
    constructor
    · rw [hpoint]
      exact obata_radial_time_identity (γ := G x) hK hp₀ hs hd hr
    · have hv := norm_velocity_obataRadial_timeChange (γ := G x) hK hp₀ hf hn (hG x) hs hd hr
      rw [hG0] at hv
      simp only [η, obataRadialFamily, Function.comp_def] at hv ⊢
      convert! hv

end LichnerowiczObata
