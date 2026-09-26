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

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothGlobalFlow
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialFlowFamily

/-! # Smooth gradient flows and their radial time change -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold Filter
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
/-- The logarithmic clock is smooth at every regular level. -/
theorem contDiffAt_obataClock (n : ℕ∞ω) {K a s : ℝ}
    (hs : -a < s ∧ s < a) : ContDiffAt ℝ n (obataClock K a) s := by
  have hp : a + s ≠ 0 := ne_of_gt (by linarith)
  have hm : a - s ≠ 0 := ne_of_gt (sub_pos.2 hs.2)
  exact (((contDiffAt_const.add contDiffAt_id).log hp).sub
    ((contDiffAt_const.sub contDiffAt_id).log hm)).div_const (2 * K * a)

/-- Resetting the initial point alongAlmostSchur a radial curve does not change the
curve. This is forced by the complete flow law and its attained level. -/
theorem obataRadialFamily_reset {X : Type*} {K a : ℝ} {f : X → ℝ} {G : X → ℝ → X}
    (hadd : ∀ x s t, G x (s + t) = G (G x t) s) {x : X} {r : ℝ}
    (hlevel : f (obataRadialFamily K a f G (x, r)) = a * Real.cos (Real.sqrt K * r))
    (s : ℝ) :
    obataRadialFamily K a f G (obataRadialFamily K a f G (x, r), s) =
      obataRadialFamily K a f G (x, s) := by
  change G (G x (obataRadialTime K a (f x) r))
    (obataRadialTime K a (f (obataRadialFamily K a f G (x, r))) s) =
      G x (obataRadialTime K a (f x) s)
  rw [← hadd, hlevel]
  congr 1
  simp only [obataRadialTime]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- A smooth complete flow stays jointly smooth after the explicit radial
time change, away from the two extremal levels. -/
theorem contMDiffOn_obataRadialFamily
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {G : M → ℝ → M}
    (hG : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun z : M × ℝ => G z.1 z.2)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (obataRadialFamily K a f G)
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) := by
  intro z hz
  have hc : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => obataClock K a (f w.1)) z :=
    (contDiffAt_obataClock ∞ hz.1).contMDiffAt.comp z ((hf.comp contMDiff_fst) z)
  have hcos : ContDiff ℝ ∞ (fun t : ℝ => a * Real.cos (Real.sqrt K * t)) := by fun_prop
  have ht : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => obataClock K a (a * Real.cos (Real.sqrt K * w.2))) z :=
    (contDiffAt_obataClock ∞ (obata_cos_level_mem hK ha hz.2)).contMDiffAt.comp z
      ((hcos.contMDiff.comp contMDiff_snd) z)
  have htime : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => obataRadialTime K a (f w.1) w.2) z := ht.sub hc
  exact ((hG _).comp z (contMDiffAt_fst.prodMk htime)).contMDiffWithinAt

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [CompactSpace M] [T2Space M]

/-- The actual intrinsic gradient of a smooth function has a jointly smooth
complete flow on a compact smooth Riemannian manifold. -/
theorem exists_smooth_global_gradient_flow {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∃ G : M → ℝ → M, ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun z : M × ℝ => G z.1 z.2) ∧
      (∀ x, G x 0 = x) ∧ ∀ x, IsMIntegralCurve (G x) (gradient (I := I) f) := by
  exact exists_smooth_global_manifold_flow (contMDiff_gradient_infty hf)
/-- One constructed smooth family has the radial ODE, unit speed, radial
coordinate identity, and extremal endpoint limits simultaneously. -/
theorem exists_smooth_obata_radial_family [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ} (hfs : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) ∧
      ∃ η : M × ℝ → M,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ η ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)) ∧
        ∀ x : M, -a < f x ∧ f x < a →
          η (x, obataRadial K a f x) = x ∧
          (∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), ∀ s : ℝ, η (η (x, r), s) = η (x, s)) ∧
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
  have hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hfs.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨p₀, q₀, hp₀, hq₀, hgp₀, hgq₀, hb, hn⟩ := obata_extrema hK hf hnon hH
  obtain ⟨G, hGc, hG0, hG⟩ := exists_smooth_global_gradient_flow hfs
  let η := obataRadialFamily K (f p₀) f G
  refine ⟨f p₀, hp₀, hb, hn, η, contMDiffOn_obataRadialFamily hK hp₀ hfs hGc, ?_⟩
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
  refine ⟨?_, ?_, hi, ?_, p, q, hp, hq, hfp, hfq⟩
  · have ht0 : obataRadialTime K (f p₀) (f x) (obataRadial K (f p₀) f x) = 0 := by
      unfold obataRadialTime
      rw [obataRadial_cos hK hp₀ x (hb x), sub_self]
    simp only [η, obataRadialFamily, ht0, hG0]
  · intro r hr s
    exact obataRadialFamily_reset
      (integralCurve_family_add (contMDiff_gradient 1 hf) hG0 hG) (hc r hr) s
  · intro r hr
    have hpoint : η (x, r) = G x (obataRadialTime K (f p₀) (f (G x 0)) r) := congrFun hη r
    constructor
    · rw [hpoint]
      exact obata_radial_time_identity (γ := G x) hK hp₀ hs hd hr
    · have hv := norm_velocity_obataRadial_timeChange (γ := G x) hK hp₀ hf hn (hG x) hs hd hr
      rw [hG0] at hv
      simpa only [η, obataRadialFamily, Function.comp_def] using hv


end LichnerowiczObata
