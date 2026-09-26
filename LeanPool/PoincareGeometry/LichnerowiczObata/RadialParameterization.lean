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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataClock
public import LeanPool.PoincareGeometry.LichnerowiczObata.RegularGradientCurves

/-! # Parameterization on the full open radial interval

The logarithmic clock gives an explicit time change of a complete gradient
curve. No extension to the endpoints or metric isometry is asserted here.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

def obataRadialTime (K a c r : ℝ) : ℝ :=
  obataClock K a (a * Real.cos (Real.sqrt K * r)) - obataClock K a c

theorem obata_cos_level_mem {K a r : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hr : 0 < r ∧ r < Real.pi / Real.sqrt K) :
    -a < a * Real.cos (Real.sqrt K * r) ∧ a * Real.cos (Real.sqrt K * r) < a := by
  have hk : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hθ : Real.sqrt K * r ∈ Ioo 0 Real.pi :=
    ⟨mul_pos hk hr.1, by nlinarith [(lt_div_iff₀ hk).mp hr.2]⟩
  have hc := Real.cosPartialHomeomorph.map_source hθ
  change -1 < Real.cos (Real.sqrt K * r) ∧ Real.cos (Real.sqrt K * r) < 1 at hc
  constructor <;> nlinarith [mul_pos ha (sub_pos.2 hc.2), mul_pos ha (by linarith : 0 < 1 + Real.cos (Real.sqrt K * r))]

theorem hasDerivAt_obataRadialTime {K a c r : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hr : 0 < r ∧ r < Real.pi / Real.sqrt K) :
    HasDerivAt (obataRadialTime K a c)
      ((1 / (K * (a ^ 2 - (a * Real.cos (Real.sqrt K * r)) ^ 2))) *
        (a * (-Real.sin (Real.sqrt K * r) * Real.sqrt K))) r := by
  have hc := (((hasDerivAt_id r).const_mul (Real.sqrt K)).cos).const_mul a
  have hd := (hasDerivAt_obataClock hK ha (obata_cos_level_mem hK ha hr)).comp r hc
  change HasDerivAt (fun s => obataClock K a (a * Real.cos (Real.sqrt K * s)) - obataClock K a c) _ r
  simpa only [Function.comp_def, id_eq, mul_one] using hd.sub_const (obataClock K a c)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [T2Space M]

/-- The explicit time change makes the Obata radial function equal to the
parameter at every point of the full open radial interval. -/
theorem obata_radial_time_identity {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} {γ : ℝ → M}
    (hs : ∀ t, -a < f (γ t) ∧ f (γ t) < a)
    (hd : ∀ t, HasDerivAt (f ∘ γ) (K * (a ^ 2 - f (γ t) ^ 2)) t)
    {r : ℝ} (hr : 0 < r ∧ r < Real.pi / Real.sqrt K) :
    obataRadial K a f (γ (obataRadialTime K a (f (γ 0)) r)) = r := by
  have he := obataClock_inverse_level hK ha hs hd (obata_cos_level_mem hK ha hr)
  change f (γ (obataRadialTime K a (f (γ 0)) r)) = a * Real.cos (Real.sqrt K * r) at he
  unfold obataRadial
  rw [he, mul_div_cancel_left₀ _ (ne_of_gt ha)]
  have hk : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  rw [Real.arccos_cos (mul_pos hk hr.1).le
    (by nlinarith [(lt_div_iff₀ hk).mp hr.2])]
  exact mul_div_cancel_left₀ _ (ne_of_gt hk)

theorem mdifferentiableAt_obata_radial_curve {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (gradient (I := I) f))
    {r : ℝ} (hr : 0 < r ∧ r < Real.pi / Real.sqrt K) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I
      (γ ∘ obataRadialTime K a (f (γ 0))) r := by
  exact (hγ _).mdifferentiableAt.comp r
    (hasDerivAt_obataRadialTime hK ha hr).differentiableAt.mdifferentiableAt

/-- Every regular point lies on a differentiable curve parameterized by the
Obata radial function over its full open interval. -/
theorem exists_full_obata_radial_parameterization
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ x : M, -a < f x ∧ f x < a → ∃ η : ℝ → M,
        η (obataRadial K a f x) = x ∧
        (∀ r, 0 < r ∧ r < Real.pi / Real.sqrt K →
          MDifferentiableAt 𝓘(ℝ, ℝ) I η r ∧ obataRadial K a f (η r) = r) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p, hp, hb, ?_⟩
  intro x hx
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_gradient_curve hf x
  have h0 : gradient (I := I) f (γ 0) ≠ 0 := by
    rw [hγ0]
    intro hz
    have he := hn x
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    have hs : 0 < f p ^ 2 - f x ^ 2 := by nlinarith [hx.1, hx.2]
    have := mul_pos hK hs
    linarith
  have hm := strictMono_gradient_curve hf hγ h0
  have hs : ∀ t, -f p < f (γ t) ∧ f (γ t) < f p := by
    intro t
    exact ⟨lt_of_le_of_lt (hb (γ (t - 1))).1 (hm (by linarith : t - 1 < t)),
      lt_of_lt_of_le (hm (by linarith : t < t + 1)) (hb (γ (t + 1))).2⟩
  have hd : ∀ t, HasDerivAt (f ∘ γ) (K * (f p ^ 2 - f (γ t) ^ 2)) t := by
    intro t
    have hd := hasDerivAt_comp_integralCurve
      ((hf (γ t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) (hγ.isMIntegralCurveAt t)
    rw [← inner_gradient, real_inner_self_eq_norm_sq, hn] at hd
    exact hd
  refine ⟨γ ∘ obataRadialTime K (f p) (f (γ 0)), ?_, ?_⟩
  · have ht0 : obataRadialTime K (f p) (f x) (obataRadial K (f p) f x) = 0 := by
      unfold obataRadialTime
      rw [obataRadial_cos hK hp x (hb x), sub_self]
    simp only [Function.comp_apply, hγ0, ht0]
  · intro r hr
    exact ⟨mdifferentiableAt_obata_radial_curve hK hp hγ hr,
      obata_radial_time_identity hK hp hs hd hr⟩

end LichnerowiczObata
