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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialParameterization

/-! # Velocity of the full radial parameterization -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

theorem obata_radial_coefficients {K a r : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hr : 0 < r ∧ r < Real.pi / Real.sqrt K) :
    (1 / (K * (a ^ 2 - (a * Real.cos (Real.sqrt K * r)) ^ 2))) *
        (a * (-Real.sin (Real.sqrt K * r) * Real.sqrt K)) =
      ((-(1 / Real.sqrt (1 - (Real.cos (Real.sqrt K * r)) ^ 2)) * (1 / a)) /
        Real.sqrt K) := by
  have hk : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hθ : 0 < Real.sqrt K * r ∧ Real.sqrt K * r < Real.pi :=
    ⟨mul_pos hk hr.1, by nlinarith [(lt_div_iff₀ hk).mp hr.2]⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have htrig : 1 - Real.cos (Real.sqrt K * r) ^ 2 = Real.sin (Real.sqrt K * r) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.sqrt K * r)]
  have hdiff : a ^ 2 - (a * Real.cos (Real.sqrt K * r)) ^ 2 =
      a ^ 2 * Real.sin (Real.sqrt K * r) ^ 2 := by
    calc
      _ = a ^ 2 * (1 - Real.cos (Real.sqrt K * r) ^ 2) := by ring
      _ = _ := by rw [htrig]
  rw [hdiff, htrig, Real.sqrt_sq hs.le]
  field_simp
  nlinarith [Real.sq_sqrt hK.le]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
/-- Chain rule for a time change of an actual manifold integral curve. -/
theorem hasMFDerivAt_integralCurve_timeChange {v : Π x : M, TangentSpace I x}
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) {τ : ℝ → ℝ} {t c : ℝ}
    (hτ : HasDerivAt τ c t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (γ ∘ τ) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (c • v (γ (τ t)))) := by
  convert! (hγ (τ t)).comp t hτ.hasFDerivAt.hasMFDerivAt using 1
  ext
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
    ContinuousLinearMap.toSpanSingleton_apply_one, one_smul]
  change c • v (γ (τ t)) = (1 * c) • v (γ (τ t))
  rw [one_mul]

/-- The full time-changed curve is an integral curve of the actual radial
gradient on the entire open radial interval. -/
theorem isMIntegralCurveOn_obataRadial_timeChange {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (gradient (I := I) f))
    (hs : ∀ t, -a < f (γ t) ∧ f (γ t) < a)
    (hd : ∀ t, HasDerivAt (f ∘ γ) (K * (a ^ 2 - f (γ t) ^ 2)) t) :
    IsMIntegralCurveOn (γ ∘ obataRadialTime K a (f (γ 0)))
      (gradient (I := I) (obataRadial K a f)) (Ioo 0 (Real.pi / Real.sqrt K)) := by
  intro r hr
  have hlevel := obataClock_inverse_level hK ha hs hd (obata_cos_level_mem hK ha hr)
  change f (γ (obataRadialTime K a (f (γ 0)) r)) = a * Real.cos (Real.sqrt K * r) at hlevel
  have hk : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hc := Real.cosPartialHomeomorph.map_source
    (show Real.sqrt K * r ∈ Ioo 0 Real.pi from
      ⟨mul_pos hk hr.1, by nlinarith [(lt_div_iff₀ hk).mp hr.2]⟩)
  change -1 < Real.cos (Real.sqrt K * r) ∧ Real.cos (Real.sqrt K * r) < 1 at hc
  have hm : f (γ (obataRadialTime K a (f (γ 0)) r)) / a ≠ -1 := by
    rw [hlevel, mul_div_cancel_left₀ _ (ne_of_gt ha)]
    exact ne_of_gt hc.1
  have hp : f (γ (obataRadialTime K a (f (γ 0)) r)) / a ≠ 1 := by
    rw [hlevel, mul_div_cancel_left₀ _ (ne_of_gt ha)]
    exact ne_of_lt hc.2
  have hg := gradient_obataRadial ((hf _).mdifferentiableAt (by norm_num)) hm hp (K := K)
  rw [hlevel, mul_div_cancel_left₀ _ (ne_of_gt ha), ← obata_radial_coefficients hK ha hr] at hg
  have ht := hasMFDerivAt_integralCurve_timeChange hγ
    (hasDerivAt_obataRadialTime (c := f (γ 0)) hK ha hr)
  rw [← hg] at ht
  exact ht.hasMFDerivWithinAt

/-- The intrinsic velocity has norm one on the full open radial interval. -/
theorem norm_velocity_obataRadial_timeChange {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ (gradient (I := I) f))
    (hs : ∀ t, -a < f (γ t) ∧ f (γ t) < a)
    (hd : ∀ t, HasDerivAt (f ∘ γ) (K * (a ^ 2 - f (γ t) ^ 2)) t)
    {r : ℝ} (hr : 0 < r ∧ r < Real.pi / Real.sqrt K) :
    ‖mfderiv 𝓘(ℝ, ℝ) I (γ ∘ obataRadialTime K a (f (γ 0))) r 1‖ = 1 := by
  have hi := isMIntegralCurveOn_obataRadial_timeChange hK ha hf hγ hs hd
  have ht := (hi r hr).hasMFDerivAt (Ioo_mem_nhds hr.1 hr.2)
  rw [ht.mfderiv]
  change ‖(1 : ℝ) • gradient (I := I) (obataRadial K a f)
    (γ (obataRadialTime K a (f (γ 0)) r))‖ = 1
  rw [one_smul]
  exact norm_gradient_obataRadial hK ha ((hf _).mdifferentiableAt (by norm_num)) (hs _) (hn _)

/-- Unit-speed radial curves on the full open interval, constructed from the
Obata equation rather than assumed as geometric input. -/
theorem exists_full_unit_radial_curves [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    [T2Space M] {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ x : M, -a < f x ∧ f x < a → ∃ η : ℝ → M,
        η (obataRadial K a f x) = x ∧
        IsMIntegralCurveOn η (gradient (I := I) (obataRadial K a f))
          (Ioo 0 (Real.pi / Real.sqrt K)) ∧
        (∀ r, 0 < r ∧ r < Real.pi / Real.sqrt K →
          obataRadial K a f (η r) = r ∧ ‖mfderiv 𝓘(ℝ, ℝ) I η r 1‖ = 1) := by
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
  refine ⟨γ ∘ obataRadialTime K (f p) (f (γ 0)), ?_,
    isMIntegralCurveOn_obataRadial_timeChange hK hp hf hγ hs hd, ?_⟩
  · have ht0 : obataRadialTime K (f p) (f x) (obataRadial K (f p) f x) = 0 := by
      unfold obataRadialTime
      rw [obataRadial_cos hK hp x (hb x), sub_self]
    simp only [Function.comp_apply, hγ0, ht0]
  · intro r hr
    exact ⟨obata_radial_time_identity hK hp hs hd hr,
      norm_velocity_obataRadial_timeChange hK hp hf hn hγ hs hd hr⟩

end LichnerowiczObata
