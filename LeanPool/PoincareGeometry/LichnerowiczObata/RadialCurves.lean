/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.EikonalConnection
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! # Local radial gradient curves

The scalar chain-rule proof is adapted from
`almost-schur/AlmostSchur/AlmostSchurEquality.lean`,
`test_hasDerivAt_comp_local_curve`, at repository commit
`3faf25aefc27842a77c37ca178e8a40a20bb20c7`.
The radial application is new; no global geodesic existence is assumed.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Scalar differentiation along an actual manifold integral curve. -/
theorem hasDerivAt_comp_integralCurve
    {q : M → ℝ} {v : Π x : M, TM x} {γ : ℝ → M} {t : ℝ}
    (hq : ContMDiffAt I 𝓘(ℝ, ℝ) 1 q (γ t))
    (hγ : IsMIntegralCurveAt γ v t) :
    HasDerivAt (q ∘ γ) (mvfderiv I q (γ t) (v (γ t))) t := by
  have hcomp := hq.mdifferentiableAt (by norm_num) |>.hasMFDerivAt.comp t
    hγ.hasMFDerivAt
  have hcomp' := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  let R : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t :=
    ContinuousLinearMap.mk
      { toFun := fun y => y
        map_add' := by intro y z; rfl
        map_smul' := by intro a y; rfl }
      continuous_id
  let L : TangentSpace 𝓘(ℝ, ℝ) (q (γ t)) →L[ℝ] ℝ :=
    ContinuousLinearMap.mk
      { toFun := fun y => y
        map_add' := by intro y z; rfl
        map_smul' := by intro a y; rfl }
      continuous_id
  have hsource := hcomp'.comp t (ContinuousLinearMap.hasFDerivAt R)
  have hdT := (ContinuousLinearMap.hasFDerivAt L).comp t hsource
  have hder := hdT.hasDerivAt
  have hder' : HasDerivAt (q ∘ γ)
      ((L.comp (mfderiv% q (γ t) ∘SL
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((fun x => v x) (γ t))) ∘ R) 1) t :=
    hder.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => by
        change q (γ s) = L (q (γ (R s)))
        rfl))
  have heq :
      (NormedSpace.fromTangentSpace (q (γ t)))
          ((mfderiv% q (γ t) ∘SL
            ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (v (γ t))) 1) =
        mvfderiv I q (γ t) (v (γ t)) := by
    simp [mvfderiv, NormedSpace.fromTangentSpace]
  exact hder'.congr_deriv (by
    simp [L, R]
    exact heq)

theorem hasDerivAt_obataRadial_curve {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {γ : ℝ → M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (gradient (I := I) (obataRadial K a f)) t)
    (hx : -a < f (γ t) ∧ f (γ t) < a) :
    HasDerivAt (obataRadial K a f ∘ γ) 1 t := by
  have hm : -1 < f (γ t) / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f (γ t) / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  have hr := contMDiffAt_obataRadial ((hf (γ t)).of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
    (K := K) (ne_of_gt hm) (ne_of_lt hp)
  have hd := hasDerivAt_comp_integralCurve hr hγ
  rw [← inner_gradient, real_inner_self_eq_norm_sq,
    norm_gradient_obataRadial hK ha ((hf (γ t)).mdifferentiableAt (by norm_num)) hx (hn _),
    one_pow] at hd
  exact hd

/-- Existence comes from the local ODE theorem for the constructed radial field. -/
theorem exists_obataRadial_curve {K a : ℝ} (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    {x : M} (hx : -a < f x ∧ f x < a) :
    ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurveAt γ (gradient (I := I) (obataRadial K a f)) 0 := by
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  letI : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  have hg := contMDiffAt_gradient 1
    (contMDiffAt_obataRadial (hf x) (K := K) (ne_of_gt hm) (ne_of_lt hp))
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := (0 : ℝ)) hg

/-- Near every regular point, there is a radial curve with the exact radial
parameterization. The statement is local, not a completeness assertion. -/
theorem exists_obataRadial_curve_linear {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {x : M} (hx : -a < f x ∧ f x < a) :
    ∃ γ : ℝ → M, ∃ ε : ℝ, 0 < ε ∧ γ 0 = x ∧
      IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f)) (Metric.ball 0 ε) ∧
      (∀ t ∈ Metric.ball 0 ε, obataRadial K a f (γ t) = obataRadial K a f x + t) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_obataRadial_curve (K := K) ha hf hx
  have hcurves : ∀ᶠ t in 𝓝 (0 : ℝ),
      IsMIntegralCurveAt γ (gradient (I := I) (obataRadial K a f)) t := by
    obtain ⟨ε, hε, hon⟩ := isMIntegralCurveAt_iff'.mp hγ
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    exact hon.isMIntegralCurveAt (Metric.isOpen_ball.mem_nhds ht)
  have hlevels : ∀ᶠ t in 𝓝 (0 : ℝ), -a < f (γ t) ∧ f (γ t) < a := by
    have hc := hf.continuous.continuousAt.comp hγ.continuousAt
    have hm : Ioo (-a) a ∈ 𝓝 ((f ∘ γ) 0) := by
      simpa only [Function.comp_apply, hγ0] using Ioo_mem_nhds hx.1 hx.2
    exact hc hm
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hcurves.and hlevels)
  have hd : ∀ t ∈ Metric.ball (0 : ℝ) ε,
      HasDerivAt (fun s => obataRadial K a f (γ s) - s) 0 t := by
    intro t ht
    have ht' := he ht
    simpa only [Function.comp_def, Pi.sub_def, id_eq, sub_self] using
      (hasDerivAt_obataRadial_curve hK ha hf hn ht'.1 ht'.2).sub (hasDerivAt_id t)
  refine ⟨γ, ε, hε, hγ0, ?_, ?_⟩
  · exact IsMIntegralCurveAt.isMIntegralCurveOn (fun t ht => (he ht).1)
  · intro t ht
    have hc := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : ℝ) ε).isPreconnected
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) ht (Metric.mem_ball_self hε)
    simp only [hγ0, sub_zero] at hc
    linarith

/-- Local radial parameterizations obtained directly from the Obata equation. -/
theorem exists_obata_radial_local_curves
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ x, -a < f x ∧ f x < a →
        ∃ γ : ℝ → M, ∃ ε : ℝ, 0 < ε ∧ γ 0 = x ∧
          IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f)) (Metric.ball 0 ε) ∧
          (∀ t ∈ Metric.ball 0 ε,
            obataRadial K a f (γ t) = obataRadial K a f x + t)) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  exact ⟨f p, hp, hb, fun _ hx => exists_obataRadial_curve_linear hK hp hf hn hx⟩

end LichnerowiczObata
