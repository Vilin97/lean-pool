/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialShapeOperator
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialCurves

/-! # Evolution of the angular metric under radial transport

This module derives metric evolution for differentiable angular fields that
commute with the radial field. It does not assume that such fields already
provide a global polar chart.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur VectorField
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

/-- Local integration of spherical metric evolution on a connected open
domain. This does not require a coordinate chart on the entire radial interval. -/
theorem sine_squared_normalized_eq_on {freq : ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T)
    (hphase : ∀ t ∈ T, freq * t ∈ Ioo 0 Real.pi) {q : ℝ → ℝ}
    (hq : ∀ t ∈ T,
      HasDerivAt q (2 * (freq * (Real.cos (freq * t) / Real.sin (freq * t))) * q t) t)
    {u w : ℝ} (hu : u ∈ T) (hw : w ∈ T) :
    q u / Real.sin (freq * u) ^ 2 = q w / Real.sin (freq * w) ^ 2 := by
  have hd (t : ℝ) (ht : t ∈ T) :
      HasDerivAt (fun z => q z / Real.sin (freq * z) ^ 2) 0 t := by
    have hsin : 0 < Real.sin (freq * t) :=
      Real.sin_pos_of_pos_of_lt_pi (hphase t ht).1 (hphase t ht).2
    have hden := (((hasDerivAt_id t).const_mul freq).sin.pow 2)
    have hdiv := (hq t ht).div hden (pow_ne_zero 2 hsin.ne')
    convert hdiv using 1 <;> first | rfl |
      (simp only [Pi.pow_apply, id_eq]; field_simp [hsin.ne']; ring)
  exact hT.is_const_of_deriv_eq_zero hconn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hw

/-- Integrating the spherical metric evolution equation gives its sine-square
factor on the full open radial interval. -/
theorem sine_squared_normalized_eq {s : ℝ} (hs : 0 < s) {q : ℝ → ℝ}
    (hq : ∀ t ∈ Ioo 0 (Real.pi / s),
      HasDerivAt q (2 * (s * (Real.cos (s * t) / Real.sin (s * t))) * q t) t)
    {u w : ℝ} (hu : u ∈ Ioo 0 (Real.pi / s)) (hw : w ∈ Ioo 0 (Real.pi / s)) :
    q u / Real.sin (s * u) ^ 2 = q w / Real.sin (s * w) ^ 2 := by
  apply sine_squared_normalized_eq_on isOpen_Ioo
    (convex_Ioo 0 (Real.pi / s)).isPreconnected _ hq hu hw
  intro t ht
  exact ⟨mul_pos hs ht.1, by nlinarith [(lt_div_iff₀ hs).mp ht.2]⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- Torsion freeness turns Lie transport into covariant transport. Together
with the derived radial shape operator and metric compatibility, this gives
the spherical metric evolution equation. -/
theorem obataRadial_angular_metric_derivative {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {x : M} (hx : -a < f x ∧ f x < a) {X Y : Π y : M, TM y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hNX : mlieBracket I (gradient (I := I) (obataRadial K a f)) X x = 0)
    (hNY : mlieBracket I (gradient (I := I) (obataRadial K a f)) Y x = 0)
    (hTX : inner ℝ (gradient (I := I) (obataRadial K a f) x) (X x) = 0)
    (hTY : inner ℝ (gradient (I := I) (obataRadial K a f) x) (Y x) = 0) :
    mvfderiv I (fun y => inner ℝ (X y) (Y y)) x (gradient (I := I) (obataRadial K a f) x) =
      2 * (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) * inner ℝ (X x) (Y x) := by
  let N := gradient (I := I) (obataRadial K a f)
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  have hN : MDiffAt (T% N) x :=
    mdifferentiableAt_gradient (contMDiffAt_obataRadial (hf x) hm.ne' hp.ne)
  have hswapX : LC X x (N x) = LC N x (X x) := by
    apply sub_eq_zero.mp
    exact ((CovariantDerivative.torsion_eq_zero_iff (cov := LC)).mp
      leviCivitaConnection_torsion hN hX).trans hNX
  have hswapY : LC Y x (N x) = LC N x (Y x) := by
    apply sub_eq_zero.mp
    exact ((CovariantDerivative.torsion_eq_zero_iff (cov := LC)).mp
      leviCivitaConnection_torsion hN hY).trans hNY
  have hd := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
    leviCivitaConnection_metricCompatible N hX hY
  change mvfderiv I (fun y => inner ℝ (X y) (Y y)) x (N x) =
    inner ℝ (LC X x (N x)) (Y x) + inner ℝ (X x) (LC Y x (N x)) at hd
  rw [hswapX, hswapY] at hd
  change mvfderiv I (fun y => inner ℝ (X y) (Y y)) x (N x) = _
  rw [hd, cov_obataRadial_gradient hK ha hf hb hH hx (X x),
    cov_obataRadial_gradient hK ha hf hb hH hx (Y x), hTX, hTY,
    zero_smul, sub_zero, real_inner_smul_left, real_inner_smul_right]
  simp only [sub_zero]
  ring

/-- Along a radial curve, inner products of commuting angular fields have
the exact sine-square scaling. Constructing these fields as global polar
coordinate directions remains a separate obligation. -/
theorem obataRadial_angular_metric_scaling {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TM y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {γ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hlevel : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ t) ∧ f (γ t) < a)
    (hr : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), obataRadial K a f (γ t) = t)
    {X Y : Π y : M, TM y}
    (hX : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% X) (γ t))
    (hY : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% Y) (γ t))
    (hNX : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K),
      mlieBracket I (gradient (I := I) (obataRadial K a f)) X (γ t) = 0)
    (hNY : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K),
      mlieBracket I (gradient (I := I) (obataRadial K a f)) Y (γ t) = 0)
    (hTX : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K),
      inner ℝ (gradient (I := I) (obataRadial K a f) (γ t)) (X (γ t)) = 0)
    (hTY : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K),
      inner ℝ (gradient (I := I) (obataRadial K a f) (γ t)) (Y (γ t)) = 0)
    {u w : ℝ} (hu : u ∈ Ioo 0 (Real.pi / Real.sqrt K)) (hw : w ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    inner ℝ (X (γ u)) (Y (γ u)) / Real.sin (Real.sqrt K * u) ^ 2 =
      inner ℝ (X (γ w)) (Y (γ w)) / Real.sin (Real.sqrt K * w) ^ 2 := by
  apply sine_squared_normalized_eq (Real.sqrt_pos.mpr hK) _ hu hw
  intro t ht
  let : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E TM :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  have hq : ContMDiffAt I 𝓘(ℝ, ℝ) 1 (fun y => inner ℝ (X y) (Y y)) (γ t) :=
    @ContMDiffAt.inner_bundle E _ _ H _ I (1 : ℕ∞ω) M _ _ E _ _ TM _
      (fun y => inferInstance) (fun y => inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y => y) X Y (γ t) (hX t ht) (hY t ht)
  have hd := hasDerivAt_comp_integralCurve hq
    (hγ.isMIntegralCurveAt (isOpen_Ioo.mem_nhds ht))
  rw [obataRadial_angular_metric_derivative hK ha hf hb hH (hlevel t ht)
    ((hX t ht).mdifferentiableAt (by norm_num)) ((hY t ht).mdifferentiableAt (by norm_num))
    (hNX t ht) (hNY t ht) (hTX t ht) (hTY t ht), hr t ht] at hd
  exact hd

end LichnerowiczObata
