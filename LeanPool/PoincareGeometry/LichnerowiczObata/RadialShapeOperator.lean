/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.HessianChainRule

/-! # Angular shape operator of the Obata distance levels -/

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

local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- The cosine reconstruction and Hessian equation determine the full radial
Hessian, including directions tangent to its level sets. -/
theorem obataRadial_hessian_scaled {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TangentSpace I y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {x : M} (hx : -a < f x ∧ f x < a) (v w : TangentSpace I x) :
    (a * Real.sqrt K * Real.sin (Real.sqrt K * obataRadial K a f x)) *
        hessian LC (obataRadial K a f) x v w =
      K * f x * (inner ℝ v w -
        inner ℝ (gradient (I := I) (obataRadial K a f) x) v *
          inner ℝ (gradient (I := I) (obataRadial K a f) x) w) := by
  let r := obataRadial K a f
  let s := Real.sqrt K
  have hs : s ^ 2 = K := Real.sq_sqrt hK.le
  have hr (y : M) (hy : -a < f y ∧ f y < a) : ContMDiffAt I 𝓘(ℝ, ℝ) 2 r y := by
    have hm : -1 < f y / a := (lt_div_iff₀ ha).2 (by nlinarith [hy.1])
    have hp : f y / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hy.2)
    exact contMDiffAt_obataRadial (hf y) hm.ne' hp.ne
  let g : ℝ → ℝ := fun t => a * Real.cos (s * t)
  let dg : ℝ → ℝ := fun t => -a * s * Real.sin (s * t)
  have hg : ContDiff ℝ 2 g := contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  have hdg (t : ℝ) : HasDerivAt g (dg t) t := by
    have ht := (((hasDerivAt_id t).const_mul s).cos.const_mul a)
    convert ht using 1 <;> first | rfl | (dsimp only [dg, id_eq]; ring)
  have hddg : HasDerivAt dg (-a * s ^ 2 * Real.cos (s * r x)) (r x) := by
    have ht := (((hasDerivAt_id (r x)).const_mul s).sin.const_mul (-a * s))
    convert ht using 1 <;> first | rfl | (dsimp only [dg, id_eq]; ring)
  have he : g ∘ r = f := funext (fun y => obataRadial_cos hK ha y (hb y))
  have hc := cov_gradient_scalar_comp LC (hr x hx) hg hdg hddg v
  rw [he] at hc
  have hc' := congrArg (fun z => inner ℝ z w) hc
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at hc'
  change hessian LC f x v w = dg (r x) * hessian LC r x v w +
    (-a * s ^ 2 * Real.cos (s * r x) * mvfderiv I r x v) *
      inner ℝ (gradient (I := I) r x) w at hc'
  rw [hH, ← inner_gradient, hs] at hc'
  have hcos : a * Real.cos (s * r x) = f x := congrFun he x
  dsimp only [dg] at hc'
  have hcoef : -a * K * Real.cos (s * r x) = -K * f x := by
    calc
      -a * K * Real.cos (s * r x) = -K * (a * Real.cos (s * r x)) := by ring
      _ = -K * f x := by rw [hcos]
  rw [hcoef] at hc'
  change (a * s * Real.sin (s * r x)) * hessian LC r x v w = _
  linear_combination hc'

/-- The exact spherical radial Hessian on the regular region. -/
theorem obataRadial_hessian {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TangentSpace I y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {x : M} (hx : -a < f x ∧ f x < a) (v w : TangentSpace I x) :
    hessian LC (obataRadial K a f) x v w =
      (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) *
      (inner ℝ v w - inner ℝ (gradient (I := I) (obataRadial K a f) x) v *
        inner ℝ (gradient (I := I) (obataRadial K a f) x) w) := by
  let r := obataRadial K a f
  let s := Real.sqrt K
  have hs : 0 < s := Real.sqrt_pos.mpr hK
  have hs2 : s ^ 2 = K := Real.sq_sqrt hK.le
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  have hsin : 0 < Real.sin (s * r x) := by
    change 0 < Real.sin (Real.sqrt K * (Real.arccos (f x / a) / Real.sqrt K))
    rw [mul_div_cancel₀ _ hs.ne', Real.sin_arccos]
    exact Real.sqrt_pos.mpr (by nlinarith)
  have hcos : a * Real.cos (s * r x) = f x := obataRadial_cos hK ha x (hb x)
  have hcoef : (a * s * Real.sin (s * r x)) *
      (s * (Real.cos (s * r x) / Real.sin (s * r x))) = K * f x := by
    calc
      (a * s * Real.sin (s * r x)) * (s * (Real.cos (s * r x) / Real.sin (s * r x))) =
          s ^ 2 * (a * Real.cos (s * r x)) := by field_simp [hsin.ne']
      _ = K * f x := by rw [hs2, hcos]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero ha.ne' hs.ne') hsin.ne')
  rw [← mul_assoc, hcoef]
  exact obataRadial_hessian_scaled hK ha hf hb hH hx v w

/-- The radial shape operator is the spherical scalar factor times projection
onto the tangent space of a radial level. -/
theorem cov_obataRadial_gradient {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ y, -a ≤ f y ∧ f y ≤ a)
    (hH : ∀ (y : M) (v w : TangentSpace I y), hessian LC f y v w = -K * f y * inner ℝ v w)
    {x : M} (hx : -a < f x ∧ f x < a) (v : TangentSpace I x) :
    LC (gradient (I := I) (obataRadial K a f)) x v =
      (Real.sqrt K * (Real.cos (Real.sqrt K * obataRadial K a f x) /
        Real.sin (Real.sqrt K * obataRadial K a f x))) •
      (v - inner ℝ (gradient (I := I) (obataRadial K a f) x) v •
        gradient (I := I) (obataRadial K a f) x) := by
  apply ext_inner_right ℝ
  intro w
  rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left]
  exact obataRadial_hessian hK ha hf hb hH hx v w

end LichnerowiczObata
