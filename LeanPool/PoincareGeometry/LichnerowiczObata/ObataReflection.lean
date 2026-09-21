/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataNormalRay

/-! # Reflection of an Obata function exchanges its radial poles -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

omit [I.Boundaryless] in
theorem obata_gradient_neg (f : M → ℝ) (x : M) :
    gradient (I := I) (fun y => -f y) x = -gradient (I := I) f x := by
  simp only [gradient, mvfderiv_fun_neg, map_neg]

omit [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)] [FiniteDimensional ℝ E] in
/-- Reflection measures the complementary distance from the opposite pole. -/
theorem obataRadial_neg (K a : ℝ) (f : M → ℝ) (x : M) :
    obataRadial K a (fun y => -f y) x = Real.pi / Real.sqrt K - obataRadial K a f x := by
  simp only [obataRadial, neg_div, Real.arccos_neg, sub_div]

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The two regular radial vector fields have opposite orientations. -/
theorem obata_radial_gradient_neg {K a : ℝ} (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {x : M}
    (hx : -a < f x ∧ f x < a) :
    gradient (I := I) (obataRadial K a (fun y => -f y)) x =
      -gradient (I := I) (obataRadial K a f) x := by
  have hm : -1 < f x / a := (lt_div_iff₀ ha).mpr (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hx.2)
  have hr := (contMDiffAt_obataRadial (hf x) (K := K) (ne_of_gt hm) (ne_of_lt hp)).mdifferentiableAt
    (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have he : obataRadial K a (fun y => -f y) =
      (fun r : ℝ => Real.pi / Real.sqrt K - r) ∘ obataRadial K a f :=
    funext (obataRadial_neg K a f)
  rw [he]
  have hd : HasDerivAt (fun r : ℝ => Real.pi / Real.sqrt K - r) (-1)
      (obataRadial K a f x) := by
    simpa using (hasDerivAt_id (obataRadial K a f x)).const_sub (Real.pi / Real.sqrt K)
  simpa using gradient_comp_hasDerivAt hr hd

/-- Reversing the radial parameter turns an actual north-oriented
integral curve into an integral curve of the reflected radial field. -/
theorem obata_radial_curve_reflection {K a : ℝ} (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {γ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hreg : ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ r) ∧ f (γ r) < a) :
    IsMIntegralCurveOn (fun r => γ (Real.pi / Real.sqrt K - r))
      (gradient (I := I) (obataRadial K a (fun y => -f y)))
      (Ioo 0 (Real.pi / Real.sqrt K)) := by
  intro r hr
  let τ := fun s : ℝ => Real.pi / Real.sqrt K - s
  have ht : τ r ∈ Ioo 0 (Real.pi / Real.sqrt K) := by
    change 0 < Real.pi / Real.sqrt K - r ∧ Real.pi / Real.sqrt K - r < Real.pi / Real.sqrt K
    constructor <;> linarith [hr.1, hr.2]
  have hτ : HasDerivAt τ (-1) r := by simpa [τ] using (hasDerivAt_id r).const_sub (Real.pi / Real.sqrt K)
  have hc : HasMFDerivAt 𝓘(ℝ, ℝ) I (γ ∘ τ) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-gradient (I := I) (obataRadial K a f) (γ (τ r)))) := by
    convert! ((hγ (τ r) ht).hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2)).comp r
      hτ.hasFDerivAt.hasMFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro s
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
    change -(s • gradient (I := I) (obataRadial K a f) (γ (τ r))) =
      (s * (-1)) • gradient (I := I) (obataRadial K a f) (γ (τ r))
    simp
  rw [← obata_radial_gradient_neg ha hf (hreg (τ r) ht)] at hc
  exact hc.hasMFDerivWithinAt

/-- A north-oriented and a south-oriented radial curve that meet at one
complementary pair of times agree at all complementary times. -/
theorem obata_opposite_radial_curves_eqOn [T2Space M] {K a : ℝ} (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {γ σ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hreg : ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ r) ∧ f (γ r) < a)
    (hσ : IsMIntegralCurveOn σ (gradient (I := I) (obataRadial K a (fun y => -f y)))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (hinit : γ (Real.pi / Real.sqrt K - r₀) = σ r₀) :
    EqOn (fun r => γ (Real.pi / Real.sqrt K - r)) σ (Ioo 0 (Real.pi / Real.sqrt K)) := by
  apply obataRadial_integralCurve_eqOn ha hf.neg hr₀ ?_
    (obata_radial_curve_reflection ha hf hγ hreg) hσ hinit
  intro r hr
  have ht : Real.pi / Real.sqrt K - r ∈ Ioo 0 (Real.pi / Real.sqrt K) := by
    constructor <;> linarith [hr.1, hr.2]
  have hh := hreg _ ht
  constructor <;> linarith [hh.1, hh.2]

omit [I.Boundaryless] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The actual covariant Hessian changes sign, using linearity of the
connection on the differentiable gradient section. -/
theorem obata_hessian_neg (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M)
    (v w : TangentSpace I x) :
    hessian cov (fun y => -f y) x v w = -hessian cov f x v w := by
  have hg : gradient (I := I) (fun y => -f y) = (-1 : ℝ) • gradient (I := I) f := by
    funext y
    simpa using obata_gradient_neg f y
  rw [hessian_apply, hg]
  rw [cov.isCovariantDerivativeOnUniv.smul_const (-1) (mdifferentiableAt_gradient (hf x))]
  simp [hessian_apply]

/-- Reflection preserves the Obata Hessian equation with the same curvature. -/
theorem obata_hessian_equation_neg
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K : ℝ}
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) (fun y => -f y) x v w =
        -K * (-f x) * inner ℝ v w := by
  intro x v w
  rw [obata_hessian_neg _ hf, hH]
  ring

end LichnerowiczObata
