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

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalRayIntegralCurve
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialCurves

/-! # Uniqueness of normal rays for the actual Obata radial field -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff
namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

omit [T2Space M] in
/-- Only the regular-level condition is needed for local smoothness of
the radial field; no regularity at either extremal level is asserted. -/
theorem contMDiffAt_obataRadial_gradient {K a : ℝ} (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    {x : M} (hx : -a < f x ∧ f x < a) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, gradient (I := I) (obataRadial K a f) y⟩ : TangentBundle I M)) x := by
  have hm : -1 < f x / a := (lt_div_iff₀ ha).mpr (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hx.2)
  let : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
  exact contMDiffAt_gradient 1
    (contMDiffAt_obataRadial (hf x) (K := K) (ne_of_gt hm) (ne_of_lt hp))

/-- Two radial integral curves agreeing once agree on the whole interval
if the first curve remains regular, despite the field's pole singularities. -/
theorem obataRadial_integralCurve_eqOn {K a : ℝ} (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    {γ γ' : ℝ → M} {s t r₀ : ℝ} (hr₀ : r₀ ∈ Ioo s t)
    (hreg : ∀ r ∈ Ioo s t, -a < f (γ r) ∧ f (γ r) < a)
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f)) (Ioo s t))
    (hγ' : IsMIntegralCurveOn γ' (gradient (I := I) (obataRadial K a f)) (Ioo s t))
    (hinit : γ r₀ = γ' r₀) : EqOn γ γ' (Ioo s t) := by
  exact integralCurve_eqOn_of_contMDiffAt_range hr₀
    (fun r hr => contMDiffAt_obataRadial_gradient ha hf (hreg r hr)) hγ hγ' hinit

/-- A normalized normal ray satisfying the retained radial derivative
identity agrees with the actual radial flow once their initial points
agree. Smoothness of the radial field is derived from the regular levels. -/
theorem obata_normal_ray_eq_radial_curve
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {K a : ℝ} (ha : 0 < a) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (ψ : P → M) (u : P) {s t r₀ : ℝ} (hs : 0 ≤ s) (hr₀ : r₀ ∈ Ioo s t)
    (hψ : ∀ r ∈ Ioo s t, MDifferentiableAt 𝓘(ℝ, P) I ψ (r • u))
    (hreg : ∀ r ∈ Ioo s t, -a < f (ψ (r • u)) ∧ f (ψ (r • u)) < a)
    (hrad : ∀ r ∈ Ioo s t, mfderiv 𝓘(ℝ, P) I ψ (r • u) (r • u) =
      r • gradient (I := I) (obataRadial K a f) (ψ (r • u)))
    (γ : ℝ → M)
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f)) (Ioo s t))
    (hinit : ψ (r₀ • u) = γ r₀) : EqOn (fun r => ψ (r • u)) γ (Ioo s t) := by
  exact normal_ray_eq_integralCurve_of_local_field ψ u
    (gradient (I := I) (obataRadial K a f)) hs hr₀
    (fun r hr => contMDiffAt_obataRadial_gradient ha hf (hreg r hr)) hψ hrad γ hγ hinit

/-- The coefficient retained by the metric normal chart becomes the
radial parameter after normalizing the initial direction in its quadratic
metric. Thus this form can be applied before changing to intrinsic coordinates. -/
theorem obata_metric_normal_ray_eq_radial_curve
    {K a : ℝ} (ha : 0 < a) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (ψ : E → M) (u : E) (g : E →L[ℝ] E →L[ℝ] ℝ) (τ : ℝ)
    (hnormal : τ * Real.sqrt (g u u) = 1)
    {s t r₀ : ℝ} (hs : 0 ≤ s) (hr₀ : r₀ ∈ Ioo s t)
    (hψ : ∀ r ∈ Ioo s t, MDifferentiableAt 𝓘(ℝ, E) I ψ (r • u))
    (hreg : ∀ r ∈ Ioo s t, -a < f (ψ (r • u)) ∧ f (ψ (r • u)) < a)
    (hrad : ∀ r ∈ Ioo s t, mfderiv 𝓘(ℝ, E) I ψ (r • u) (r • u) =
      (τ * Real.sqrt (g (r • u) (r • u))) •
        gradient (I := I) (obataRadial K a f) (ψ (r • u)))
    (γ : ℝ → M)
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f)) (Ioo s t))
    (hinit : ψ (r₀ • u) = γ r₀) : EqOn (fun r => ψ (r • u)) γ (Ioo s t) := by
  apply obata_normal_ray_eq_radial_curve ha hf ψ u hs hr₀ hψ hreg ?_ γ hγ hinit
  intro r hr
  have hquad : g (r • u) (r • u) = r ^ 2 * g u u := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hc : τ * Real.sqrt (g (r • u) (r • u)) = r := by
    rw [hquad, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq (lt_of_le_of_lt hs hr.1).le]
    calc
      τ * (r * Real.sqrt (g u u)) = r * (τ * Real.sqrt (g u u)) := by ring
      _ = r := by rw [hnormal, mul_one]
  rw [hrad r hr, hc]

end LichnerowiczObata
