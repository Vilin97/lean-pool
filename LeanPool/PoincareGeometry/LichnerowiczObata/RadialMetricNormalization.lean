/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicFlowMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialVariation

/-! # Initial-level normalization of the radial variation metric -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

/-- At the initial radial level the actual variation metric is the original
inner product on angular vectors. -/
theorem radialVariationMetric_initial {ρ : M → ℝ} {η : M × ℝ → M} {x : M}
    (hη : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I η (x, ρ x))
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hinit : (fun y => η (y, ρ y)) =ᶠ[𝓝 x] id) (v w : TM x)
    (hv : mfderiv I 𝓘(ℝ, ℝ) ρ x v = 0) (hw : mfderiv I 𝓘(ℝ, ℝ) ρ x w = 0) :
    radialVariationMetric (I := I) η x v w (ρ x) = inner ℝ v w := by
  have he : η (x, ρ x) = x := hinit.eq_of_nhds
  simp only [radialVariationMetric,
    radial_initial_derivative_of_tangent hη hρ hinit v hv,
    radial_initial_derivative_of_tangent hη hρ hinit w hw]
  rw [he]

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The exact radial transport metric, normalized by the actual initial
inner product rather than an unspecified integration constant. -/
theorem radialVariationMetric_eq_sine_ratio {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} {η : M × ℝ → M} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (hinit : ∀ y, -a < f y ∧ f y < a → η (y, obataRadial K a f y) = y)
    (x : M) (hx : -a < f x ∧ f x < a) (v w : TM x)
    (hv : mfderiv I 𝓘(ℝ, ℝ) (obataRadial K a f) x v = 0)
    (hw : mfderiv I 𝓘(ℝ, ℝ) (obataRadial K a f) x w = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    radialVariationMetric (I := I) η x v w t =
      (Real.sin (Real.sqrt K * t) ^ 2 /
        Real.sin (Real.sqrt K * obataRadial K a f x) ^ 2) * inner ℝ v w := by
  have hdivm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hdivp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa only [one_mul] using hx.2)
  have hk : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hr : obataRadial K a f x ∈ Ioo 0 (Real.pi / Real.sqrt K) := by
    exact ⟨div_pos (Real.arccos_pos.mpr hdivp) hk,
      (div_lt_div_iff_of_pos_right hk).mpr (Real.arccos_lt_pi.mpr hdivm)⟩
  have hU : IsOpen {y : M | -a < f y ∧ f y < a} :=
    (isOpen_lt continuous_const hf.continuous).inter (isOpen_lt hf.continuous continuous_const)
  have hρ : MDiffAt (obataRadial K a f) x :=
    (contMDiffAt_obataRadial (K := K) (hf x) hdivm.ne' hdivp.ne).mdifferentiableAt (by norm_num)
  have hpt : (x, obataRadial K a f x) ∈
      {y : M | -a < f y ∧ f y < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K) := ⟨hx, hr⟩
  have hη₀ : MDiffAt η (x, obataRadial K a f x) :=
    ((hη _ hpt).contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds hpt)).mdifferentiableAt
      (by norm_num)
  have hi : (fun y => η (y, obataRadial K a f y)) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hinit y hy
  have hbase := radialVariationMetric_initial hη₀ hρ hi v w hv hw
  have he := radialVariationMetric_sine_squared_normalized_eq hK hf.continuous hη hm x hx v w ht hr
  rw [hbase] at he
  have hsin : 0 < Real.sin (Real.sqrt K * t) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos hk ht.1) (by nlinarith [(lt_div_iff₀ hk).mp ht.2])
  rw [div_eq_iff (pow_ne_zero 2 hsin.ne')] at he
  rw [he]
  ring

end LichnerowiczObata
