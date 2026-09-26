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

public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicNormalMetric
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialMetricNormalization
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Normal angular vectors are tangent to radial levels -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
section Scalar
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The scaled norm identity forces angular derivatives of a scalar radius
to vanish. Squaring avoids imposing differentiability of the norm at zero. -/
theorem fderiv_eq_zero_of_scaled_norm_identity {r : E → ℝ} {u w : E} {t : ℝ}
    (L : E →L[ℝ] V) (hr : DifferentiableAt ℝ r u) (hru : r u ≠ 0)
    (he : r =ᶠ[𝓝 u] (fun y => t * ‖L y‖)) (hw : inner ℝ (L u) (L w) = 0) :
    fderiv ℝ r u w = 0 := by
  have hs : (fun y => r y ^ 2) =ᶠ[𝓝 u] (fun y => t ^ 2 * ‖L y‖ ^ 2) := by
    filter_upwards [he] with y hy
    rw [hy, mul_pow]
  have hleft := hr.hasFDerivAt.pow 2
  have hright := ((L.hasFDerivAt (x := u)).norm_sq).const_mul (t ^ 2)
  have hd := congrArg (fun A : E →L[ℝ] ℝ => A w)
    (hleft.fderiv.symm.trans (hs.fderiv_eq.trans hright.fderiv))
  have heq : 2 * r u * fderiv ℝ r u w = 0 := by
    simpa [ContinuousLinearMap.comp_apply, hw] using hd
  exact (mul_eq_zero.mp heq).resolve_left (mul_ne_zero (by norm_num) hru)

end Scalar

section Manifold
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Angular vectors pushed forward by a radial normal parameterization are
in the kernel of the actual manifold derivative of the radius. -/
theorem mfderiv_normal_angular_eq_zero {ρ : M → ℝ} {ψ : E → M}
    {u w : E} {t : ℝ} (L : E →L[ℝ] V)
    (hψ : MDifferentiableAt 𝓘(ℝ, E) I ψ u)
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ (ψ u)) (hru : ρ (ψ u) ≠ 0)
    (he : (ρ ∘ ψ) =ᶠ[𝓝 u] (fun y => t * ‖L y‖))
    (hw : inner ℝ (L u) (L w) = 0) :
    mfderiv I 𝓘(ℝ, ℝ) ρ (ψ u) (mfderiv 𝓘(ℝ, E) I ψ u w) = 0 := by
  have hc : DifferentiableAt ℝ (ρ ∘ ψ) u :=
    mdifferentiableAt_iff_differentiableAt.mp (hρ.comp u hψ)
  have hz := fderiv_eq_zero_of_scaled_norm_identity L hc hru he hw
  have hd := mfderiv_comp_apply u hρ hψ w
  rw [mfderiv_eq_fderiv] at hd
  exact hd.symm.trans hz

end Manifold

section Transport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A pole-normalized angular pairing propagates to every regular radius.
Tangency is deduced from the normal radius identity, not assumed separately. -/
theorem normal_angular_metric_transport {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} {η : M × ℝ → M} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (hinit : ∀ x, -a < f x ∧ f x < a → η (x, obataRadial K a f x) = x)
    {ψ : P → M} {u w v : P} {t B : ℝ} (L : P →L[ℝ] V)
    (hψ : MDifferentiableAt 𝓘(ℝ, P) I ψ u)
    (hreg : -a < f (ψ u) ∧ f (ψ u) < a)
    (hrad : (obataRadial K a f ∘ ψ) =ᶠ[𝓝 u] (fun y => t * ‖L y‖))
    (hw : inner ℝ (L u) (L w) = 0) (hv : inner ℝ (L u) (L v) = 0)
    (hbase : inner ℝ (mfderiv 𝓘(ℝ, P) I ψ u w) (mfderiv 𝓘(ℝ, P) I ψ u v) =
      (Real.sin (Real.sqrt K * obataRadial K a f (ψ u)) ^ 2 / K) * B)
    {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    radialVariationMetric (I := I) η (ψ u)
      (mfderiv 𝓘(ℝ, P) I ψ u w) (mfderiv 𝓘(ℝ, P) I ψ u v) r =
        (Real.sin (Real.sqrt K * r) ^ 2 / K) * B := by
  have hlo : -1 < f (ψ u) / a := (lt_div_iff₀ ha).mpr (by nlinarith [hreg.1])
  have hhi : f (ψ u) / a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hreg.2)
  have hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) (obataRadial K a f) (ψ u) :=
    (contMDiffAt_obataRadial (K := K) (hf (ψ u)) hlo.ne' hhi.ne).mdifferentiableAt (by norm_num)
  have hpos : 0 < obataRadial K a f (ψ u) :=
    div_pos (Real.arccos_pos.mpr hhi) (Real.sqrt_pos.mpr hK)
  have htangw := mfderiv_normal_angular_eq_zero L hψ hρ hpos.ne' hrad hw
  have htangv := mfderiv_normal_angular_eq_zero L hψ hρ hpos.ne' hrad hv
  have he := radialVariationMetric_eq_sine_ratio hK ha hf hη hm hinit (ψ u) hreg
    (mfderiv 𝓘(ℝ, P) I ψ u w) (mfderiv 𝓘(ℝ, P) I ψ u v) htangw htangv hr
  have harg : Real.sqrt K * obataRadial K a f (ψ u) = Real.arccos (f (ψ u) / a) := by
    unfold obataRadial
    field_simp
  have hsin : Real.sin (Real.sqrt K * obataRadial K a f (ψ u)) ≠ 0 := by
    rw [harg]
    exact (Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hhi)
      (Real.arccos_lt_pi.mpr hlo)).ne'
  rw [he, hbase]
  field_simp [hsin, hK.ne']

/-- The propagated pairing is the metric of the actual composite map from
normal parameters to the chosen radial level. -/
theorem normal_angular_composite_metric {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} {η : M × ℝ → M} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I 1 η
      ({x | -a < f x ∧ f x < a} ×ˢ Ioo 0 (Real.pi / Real.sqrt K)))
    (hm : RadialChartMetricEvolution (I := I) K a f η)
    (hinit : ∀ x, -a < f x ∧ f x < a → η (x, obataRadial K a f x) = x)
    {ψ : P → M} {u w v : P} {t B : ℝ} (L : P →L[ℝ] V)
    (hψ : MDifferentiableAt 𝓘(ℝ, P) I ψ u)
    (hreg : -a < f (ψ u) ∧ f (ψ u) < a)
    (hrad : (obataRadial K a f ∘ ψ) =ᶠ[𝓝 u] (fun y => t * ‖L y‖))
    (hw : inner ℝ (L u) (L w) = 0) (hv : inner ℝ (L u) (L v) = 0)
    (hbase : inner ℝ (mfderiv 𝓘(ℝ, P) I ψ u w) (mfderiv 𝓘(ℝ, P) I ψ u v) =
      (Real.sin (Real.sqrt K * obataRadial K a f (ψ u)) ^ 2 / K) * B)
    {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    inner ℝ (mfderiv 𝓘(ℝ, P) I (fun y => η (ψ y, r)) u w)
      (mfderiv 𝓘(ℝ, P) I (fun y => η (ψ y, r)) u v) =
        (Real.sin (Real.sqrt K * r) ^ 2 / K) * B := by
  have hU : IsOpen {x : M | -a < f x ∧ f x < a} :=
    (isOpen_lt continuous_const hf.continuous).inter (isOpen_lt hf.continuous continuous_const)
  have hpt : (ψ u, r) ∈ {x : M | -a < f x ∧ f x < a} ×ˢ
      Ioo 0 (Real.pi / Real.sqrt K) := ⟨hreg, hr⟩
  have hηpt := ((hη _ hpt).contMDiffAt ((hU.prod isOpen_Ioo).mem_nhds hpt)).mdifferentiableAt
    (by norm_num)
  have hs : MDifferentiableAt I I (fun x => η (x, r)) (ψ u) :=
    hηpt.comp (ψ u) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have he := normal_angular_metric_transport hK ha hf hη hm hinit L hψ hreg hrad hw hv hbase hr
  have hwc := mfderiv_comp_apply u hs hψ w
  have hvc := mfderiv_comp_apply u hs hψ v
  change mfderiv 𝓘(ℝ, P) I (fun y => η (ψ y, r)) u w = _ at hwc
  change mfderiv 𝓘(ℝ, P) I (fun y => η (ψ y, r)) u v = _ at hvc
  rw [hwc, hvc]
  exact he

end Transport
end LichnerowiczObata
