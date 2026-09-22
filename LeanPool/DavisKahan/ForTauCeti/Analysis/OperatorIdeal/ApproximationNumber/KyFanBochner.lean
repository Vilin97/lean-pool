/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Ky Fan gauges against Bochner integrals and unitary conjugation

Two facts about the finite Ky Fan gauges that an operator-valued integral needs.  They are
proved at different scalar scopes, deliberately: the unitary-invariance half below is generic
over `RCLike`, while the Bochner half is stated for complex operator spaces.

## Minkowski's integral inequality

```
(∫ f a ∂μ).kyFanGauge k ≤ ∫ (f a).kyFanGauge k ∂μ.
```

The gauge is a genuine seminorm — subadditivity is the Ky Fan triangle inequality, the one
nontrivial input — and it is continuous because `T.kyFanGauge k ≤ k * ‖T‖`.  Both statements
of this half, the continuity and the integral estimate, are over `ℂ`: the underlying seminorm
inequality `seminorm_integral_le` holds over any `RCLike` scalar field, but it needs the real
normed-space structure `[NormedSpace ℝ X]` and `[IsScalarTower ℝ 𝕜 X]` on the space being
integrated over, and those do not simply synthesize for an operator space over a generic
`RCLike` field.

Neither fact alone gives the integral inequality: Mathlib has
`norm_integral_le_integral_norm` for the *norm* of a Banach space and nothing for a seminorm
on it, so the private `seminorm_integral_le` below supplies the general statement by
Hahn--Banach.  Pick a functional that is dominated by the seminorm and attains it at the
value of the integral; that functional commutes with the Bochner integral, and the ordinary
norm inequality for scalars finishes the estimate.

## Unitary invariance

```
(L ∘L T ∘L R).kyFanGauge k = T.kyFanGauge k    for unitary `L` and `R`.
```

The `≤` half is the two-sided ideal inequality `kyFanGauge_comp_le` with both norms at most
one; the `≥` half is the same inequality applied to `T = L⋆ (L T R) R⋆`, whose factors are
unitary as well.  Nothing in this half is field-specific, so it is stated over an arbitrary
`RCLike` scalar field.  This is what makes a Ky Fan gauge blind to the unitary orbit of an
operator, which is how an oscillatory integral of unitary conjugates is estimated by the
gauge of the operator being conjugated.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Experimental/MathAhead/HiddenFoundations/KyFanBochner.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.MathAhead.HiddenFoundations.{`
  `kyFanApproximationSeminorm, kyFanApproximationSeminorm_apply,`
  `continuous_kyFanApproximationGauge, kyFanApproximationGauge_integral_le,`
  `kyFanApproximationGauge_unitary_left_right}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **restated and reproved**.  The source was an uncompiled proof sketch:
  it named a `Seminorm.integral_le` that does not exist in Mathlib, dropped its unitary
  invariance onto an unstated `norm_eq_one_of_isometry_and_surjective`, and was fixed to
  `ℂ`.  The statements move to `ContinuousLinearMap.kyFanGauge`, the unitary-invariance
  scalars to an arbitrary `RCLike` field, and the two missing inputs are proved here.  The
  Bochner statements remain over `ℂ`, for the instance reason recorded above.
* Extraction motive: the arbitrary-Hilbert-space `π/2` Sylvester estimate in every finite
  Ky Fan gauge (`DavisKahan/InfiniteDimensional/Sylvester/GeneralSeparationKyFan.lean`)
  is an integral of unitary conjugates, so it needs exactly these two facts and nothing
  else that is paper-specific.
* Spectra influence: none.
-/

public section

open MeasureTheory

namespace ContinuousLinearMap

noncomputable section

universe u v w

/-- **Minkowski's integral inequality for a seminorm dominated by the norm.**

Mathlib's `norm_integral_le_integral_norm` is the special case `p = ‖·‖`; there is no
statement for a seminorm, and the Ky Fan gauges are seminorms that are not the norm.

The proof is Hahn--Banach.  For `v = ∫ f` pick a linear functional `g` on the line through
`v` with `g v = p v` and `‖g x‖ = p x` there; `Module.Dual.exists_extension_of_le_seminorm`
extends it to the whole space still dominated by `p`, the domination makes it continuous,
and a continuous linear functional commutes with the Bochner integral.  Then
`p v = ‖g v‖ = ‖∫ g (f a)‖ ≤ ∫ ‖g (f a)‖ ≤ ∫ p (f a)`. -/
private theorem seminorm_integral_le {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] 
    [CompleteSpace X]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p : Seminorm 𝕜 X) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, p x ≤ C * ‖x‖)
    {f : α → X} (hf : Integrable f μ) :
    p (∫ a, f a ∂μ) ≤ ∫ a, p (f a) ∂μ := by
  have hcont : Continuous p := by
    refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun x y => ?_).continuous
    have hle : |p x - p y| ≤ C * ‖x - y‖ :=
      (abs_sub_map_le_sub p x y).trans (hC (x - y))
    rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal C hC0]
  have hmeas : AEStronglyMeasurable (fun a => p (f a)) μ :=
    hcont.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hpi : Integrable (fun a => p (f a)) μ := by
    refine Integrable.mono' (hf.norm.const_mul C) hmeas ?_
    filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg p (f a))]
    exact hC (f a)
  rcases eq_or_lt_of_le (apply_nonneg p (∫ a, f a ∂μ)) with hzero | hpos
  · rw [← hzero]
    exact integral_nonneg fun a => apply_nonneg p (f a)
  set v : X := ∫ a, f a ∂μ with hv_def
  have hvne : v ≠ 0 := fun h => by simp [h] at hpos
  -- a functional on the line through `v` that is exactly `p` there
  set e := LinearEquiv.toSpanNonzeroSingleton 𝕜 X v hvne with he_def
  set g₀ : Module.Dual 𝕜 (𝕜 ∙ v) := (p v : 𝕜) • e.symm.toLinearMap with hg₀_def
  have hcoe : ∀ x : (𝕜 ∙ v), (e.symm x : 𝕜) • v = (x : X) := fun x =>
    LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul 𝕜 X v hvne x
  have hg₀ : ∀ x : (𝕜 ∙ v), ‖g₀ x‖ ≤ p (x : X) := by
    intro x
    have hx : p (x : X) = ‖(e.symm x : 𝕜)‖ * p v := by
      rw [← hcoe x, map_smul_eq_mul]
    rw [hx, hg₀_def]
    simp only [LinearMap.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg hpos.le, LinearEquiv.coe_coe]
    rw [mul_comm]
  obtain ⟨g, hgext, hgle⟩ :=
    Module.Dual.exists_extension_of_le_seminorm (Submodule.span 𝕜 {v}) g₀ hg₀
  have hφbound : ∀ x, ‖g x‖ ≤ C * ‖x‖ := fun x => (hgle x).trans (hC x)
  set φ : X →L[𝕜] 𝕜 := g.mkContinuous C hφbound with hφ_def
  have hφle : ∀ x, ‖φ x‖ ≤ p x := hgle
  have hφv : φ v = (p v : 𝕜) := by
    have hmem : v ∈ Submodule.span 𝕜 ({v} : Set X) := Submodule.mem_span_singleton_self v
    have hone : e.symm ⟨v, hmem⟩ = (1 : 𝕜) := by
      have hsm : (e.symm ⟨v, hmem⟩ : 𝕜) • v = v := hcoe ⟨v, hmem⟩
      have hsub : ((e.symm ⟨v, hmem⟩ : 𝕜) - 1) • v = 0 := by
        rw [sub_smul, one_smul, hsm, sub_self]
      rcases smul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hvne
    have h := hgext ⟨v, hmem⟩
    simp only [hg₀_def, LinearMap.smul_apply, LinearEquiv.coe_coe, hone, smul_eq_mul,
      mul_one] at h
    simpa [hφ_def] using h
  calc
    p v = ‖(p v : 𝕜)‖ := by rw [RCLike.norm_ofReal, abs_of_nonneg hpos.le]
    _ = ‖φ v‖ := by rw [hφv]
    _ = ‖∫ a, φ (f a) ∂μ‖ := by
      rw [hv_def, ← ContinuousLinearMap.integral_comp_comm φ hf]
    _ ≤ ∫ a, ‖φ (f a)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a, p (f a) ∂μ := integral_mono (φ.integrable_comp hf).norm hpi fun a => hφle (f a)

variable {𝕜 : Type u} [RCLike 𝕜]

section Unitary

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A unitary operator is a contraction.  On the zero space it is also the zero operator, so
the norm is `≤ 1` rather than `= 1`; that is all a two-sided ideal estimate needs, and it
avoids a `Nontrivial` hypothesis. -/
theorem norm_le_one_of_mem_unitary {L : E →L[𝕜] E}
    (hL : L ∈ unitary (E →L[𝕜] E)) : ‖L‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact le_of_eq (norm_map_of_mem_unitary hL x)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Sandwiching between two contractions cannot increase a Ky Fan gauge. -/
theorem kyFanGauge_comp_comp_le_of_norm_le_one {L : F →L[𝕜] F} {R : E →L[𝕜] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (T : E →L[𝕜] F) (k : ℕ) :
    (L ∘L T ∘L R).kyFanGauge k ≤ T.kyFanGauge k := by
  refine (kyFanGauge_comp_le L T R k).trans ?_
  have hg : 0 ≤ T.kyFanGauge k := T.kyFanGauge_nonneg k
  calc ‖L‖ * T.kyFanGauge k * ‖R‖
      ≤ 1 * T.kyFanGauge k * ‖R‖ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hg) (norm_nonneg R)
    _ = T.kyFanGauge k * ‖R‖ := by rw [one_mul]
    _ ≤ T.kyFanGauge k * 1 := mul_le_mul_of_nonneg_left hR hg
    _ = T.kyFanGauge k := mul_one _

/-- **Every finite Ky Fan gauge is invariant under multiplication by a unitary on either
side.**  The `≥` half is the `≤` half applied to `T = L⋆ (L T R) R⋆`. -/
theorem kyFanGauge_unitary_comp_comp {L : F →L[𝕜] F} {R : E →L[𝕜] E}
    (hL : L ∈ unitary (F →L[𝕜] F)) (hR : R ∈ unitary (E →L[𝕜] E))
    (T : E →L[𝕜] F) (k : ℕ) :
    (L ∘L T ∘L R).kyFanGauge k = T.kyFanGauge k := by
  refine le_antisymm (kyFanGauge_comp_comp_le_of_norm_le_one (norm_le_one_of_mem_unitary hL)
    (norm_le_one_of_mem_unitary hR) T k) ?_
  have hrecover : (star L ∘L (L ∘L T ∘L R) ∘L star R) = T := by
    have hx : ∀ x : E, R (star R x) = x := fun x => by
      have h := DFunLike.congr_fun (Unitary.mul_star_self_of_mem hR) x
      simpa using h
    have hy : ∀ y : F, star L (L y) = y := fun y => by
      have h := DFunLike.congr_fun (Unitary.star_mul_self_of_mem hL) y
      simpa using h
    ext x
    simp only [comp_apply]
    rw [hx, hy]
  calc
    T.kyFanGauge k = (star L ∘L (L ∘L T ∘L R) ∘L star R).kyFanGauge k := by rw [hrecover]
    _ ≤ (L ∘L T ∘L R).kyFanGauge k :=
      kyFanGauge_comp_comp_le_of_norm_le_one
        (norm_le_one_of_mem_unitary (Unitary.star_mem hL))
        (norm_le_one_of_mem_unitary (Unitary.star_mem hR)) _ k

end Unitary

section Bochner

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The `k`th Ky Fan gauge packaged as a seminorm on the operator space.

Subadditivity is the Ky Fan triangle inequality, which is the whole content; the other three
fields are immediate.  Kept `private`: a public `Seminorm`-valued definition is useless
without an `_apply` lemma, and that lemma has to unfold the definition, which under this
repository's Tau Ceti rubric would mean an `@[expose]` that buys nothing — every consumer
wants the two theorems below, not the bundled object. -/
private def kyFanGaugeSeminorm (k : ℕ) : Seminorm ℂ (E →L[ℂ] F) where
  toFun T := T.kyFanGauge k
  map_zero' := kyFanGauge_zero k
  add_le' S T := kyFanGauge_add_le_complex S T k
  neg' T := T.kyFanGauge_neg k
  smul' c T := kyFanGauge_smul c T k

private theorem kyFanGaugeSeminorm_apply (k : ℕ) (T : E →L[ℂ] F) :
    kyFanGaugeSeminorm (E := E) (F := F) k T = T.kyFanGauge k := rfl

/-- **A finite Ky Fan gauge is operator-norm continuous.**  It is a seminorm bounded by
`k‖·‖`, hence Lipschitz. -/
theorem continuous_kyFanGauge (k : ℕ) :
    Continuous fun T : E →L[ℂ] F => T.kyFanGauge k := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (k : ℝ)) fun S T => ?_).continuous
  have h := abs_sub_map_le_sub (kyFanGaugeSeminorm (E := E) (F := F) k) S T
  rw [kyFanGaugeSeminorm_apply, kyFanGaugeSeminorm_apply, kyFanGaugeSeminorm_apply] at h
  have hle : |S.kyFanGauge k - T.kyFanGauge k| ≤ (k : ℝ) * ‖S - T‖ :=
    h.trans (kyFanGauge_le_nat_mul_opNorm (S - T) k)
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (Nat.cast_nonneg k)]

/-- **Minkowski's integral inequality for a finite Ky Fan gauge**: the gauge of a Bochner
integral of operators is at most the integral of the gauges. -/
theorem kyFanGauge_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (k : ℕ) {f : α → E →L[ℂ] F} (hf : Integrable f μ) :
    (∫ a, f a ∂μ).kyFanGauge k ≤ ∫ a, (f a).kyFanGauge k ∂μ := by
  have h := seminorm_integral_le (kyFanGaugeSeminorm (E := E) (F := F) k)
    (Nat.cast_nonneg k) (fun T => kyFanGauge_le_nat_mul_opNorm T k) hf
  rw [kyFanGaugeSeminorm_apply] at h
  simpa only [kyFanGaugeSeminorm_apply] using h

end Bochner

end

end ContinuousLinearMap
