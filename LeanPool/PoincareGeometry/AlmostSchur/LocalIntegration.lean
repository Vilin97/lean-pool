/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

/-!
# Local integration with a positive density

The divergence is the actual trace of the Fréchet derivative. The weighted
divergence is `ρ⁻¹ div(ρ X)`, with measure `ρ dx`. Compact support discharges
the integrability and boundary obligations in the local Green formula.
These are coordinate-domain results, not yet a manifold divergence theorem.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace AlmostSchur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  {μ : Measure V} [IsAddHaarMeasure μ]

/-- Divergence on a finite-dimensional inner product space. -/
def localDivergence (X : V → V) (x : V) : ℝ :=
  LinearMap.trace ℝ V (fderiv ℝ X x).toLinearMap

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem localDivergence_eq_sum (X : V → V) (x : V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    localDivergence X x = ∑ i, inner ℝ (b i) (fderiv ℝ X x (b i)) := by
  exact LinearMap.trace_eq_sum_inner _ b

omit [MeasurableSpace V] [BorelSpace V] in
/-- The derivative of the scalar coefficient contributes the rank-one trace. -/
theorem localDivergence_smul (f : V → ℝ) (X : V → V) (x : V)
    (hf : DifferentiableAt ℝ f x) (hX : DifferentiableAt ℝ X x) :
    localDivergence (fun y => f y • X y) x =
      f x * localDivergence X x + fderiv ℝ f x (X x) := by
  simp [localDivergence, fderiv_fun_smul hf hX, LinearMap.trace_smulRight]

/-- A positive density against Haar measure; positivity is required by the
theorems rather than encoded in a totalized division. -/
def localDensityMeasure (μ : Measure V) (ρ : V → ℝ) : Measure V :=
  μ.withDensity (fun x => ENNReal.ofReal (ρ x))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [IsAddHaarMeasure μ] in
theorem integral_localDensityMeasure (ρ : V → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (f : V → ℝ) :
    ∫ x, f x ∂localDensityMeasure μ ρ = ∫ x, ρ x * f x ∂μ := by
  rw [localDensityMeasure, integral_withDensity_eq_integral_toReal_smul
    hρ.measurable.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [IsAddHaarMeasure μ] in
theorem integrable_localDensityMeasure (ρ : V → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (f : V → ℝ) :
    Integrable f (localDensityMeasure μ ρ) ↔ Integrable (fun x => ρ x * f x) μ := by
  rw [localDensityMeasure, integrable_withDensity_iff_integrable_smul'
    hρ.measurable.ennreal_ofReal (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

/-- Divergence relative to a coordinate density, before identifying it with
the trace of a metric connection. -/
def localDensityDivergence (ρ : V → ℝ) (X : V → V) (x : V) : ℝ :=
  localDivergence (fun y => ρ y • X y) x / ρ x

omit [MeasurableSpace V] [BorelSpace V] in
theorem localDensityDivergence_eq (ρ : V → ℝ) (X : V → V) (x : V)
    (hρ : DifferentiableAt ℝ ρ x) (hX : DifferentiableAt ℝ X x) (hpos : 0 < ρ x) :
    localDensityDivergence ρ X x =
      localDivergence X x + fderiv ℝ ρ x (X x) / ρ x := by
  rw [localDensityDivergence, localDivergence_smul ρ X x hρ hX]
  field_simp [hpos.ne']

theorem integral_mul_localDivergence (f : V → ℝ) (X : V → V)
    (hf : ContDiff ℝ 1 f) (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    ∫ x, f x * localDivergence X x ∂μ = - ∫ x, fderiv ℝ f x (X x) ∂μ := by
  classical
  let b := stdOrthonormalBasis ℝ V
  have hcomp (i : Fin (Module.finrank ℝ V)) :
      ContDiff ℝ 1 (fun x => inner ℝ (b i) (X x)) :=
    (innerSL ℝ (b i)).contDiff.comp hX
  have hcompc (i : Fin (Module.finrank ℝ V)) :
      HasCompactSupport (fun x => inner ℝ (b i) (X x)) :=
    hc.comp_left (by simp)
  have hder (i : Fin (Module.finrank ℝ V)) (x : V) :
      fderiv ℝ (fun y => inner ℝ (b i) (X y)) x (b i) =
        inner ℝ (b i) (fderiv ℝ X x (b i)) := by
    exact congrArg (fun L : V →L[ℝ] ℝ => L (b i))
      (((innerSL ℝ (b i)).hasFDerivAt.comp x
        (hX.differentiable (by norm_num) x).hasFDerivAt).fderiv)
  have hi (i : Fin (Module.finrank ℝ V)) :
      ∫ x, f x * inner ℝ (b i) (fderiv ℝ X x (b i)) ∂μ =
        -∫ x, fderiv ℝ f x (b i) * inner ℝ (b i) (X x) ∂μ := by
    simp_rw [← hder]
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
        (hcomp i).continuous).integrable_of_hasCompactSupport (hcompc i).mul_left
    · exact (hf.continuous.mul ((hcomp i).continuous_fderiv (by norm_num) |>.clm_apply
        continuous_const)).integrable_of_hasCompactSupport
          ((hcompc i).fderiv_apply ℝ (b i)).mul_left
    · exact (hf.continuous.mul (hcomp i).continuous).integrable_of_hasCompactSupport
        (hcompc i).mul_left
    · exact fun x _ => hf.differentiable (by norm_num) x
    · exact fun x _ => (hcomp i).differentiable (by norm_num) x
  have hl (i : Fin (Module.finrank ℝ V)) :
      Integrable (fun x => f x * inner ℝ (b i) (fderiv ℝ X x (b i))) μ := by
    simp_rw [← hder]
    exact (hf.continuous.mul ((hcomp i).continuous_fderiv (by norm_num) |>.clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        ((hcompc i).fderiv_apply ℝ (b i)).mul_left
  have hr (i : Fin (Module.finrank ℝ V)) :
      Integrable (fun x => fderiv ℝ f x (b i) * inner ℝ (b i) (X x)) μ := by
    exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.mul
      (hcomp i).continuous).integrable_of_hasCompactSupport (hcompc i).mul_left
  simp_rw [localDivergence_eq_sum X _ b, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    conv_rhs => rw [← b.sum_repr (X x)]
    simp [_root_.map_sum, map_smul, OrthonormalBasis.repr_apply_apply, mul_comm]

/-- Green's formula for a positive C1 density. No integrability or boundary
identity is assumed: C1 regularity and compact support supply them. -/
theorem integral_mul_localDensityDivergence (ρ f : V → ℝ) (X : V → V)
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (hf : ContDiff ℝ 1 f) (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) :
    ∫ x, f x * localDensityDivergence ρ X x ∂localDensityMeasure μ ρ =
      -∫ x, fderiv ℝ f x (X x) ∂localDensityMeasure μ ρ := by
  rw [integral_localDensityMeasure ρ hρ.continuous (fun x => (hpos x).le),
    integral_localDensityMeasure ρ hρ.continuous (fun x => (hpos x).le)]
  have heq (x : V) : ρ x * (f x * localDensityDivergence ρ X x) =
      f x * localDivergence (fun y => ρ y • X y) x := by
    dsimp [localDensityDivergence]
    field_simp [(hpos x).ne']
  simp_rw [heq]
  simpa only [map_smul, smul_eq_mul] using!
    (integral_mul_localDivergence (μ := μ) f (fun y => ρ y • X y)
      hf (hρ.smul hX) hc.smul_left)

end AlmostSchur
