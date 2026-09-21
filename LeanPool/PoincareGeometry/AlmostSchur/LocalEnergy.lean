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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalIntegration
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Energy identity for local divergence-form operators

The coefficient `A` represents the inverse metric relative to the fixed
Euclidean inner product. The flux uses the actual derivative of the function.
Green's identity and formal symmetry are proved, not postulated. This does
not assert Poisson solvability or global manifold integration by parts.
-/

@[expose] public noncomputable section
open MeasureTheory MeasureTheory.Measure

namespace AlmostSchur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Raising the actual differential with a coordinate cometric. -/
def localCometricGradient (A : V → V →L[ℝ] V) (f : V → ℝ) (x : V) : V :=
  A x (_root_.gradient f x)

theorem contDiff_localCometricGradient (A : V → V →L[ℝ] V) (f : V → ℝ)
    (hA : ContDiff ℝ 1 A) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (localCometricGradient A f) := by
  have hg : ContDiff ℝ 1 (_root_.gradient f) :=
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  exact hA.clm_apply hg

theorem hasCompactSupport_localCometricGradient (A : V → V →L[ℝ] V) (f : V → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (localCometricGradient A f) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  exact hx (by simp [localCometricGradient, _root_.gradient, hz])

/-- The genuine second-order divergence-form operator `ρ⁻¹ div(ρ A grad f)`. -/
def localEllipticOperator (ρ : V → ℝ) (A : V → V →L[ℝ] V) (f : V → ℝ) : V → ℝ :=
  localDensityDivergence ρ (localCometricGradient A f)

/-- Differential energy pairing associated to the cometric. -/
def localEnergyPairing (A : V → V →L[ℝ] V) (f g : V → ℝ) (x : V) : ℝ :=
  inner ℝ (_root_.gradient f x) (localCometricGradient A g x)

theorem localEnergyPairing_eq_differential (A : V → V →L[ℝ] V)
    (f g : V → ℝ) (x : V) :
    localEnergyPairing A f g x = fderiv ℝ f x (localCometricGradient A g x) :=
  inner_gradient_left

theorem localEnergyPairing_comm (A : V → V →L[ℝ] V) (f g : V → ℝ) (x : V)
    (hsym : (A x).IsSymmetric) :
    localEnergyPairing A f g x = localEnergyPairing A g f x := by
  change inner ℝ (_root_.gradient f x) (A x (_root_.gradient g x)) =
    inner ℝ (_root_.gradient g x) (A x (_root_.gradient f x))
  exact (hsym (_root_.gradient f x) (_root_.gradient g x)).symm.trans (real_inner_comm _ _)

variable [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [IsAddHaarMeasure μ]

/-- The energy integrand is integrable, independently of any identity between
totalized Bochner integrals. -/
theorem integrable_localEnergyPairing (ρ : V → ℝ) (A : V → V →L[ℝ] V)
    (f g : V → ℝ) (hρ : Continuous ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hA : Continuous A) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) :
    Integrable (localEnergyPairing A f g) (localDensityMeasure μ ρ) := by
  rw [integrable_localDensityMeasure ρ hρ hpos]
  have hgf : Continuous (_root_.gradient f) :=
    (InnerProductSpace.toDual ℝ V).symm.continuous.comp (hf.continuous_fderiv (by norm_num))
  have hgg : Continuous (_root_.gradient g) :=
    (InnerProductSpace.toDual ℝ V).symm.continuous.comp (hg.continuous_fderiv (by norm_num))
  have hE : Continuous (localEnergyPairing A f g) := hgf.inner (hA.clm_apply hgg)
  have hEc : HasCompactSupport (localEnergyPairing A f g) := by
    apply (hasCompactSupport_localCometricGradient A g hc).mono
    intro x hx hn
    exact hx (by simp [localEnergyPairing, hn])
  exact (hρ.mul hE).integrable_of_hasCompactSupport hEc.mul_left

/-- The local Green identity specialized to a cometric gradient. -/
theorem integral_localEllipticOperator (ρ : V → ℝ) (A : V → V →L[ℝ] V)
    (f g : V → ℝ) (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (hA : ContDiff ℝ 1 A) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) :
    ∫ x, f x * localEllipticOperator ρ A g x ∂localDensityMeasure μ ρ =
      -∫ x, localEnergyPairing A f g x ∂localDensityMeasure μ ρ := by
  simp_rw [localEnergyPairing_eq_differential]
  exact integral_mul_localDensityDivergence ρ f _ hρ hpos hf
    (contDiff_localCometricGradient A g hA hg) (hasCompactSupport_localCometricGradient A g hc)

/-- Formal self-adjointness is a consequence of Green's formula and symmetry
of the cometric, not an assumed property of the differential operator. -/
theorem integral_localEllipticOperator_comm (ρ : V → ℝ) (A : V → V →L[ℝ] V)
    (f g : V → ℝ) (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (hA : ContDiff ℝ 1 A) (hsym : ∀ x, (A x).IsSymmetric)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∫ x, f x * localEllipticOperator ρ A g x ∂localDensityMeasure μ ρ =
      ∫ x, g x * localEllipticOperator ρ A f x ∂localDensityMeasure μ ρ := by
  rw [integral_localEllipticOperator ρ A f g hρ hpos hA (hf.of_le (by norm_num)) hg hgc,
    integral_localEllipticOperator ρ A g f hρ hpos hA (hg.of_le (by norm_num)) hf hfc]
  simp_rw [localEnergyPairing_comm A f g _ (hsym _)]

/-- The `div grad` sign convention gives a nonpositive quadratic form. -/
theorem integral_localEllipticOperator_self_nonpos (ρ : V → ℝ)
    (A : V → V →L[ℝ] V) (f : V → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x, 0 < ρ x) (hA : ContDiff ℝ 1 A)
    (hpositive : ∀ x v, 0 ≤ inner ℝ v (A x v))
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∫ x, f x * localEllipticOperator ρ A f x ∂localDensityMeasure μ ρ ≤ 0 := by
  rw [integral_localEllipticOperator ρ A f f hρ hpos hA (hf.of_le (by norm_num)) hf hc]
  exact neg_nonpos.2 (integral_nonneg (fun x => hpositive x (_root_.gradient f x)))

/-- Strictly positive cometric energy vanishes exactly when the actual
differential vanishes everywhere, not merely almost everywhere. -/
theorem integral_localEllipticOperator_self_eq_zero_iff (ρ : V → ℝ)
    (A : V → V →L[ℝ] V) (f : V → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hpos : ∀ x, 0 < ρ x) (hA : ContDiff ℝ 1 A)
    (hpositive : ∀ x v, v ≠ 0 → 0 < inner ℝ v (A x v))
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (∫ x, f x * localEllipticOperator ρ A f x ∂localDensityMeasure μ ρ) = 0 ↔
      ∀ x, fderiv ℝ f x = 0 := by
  rw [integral_localEllipticOperator ρ A f f hρ hpos hA (hf.of_le (by norm_num)) hf hc,
    neg_eq_zero, integral_localDensityMeasure ρ hρ.continuous (fun x => (hpos x).le)]
  have hgrad : Continuous (_root_.gradient f) :=
    (InnerProductSpace.toDual ℝ V).symm.continuous.comp (hf.continuous_fderiv (by norm_num))
  have hE : Continuous (fun x => ρ x * localEnergyPairing A f f x) :=
    hρ.continuous.mul (hgrad.inner (hA.continuous.clm_apply hgrad))
  have hint : Integrable (fun x => ρ x * localEnergyPairing A f f x) μ :=
    (integrable_localDensityMeasure ρ hρ.continuous (fun x => (hpos x).le) _).mp
      (integrable_localEnergyPairing ρ A f f hρ.continuous (fun x => (hpos x).le)
        hA.continuous (hf.of_le (by norm_num)) hf hc)
  have hn (x : V) : 0 ≤ ρ x * localEnergyPairing A f f x := by
    apply mul_nonneg (hpos x).le
    by_cases hv : _root_.gradient f x = 0
    · simp [localEnergyPairing, hv]
    · exact (hpositive x _ hv).le
  constructor
  · intro hzero
    have hae := (integral_eq_zero_iff_of_nonneg hn hint).mp hzero
    have heq := MeasureTheory.Measure.eq_of_ae_eq hae hE continuous_const
    intro x
    have hgzero : _root_.gradient f x = 0 := by
      by_contra hv
      have hp := mul_pos (hpos x) (hpositive x _ hv)
      have hz := congrFun heq x
      exact (ne_of_gt hp) hz
    have hdual := congrArg (InnerProductSpace.toDual ℝ V) hgzero
    simpa only [_root_.gradient, LinearIsometryEquiv.apply_symm_apply, map_zero] using hdual
  · intro hzero
    have heq (x : V) : localEnergyPairing A f f x = 0 := by
      simp [localEnergyPairing, _root_.gradient, hzero x]
    simp only [heq, mul_zero, integral_zero]

end AlmostSchur
