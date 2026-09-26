/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceCk
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The autonomous fundamental solution is the operator exponential

For a **time-independent** (autonomous) linear generator `A₀ : E →L[ℝ] E`, the campaign's resolvent
`fundamentalSolution` (built abstractly from any flow family `Φ` of the linear variational field via
Picard–Lindelöf / Grönwall uniqueness) coincides with Mathlib's analytic operator exponential:

`fundamentalSolution hA hΦ h0 t = NormedSpace.exp ((t - t₀) • A₀)`.

This is the bridge from the `IsIntegralCurve`-based resolvent used throughout the smooth-dependence
layer to the analytic `NormedSpace.exp`.  It matters because `NormedSpace.exp` is analytic in its
argument, so this identity transports the exponential's analytic dependence on the operator to the
autonomous resolvent — precisely the smooth-dependence structure needed for the **frozen** (autonomous,
bounded-linear) geometric Ricci–DeTurck chart generator, whose fibre generator depends on the spatial
point.  Everything is proved from Mathlib's `hasDerivAt_exp_smul_const'` and the campaign's global
integral-curve uniqueness `eq_of_isIntegralCurve_of_eq_at`; no PDE or manifold content is used.
-/

@[expose] public section

@[expose] public noncomputable section

open Set
open scoped Topology NNReal Nat

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The operator-exponential curve solves the autonomous linear ODE.**  For a fixed generator
`A₀ : E →L[ℝ] E` and initial point `x`, the path `t ↦ exp ((t - t₀) • A₀) x` is a global integral
curve of the (time-independent) vector variational field `variationalFieldVec (fun _ => A₀)`, i.e. it
obeys `γ'(t) = A₀ (γ t)` everywhere.  Proved from Mathlib's `hasDerivAt_exp_smul_const'`
(`d/du exp (u • A₀) = A₀ * exp (u • A₀)`) precomposed with the shift `t ↦ t - t₀` and evaluated at the
fixed direction `x` via `HasDerivAt.clm_apply`. -/
theorem isIntegralCurve_exp_smul_const (A₀ : E →L[ℝ] E) (t₀ : ℝ) (x : E) :
    IsIntegralCurve (fun t => NormedSpace.exp ((t - t₀) • A₀) x)
      (variationalFieldVec (fun _ => A₀)) := by
  intro t
  have hbase : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A₀))
      (A₀ * NormedSpace.exp ((t - t₀) • A₀)) (t - t₀) :=
    hasDerivAt_exp_smul_const' A₀ (t - t₀)
  have hshift : HasDerivAt (fun t : ℝ => t - t₀) (1 : ℝ) t :=
    (hasDerivAt_id t).sub_const t₀
  have hcomp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀))
      (A₀ * NormedSpace.exp ((t - t₀) • A₀)) t := by
    have hfun :
        (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀)) =
          (fun u : ℝ => NormedSpace.exp (u • A₀)) ∘ (fun t : ℝ => t - t₀) := by
      funext s
      rfl
    rw [hfun]
    simpa only [one_smul] using HasDerivAt.scomp t hbase hshift
  have hpt : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀) x)
      ((A₀ * NormedSpace.exp ((t - t₀) • A₀)) x) t := by
    have := HasDerivAt.clm_apply hcomp (hasDerivAt_const t x)
    simpa using this
  simpa [variationalFieldVec, ContinuousLinearMap.mul_apply] using hpt

/-! ### The affine autonomous ODE `y' = L y + b`

The frozen (autonomous) Ricci–DeTurck chart operator is **affine** in the section state,
`A τ s = L s + b`, so its Banach evolution solves the *affine* linear ODE `y' = L y + b`, **not** the
homogeneous one solved by `exp ((t - t₀) • L)`.  We solve the affine ODE explicitly and globally by the
classical augmentation trick: adjoin a scalar coordinate that carries the constant `b`.  On `E × ℝ` the
**augmented generator** `(v, s) ↦ (L v + s • b, 0)` is a genuine bounded linear operator whose scalar
coordinate is conserved (`≡ 1`), and the first coordinate of its operator-exponential orbit through
`(y₀, 1)` is the affine solution.  Everything reduces to `isIntegralCurve_exp_smul_const` on `E × ℝ`;
no PDE, integral, or manifold content is used. -/

/-- **The augmented generator** on `E × ℝ` turning the affine ODE `y' = L y + b` into a homogeneous
linear one: `(v, s) ↦ (L v + s • b, 0)`.  The scalar coordinate `s` carries the inhomogeneity `b` and
is conserved by the flow (its own derivative is `0`), so starting it at `1` reproduces the `+ b`. -/
noncomputable def affineAugment (L : E →L[ℝ] E) (b : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (L.comp (ContinuousLinearMap.fst ℝ E ℝ)
      + (ContinuousLinearMap.snd ℝ E ℝ).smulRight b).prod (0 : (E × ℝ) →L[ℝ] ℝ)

omit [CompleteSpace E] in
@[simp] theorem affineAugment_apply (L : E →L[ℝ] E) (b : E) (p : E × ℝ) :
    affineAugment L b p = (L p.1 + p.2 • b, 0) := by
  simp [affineAugment]

/-- **The affine autonomous fundamental solution** `y(t)`: the first coordinate of the augmented
operator-exponential orbit through `(y₀, 1)`.  It is the global solution of `y' = L y + b`,
`y t₀ = y₀`. -/
noncomputable def affineFundamentalSolution
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) : E :=
  (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1)).1

/-- **The scalar coordinate is conserved.**  The second coordinate of the augmented orbit through
`(y₀, 1)` is identically `1`: it solves `s' = 0` with `s t₀ = 1`, so global constancy
(`is_const_of_deriv_eq_zero`) pins it to `1`.  This is exactly what turns the augmented flow's first
coordinate into the genuine `+ b` inhomogeneity. -/
theorem affineAugment_snd_orbit_eq_one (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1)).2 = 1 := by
  have hsnd : ∀ s : ℝ,
      @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ
        Real.normedAddCommGroup.toAddCommGroup
        RCLike.toInnerProductSpaceReal.toModule
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (inferInstance : ContinuousSMul ℝ ℝ)
        (fun s => (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)).2) 0 s := by
    intro s
    have hc :
        HasDerivAt (fun s => NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1))
          (affineAugment L b (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1))) s := by
      simpa [variationalFieldVec] using
        isIntegralCurve_exp_smul_const (affineAugment L b) t₀ (y₀, 1) s
    have hproj := (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt s hc
    have hfun :
        (fun s : ℝ =>
          (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)).2) =
          Prod.snd ∘ (fun s : ℝ =>
            NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)) := by
      funext u
      rfl
    rw [hfun]
    exact hproj
  have hconst :=
    is_const_of_deriv_eq_zero
      (f := fun s => (NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)).2)
      (fun s => (hsnd s).differentiableAt) (fun s => (hsnd s).deriv) t t₀
  have h0 : (NormedSpace.exp ((t₀ - t₀) • affineAugment L b) (y₀, 1)).2 = 1 := by
    simp [sub_self, zero_smul, NormedSpace.exp_zero]
  exact hconst.trans h0

omit [CompleteSpace E] in
/-- **`y t₀ = y₀`.**  The affine fundamental solution starts at the initial value. -/
theorem affineFundamentalSolution_initial (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) :
    affineFundamentalSolution L b t₀ y₀ t₀ = y₀ := by
  simp [affineFundamentalSolution, sub_self, zero_smul, NormedSpace.exp_zero,
    ContinuousLinearMap.one_apply]

/-- **The affine fundamental solution solves the affine ODE `y' = L y + b`.**  For every time `t`,
`HasDerivAt (affineFundamentalSolution L b t₀ y₀) (L (affineFundamentalSolution L b t₀ y₀ t) + b) t`.
The augmented orbit is a global integral curve of the autonomous, bounded-linear augmented generator by
`isIntegralCurve_exp_smul_const`; projecting to the first coordinate and using that the scalar
coordinate stays `1` (`affineAugment_snd_orbit_eq_one`) yields the affine field `L y + b`.  This is the
Banach evolution of the frozen (affine) Ricci–DeTurck chart operator `A τ s = L s + b`. -/
theorem hasDerivAt_affineFundamentalSolution
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    HasDerivAt (affineFundamentalSolution L b t₀ y₀)
      (L (affineFundamentalSolution L b t₀ y₀ t) + b) t := by
  have hc :
      HasDerivAt (fun s => NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1))
        (affineAugment L b (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1))) t := by
    simpa [variationalFieldVec] using
      isIntegralCurve_exp_smul_const (affineAugment L b) t₀ (y₀, 1) t
  have hproj := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t hc
  have hfst :
      HasDerivAt (affineFundamentalSolution L b t₀ y₀)
        ((affineAugment L b (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1))).1) t := by
    have hfun :
        affineFundamentalSolution L b t₀ y₀ =
          Prod.fst ∘ (fun s : ℝ =>
            NormedSpace.exp ((s - t₀) • affineAugment L b) (y₀, 1)) := by
      funext s
      rfl
    rw [hfun]
    exact hproj
  have hval :
      (affineAugment L b (NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1))).1
        = L (affineFundamentalSolution L b t₀ y₀ t) + b := by
    rw [affineAugment_apply]
    simp only [affineFundamentalSolution]
    rw [affineAugment_snd_orbit_eq_one, one_smul]
  rw [hval] at hfst
  exact hfst

omit [CompleteSpace E] in
/-- **Uniqueness for the affine autonomous ODE `y' = L y + b`.**  Two global solutions that agree at
one time agree everywhere.  Their difference solves the *homogeneous* linear equation `d' = L d` with
`d t₀ = 0`, so homogeneous integral-curve uniqueness (`variationalVec_eq_of_isIntegralCurve`, with the
zero curve) forces it to vanish identically. -/
theorem affineODE_unique (L : E →L[ℝ] E) (b : E) {y₁ y₂ : ℝ → E}
    (h1 : ∀ t, HasDerivAt y₁ (L (y₁ t) + b) t)
    (h2 : ∀ t, HasDerivAt y₂ (L (y₂ t) + b) t)
    {t₀ : ℝ} (h : y₁ t₀ = y₂ t₀) (t : ℝ) : y₁ t = y₂ t := by
  have hu1 : IsIntegralCurve (fun t => y₁ t - y₂ t) (variationalFieldVec (fun _ => L)) := by
    intro t
    have hd := (h1 t).sub (h2 t)
    have heq : (L (y₁ t) + b) - (L (y₂ t) + b) = L (y₁ t - y₂ t) := by
      rw [map_sub]; abel
    have hfun : (fun t : ℝ => y₁ t - y₂ t) = y₁ - y₂ := by
      funext s
      rfl
    rw [hfun]
    simpa [variationalFieldVec, heq] using hd
  have hu2 : IsIntegralCurve (fun _ : ℝ => (0 : E)) (variationalFieldVec (fun _ => L)) := by
    intro t
    simpa [variationalFieldVec] using hasDerivAt_const t (0 : E)
  have hzero : (fun t => y₁ t - y₂ t) t₀ = (fun _ : ℝ => (0 : E)) t₀ := by
    simp [h]
  have hdiff := variationalVec_eq_of_isIntegralCurve
    (A := fun _ => L) (K := ‖L‖₊) (fun _ => le_rfl) hu1 hu2 hzero t
  simpa [sub_eq_zero] using hdiff

/-- **The affine fundamental solution is the unique solution.**  Any global solution `y` of
`y' = L y + b` with `y t₀ = y₀` coincides with `affineFundamentalSolution L b t₀ y₀`.  This is the
uniqueness half of the affine Cauchy problem for the frozen chart operator, the ingredient that a
chart-closure `encode` field consumes. -/
theorem eq_affineFundamentalSolution_of_hasDerivAt
    (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) {y : ℝ → E}
    (hy : ∀ t, HasDerivAt y (L (y t) + b) t) (h0 : y t₀ = y₀) (t : ℝ) :
    y t = affineFundamentalSolution L b t₀ y₀ t := by
  refine affineODE_unique L b hy
    (fun s => hasDerivAt_affineFundamentalSolution L b t₀ y₀ s) (t₀ := t₀) ?_ t
  rw [h0, affineFundamentalSolution_initial]

variable {Φ : E → ℝ → E} {t₀ : ℝ}

/-- **The autonomous fundamental solution is the operator exponential.**  For a *time-independent*
generator `A₀ : E →L[ℝ] E` the campaign resolvent (built from any flow family `Φ` of the linear
variational field anchored at `t₀`) equals `NormedSpace.exp ((t - t₀) • A₀)`.

Both sides are integral curves (at each fixed direction `x`) of the same globally
`‖A₀‖`-Lipschitz autonomous field `variationalFieldVec (fun _ => A₀)`, and both send `t₀ ↦ x`
(`Φ x t₀ = x` and `exp (0 • A₀) x = x`); global integral-curve uniqueness
(`eq_of_isIntegralCurve_of_eq_at`) forces them to agree at every time and every direction. -/
theorem fundamentalSolution_const_eq_exp {A₀ : E →L[ℝ] E} {K : ℝ≥0}
    (hA : ∀ t, ‖(fun _ : ℝ => A₀) t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec (fun _ => A₀)))
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    fundamentalSolution hA hΦ h0 t = NormedSpace.exp ((t - t₀) • A₀) := by
  ext x
  rw [fundamentalSolution_apply]
  refine eq_of_isIntegralCurve_of_eq_at (K := K) (t₁ := t₀)
    (fun s => lipschitzWith_variationalFieldVec hA s) (hΦ x)
    (isIntegralCurve_exp_smul_const A₀ t₀ x) ?_ t
  rw [h0]
  simp [NormedSpace.exp_zero]

/-- **The operator-exponential map is smooth.**  For a fixed scalar `s`, the map
`A₀ ↦ exp (s • A₀)` on `E →L[ℝ] E` is `ContDiff ℝ n` for every `n`.  Immediate from the analyticity of
`NormedSpace.exp` on the (complete) operator Banach algebra (`NormedSpace.exp_analytic`, whose power
series has infinite radius) composed with the smooth scalar rescaling `A₀ ↦ s • A₀`. -/
theorem contDiff_exp_smul_const (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun A₀ : E →L[ℝ] E => NormedSpace.exp (s • A₀)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact ContDiff.comp hana.contDiff (contDiff_const_smul s)

/-- **Smooth dependence of the autonomous resolvent on a parameter.**  If a family of autonomous
generators `A : X → (E →L[ℝ] E)` over a normed parameter space `X` is `C^n`, then the autonomous
resolvent `x ↦ exp (s • A x)` is `C^n`.  This transports smooth dependence of the generator to smooth
dependence of the resolvent — the parameter-smoothness form that, via `fundamentalSolution_const_eq_exp`,
turns spatial (`x`-dependent) smoothness of a frozen bounded-linear generator into spatial smoothness of
its Banach evolution, with no `IsIntegralCurve` bookkeeping. -/
theorem contDiff_exp_smul_of_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → (E →L[ℝ] E)} {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) (s : ℝ) :
    ContDiff ℝ n (fun x => NormedSpace.exp (s • A x)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact ContDiff.comp hana.contDiff (ContDiff.const_smul s hA)

/-- **Joint `(time, parameter)` smoothness of the parametrized autonomous resolvent.**  If a family of
autonomous generators `A : X → (E →L[ℝ] E)` over a normed parameter space `X` is `C^n`, then the
time-dependent resolvent `(t, x) ↦ exp ((t - t₀) • A x)` is jointly `C^n` on `ℝ × X`.  This is the exact
joint-smoothness shape a downstream realization consumes: for the frozen (autonomous, bounded-linear)
Ricci–DeTurck chart generator whose fibre generator `A x` depends `C^n`-smoothly on the spatial point `x`,
`fundamentalSolution_const_eq_exp` identifies its Banach evolution with `exp ((t - t₀) • A x)`, so this
lemma yields joint smoothness of that evolution in `(time, space)` — the parabolic-free regularity of a
0th-order generator's flow.  Assembled from the smoothness of `NormedSpace.exp`, the bilinear scalar
action, and the coordinate projections. -/
theorem contDiff_exp_sub_smul_of_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → (E →L[ℝ] E)} {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) (t₀ : ℝ) :
    ContDiff ℝ n (fun p : ℝ × X => NormedSpace.exp ((p.1 - t₀) • A p.2)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  have h1 : ContDiff ℝ n (fun p : ℝ × X => p.1 - t₀) :=
    ContDiff.sub contDiff_fst contDiff_const
  have h2 : ContDiff ℝ n (fun p : ℝ × X => A p.2) := ContDiff.comp hA contDiff_snd
  exact ContDiff.comp hana.contDiff (ContDiff.smul h1 h2)

/-- **The operator/algebra exponential is dominated by the scalar exponential of the norm.**
`‖exp x‖ ≤ Real.exp ‖x‖` for every element `x` of a complete normed algebra over `ℝ` whose unit has
norm one.  This is the elementary series comparison `‖∑ₙ xⁿ/n!‖ ≤ ∑ₙ ‖x‖ⁿ/n! = exp ‖x‖`, using
`‖xⁿ‖ ≤ ‖x‖ⁿ` termwise.  It is the missing Mathlib fact (only summability of the exponential series is
available there) underlying every resolvent growth estimate `‖exp(τ·L)‖ ≤ exp(‖L‖·|τ|)`. -/
theorem norm_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (x : 𝔸) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hsum : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • x ^ n) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hsumR : HasSum (fun n : ℕ => (n !⁻¹ : ℝ) • ‖x‖ ^ n) (NormedSpace.exp ‖x‖) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have hnormsummable : Summable (fun n : ℕ => ‖(n !⁻¹ : ℝ) • x ^ n‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have hRsummable : Summable (fun n : ℕ => (n !⁻¹ : ℝ) • ‖x‖ ^ n) := hsumR.summable
  calc
    ‖NormedSpace.exp x‖ = ‖∑' n : ℕ, (n !⁻¹ : ℝ) • x ^ n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖(n !⁻¹ : ℝ) • x ^ n‖ := norm_tsum_le_tsum_norm hnormsummable
    _ ≤ ∑' n : ℕ, (n !⁻¹ : ℝ) • ‖x‖ ^ n := by
        refine hnormsummable.tsum_le_tsum (fun n => ?_) hRsummable
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)
    _ = NormedSpace.exp ‖x‖ := hsumR.tsum_eq
    _ = Real.exp ‖x‖ := by rw [Real.exp_eq_exp_ℝ]

/-- **Resolvent growth bound.**  `‖exp (τ • x)‖ ≤ Real.exp (|τ| * ‖x‖)` for a scalar `τ : ℝ` and an
element `x` of a complete unit-norm-one normed `ℝ`-algebra.  Specialised to a bounded operator
`x = L : E →L[ℝ] E` this is the semigroup growth bound `‖exp(τ·L)‖ ≤ exp(|τ|·‖L‖)`. -/
theorem norm_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (τ : ℝ) (x : 𝔸) :
    ‖NormedSpace.exp (τ • x)‖ ≤ Real.exp (|τ| * ‖x‖) := by
  have h := norm_exp_le (τ • x)
  rwa [norm_smul, Real.norm_eq_abs] at h

/-- **Operator-norm bound for the augmented generator.**  `‖affineAugment L b‖ ≤ ‖L‖ + ‖b‖`.
The augmentation `(v, s) ↦ (L v + s • b, 0)` never amplifies more than the linear part plus the
source: at every `p = (v, s)`, `‖L v + s • b‖ ≤ ‖L‖‖v‖ + |s|‖b‖ ≤ (‖L‖ + ‖b‖)‖p‖` since both
coordinate norms are `≤ ‖p‖`.  This is the operator-norm growth constant of the affine chart split
that the resolvent bound consumes. -/
theorem norm_affineAugment_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (b : E) :
    ‖affineAugment L b‖ ≤ ‖L‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun p => ?_)
  rw [affineAugment_apply, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  have hp1 : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hp2 : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  calc ‖L p.1 + p.2 • b‖
      ≤ ‖L p.1‖ + ‖p.2 • b‖ := norm_add_le _ _
    _ ≤ ‖L‖ * ‖p‖ + ‖b‖ * ‖p‖ := by
        gcongr
        · exact (L.le_opNorm p.1).trans (by gcongr)
        · rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs, mul_comm]
          gcongr
    _ = (‖L‖ + ‖b‖) * ‖p‖ := by ring

/-- **Exponential growth bound for the frozen (affine) Ricci–DeTurck chart evolution.**
`‖affineFundamentalSolution L b t₀ y₀ t‖ ≤ Real.exp (|t - t₀| · (‖L‖ + ‖b‖)) · ‖(y₀, 1)‖`.
The explicit evolution is the first coordinate of the augmented operator-exponential orbit through
`(y₀, 1)`; the first-coordinate projection is `1`-Lipschitz, the orbit is dominated by
`‖exp((t - t₀) • affineAugment L b)‖ · ‖(y₀, 1)‖`, and the resolvent growth bound
`norm_exp_smul_le` together with `norm_affineAugment_le` controls the operator exponential.  This is
the at-most-exponential-in-time stability estimate of the honest frozen geometric chart solution — the
whole-section growth control a mild/Duhamel argument consumes. -/
theorem norm_affineFundamentalSolution_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ : E) (t : ℝ) :
    ‖affineFundamentalSolution L b t₀ y₀ t‖
      ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖(y₀, (1 : ℝ))‖ := by
  rw [affineFundamentalSolution]
  calc ‖(NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, (1 : ℝ))).1‖
      ≤ ‖NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, (1 : ℝ))‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ ‖NormedSpace.exp ((t - t₀) • affineAugment L b)‖ * ‖(y₀, (1 : ℝ))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖(y₀, (1 : ℝ))‖ := by
        gcongr
        calc ‖NormedSpace.exp ((t - t₀) • affineAugment L b)‖
            ≤ Real.exp (|t - t₀| * ‖affineAugment L b‖) :=
              norm_exp_smul_le (t - t₀) (affineAugment L b)
          _ ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) :=
              Real.exp_le_exp.2
                (mul_le_mul_of_nonneg_left (norm_affineAugment_le L b) (abs_nonneg _))

/-- **Continuous dependence on initial data for the frozen (affine) chart evolution.**
`‖affineFundamentalSolution L b t₀ y₀ t − affineFundamentalSolution L b t₀ y₀' t‖ ≤
Real.exp (|t - t₀| · (‖L‖ + ‖b‖)) · ‖y₀ − y₀'‖`.  The evolution is *affine* in the initial value, so
the difference of two orbits is the homogeneous orbit of `(y₀ − y₀', 0)`:
`(exp A (y₀,1)).1 − (exp A (y₀',1)).1 = (exp A ((y₀,1) − (y₀',1))).1 = (exp A (y₀ − y₀', 0)).1`
by linearity of `exp A` and of the projection, with `(y₀,1) − (y₀',1) = (y₀ − y₀', 0)`.  The resolvent
growth bound then controls it.  This is the Lipschitz-in-initial-data / well-posedness stability of the
honest frozen geometric section-space evolution, with the same at-most-exponential rate. -/
theorem norm_affineFundamentalSolution_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (L : E →L[ℝ] E) (b : E) (t₀ : ℝ) (y₀ y₀' : E) (t : ℝ) :
    ‖affineFundamentalSolution L b t₀ y₀ t - affineFundamentalSolution L b t₀ y₀' t‖
      ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖y₀ - y₀'‖ := by
  set A := (t - t₀) • affineAugment L b with hA
  have key : (NormedSpace.exp A (y₀, (1:ℝ))).1 - (NormedSpace.exp A (y₀', (1:ℝ))).1
      = (NormedSpace.exp A (y₀ - y₀', (0:ℝ))).1 := by
    rw [← Prod.fst_sub, ← ContinuousLinearMap.map_sub]
    congr 2
    rw [Prod.mk_sub_mk, sub_self]
  rw [affineFundamentalSolution, affineFundamentalSolution, ← hA, key]
  have hnorm0 : ‖(y₀ - y₀', (0:ℝ))‖ = ‖y₀ - y₀'‖ := by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  calc ‖(NormedSpace.exp A (y₀ - y₀', (0:ℝ))).1‖
      ≤ ‖NormedSpace.exp A (y₀ - y₀', (0:ℝ))‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ ‖NormedSpace.exp A‖ * ‖(y₀ - y₀', (0:ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖(y₀ - y₀', (0:ℝ))‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hA]
        refine (norm_exp_smul_le (t - t₀) (affineAugment L b)).trans ?_
        exact Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left (norm_affineAugment_le L b) (abs_nonneg _))
    _ = Real.exp (|t - t₀| * (‖L‖ + ‖b‖)) * ‖y₀ - y₀'‖ := by rw [hnorm0]

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
