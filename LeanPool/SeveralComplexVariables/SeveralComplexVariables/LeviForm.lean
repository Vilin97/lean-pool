/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Plurisubharmonic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Subharmonic.SmoothCriterion

/-!
# The Levi form

The Levi form of a real `C²` function on a complex normed space, at a point `a` in a direction
`w`, is defined here in coordinate-free form as one quarter of the sum of the real Hessian
evaluated on `(w, w)` and on `(I • w, I • w)`. On `ℂⁿ` this is the classical Hermitian form `∑
∂²f/∂z_ν∂\bar z_μ w_ν \bar w_μ`; the definition avoids Wirtinger derivatives.

The Levi form in direction `w` is one quarter of the Laplacian of the slice `t ↦ f (a + t • w)`
at `t = 0`. Together with the Laplacian criterion for subharmonicity this gives the `C²`
criterion: a `C²` function on an open set is plurisubharmonic exactly when its Levi form is
positive semidefinite at every point.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 2 ("The Levi
Form", Theorem 2.8); [Hörmander][Hormander1973] (1973), Theorem 2.6.2; [Range][Range1986]
(1986), Chapter II, Section 2.6.

## Main definitions

* `leviForm`: The Levi form of a real function at `a` in direction `w`: one quarter of the sum of
  the real Hessian evaluated on `(w, w)` and on `(I • w, I • w)`.

## Main results

* `PlurisubharmonicOn.leviForm_nonneg`: **Necessity.** The Levi form of a `C²` plurisubharmonic
  function is positive semidefinite.
* `plurisubharmonicOn_of_leviForm_nonneg`: **Sufficiency.** A `C²` function on an open set with
  positive semidefinite Levi form is plurisubharmonic.
* `plurisubharmonicOn_iff_leviForm_nonneg`: **The `C²` criterion for plurisubharmonicity.** A `C²`
  function on an open set is plurisubharmonic exactly when its Levi form is positive semidefinite
  everywhere.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology Laplacian

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Levi form of a real function at `a` in direction `w`: one quarter of the sum of the real
Hessian evaluated on `(w, w)` and on `(I • w, I • w)`. -/
@[expose] def leviForm (f : E → ℝ) (a w : E) : ℝ :=
  (iteratedFDeriv ℝ 2 f a ![w, w] + iteratedFDeriv ℝ 2 f a ![I • w, I • w]) / 4

/-- The Levi form in terms of the second Fréchet derivative. -/
theorem leviForm_eq_fderiv (f : E → ℝ) (a w : E) :
    leviForm f a w = (fderiv ℝ (fderiv ℝ f) a w w + fderiv ℝ (fderiv ℝ f) a (I • w) (I • w)) / 4
      := by
  simp [leviForm, iteratedFDeriv_two_apply]

variable {f : E → ℝ} {U : Set E}

/-- The second derivative of a complex-line slice of a `C²` function is the second derivative of the
function evaluated on the direction vectors. -/
theorem fderiv_fderiv_slice {a w : E} {t₀ : ℂ} (hf : ContDiffAt ℝ 2 f (a + t₀ • w)) (s s' : ℂ) :
    fderiv ℝ (fderiv ℝ (fun t : ℂ => f (a + t • w))) t₀ s s' =
      fderiv ℝ (fderiv ℝ f) (a + t₀ • w) (s • w) (s' • w) := by
  set φ : ℂ → E := fun t => a + ((ContinuousLinearMap.id ℝ ℂ).smulRight w) t with hφdef
  have hφ : ∀ t, HasFDerivAt φ ((ContinuousLinearMap.id ℝ ℂ).smulRight w) t := fun t =>
    ((ContinuousLinearMap.id ℝ ℂ).smulRight w).hasFDerivAt.const_add a
  have hφc : Continuous φ := ((ContinuousLinearMap.id ℝ ℂ).smulRight w).continuous.const_add a
  have hev : ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ 2 f (φ t) :=
    hφc.continuousAt.eventually (hf.eventually (by simp))
  have hg : (fun t => fderiv ℝ (f ∘ φ) t) =ᶠ[𝓝 t₀]
      fun t => (fderiv ℝ f (φ t)).comp ((ContinuousLinearMap.id ℝ ℂ).smulRight w) := by
    filter_upwards [hev] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp t (hφ t)).fderiv
  have hD2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (φ t₀)) (φ t₀) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasFDerivAt (fun t => fderiv ℝ f (φ t))
      ((fderiv ℝ (fderiv ℝ f) (φ t₀)).comp ((ContinuousLinearMap.id ℝ ℂ).smulRight w)) t₀
        := hD2.comp t₀ (hφ t₀)
  have hfin := hcomp.clm_comp (hasFDerivAt_const ((ContinuousLinearMap.id ℝ ℂ).smulRight w) t₀)
  have hgφ : (fun t : ℂ => f (a + t • w)) = f ∘ φ := rfl
  rw [hgφ, hg.fderiv_eq, hfin.fderiv]
  simp [ContinuousLinearMap.compL_apply]
  rfl

/-- The first derivative of a complex-line slice of a differentiable function. -/
theorem fderiv_slice {a w : E} {t₀ : ℂ} (hf : DifferentiableAt ℝ f (a + t₀ • w)) :
    fderiv ℝ (fun t : ℂ => f (a + t • w)) t₀ = (fderiv ℝ f (a + t₀ • w)).comp
      ((ContinuousLinearMap.id ℝ ℂ).smulRight w) := by
  have hφ : HasFDerivAt (fun t : ℂ => a + ((ContinuousLinearMap.id ℝ ℂ).smulRight w) t)
    ((ContinuousLinearMap.id ℝ ℂ).smulRight w) t₀ :=
    ((ContinuousLinearMap.id ℝ ℂ).smulRight w).hasFDerivAt.const_add a
  exact (hf.hasFDerivAt.comp t₀ hφ).fderiv

/-- The Laplacian of a complex-line slice is four times the Levi form in that direction. -/
theorem laplacian_slice {a w : E} {t₀ : ℂ} (hf : ContDiffAt ℝ 2 f (a + t₀ • w)) :
    Δ (fun t : ℂ => f (a + t • w)) t₀ = 4 * leviForm f (a + t₀ • w) w := by
  rw [laplacian_eq_fderiv_fderiv, fderiv_fderiv_slice hf, fderiv_fderiv_slice hf,
    leviForm_eq_fderiv, one_smul]
  ring

/-- **Necessity.** The Levi form of a `C²` plurisubharmonic function is positive semidefinite. -/
theorem PlurisubharmonicOn.leviForm_nonneg (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hpsh : PlurisubharmonicOn f U) {a : E} (ha : a ∈ U) (w : E) : 0 ≤ leviForm f a w := by
  have ha' : a + (0 : ℂ) • w ∈ U := by simpa using ha
  have hc : ContDiffAt ℝ 2 (fun t : ℂ => f (a + t • w)) 0 :=
    (hf.contDiffAt (hU.mem_nhds ha')).comp 0
      (by fun_prop : ContDiff ℝ 2 fun t : ℂ => a + t • w).contDiffAt
  have := (hpsh.hasSubmeanAt_slice ha w).laplacian_nonneg hc
  rw [laplacian_slice (hf.contDiffAt (hU.mem_nhds ha'))] at this
  simp only [zero_smul, add_zero] at this
  linarith

/-- **Sufficiency.** A `C²` function on an open set with positive semidefinite Levi form is
plurisubharmonic. -/
theorem plurisubharmonicOn_of_leviForm_nonneg (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (h : ∀ a ∈ U, ∀ w : E, 0 ≤ leviForm f a w) : PlurisubharmonicOn f U := by
  refine ⟨hf.continuousOn.upperSemicontinuousOn, fun a ha w => ?_⟩
  apply subharmonicOn_of_laplacian_nonneg
    (hU.preimage (by fun_prop : Continuous fun t : ℂ => a + t • w))
  · exact hf.comp (by fun_prop : ContDiff ℝ 2 fun t : ℂ => a + t • w).contDiffOn fun _ ht => ht
  · intro t ht
    rw [laplacian_slice (hf.contDiffAt (hU.mem_nhds ht))]
    exact mul_nonneg (by norm_num) (h _ ht w)

/-- **The `C²` criterion for plurisubharmonicity.** A `C²` function on an open set is
plurisubharmonic exactly when its Levi form is positive semidefinite everywhere. -/
theorem plurisubharmonicOn_iff_leviForm_nonneg (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    PlurisubharmonicOn f U ↔ ∀ a ∈ U, ∀ w : E, 0 ≤ leviForm f a w :=
  ⟨fun hpsh _ ha w => hpsh.leviForm_nonneg hU hf ha w,
    fun h => plurisubharmonicOn_of_leviForm_nonneg hU hf h⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
