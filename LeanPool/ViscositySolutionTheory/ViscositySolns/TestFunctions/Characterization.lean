/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.TestFunctions.Solutions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Smooth test-function characterization of viscosity solutions

This file proves the classical CIL Section 2 equivalence between the semijet
definition of viscosity sub- and supersolutions and the smooth test-function
formulation: on an open domain, for an operator that is continuous in the
Hessian argument and depends on it only through its symmetric part, `u` is a
viscosity subsolution if and only if `u` is upper semicontinuous and
`F (x, u x, Dφ x, D²φ x) <= 0` whenever `φ` is a `C²` function such that
`u - φ` has a local maximum at `x` relative to the domain.

The forward direction localizes the Taylor bridge of
`ViscositySolns.TestFunctions.Solutions` to a ball. The converse applies the
test-function inequality to the epsilon-inflated quadratic models
`quadraticModel x (u x) p (symHessian X + ε • 1)` and passes to the limit
`ε → 0` using the continuity of the operator in the Hessian slot.

## Main definitions and results

- `SmoothTestFunctionSubsolution`, `SmoothTestFunctionSupersolution`: the
  classical smooth test-function formulations, phrased with `ContDiff` and
  mathlib's canonical `fderiv` data at the contact point.
- `viscositySubsolution_iff_smoothTestFunctionSubsolution`
- `viscositySupersolution_iff_smoothTestFunctionSupersolution`
-/

@[expose] public noncomputable section

open Filter
open Matrix
open scoped ContDiff

namespace ViscositySolns

variable {n : Nat}

/-! ### The smooth test-function formulations -/

/--
The classical smooth test-function formulation of viscosity subsolutions:
`u` is upper semicontinuous, and the operator inequality holds at every point
where a globally `C²` test function touches `u` from above, evaluated on the
coordinate gradient and Hessian extracted from mathlib's canonical first and
second Fréchet derivatives at the contact point.
-/
def SmoothTestFunctionSubsolution (C : Set (Point n)) (F : Operator n)
    (u : Point n -> Real) : Prop :=
  UpperSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall φ : Point n -> Real,
      ContDiff Real 2 φ ->
      TouchesAboveOn C u φ x ->
        F x (u x) (linearMapGradient (fderiv Real φ x))
          (bilinearMapHessian (fderiv Real (fderiv Real φ) x)) <= 0

/--
The classical smooth test-function formulation of viscosity supersolutions:
`u` is lower semicontinuous, and the operator inequality holds at every point
where a globally `C²` test function touches `u` from below.
-/
def SmoothTestFunctionSupersolution (C : Set (Point n)) (F : Operator n)
    (u : Point n -> Real) : Prop :=
  LowerSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall φ : Point n -> Real,
      ContDiff Real 2 φ ->
      TouchesBelowOn C u φ x ->
        0 <= F x (u x) (linearMapGradient (fderiv Real φ x))
          (bilinearMapHessian (fderiv Real (fderiv Real φ) x))

/-! ### Smoothness and derivatives of the quadratic model -/

/-- The quadratic model is the Fréchet second-order model of its jet data. -/
theorem quadraticModel_eq_frechetSecondOrderModel (x0 : Point n) (r : Real)
    (p : Point n) (X : Hessian n) :
    quadraticModel x0 r p X =
      frechetSecondOrderModel x0 r (gradientLinearMap p) (hessianBilinearMap X) := by
  funext x
  exact (frechetSecondOrderModel_of_jet x0 r ⟨p, X⟩ x).symm

/-- The Fréchet second-order model is a `C²` function of the base point. -/
theorem contDiff_frechetSecondOrderModel (x0 : Point n) (r : Real)
    (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real) :
    ContDiff Real 2 (frechetSecondOrderModel x0 r Dφ D2φ) := by
  have hshift : ContDiff Real (2 : ℕ∞ω) (fun y : Point n => y - x0) :=
    contDiff_id.sub contDiff_const
  have hlin : ContDiff Real (2 : ℕ∞ω) (fun y : Point n => Dφ (y - x0)) :=
    Dφ.contDiff.comp hshift
  have hbil :
      ContDiff Real (2 : ℕ∞ω) (fun y : Point n => D2φ (y - x0) (y - x0)) :=
    (D2φ.contDiff.comp hshift).clm_apply hshift
  have hsum :
      ContDiff Real (2 : ℕ∞ω)
        (fun y : Point n =>
          r + Dφ (y - x0) + (1 / 2 : Real) * D2φ (y - x0) (y - x0)) :=
    (contDiff_const.add hlin).add (contDiff_const.mul hbil)
  exact hsum

/--
Global version of the model derivative: for a symmetric bilinear second
derivative, the Fréchet quadratic model has derivative `Dφ + D²φ (x - x₀)`
at every point.
-/
theorem hasFDerivAt_frechetSecondOrderModel (x0 : Point n) (r : Real)
    (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real)
    (hD2φ : IsSymmetricBilinear D2φ) (x : Point n) :
    HasFDerivAt (frechetSecondOrderModel x0 r Dφ D2φ)
      (Dφ + D2φ (x - x0)) x := by
  have h :=
    hasFDerivWithinAt_frechetSecondOrderModel (C := Set.univ) x0 r Dφ D2φ hD2φ x
  exact hasFDerivWithinAt_univ.mp h

/-- The canonical first derivative of a quadratic model at its center point. -/
theorem fderiv_quadraticModel_center (x0 : Point n) (r : Real) (p : Point n)
    {X : Hessian n} (hX : IsSymmetricBilinear (hessianBilinearMap X)) :
    fderiv Real (quadraticModel x0 r p X) x0 = gradientLinearMap p := by
  rw [quadraticModel_eq_frechetSecondOrderModel]
  have h :
      HasFDerivAt
        (frechetSecondOrderModel x0 r (gradientLinearMap p) (hessianBilinearMap X))
        (gradientLinearMap p) x0 := by
    simpa using
      hasFDerivAt_frechetSecondOrderModel x0 r (gradientLinearMap p)
        (hessianBilinearMap X) hX x0
  exact h.fderiv

/-- The canonical second derivative of a quadratic model at its center point. -/
theorem fderiv_fderiv_quadraticModel_center (x0 : Point n) (r : Real)
    (p : Point n) {X : Hessian n}
    (hX : IsSymmetricBilinear (hessianBilinearMap X)) :
    fderiv Real (fderiv Real (quadraticModel x0 r p X)) x0 =
      hessianBilinearMap X := by
  rw [quadraticModel_eq_frechetSecondOrderModel]
  have hfun :
      fderiv Real
          (frechetSecondOrderModel x0 r (gradientLinearMap p)
            (hessianBilinearMap X)) =
        fun y : Point n => gradientLinearMap p + hessianBilinearMap X (y - x0) :=
    funext fun y =>
      (hasFDerivAt_frechetSecondOrderModel x0 r (gradientLinearMap p)
        (hessianBilinearMap X) hX y).fderiv
  rw [hfun]
  have h1 :
      HasFDerivAt (fun y : Point n => hessianBilinearMap X (y - x0))
        (hessianBilinearMap X) x0 := by
    simpa [map_sub] using
      (hessianBilinearMap X).hasFDerivAt.sub_const (hessianBilinearMap X x0)
  exact (h1.const_add (gradientLinearMap p)).fderiv

/-! ### Symmetric Hessians and their bilinear maps -/

/--
The bilinear map of an entrywise-symmetric coordinate Hessian is symmetric.
-/
theorem isSymmetricBilinear_hessianBilinearMap {X : Hessian n}
    (hX : forall i j : Fin n, X i j = X j i) :
    IsSymmetricBilinear (hessianBilinearMap X) := by
  intro v w
  simp only [hessianBilinearMap_apply, dotProduct, Matrix.mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hX j i]
  ring

/-- The symmetric part of a Hessian, shifted by a multiple of the identity,
is entrywise symmetric. -/
theorem symHessian_add_smul_one_symm (X : Hessian n) (c : Real) :
    forall i j : Fin n,
      (symHessian X + c • (1 : Hessian n)) i j =
        (symHessian X + c • (1 : Hessian n)) j i := by
  intro i j
  by_cases h : i = j
  · subst h
    rfl
  · have h' : ¬j = i := fun hh => h hh.symm
    simp [symHessian_apply, Matrix.add_apply, Matrix.smul_apply, h, h']
    ring

/--
Shifting the Hessian of a quadratic model by `c • 1` adds the coordinate
quadratic form `c / 2 * <x - x0, x - x0>`.
-/
theorem quadraticModel_add_smul_one (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) (c : Real) (x : Point n) :
    quadraticModel x0 r p (X + c • (1 : Hessian n)) x =
      quadraticModel x0 r p X x +
        (c / 2) * dotProduct (x - x0) (x - x0) := by
  simp only [quadraticModel, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, add_dotProduct, smul_dotProduct]
  ring

/-- The value of a quadratic model at its center point. -/
theorem quadraticModel_center (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) :
    quadraticModel x0 r p X x0 = r := by
  simp [quadraticModel]

/-! ### Eventual bounds from semijet remainders -/

/--
A semijet remainder is eventually dominated in absolute value by any positive
multiple of the squared distance to the base point.
-/
theorem SemijetRemainder.eventually_abs_le {C : Set (Point n)} {x0 : Point n}
    {rho : Point n -> Real} (hρ : SemijetRemainder C x0 rho) {c : Real}
    (hc : 0 < c) :
    ∀ᶠ x in nhdsWithin x0 C, |rho x| <= c * ‖x - x0‖ ^ 2 := by
  have h := hρ.def hc
  filter_upwards [h] with x hx
  have hg : ‖(‖x - x0‖ ^ 2 : Real)‖ = ‖x - x0‖ ^ 2 := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (pow_nonneg (norm_nonneg _) 2)
  calc
    |rho x| = ‖rho x‖ := (Real.norm_eq_abs (rho x)).symm
    _ <= c * ‖(‖x - x0‖ ^ 2 : Real)‖ := hx
    _ = c * ‖x - x0‖ ^ 2 := by rw [hg]

/-! ### The forward direction: subsolutions satisfy the smooth inequality -/

/--
On an open domain, a globally `C²` function has the abstract second-order
expansion associated to its canonical global `fderiv` data.
-/
theorem hasSecondOrderExpansionWithin_of_contDiff_two_isOpen
    {C : Set (Point n)} {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (hC : IsOpen C) (hx0 : x0 ∈ C)
    (hφ : ContDiff Real 2 φ)
    (hDφ : fderiv Real φ x0 = J.toFirstDerivative)
    (hD2φ : fderiv Real (fderiv Real φ) x0 = J.toSecondDerivative) :
    HasSecondOrderExpansionWithin C φ x0 J := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hC x0 hx0
  have hx0B : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hr
  have hopen : IsOpen (Metric.ball x0 r) := Metric.isOpen_ball
  have hDW :
      forall y : Point n, y ∈ Metric.ball x0 r ->
        fderivWithin Real φ (Metric.ball x0 r) y = fderiv Real φ y :=
    fun y hy => fderivWithin_of_isOpen hopen hy
  have hDφ' :
      fderivWithin Real φ (Metric.ball x0 r) x0 = J.toFirstDerivative := by
    rw [hDW x0 hx0B]
    exact hDφ
  have hD2φ' :
      fderivWithin Real (fderivWithin Real φ (Metric.ball x0 r))
        (Metric.ball x0 r) x0 = J.toSecondDerivative := by
    have hcongr :
        fderivWithin Real (fderivWithin Real φ (Metric.ball x0 r))
            (Metric.ball x0 r) x0 =
          fderivWithin Real (fderiv Real φ) (Metric.ball x0 r) x0 :=
      fderivWithin_congr hDW (hDW x0 hx0B)
    rw [hcongr, fderivWithin_of_isOpen hopen hx0B]
    exact hD2φ
  have hexpB : HasSecondOrderExpansionWithin (Metric.ball x0 r) φ x0 J :=
    hasSecondOrderExpansionWithin_of_contDiffOn_two (convex_ball x0 r)
      hopen.uniqueDiffOn hx0B
      (by
        rw [hopen.interior_eq]
        exact subset_closure hx0B)
      hφ.contDiffOn hDφ' hD2φ'
  have hnhds : nhdsWithin x0 (Metric.ball x0 r) = nhdsWithin x0 C := by
    rw [nhdsWithin_eq_nhds.mpr (hopen.mem_nhds hx0B),
      nhdsWithin_eq_nhds.mpr (hC.mem_nhds hx0)]
  exact (hasSecondOrderExpansionWithin_congr_nhdsWithin hnhds).mp hexpB

/--
On an open domain, a viscosity subsolution satisfies the smooth test-function
inequality for the canonical global derivative data of any `C²` function
touching it from above.
-/
theorem ViscositySubsolution.smoothTestFunctionSubsolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hu : ViscositySubsolution C F u) (hC : IsOpen C) :
    SmoothTestFunctionSubsolution C F u := by
  refine ⟨hu.1, ?_⟩
  intro x hx φ hφ htouch
  have hexp :
      HasSecondOrderExpansionWithin C φ x
        (Jet.ofDerivatives (fderiv Real φ x) (fderiv Real (fderiv Real φ) x)) :=
    hasSecondOrderExpansionWithin_of_contDiff_two_isOpen hC hx hφ
      (Jet.toFirstDerivative_ofDerivatives _ _).symm
      (Jet.toSecondDerivative_ofDerivatives _ _).symm
  exact hu.of_touchesAbove_hasSecondOrderExpansionWithin hx htouch hexp

/--
On an open domain, a viscosity supersolution satisfies the smooth
test-function inequality for the canonical global derivative data of any `C²`
function touching it from below.
-/
theorem ViscositySupersolution.smoothTestFunctionSupersolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hu : ViscositySupersolution C F u) (hC : IsOpen C) :
    SmoothTestFunctionSupersolution C F u := by
  refine ⟨hu.1, ?_⟩
  intro x hx φ hφ htouch
  have hexp :
      HasSecondOrderExpansionWithin C φ x
        (Jet.ofDerivatives (fderiv Real φ x) (fderiv Real (fderiv Real φ) x)) :=
    hasSecondOrderExpansionWithin_of_contDiff_two_isOpen hC hx hφ
      (Jet.toFirstDerivative_ofDerivatives _ _).symm
      (Jet.toSecondDerivative_ofDerivatives _ _).symm
  exact hu.of_touchesBelow_hasSecondOrderExpansionWithin hx htouch hexp

/-! ### The converse direction: the epsilon-inflated quadratic model -/

/--
Core computation for the converse: applying the smooth test-function
inequality of a subsolution candidate to the inflated quadratic model
`quadraticModel x (u x) J.gradient (symHessian J.hessian + ε • 1)` yields the
operator inequality at the shifted symmetric Hessian.
-/
theorem smooth_test_key_subsolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n}
    {J : Jet n}
    (h : forall y : Point n, y ∈ C -> forall φ : Point n -> Real,
      ContDiff Real 2 φ ->
      TouchesAboveOn C u φ y ->
        F y (u y) (linearMapGradient (fderiv Real φ y))
          (bilinearMapHessian (fderiv Real (fderiv Real φ) y)) <= 0)
    (hx : x ∈ C) (hJ : J ∈ Superjet C u x) {ε : Real} (hε : 0 < ε) :
    F x (u x) J.gradient (symHessian J.hessian + ε • (1 : Hessian n)) <= 0 := by
  obtain ⟨ρ, hρ, hle⟩ := hJ
  have hXsym :
      forall i j : Fin n,
        (symHessian J.hessian + ε • (1 : Hessian n)) i j =
          (symHessian J.hessian + ε • (1 : Hessian n)) j i :=
    symHessian_add_smul_one_symm J.hessian ε
  have hXbil :
      IsSymmetricBilinear
        (hessianBilinearMap (symHessian J.hessian + ε • (1 : Hessian n))) :=
    isSymmetricBilinear_hessianBilinearMap hXsym
  have hφsmooth :
      ContDiff Real 2
        (quadraticModel x (u x) J.gradient
          (symHessian J.hessian + ε • (1 : Hessian n))) :=
    contDiff_quadraticModel _ _ _ _
  have htouch :
      TouchesAboveOn C u
        (quadraticModel x (u x) J.gradient
          (symHessian J.hessian + ε • (1 : Hessian n))) x := by
    have hρbound := hρ.eventually_abs_le (half_pos hε)
    filter_upwards [hle, hρbound] with y hy hb
    have hquad :
        quadraticModel x (u x) J.gradient
            (symHessian J.hessian + ε • (1 : Hessian n)) y =
          quadraticModel x (u x) J.gradient J.hessian y +
            (ε / 2) * dotProduct (y - x) (y - x) := by
      rw [quadraticModel_add_smul_one, quadraticModel_symHessian]
    have hnormsq : ‖y - x‖ ^ 2 <= dotProduct (y - x) (y - x) :=
      norm_sq_le_dotProduct_self (y - x)
    have hρle : ρ y <= (ε / 2) * dotProduct (y - x) (y - x) := by
      have h1 : ρ y <= (ε / 2) * ‖y - x‖ ^ 2 :=
        le_trans (le_abs_self _) hb
      nlinarith [hnormsq, half_pos hε]
    have hval :
        quadraticModel x (u x) J.gradient
            (symHessian J.hessian + ε • (1 : Hessian n)) x = u x :=
      quadraticModel_center _ _ _ _
    have huy :
        u y <=
          quadraticModel x (u x) J.gradient
            (symHessian J.hessian + ε • (1 : Hessian n)) y := by
      rw [hquad]
      linarith [hy]
    rw [hval]
    linarith [huy]
  have happ := h x hx _ hφsmooth htouch
  have hD1 :
      fderiv Real
          (quadraticModel x (u x) J.gradient
            (symHessian J.hessian + ε • (1 : Hessian n))) x =
        gradientLinearMap J.gradient :=
    fderiv_quadraticModel_center x (u x) J.gradient hXbil
  have hD2 :
      fderiv Real
          (fderiv Real
            (quadraticModel x (u x) J.gradient
              (symHessian J.hessian + ε • (1 : Hessian n)))) x =
        hessianBilinearMap (symHessian J.hessian + ε • (1 : Hessian n)) :=
    fderiv_fderiv_quadraticModel_center x (u x) J.gradient hXbil
  rw [hD1, hD2, linearMapGradient_gradientLinearMap,
    bilinearMapHessian_hessianBilinearMap] at happ
  exact happ

/--
Core computation for the converse (supersolution side): the smooth
test-function inequality applied to the deflated quadratic model yields the
operator inequality at the shifted symmetric Hessian.
-/
theorem smooth_test_key_supersolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n}
    {J : Jet n}
    (h : forall y : Point n, y ∈ C -> forall φ : Point n -> Real,
      ContDiff Real 2 φ ->
      TouchesBelowOn C u φ y ->
        0 <= F y (u y) (linearMapGradient (fderiv Real φ y))
          (bilinearMapHessian (fderiv Real (fderiv Real φ) y)))
    (hx : x ∈ C) (hJ : J ∈ Subjet C u x) {ε : Real} (hε : 0 < ε) :
    0 <= F x (u x) J.gradient
      (symHessian J.hessian + (-ε) • (1 : Hessian n)) := by
  obtain ⟨ρ, hρ, hle⟩ := hJ
  have hXsym :
      forall i j : Fin n,
        (symHessian J.hessian + (-ε) • (1 : Hessian n)) i j =
          (symHessian J.hessian + (-ε) • (1 : Hessian n)) j i :=
    symHessian_add_smul_one_symm J.hessian (-ε)
  have hXbil :
      IsSymmetricBilinear
        (hessianBilinearMap (symHessian J.hessian + (-ε) • (1 : Hessian n))) :=
    isSymmetricBilinear_hessianBilinearMap hXsym
  have hφsmooth :
      ContDiff Real 2
        (quadraticModel x (u x) J.gradient
          (symHessian J.hessian + (-ε) • (1 : Hessian n))) :=
    contDiff_quadraticModel _ _ _ _
  have htouch :
      TouchesBelowOn C u
        (quadraticModel x (u x) J.gradient
          (symHessian J.hessian + (-ε) • (1 : Hessian n))) x := by
    have hρbound := hρ.eventually_abs_le (half_pos hε)
    filter_upwards [hle, hρbound] with y hy hb
    have hquad :
        quadraticModel x (u x) J.gradient
            (symHessian J.hessian + (-ε) • (1 : Hessian n)) y =
          quadraticModel x (u x) J.gradient J.hessian y +
            (-ε / 2) * dotProduct (y - x) (y - x) := by
      rw [quadraticModel_add_smul_one, quadraticModel_symHessian]
    have hnormsq : ‖y - x‖ ^ 2 <= dotProduct (y - x) (y - x) :=
      norm_sq_le_dotProduct_self (y - x)
    have hρge : -((ε / 2) * dotProduct (y - x) (y - x)) <= ρ y := by
      have h1 : -((ε / 2) * ‖y - x‖ ^ 2) <= ρ y := by
        have := neg_abs_le (ρ y)
        linarith [hb]
      nlinarith [hnormsq, half_pos hε]
    have hval :
        quadraticModel x (u x) J.gradient
            (symHessian J.hessian + (-ε) • (1 : Hessian n)) x = u x :=
      quadraticModel_center _ _ _ _
    have huy :
        quadraticModel x (u x) J.gradient
            (symHessian J.hessian + (-ε) • (1 : Hessian n)) y <= u y := by
      rw [hquad]
      linarith [hy]
    rw [hval]
    linarith [huy]
  have happ := h x hx _ hφsmooth htouch
  have hD1 :
      fderiv Real
          (quadraticModel x (u x) J.gradient
            (symHessian J.hessian + (-ε) • (1 : Hessian n))) x =
        gradientLinearMap J.gradient :=
    fderiv_quadraticModel_center x (u x) J.gradient hXbil
  have hD2 :
      fderiv Real
          (fderiv Real
            (quadraticModel x (u x) J.gradient
              (symHessian J.hessian + (-ε) • (1 : Hessian n)))) x =
        hessianBilinearMap (symHessian J.hessian + (-ε) • (1 : Hessian n)) :=
    fderiv_fderiv_quadraticModel_center x (u x) J.gradient hXbil
  rw [hD1, hD2, linearMapGradient_gradientLinearMap,
    bilinearMapHessian_hessianBilinearMap] at happ
  exact happ

/--
The converse direction for subsolutions: on any domain, the smooth
test-function formulation implies the semijet formulation, provided the
operator is continuous in the Hessian argument and depends on it only through
its symmetric part.
-/
theorem ViscositySubsolution.of_smoothTestFunctionSubsolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : HessianSymmetricInvariant F)
    (h : SmoothTestFunctionSubsolution C F u) :
    ViscositySubsolution C F u := by
  refine ⟨h.1, ?_⟩
  intro x hx J hJ
  have key : forall ε : Real, 0 < ε ->
      F x (u x) J.gradient (symHessian J.hessian + ε • (1 : Hessian n)) <= 0 :=
    fun ε hε => smooth_test_key_subsolution h.2 hx hJ hε
  have hcont :
      Continuous fun ε : Real =>
        F x (u x) J.gradient (symHessian J.hessian + ε • (1 : Hessian n)) :=
    (hFcont x (u x) J.gradient).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have htend :
      Tendsto
        (fun ε : Real =>
          F x (u x) J.gradient (symHessian J.hessian + ε • (1 : Hessian n)))
        (nhdsWithin 0 (Set.Ioi (0 : Real)))
        (nhds (F x (u x) J.gradient (symHessian J.hessian))) := by
    have h0 := (hcont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : Real)))
    simpa using h0
  have hlim : F x (u x) J.gradient (symHessian J.hessian) <= 0 :=
    le_of_tendsto htend
      (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  calc
    F x (u x) J.gradient J.hessian =
        F x (u x) J.gradient (symHessian J.hessian) :=
      hFsym x (u x) J.gradient J.hessian
    _ <= 0 := hlim

/--
The converse direction for supersolutions: the smooth test-function
formulation implies the semijet formulation, provided the operator is
continuous in the Hessian argument and depends on it only through its
symmetric part.
-/
theorem ViscositySupersolution.of_smoothTestFunctionSupersolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : HessianSymmetricInvariant F)
    (h : SmoothTestFunctionSupersolution C F u) :
    ViscositySupersolution C F u := by
  refine ⟨h.1, ?_⟩
  intro x hx J hJ
  have key : forall ε : Real, 0 < ε ->
      0 <= F x (u x) J.gradient
        (symHessian J.hessian + (-ε) • (1 : Hessian n)) :=
    fun ε hε => smooth_test_key_supersolution h.2 hx hJ hε
  have hcont :
      Continuous fun ε : Real =>
        F x (u x) J.gradient (symHessian J.hessian + (-ε) • (1 : Hessian n)) :=
    (hFcont x (u x) J.gradient).comp
      (continuous_const.add ((continuous_neg.smul continuous_const)))
  have htend :
      Tendsto
        (fun ε : Real =>
          F x (u x) J.gradient (symHessian J.hessian + (-ε) • (1 : Hessian n)))
        (nhdsWithin 0 (Set.Ioi (0 : Real)))
        (nhds (F x (u x) J.gradient (symHessian J.hessian))) := by
    have h0 := (hcont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : Real)))
    simpa using h0
  have hlim : 0 <= F x (u x) J.gradient (symHessian J.hessian) :=
    ge_of_tendsto htend
      (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  calc
    (0 : Real) <= F x (u x) J.gradient (symHessian J.hessian) := hlim
    _ = F x (u x) J.gradient J.hessian :=
      (hFsym x (u x) J.gradient J.hessian).symm

/-! ### The characterizations -/

/--
CIL Section 2, smooth test-function characterization of subsolutions: on an
open domain, for an operator continuous in the Hessian argument and depending
on it only through its symmetric part, the semijet and smooth test-function
formulations of viscosity subsolutions coincide.
-/
theorem viscositySubsolution_iff_smoothTestFunctionSubsolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : HessianSymmetricInvariant F) :
    ViscositySubsolution C F u <-> SmoothTestFunctionSubsolution C F u :=
  ⟨fun hu => hu.smoothTestFunctionSubsolution hC,
    fun h => ViscositySubsolution.of_smoothTestFunctionSubsolution hFcont hFsym h⟩

/--
CIL Section 2, smooth test-function characterization of supersolutions: on an
open domain, for an operator continuous in the Hessian argument and depending
on it only through its symmetric part, the semijet and smooth test-function
formulations of viscosity supersolutions coincide.
-/
theorem viscositySupersolution_iff_smoothTestFunctionSupersolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : HessianSymmetricInvariant F) :
    ViscositySupersolution C F u <-> SmoothTestFunctionSupersolution C F u :=
  ⟨fun hu => hu.smoothTestFunctionSupersolution hC,
    fun h => ViscositySupersolution.of_smoothTestFunctionSupersolution hFcont hFsym h⟩

end ViscositySolns
