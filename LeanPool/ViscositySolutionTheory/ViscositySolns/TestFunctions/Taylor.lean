/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.TestFunctions.Smooth
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Taylor bridges for test functions

This file packages Taylor-style little-oh remainders into the abstract
second-order expansion predicate used by the viscosity solution definitions.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff

namespace ViscositySolns

variable {n : Nat}

/-- Symmetry of a bundled bilinear second-derivative map. -/
def IsSymmetricBilinear (D2φ : Point n →L[Real] Point n →L[Real] Real) : Prop :=
  ∀ v w : Point n, D2φ v w = D2φ w v

/-- Mathlib's symmetry predicate for the second derivative gives the bundled bilinear symmetry
used by the Taylor model derivative. -/
theorem isSymmetricBilinear_fderivWithin_fderivWithin {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n}
    (h : IsSymmSndFDerivWithinAt Real φ C x0) :
    IsSymmetricBilinear (fderivWithin Real (fderivWithin Real φ C) C x0) :=
  h

/--
The second-order Taylor polynomial written using Fréchet derivative data rather
than coordinate gradients and Hessian matrices.
-/
def frechetSecondOrderModel (x0 : Point n) (r : Real) (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real) (x : Point n) : Real :=
  r + Dφ (x - x0) + (1 / 2 : Real) * D2φ (x - x0) (x - x0)

@[simp]
theorem frechetSecondOrderModel_of_jet (x0 : Point n) (r : Real) (J : Jet n) (x : Point n) :
    frechetSecondOrderModel x0 r J.toFirstDerivative J.toSecondDerivative x =
      quadraticModel x0 r J.gradient J.hessian x := by
  rw [quadraticModel_eq_linearMap]
  rfl

/--
Fixed quadratic models are smooth.

In quantified mathematical form, for fixed `x0`, `r`, `p`, and `X`, the
function
`x ↦ r + p · (x - x0) + (1 / 2) ⟪X(x - x0), x - x0⟫`
is `C^k` for every differentiability order `k`.
-/
theorem contDiff_quadraticModel {k : ℕ∞ω}
    (x0 : Point n) (r : Real) (p : Point n) (X : Hessian n) :
    ContDiff Real k (fun x : Point n => quadraticModel x0 r p X x) := by
  let J : Jet n := { gradient := p, hessian := X }
  have hdx : ContDiff Real k (fun x : Point n => x - x0) :=
    contDiff_id.sub contDiff_const
  have hlin : ContDiff Real k (fun x : Point n => J.toFirstDerivative (x - x0)) :=
    J.toFirstDerivative.contDiff.comp hdx
  have hquad :
      ContDiff Real k (fun x : Point n => J.toSecondDerivative (x - x0) (x - x0)) := by
    have hbilin :
        ContDiff Real k
          (fun y : Point n × Point n => J.toSecondDerivative y.1 y.2) :=
      J.toSecondDerivative.isBoundedBilinearMap.contDiff
    simpa using hbilin.comp₂ hdx hdx
  have htotal :
      ContDiff Real k (fun x : Point n =>
        r + J.toFirstDerivative (x - x0) +
          (1 / 2 : Real) * J.toSecondDerivative (x - x0) (x - x0)) :=
    (contDiff_const.add hlin).add (contDiff_const.mul hquad)
  have hfun :
      (fun x : Point n =>
        r + J.toFirstDerivative (x - x0) +
          (1 / 2 : Real) * J.toSecondDerivative (x - x0) (x - x0)) =
        (fun x : Point n => quadraticModel x0 r p X x) := by
    ext x
    rw [quadraticModel_eq_linearMap x0 r J x]
  simpa [← hfun] using htotal

/--
For a symmetric bilinear second derivative, the derivative of the Fréchet
quadratic model at `x` is `Dφ + D²φ (x - x₀)`.
-/
theorem hasFDerivWithinAt_frechetSecondOrderModel {C : Set (Point n)}
    (x0 : Point n) (r : Real) (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real)
    (hD2φ : IsSymmetricBilinear D2φ) (x : Point n) :
    HasFDerivWithinAt
      (fun y : Point n => frechetSecondOrderModel x0 r Dφ D2φ y)
      (Dφ + D2φ (x - x0)) C x := by
  let dx : Point n := x - x0
  let shift : Point n →L[Real] Point n :=
    (ContinuousLinearMap.id Real (Point n)) - (0 : Point n →L[Real] Point n)
  have hshift_apply (y : Point n) : shift y = y := by
    simp [shift]
  have hlin :
      HasFDerivWithinAt (fun y : Point n => Dφ (y - x0)) Dφ C x := by
    simpa [map_sub] using
      (Dφ.hasFDerivWithinAt (s := C) (x := x)).sub_const (Dφ x0)
  have hquad_raw :
      HasFDerivWithinAt (fun y : Point n => D2φ (y - x0) (y - x0))
        (D2φ.precompR (Point n) dx (ContinuousLinearMap.id Real (Point n)) +
          D2φ.precompL (Point n) (ContinuousLinearMap.id Real (Point n)) dx) C x := by
    let shiftFun : Point n -> Point n := fun y => y - x0
    have hshift_deriv :
        HasFDerivWithinAt shiftFun (ContinuousLinearMap.id Real (Point n)) C x := by
      simpa [shiftFun, sub_eq_add_neg] using
        (ContinuousLinearMap.id Real (Point n)).hasFDerivWithinAt.add_const (-x0)
    simpa [shiftFun, dx] using D2φ.hasFDerivWithinAt_of_bilinear hshift_deriv hshift_deriv
  have hquad_deriv :
      HasFDerivWithinAt (fun y : Point n => (1 / 2 : Real) * D2φ (y - x0) (y - x0))
        (D2φ (x - x0)) C x := by
    refine (hquad_raw.const_smul (1 / 2 : Real)).congr_fderiv ?_
    ext v
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.id_apply]
    rw [hD2φ v dx]
    simp [dx]
    ring_nf
  have hsum0 :
      HasFDerivWithinAt
        ((fun _ : Point n => r) +
          ((fun y : Point n => Dφ (y - x0)) +
            (fun y : Point n => (1 / 2 : Real) * D2φ (y - x0) (y - x0))))
        (0 + (Dφ + D2φ (x - x0))) C x :=
    (hasFDerivWithinAt_const r x C).add (hlin.add hquad_deriv)
  have hsum :
      HasFDerivWithinAt
        ((fun _ : Point n => r) +
          ((fun y : Point n => Dφ (y - x0)) +
            (fun y : Point n => (1 / 2 : Real) * D2φ (y - x0) (y - x0))))
        (Dφ + D2φ (x - x0)) C x :=
    hsum0.congr_fderiv (by simp)
  refine hsum.congr (fun y _ => ?_) ?_
  · simp [frechetSecondOrderModel]
    ring
  · simp [frechetSecondOrderModel]
    ring

/--
Derivative of the residual after subtracting the Fréchet second-order model.
-/
theorem hasFDerivWithinAt_frechetSecondOrderResidual {C : Set (Point n)}
    {φ : Point n -> Real} {x0 x : Point n}
    {Dφ : Point n →L[Real] Real} {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hD2φ : IsSymmetricBilinear D2φ)
    (hφ : HasFDerivWithinAt φ (Dφ_at x) C x) :
    HasFDerivWithinAt
      (fun y : Point n => φ y - frechetSecondOrderModel x0 (φ x0) Dφ D2φ y)
      (Dφ_at x - (Dφ + D2φ (x - x0))) C x :=
  hφ.sub (hasFDerivWithinAt_frechetSecondOrderModel x0 (φ x0) Dφ D2φ hD2φ x)

/--
If the first-derivative map has derivative `D²φ` at `x₀`, then the derivative
residual for the second-order Taylor model is `o(‖x - x₀‖)`.
-/
theorem frechetDerivativeResidual_isLittleO_of_hasFDerivWithinAt {C : Set (Point n)}
    {x0 : Point n} {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hDφ0 : Dφ_at x0 = Dφ)
    (hDφ_deriv : HasFDerivWithinAt Dφ_at D2φ C x0) :
    Asymptotics.IsLittleO (nhdsWithin x0 C)
      (fun x : Point n => Dφ_at x - (Dφ + D2φ (x - x0)))
      (fun x : Point n => ‖x - x0‖) := by
  have hraw := hDφ_deriv.isLittleO.norm_right
  exact hraw.congr_left fun x => by
    ext v
    simp [hDφ0]
    ring

/--
A Fréchet second-order Taylor expansion with coordinate derivative data gives
the abstract second-order expansion predicate used for viscosity test functions.
-/
theorem hasSecondOrderExpansionWithin_of_frechetLittleO {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (hφ : Asymptotics.IsLittleO (nhdsWithin x0 C)
      (fun x : Point n =>
        φ x - frechetSecondOrderModel x0 (φ x0) J.toFirstDerivative J.toSecondDerivative x)
      (fun x : Point n => ‖x - x0‖ ^ 2)) :
    HasSecondOrderExpansionWithin C φ x0 J := by
  refine ⟨fun x => φ x - quadraticModel x0 (φ x0) J.gradient J.hessian x, ?_, ?_⟩
  · exact hφ.congr_left fun x => by
      rw [frechetSecondOrderModel_of_jet]
  · exact Eventually.of_forall fun x => by ring

/--
Version of `hasSecondOrderExpansionWithin_of_frechetLittleO` with explicit
Fréchet derivative maps. The equalities identify those maps with the coordinate
jet data.
-/
theorem hasSecondOrderExpansionWithin_of_frechetTaylor {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    {Dφ : Point n →L[Real] Real} {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hDφ : Dφ = J.toFirstDerivative) (hD2φ : D2φ = J.toSecondDerivative)
    (hφ : Asymptotics.IsLittleO (nhdsWithin x0 C)
      (fun x : Point n => φ x - frechetSecondOrderModel x0 (φ x0) Dφ D2φ x)
      (fun x : Point n => ‖x - x0‖ ^ 2)) :
    HasSecondOrderExpansionWithin C φ x0 J := by
  subst Dφ
  subst D2φ
  exact hasSecondOrderExpansionWithin_of_frechetLittleO hφ

/--
Mean-value upgrade from a little-oh first-derivative residual to a second-order
little-oh residual on a convex domain.
-/
theorem isLittleO_second_order_of_hasFDerivWithinAt_isLittleO_deriv {C : Set (Point n)}
    {x0 : Point n} {R : Point n -> Real} {R' : Point n -> Point n →L[Real] Real}
    (hC : Convex Real C) (hx0 : x0 ∈ C)
    (hRderiv : ∀ x ∈ C, HasFDerivWithinAt R (R' x) C x)
    (hR' : Asymptotics.IsLittleO (nhdsWithin x0 C) R'
      (fun x : Point n => ‖x - x0‖))
    (hR0 : R x0 = 0) :
    Asymptotics.IsLittleO (nhdsWithin x0 C) R (fun x : Point n => ‖x - x0‖ ^ 2) := by
  have hRpow :
      Asymptotics.IsLittleO (nhdsWithin x0 C) R'
        (fun x : Point n => ‖x - x0‖ ^ 1) :=
    hR'.congr_right fun x => by ring
  have h := hC.isLittleO_pow_succ (x₀ := x0) (n := 1) hx0 hRderiv hRpow
  have h' :
      Asymptotics.IsLittleO (nhdsWithin x0 C) (fun x : Point n => R x - R x0)
        (fun x : Point n => ‖x - x0‖ ^ 2) := by
    simpa using h
  exact h'.congr_left fun x => by simp [hR0]

/--
If the residual after subtracting the Fréchet second-order Taylor polynomial has
first derivative `o(‖x - x₀‖)`, then it has the little-oh remainder needed for
the viscosity expansion predicate.
-/
theorem frechetLittleO_of_hasFDerivWithinAt_isLittleO_deriv {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n}
    {Dφ : Point n →L[Real] Real} {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {R' : Point n -> Point n →L[Real] Real}
    (hC : Convex Real C) (hx0 : x0 ∈ C)
    (hRderiv :
      ∀ x ∈ C,
        HasFDerivWithinAt
          (fun y : Point n => φ y - frechetSecondOrderModel x0 (φ x0) Dφ D2φ y)
          (R' x) C x)
    (hR' : Asymptotics.IsLittleO (nhdsWithin x0 C) R'
      (fun x : Point n => ‖x - x0‖)) :
    Asymptotics.IsLittleO (nhdsWithin x0 C)
      (fun x : Point n => φ x - frechetSecondOrderModel x0 (φ x0) Dφ D2φ x)
      (fun x : Point n => ‖x - x0‖ ^ 2) := by
  refine isLittleO_second_order_of_hasFDerivWithinAt_isLittleO_deriv
    hC hx0 hRderiv hR' ?_
  simp [frechetSecondOrderModel]

/--
A derivative-residual form of the Fréchet Taylor bridge. This is often easier
to feed from continuity of the second derivative than the final little-oh
remainder itself.
-/
theorem hasSecondOrderExpansionWithin_of_frechetDerivativeRemainder {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    {Dφ : Point n →L[Real] Real} {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {R' : Point n -> Point n →L[Real] Real}
    (hC : Convex Real C) (hx0 : x0 ∈ C)
    (hDφ : Dφ = J.toFirstDerivative) (hD2φ : D2φ = J.toSecondDerivative)
    (hRderiv :
      ∀ x ∈ C,
        HasFDerivWithinAt
          (fun y : Point n => φ y - frechetSecondOrderModel x0 (φ x0) Dφ D2φ y)
          (R' x) C x)
    (hR' : Asymptotics.IsLittleO (nhdsWithin x0 C) R'
      (fun x : Point n => ‖x - x0‖)) :
    HasSecondOrderExpansionWithin C φ x0 J :=
  hasSecondOrderExpansionWithin_of_frechetTaylor hDφ hD2φ
    (frechetLittleO_of_hasFDerivWithinAt_isLittleO_deriv hC hx0 hRderiv hR')

/--
Smooth-test-function bridge from first- and second-derivative data. The
hypotheses say that `Dφ_at` is the Fréchet derivative of `φ` on `C`, that
`Dφ_at` has derivative `D²φ` at `x₀`, and that this derivative data matches the
coordinate jet.
-/
theorem hasSecondOrderExpansionWithin_of_frechetC2Data {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    {Dφ : Point n →L[Real] Real} {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hC : Convex Real C) (hx0 : x0 ∈ C)
    (hD2sym : IsSymmetricBilinear D2φ)
    (hDφ : Dφ = J.toFirstDerivative) (hD2φ : D2φ = J.toSecondDerivative)
    (hDφ0 : Dφ_at x0 = Dφ)
    (hφ_deriv : ∀ x ∈ C, HasFDerivWithinAt φ (Dφ_at x) C x)
    (hDφ_deriv : HasFDerivWithinAt Dφ_at D2φ C x0) :
    HasSecondOrderExpansionWithin C φ x0 J :=
  hasSecondOrderExpansionWithin_of_frechetDerivativeRemainder hC hx0 hDφ hD2φ
    (fun x hx => hasFDerivWithinAt_frechetSecondOrderResidual hD2sym (hφ_deriv x hx))
    (frechetDerivativeResidual_isLittleO_of_hasFDerivWithinAt hDφ0 hDφ_deriv)

/--
Canonical `fderivWithin` version of the smooth-test-function bridge. This
specializes `hasSecondOrderExpansionWithin_of_frechetC2Data` to mathlib's
chosen first and second derivative maps.
-/
theorem hasSecondOrderExpansionWithin_of_fderivWithinC2Data {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (hC : Convex Real C) (hx0 : x0 ∈ C)
    (hD2sym : IsSymmSndFDerivWithinAt Real φ C x0)
    (hDφ : fderivWithin Real φ C x0 = J.toFirstDerivative)
    (hD2φ : fderivWithin Real (fderivWithin Real φ C) C x0 = J.toSecondDerivative)
    (hφ_deriv : ∀ x ∈ C, HasFDerivWithinAt φ (fderivWithin Real φ C x) C x)
    (hDφ_deriv :
      HasFDerivWithinAt (fderivWithin Real φ C)
        (fderivWithin Real (fderivWithin Real φ C) C x0) C x0) :
    HasSecondOrderExpansionWithin C φ x0 J :=
  hasSecondOrderExpansionWithin_of_frechetC2Data hC hx0
    (isSymmetricBilinear_fderivWithin_fderivWithin hD2sym) hDφ hD2φ rfl
    hφ_deriv hDφ_deriv

/--
Canonical `fderivWithin` theorem with differentiability hypotheses. The
derivative maps are mathlib's `fderivWithin` choices.
-/
theorem hasSecondOrderExpansionWithin_of_fderivWithinDifferentiable {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (hC : Convex Real C) (hx0 : x0 ∈ C)
    (hD2sym : IsSymmSndFDerivWithinAt Real φ C x0)
    (hDφ : fderivWithin Real φ C x0 = J.toFirstDerivative)
    (hD2φ : fderivWithin Real (fderivWithin Real φ C) C x0 = J.toSecondDerivative)
    (hφ_diff : ∀ x ∈ C, DifferentiableWithinAt Real φ C x)
    (hDφ_diff : DifferentiableWithinAt Real (fderivWithin Real φ C) C x0) :
    HasSecondOrderExpansionWithin C φ x0 J :=
  hasSecondOrderExpansionWithin_of_fderivWithinC2Data hC hx0 hD2sym hDφ hD2φ
    (fun x hx => (hφ_diff x hx).hasFDerivWithinAt)
    hDφ_diff.hasFDerivWithinAt

/--
`C^2` functions on a uniquely differentiable convex domain have the abstract
second-order expansion associated to their canonical `fderivWithin` data.
-/
theorem hasSecondOrderExpansionWithin_of_contDiffOn_two {C : Set (Point n)}
    {φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C) (hx0 : x0 ∈ C)
    (hx0_closure : x0 ∈ closure (interior C))
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C)
    (hDφ : fderivWithin Real φ C x0 = J.toFirstDerivative)
    (hD2φ : fderivWithin Real (fderivWithin Real φ C) C x0 = J.toSecondDerivative) :
    HasSecondOrderExpansionWithin C φ x0 J := by
  have hφ_diff : ∀ x ∈ C, DifferentiableWithinAt Real φ C x :=
    fun x hx => (hφ x hx).differentiableWithinAt (by norm_num)
  have hDφ_cont :
      ContDiffOn Real (1 : ℕ∞ω) (fderivWithin Real φ C) C :=
    hφ.fderivWithin (m := (1 : ℕ∞ω)) huniq (by norm_num)
  have hDφ_diff : DifferentiableWithinAt Real (fderivWithin Real φ C) C x0 :=
    (hDφ_cont.differentiableOn (by norm_num)) x0 hx0
  have hD2sym : IsSymmSndFDerivWithinAt Real φ C x0 :=
    (hφ x0 hx0).isSymmSndFDerivWithinAt (by norm_num) huniq hx0_closure hx0
  exact hasSecondOrderExpansionWithin_of_fderivWithinDifferentiable
    hC hx0 hD2sym hDφ hD2φ hφ_diff hDφ_diff

end ViscositySolns
