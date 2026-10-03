/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Second-order semijets

This file contains superjets, subjets, their excess characterizations, and the
abstract test-function bridge for semijets.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The second-order superjet `J^{2,+}_C u(x0)`.

The inequality is the CIL condition
`u x <= u x0 + <p, x - x0> + 1/2 <X (x - x0), x - x0> + o(|x - x0|^2)`
as `C ∋ x -> x0`.
-/
def Superjet (C : Set (Point n)) (u : Point n -> Real) (x0 : Point n) : Set (Jet n) :=
  {J |
    exists rho : Point n -> Real,
      SemijetRemainder C x0 rho /\
        Filter.Eventually
          (fun x : Point n =>
            u x <= quadraticModel x0 (u x0) J.gradient J.hessian x + rho x)
          (nhdsWithin x0 C)}

/--
The second-order subjet `J^{2,-}_C u(x0)`.

This is the sign-reversed companion to `Superjet`: the same quadratic expansion
supports `u` from below, up to an `o(|x - x0|^2)` error.
-/
def Subjet (C : Set (Point n)) (u : Point n -> Real) (x0 : Point n) : Set (Jet n) :=
  {J |
    exists rho : Point n -> Real,
      SemijetRemainder C x0 rho /\
        Filter.Eventually
          (fun x : Point n =>
            quadraticModel x0 (u x0) J.gradient J.hessian x + rho x <= u x)
          (nhdsWithin x0 C)}

/--
Superjet fibers only depend on the germ of the domain at the base point.
-/
theorem superjet_congr_nhdsWithin {C D : Set (Point n)} {u : Point n -> Real}
    {x : Point n} (h : nhdsWithin x C = nhdsWithin x D) :
    Superjet C u x = Superjet D u x := by
  ext J
  constructor
  · rintro ⟨rho, hrho, hineq⟩
    exact ⟨rho, (semijetRemainder_congr_nhdsWithin h).1 hrho,
      by simpa [h] using hineq⟩
  · rintro ⟨rho, hrho, hineq⟩
    exact ⟨rho, (semijetRemainder_congr_nhdsWithin h.symm).1 hrho,
      by simpa [h.symm] using hineq⟩

/--
Subjet fibers only depend on the germ of the domain at the base point.
-/
theorem subjet_congr_nhdsWithin {C D : Set (Point n)} {u : Point n -> Real}
    {x : Point n} (h : nhdsWithin x C = nhdsWithin x D) :
    Subjet C u x = Subjet D u x := by
  ext J
  constructor
  · rintro ⟨rho, hrho, hineq⟩
    exact ⟨rho, (semijetRemainder_congr_nhdsWithin h).1 hrho,
      by simpa [h] using hineq⟩
  · rintro ⟨rho, hrho, hineq⟩
    exact ⟨rho, (semijetRemainder_congr_nhdsWithin h.symm).1 hrho,
      by simpa [h.symm] using hineq⟩

/--
The normalized numerator for the superjet condition. Superjets make this excess
nonpositive up to an `o(|y - x|^2)` error.
-/
def SuperjetExcess (u : Point n -> Real) (x : Point n) (J : Jet n) (y : Point n) :
    Real :=
  u y - quadraticModel x (u x) J.gradient J.hessian y

/--
The normalized numerator for the subjet condition. Subjets make this excess
nonpositive up to an `o(|y - x|^2)` error.
-/
def SubjetExcess (u : Point n -> Real) (x : Point n) (J : Jet n) (y : Point n) :
    Real :=
  quadraticModel x (u x) J.gradient J.hessian y - u y

/--
For fixed base point and evaluation point, the superjet excess depends
continuously on the jet variables.
-/
theorem continuous_superjetExcess_jet (u : Point n -> Real) (x y : Point n) :
    Continuous fun J : Jet n => SuperjetExcess u x J y := by
  unfold SuperjetExcess
  exact continuous_const.sub (continuous_quadraticModel_jet x (u x) y)

/--
For fixed base point and evaluation point, the subjet excess depends
continuously on the jet variables.
-/
theorem continuous_subjetExcess_jet (u : Point n -> Real) (x y : Point n) :
    Continuous fun J : Jet n => SubjetExcess u x J y := by
  unfold SubjetExcess
  exact (continuous_quadraticModel_jet x (u x) y).sub continuous_const

/--
Changing the jet in the superjet excess adds exactly the quadratic model of the
difference jet. This is the algebraic estimate used before introducing the
singular `‖y - x‖^2` scale.
-/
theorem superjetExcess_eq_add_quadraticModel_sub (u : Point n -> Real)
    (x : Point n) (J K : Jet n) (y : Point n) :
    SuperjetExcess u x J y =
      SuperjetExcess u x K y +
        quadraticModel x 0 (K - J).gradient (K - J).hessian y := by
  have hq :
      quadraticModel x 0 (K.gradient - J.gradient) (K.hessian - J.hessian) y =
        quadraticModel x (u x) K.gradient K.hessian y -
          quadraticModel x (u x) J.gradient J.hessian y := by
    have h := quadraticModel_sub x (u x) (u x) K.gradient J.gradient
      K.hessian J.hessian y
    simpa using h
  simp only [Jet.sub_gradient, Jet.sub_hessian]
  rw [hq]
  unfold SuperjetExcess
  ring

/--
Changing the jet in the subjet excess adds exactly the quadratic model of the
difference jet.
-/
theorem subjetExcess_eq_add_quadraticModel_sub (u : Point n -> Real)
    (x : Point n) (J K : Jet n) (y : Point n) :
    SubjetExcess u x J y =
      SubjetExcess u x K y +
        quadraticModel x 0 (J - K).gradient (J - K).hessian y := by
  have hq :
      quadraticModel x 0 (J.gradient - K.gradient) (J.hessian - K.hessian) y =
        quadraticModel x (u x) J.gradient J.hessian y -
          quadraticModel x (u x) K.gradient K.hessian y := by
    have h := quadraticModel_sub x (u x) (u x) J.gradient K.gradient
      J.hessian K.hessian y
    simpa using h
  simp only [Jet.sub_gradient, Jet.sub_hessian]
  rw [hq]
  unfold SubjetExcess
  ring

/--
An excess is second-order nonpositive at `x` relative to `C`: for every positive
`ε`, the set of points `y` satisfying `excess y <= ε * ‖y - x‖^2` is a
relative neighborhood of `x` in `C`.

This is the epsilon form of the limsup characterization of semijets.
-/
def SecondOrderNonposWithin (C : Set (Point n)) (x : Point n)
    (excess : Point n -> Real) : Prop :=
  forall ε : Real, 0 < ε ->
    ∀ᶠ y in nhdsWithin x C, excess y <= ε * (‖y - x‖ ^ 2)

theorem superjetExcess_secondOrderNonposWithin {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet C u x) :
    SecondOrderNonposWithin C x (SuperjetExcess u x J) := by
  intro ε hε
  rcases hJ with ⟨rho, hrho, hineq⟩
  have hrhoε : ∀ᶠ y in nhdsWithin x C, ‖rho y‖ <= ε * (‖y - x‖ ^ 2) := by
    have h := hrho.bound hε
    filter_upwards [h] with y hy
    simpa using hy
  filter_upwards [hineq, hrhoε] with y hy hρy
  unfold SuperjetExcess
  have hrho_le_norm : rho y <= ‖rho y‖ := by
    simpa [Real.norm_eq_abs] using le_abs_self (rho y)
  linarith

theorem subjetExcess_secondOrderNonposWithin {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hJ : J ∈ Subjet C u x) :
    SecondOrderNonposWithin C x (SubjetExcess u x J) := by
  intro ε hε
  rcases hJ with ⟨rho, hrho, hineq⟩
  have hrhoε : ∀ᶠ y in nhdsWithin x C, ‖rho y‖ <= ε * (‖y - x‖ ^ 2) := by
    have h := hrho.bound hε
    filter_upwards [h] with y hy
    simpa using hy
  filter_upwards [hineq, hrhoε] with y hy hρy
  unfold SubjetExcess
  have hneg_rho_le_norm : -rho y <= ‖rho y‖ := by
    simpa [Real.norm_eq_abs] using neg_le_abs (rho y)
  linarith

theorem secondOrderNonposWithin_positivePart_isLittleO {C : Set (Point n)}
    {x : Point n} {excess : Point n -> Real}
    (h : SecondOrderNonposWithin C x excess) :
    SemijetRemainder C x (fun y => max (excess y) 0) := by
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hb := h c hc
  filter_upwards [hb] with y hy
  have hnonneg : 0 <= c * ‖y - x‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  have hmax : max (excess y) 0 <= c * ‖y - x‖ ^ 2 :=
    max_le hy hnonneg
  have hmax_nonneg : 0 <= max (excess y) 0 := le_max_right _ _
  simpa [Real.norm_eq_abs, abs_of_nonneg hmax_nonneg] using hmax

theorem superjet_of_superjetExcess_secondOrderNonposWithin {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J : Jet n}
    (h : SecondOrderNonposWithin C x (SuperjetExcess u x J)) :
    J ∈ Superjet C u x := by
  let rho : Point n -> Real := fun y => max (SuperjetExcess u x J y) 0
  refine ⟨rho, secondOrderNonposWithin_positivePart_isLittleO h, ?_⟩
  filter_upwards with y
  unfold rho SuperjetExcess
  have hle : u y - quadraticModel x (u x) J.gradient J.hessian y <=
      max (u y - quadraticModel x (u x) J.gradient J.hessian y) 0 :=
    le_max_left _ _
  linarith

theorem subjet_of_subjetExcess_secondOrderNonposWithin {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J : Jet n}
    (h : SecondOrderNonposWithin C x (SubjetExcess u x J)) :
    J ∈ Subjet C u x := by
  let rho : Point n -> Real := fun y => -max (SubjetExcess u x J y) 0
  have hposLittle :
      SemijetRemainder C x (fun y => max (SubjetExcess u x J y) 0) :=
    secondOrderNonposWithin_positivePart_isLittleO h
  refine ⟨rho, semijetRemainder_neg hposLittle, ?_⟩
  filter_upwards with y
  unfold rho SubjetExcess
  have hle : quadraticModel x (u x) J.gradient J.hessian y - u y <=
      max (quadraticModel x (u x) J.gradient J.hessian y - u y) 0 :=
    le_max_left _ _
  linarith

theorem superjet_iff_superjetExcess_secondOrderNonposWithin {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J : Jet n} :
    J ∈ Superjet C u x ↔ SecondOrderNonposWithin C x (SuperjetExcess u x J) :=
  ⟨superjetExcess_secondOrderNonposWithin,
    superjet_of_superjetExcess_secondOrderNonposWithin⟩

theorem subjet_iff_subjetExcess_secondOrderNonposWithin {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {J : Jet n} :
    J ∈ Subjet C u x ↔ SecondOrderNonposWithin C x (SubjetExcess u x J) :=
  ⟨subjetExcess_secondOrderNonposWithin,
    subjet_of_subjetExcess_secondOrderNonposWithin⟩

theorem superjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue
    {C : Set (Point n)} {u φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (h_le : Filter.Eventually (fun x : Point n => u x <= φ x) (nhdsWithin x0 C))
    (hφ : HasSecondOrderExpansionWithinAtValue C φ x0 (u x0) J) :
    J ∈ Superjet C u x0 := by
  rcases hφ with ⟨rho, hrho, hφ⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [h_le, hφ] with x hux hφx
  rwa [hφx] at hux

theorem subjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue
    {C : Set (Point n)} {u φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (h_le : Filter.Eventually (fun x : Point n => φ x <= u x) (nhdsWithin x0 C))
    (hφ : HasSecondOrderExpansionWithinAtValue C φ x0 (u x0) J) :
    J ∈ Subjet C u x0 := by
  rcases hφ with ⟨rho, hrho, hφ⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [h_le, hφ] with x hux hφx
  rwa [hφx] at hux

theorem superjet_iff_exists_eventually_le_hasSecondOrderExpansionWithinAtValue
    {C : Set (Point n)} {u : Point n -> Real} {x0 : Point n} {J : Jet n} :
    J ∈ Superjet C u x0 <->
      exists φ : Point n -> Real,
        Filter.Eventually (fun x : Point n => u x <= φ x) (nhdsWithin x0 C) /\
          HasSecondOrderExpansionWithinAtValue C φ x0 (u x0) J := by
  constructor
  · rintro ⟨rho, hrho, h_le⟩
    refine ⟨fun x : Point n => quadraticModel x0 (u x0) J.gradient J.hessian x + rho x,
      h_le, ?_⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards with x
    rfl
  · rintro ⟨φ, h_le, hφ⟩
    exact superjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue h_le hφ

theorem subjet_iff_exists_eventually_le_hasSecondOrderExpansionWithinAtValue
    {C : Set (Point n)} {u : Point n -> Real} {x0 : Point n} {J : Jet n} :
    J ∈ Subjet C u x0 <->
      exists φ : Point n -> Real,
        Filter.Eventually (fun x : Point n => φ x <= u x) (nhdsWithin x0 C) /\
          HasSecondOrderExpansionWithinAtValue C φ x0 (u x0) J := by
  constructor
  · rintro ⟨rho, hrho, h_le⟩
    refine ⟨fun x : Point n => quadraticModel x0 (u x0) J.gradient J.hessian x + rho x,
      h_le, ?_⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards with x
    rfl
  · rintro ⟨φ, h_le, hφ⟩
    exact subjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue h_le hφ

theorem superjet_of_touchesAbove_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (htouch : TouchesAboveOn C u φ x0)
    (hφ : HasSecondOrderExpansionWithin C φ x0 J) :
    J ∈ Superjet C u x0 := by
  rcases hφ with ⟨rho, hrho, hφ⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [htouch, hφ] with x htouchx hφx
  calc
    u x <= φ x + (u x0 - φ x0) := by linarith
    _ = quadraticModel x0 (u x0) J.gradient J.hessian x + rho x := by
      rw [hφx]
      simp [quadraticModel]
      ring

theorem subjet_of_touchesBelow_hasSecondOrderExpansionWithin
    {C : Set (Point n)} {u φ : Point n -> Real} {x0 : Point n} {J : Jet n}
    (htouch : TouchesBelowOn C u φ x0)
    (hφ : HasSecondOrderExpansionWithin C φ x0 J) :
    J ∈ Subjet C u x0 := by
  rcases hφ with ⟨rho, hrho, hφ⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [htouch, hφ] with x htouchx hφx
  calc
    quadraticModel x0 (u x0) J.gradient J.hessian x + rho x =
        φ x + (u x0 - φ x0) := by
      rw [hφx]
      simp [quadraticModel]
      ring
    _ <= u x := by linarith

end ViscositySolns
