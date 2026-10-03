/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Calculus.QuadraticControl

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Semijet calculus (ShiftsClosedness)

Part of the calculus lemmas for second-order superjets and subjets.
Split from `Calculus.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Adding a function with second-order expansion shifts superjets by its jet.
-/
theorem superjet_add_hasSecondOrderExpansionWithin {C : Set (Point n)}
    {u φ : Point n -> Real} {x : Point n} {J A : Jet n}
    (hJ : J ∈ Superjet C u x)
    (hφ : HasSecondOrderExpansionWithin C φ x A) :
    J + A ∈ Superjet C (fun y => u y + φ y) x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  rcases hφ with ⟨sigma, hsigma, hphi⟩
  refine ⟨fun y => rho y + sigma y, semijetRemainder_add hrho hsigma, ?_⟩
  filter_upwards [hu, hphi] with y huy hphiy
  rw [Jet.add_gradient, Jet.add_hessian, quadraticModel_add]
  rw [hphiy]
  linarith

/--
Adding a function with second-order expansion shifts subjets by its jet.
-/
theorem subjet_add_hasSecondOrderExpansionWithin {C : Set (Point n)}
    {u φ : Point n -> Real} {x : Point n} {J A : Jet n}
    (hJ : J ∈ Subjet C u x)
    (hφ : HasSecondOrderExpansionWithin C φ x A) :
    J + A ∈ Subjet C (fun y => u y + φ y) x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  rcases hφ with ⟨sigma, hsigma, hphi⟩
  refine ⟨fun y => rho y + sigma y, semijetRemainder_add hrho hsigma, ?_⟩
  filter_upwards [hu, hphi] with y huy hphiy
  rw [Jet.add_gradient, Jet.add_hessian, quadraticModel_add]
  rw [hphiy]
  linarith

/--
Subtracting the jet of a function with second-order expansion pulls back a
superjet of `u + φ` to a superjet of `u`.
-/
theorem superjet_sub_of_add_hasSecondOrderExpansionWithin {C : Set (Point n)}
    {u φ : Point n -> Real} {x : Point n} {J A : Jet n}
    (hJ : J ∈ Superjet C (fun y => u y + φ y) x)
    (hφ : HasSecondOrderExpansionWithin C φ x A) :
    J - A ∈ Superjet C u x := by
  rcases hJ with ⟨rho, hrho, huφ⟩
  rcases hφ with ⟨sigma, hsigma, hphi⟩
  refine ⟨fun y => rho y - sigma y, semijetRemainder_sub hrho hsigma, ?_⟩
  filter_upwards [huφ, hphi] with y huy hphiy
  calc
    u y = (u y + φ y) - φ y := by ring
    _ <= (quadraticModel x ((fun y => u y + φ y) x) J.gradient J.hessian y +
          rho y) - φ y := by
      linarith
    _ = (quadraticModel x ((fun y => u y + φ y) x) J.gradient J.hessian y +
          rho y) - (quadraticModel x (φ x) A.gradient A.hessian y + sigma y) := by
      rw [hphiy]
    _ = quadraticModel x (u x) (J - A).gradient (J - A).hessian y +
          (rho y - sigma y) := by
      have hq :
          quadraticModel x (u x) (J.gradient - A.gradient) (J.hessian - A.hessian) y =
            quadraticModel x (u x + φ x) J.gradient J.hessian y -
              quadraticModel x (φ x) A.gradient A.hessian y := by
        have h := quadraticModel_sub x (u x + φ x) (φ x) J.gradient A.gradient
          J.hessian A.hessian y
        simpa using h
      simp only [Jet.sub_gradient, Jet.sub_hessian]
      rw [hq]
      ring

/--
Subtracting the jet of a function with second-order expansion pulls back a
subjet of `u + φ` to a subjet of `u`.
-/
theorem subjet_sub_of_add_hasSecondOrderExpansionWithin {C : Set (Point n)}
    {u φ : Point n -> Real} {x : Point n} {J A : Jet n}
    (hJ : J ∈ Subjet C (fun y => u y + φ y) x)
    (hφ : HasSecondOrderExpansionWithin C φ x A) :
    J - A ∈ Subjet C u x := by
  rcases hJ with ⟨rho, hrho, huφ⟩
  rcases hφ with ⟨sigma, hsigma, hphi⟩
  refine ⟨fun y => rho y - sigma y, semijetRemainder_sub hrho hsigma, ?_⟩
  filter_upwards [huφ, hphi] with y huy hphiy
  calc
    quadraticModel x (u x) (J - A).gradient (J - A).hessian y +
        (rho y - sigma y) =
        (quadraticModel x ((fun y => u y + φ y) x) J.gradient J.hessian y +
          rho y) - (quadraticModel x (φ x) A.gradient A.hessian y + sigma y) := by
      have hq :
          quadraticModel x (u x) (J.gradient - A.gradient) (J.hessian - A.hessian) y =
            quadraticModel x (u x + φ x) J.gradient J.hessian y -
              quadraticModel x (φ x) A.gradient A.hessian y := by
        have h := quadraticModel_sub x (u x + φ x) (φ x) J.gradient A.gradient
          J.hessian A.hessian y
        simpa using h
      simp only [Jet.sub_gradient, Jet.sub_hessian]
      rw [hq]
      ring
    _ = (quadraticModel x ((fun y => u y + φ y) x) J.gradient J.hessian y +
          rho y) - φ y := by
      rw [hphiy]
    _ <= (u y + φ y) - φ y := by linarith
    _ = u y := by ring

/--
Shift equivalence for superjets under addition of a function with second-order
expansion.
-/
theorem superjet_add_hasSecondOrderExpansionWithin_iff {C : Set (Point n)}
    {u φ : Point n -> Real} {x : Point n} {J A : Jet n}
    (hφ : HasSecondOrderExpansionWithin C φ x A) :
    J ∈ Superjet C (fun y => u y + φ y) x ↔ J - A ∈ Superjet C u x := by
  constructor
  · intro hJ
    exact superjet_sub_of_add_hasSecondOrderExpansionWithin hJ hφ
  · intro hJ
    have h := superjet_add_hasSecondOrderExpansionWithin hJ hφ
    have hEq : J - A + A = J := sub_add_cancel J A
    simpa [hEq] using h

/--
Shift equivalence for subjets under addition of a function with second-order
expansion.
-/
theorem subjet_add_hasSecondOrderExpansionWithin_iff {C : Set (Point n)}
    {u φ : Point n -> Real} {x : Point n} {J A : Jet n}
    (hφ : HasSecondOrderExpansionWithin C φ x A) :
    J ∈ Subjet C (fun y => u y + φ y) x ↔ J - A ∈ Subjet C u x := by
  constructor
  · intro hJ
    exact subjet_sub_of_add_hasSecondOrderExpansionWithin hJ hφ
  · intro hJ
    have h := subjet_add_hasSecondOrderExpansionWithin hJ hφ
    have hEq : J - A + A = J := sub_add_cancel J A
    simpa [hEq] using h

/--
Enlarging the Hessian of a superjet preserves membership. This is the basic
Loewner-order monotonicity of second-order superjets.
-/
theorem superjet_mono_hessian {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} {Y : Hessian n}
    (hJ : J ∈ Superjet C u x) (hXY : J.hessian <= Y) :
    ({ gradient := J.gradient, hessian := Y } : Jet n) ∈ Superjet C u x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hu] with y huy
  calc
    u y <= quadraticModel x (u x) J.gradient J.hessian y + rho y := huy
    _ <= quadraticModel x (u x) J.gradient Y y + rho y := by
      have hq : quadraticModel x (u x) J.gradient J.hessian y <=
          quadraticModel x (u x) J.gradient Y y :=
        quadraticModel_le_of_hessian_le hXY y
      linarith

/--
Shrinking the Hessian of a subjet preserves membership. This is the subjet
counterpart to `superjet_mono_hessian`.
-/
theorem subjet_mono_hessian {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} {Y : Hessian n}
    (hJ : J ∈ Subjet C u x) (hYX : Y <= J.hessian) :
    ({ gradient := J.gradient, hessian := Y } : Jet n) ∈ Subjet C u x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hu] with y huy
  calc
    quadraticModel x (u x) J.gradient Y y + rho y <=
        quadraticModel x (u x) J.gradient J.hessian y + rho y := by
      have hq : quadraticModel x (u x) J.gradient Y y <=
          quadraticModel x (u x) J.gradient J.hessian y :=
        quadraticModel_le_of_hessian_le hYX y
      linarith
    _ <= u y := huy

/--
A positive identity-Hessian perturbation turns a superjet into an eventual
ordinary upper support with no remainder term.
-/
theorem eventually_le_quadraticModel_hessian_add_identity_of_superjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    {δ : Real} (hδ : 0 < δ) (hJ : J ∈ Superjet C u x) :
    ∀ᶠ y in nhdsWithin x C,
      u y <= quadraticModel x (u x) J.gradient (J.hessian + δ • (1 : Hessian n)) y := by
  rcases hJ with ⟨rho, hrho, hu⟩
  have hcoef_pos : 0 < (1 / 2 : Real) * δ := by positivity
  have hrho_bound : ∀ᶠ y in nhdsWithin x C,
      ‖rho y‖ <= ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 := by
    filter_upwards [hrho.bound hcoef_pos] with y hy
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcoef_pos.le (sq_nonneg ‖y - x‖))] using hy
  filter_upwards [hu, hrho_bound] with y huy hρ
  have hρ_le : rho y <= ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 := by
    have hρ_abs : rho y <= ‖rho y‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (rho y)
    exact hρ_abs.trans hρ
  have hidentity :
      ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 <=
        quadraticModel x 0 0 (δ • (1 : Hessian n)) y :=
    quadraticModel_scalar_identity_lower_bound x y hδ.le
  have hsplit :
      quadraticModel x (u x) J.gradient (J.hessian + δ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y +
          quadraticModel x 0 0 (δ • (1 : Hessian n)) y := by
    simpa using
      (quadraticModel_add x (u x) 0 J.gradient 0
        J.hessian (δ • (1 : Hessian n)) y)
  calc
    u y <= quadraticModel x (u x) J.gradient J.hessian y + rho y := huy
    _ <= quadraticModel x (u x) J.gradient J.hessian y +
        ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 := by linarith
    _ <= quadraticModel x (u x) J.gradient J.hessian y +
        quadraticModel x 0 0 (δ • (1 : Hessian n)) y := by linarith
    _ = quadraticModel x (u x) J.gradient (J.hessian + δ • (1 : Hessian n)) y :=
      hsplit.symm

/--
A positive identity-Hessian subtraction turns a subjet into an eventual
ordinary lower support with no remainder term.
-/
theorem eventually_quadraticModel_hessian_sub_identity_le_of_subjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    {δ : Real} (hδ : 0 < δ) (hJ : J ∈ Subjet C u x) :
    ∀ᶠ y in nhdsWithin x C,
      quadraticModel x (u x) J.gradient (J.hessian - δ • (1 : Hessian n)) y <= u y := by
  rcases hJ with ⟨rho, hrho, hu⟩
  have hcoef_pos : 0 < (1 / 2 : Real) * δ := by positivity
  have hrho_bound : ∀ᶠ y in nhdsWithin x C,
      ‖rho y‖ <= ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 := by
    filter_upwards [hrho.bound hcoef_pos] with y hy
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcoef_pos.le (sq_nonneg ‖y - x‖))] using hy
  filter_upwards [hu, hrho_bound] with y huy hρ
  have hnegρ_le : -rho y <= ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 := by
    have hρ_abs : -rho y <= ‖rho y‖ := by
      simpa [Real.norm_eq_abs] using neg_le_abs (rho y)
    exact hρ_abs.trans hρ
  have hidentity :
      ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 <=
        quadraticModel x 0 0 (δ • (1 : Hessian n)) y :=
    quadraticModel_scalar_identity_lower_bound x y hδ.le
  have hsplit :
      quadraticModel x (u x) J.gradient (J.hessian - δ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y -
          quadraticModel x 0 0 (δ • (1 : Hessian n)) y := by
    simpa using
      (quadraticModel_sub x (u x) 0 J.gradient 0
        J.hessian (δ • (1 : Hessian n)) y)
  calc
    quadraticModel x (u x) J.gradient (J.hessian - δ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y -
          quadraticModel x 0 0 (δ • (1 : Hessian n)) y := hsplit
    _ <= quadraticModel x (u x) J.gradient J.hessian y -
        ((1 / 2 : Real) * δ) * ‖y - x‖ ^ 2 := by linarith
    _ <= quadraticModel x (u x) J.gradient J.hessian y + rho y := by linarith
    _ <= u y := huy

/--
A lifted, downward-bent subjet quadratic is strictly below the function at
nearby points where the vertical lift is smaller than the bend margin.

The constant `1 / 4` leaves half of the identity-Hessian bend to absorb the
subjet `o(|y-x|^2)` remainder and half as a strict gap. This is the local
estimate needed before choosing annulus radii in the Perron bump argument.
-/
theorem eventually_quadraticModel_lift_hessian_sub_identity_lt_of_subjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    {δ γ : Real} (hγ : 0 < γ) (hJ : J ∈ Subjet C u x) :
    ∀ᶠ y in nhdsWithin x C,
      δ < ((1 / 4 : Real) * γ) * ‖y - x‖ ^ 2 ->
        quadraticModel x (u x + δ) J.gradient
            (J.hessian - γ • (1 : Hessian n)) y < u y := by
  rcases hJ with ⟨rho, hrho, hu⟩
  have hcoef_pos : 0 < (1 / 4 : Real) * γ := by positivity
  have hrho_bound : ∀ᶠ y in nhdsWithin x C,
      ‖rho y‖ <= ((1 / 4 : Real) * γ) * ‖y - x‖ ^ 2 := by
    filter_upwards [hrho.bound hcoef_pos] with y hy
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcoef_pos.le (sq_nonneg ‖y - x‖))] using hy
  filter_upwards [hu, hrho_bound] with y huy hρ hmargin
  have hnegρ_le : -rho y <= ((1 / 4 : Real) * γ) * ‖y - x‖ ^ 2 := by
    have hρ_abs : -rho y <= ‖rho y‖ := by
      simpa [Real.norm_eq_abs] using neg_le_abs (rho y)
    exact hρ_abs.trans hρ
  have hidentity :
      ((1 / 2 : Real) * γ) * ‖y - x‖ ^ 2 <=
        quadraticModel x 0 0 (γ • (1 : Hessian n)) y :=
    quadraticModel_scalar_identity_lower_bound x y hγ.le
  have hsplit :
      quadraticModel x (u x + δ) J.gradient (J.hessian - γ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y + δ -
          quadraticModel x 0 0 (γ • (1 : Hessian n)) y := by
    have hsub :
        quadraticModel x (u x) J.gradient (J.hessian - γ • (1 : Hessian n)) y =
          quadraticModel x (u x) J.gradient J.hessian y -
            quadraticModel x 0 0 (γ • (1 : Hessian n)) y := by
      simpa using
        (quadraticModel_sub x (u x) 0 J.gradient 0
          J.hessian (γ • (1 : Hessian n)) y)
    calc
      quadraticModel x (u x + δ) J.gradient (J.hessian - γ • (1 : Hessian n)) y =
          quadraticModel x (u x) J.gradient (J.hessian - γ • (1 : Hessian n)) y +
            δ := by
            simp [quadraticModel]
            ring
      _ = quadraticModel x (u x) J.gradient J.hessian y + δ -
          quadraticModel x 0 0 (γ • (1 : Hessian n)) y := by
            rw [hsub]
            ring
  calc
    quadraticModel x (u x + δ) J.gradient
        (J.hessian - γ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y + δ -
          quadraticModel x 0 0 (γ • (1 : Hessian n)) y := hsplit
    _ <= quadraticModel x (u x) J.gradient J.hessian y + δ -
        ((1 / 2 : Real) * γ) * ‖y - x‖ ^ 2 := by linarith
    _ < quadraticModel x (u x) J.gradient J.hessian y + rho y := by linarith
    _ <= u y := huy

/--
Uniform version of
`eventually_quadraticModel_lift_hessian_sub_identity_lt_of_subjet`: for a
fixed downward identity-Hessian bend, one relative neighborhood works for all
vertical lifts that fit inside the bend margin at the evaluation point.
-/
theorem eventually_forall_quadraticModel_lift_hessian_sub_identity_lt_of_subjet
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    {γ : Real} (hγ : 0 < γ) (hJ : J ∈ Subjet C u x) :
    ∀ᶠ y in nhdsWithin x C, ∀ δ : Real,
      δ < ((1 / 4 : Real) * γ) * ‖y - x‖ ^ 2 ->
        quadraticModel x (u x + δ) J.gradient
            (J.hessian - γ • (1 : Hessian n)) y < u y := by
  rcases hJ with ⟨rho, hrho, hu⟩
  have hcoef_pos : 0 < (1 / 4 : Real) * γ := by positivity
  have hrho_bound : ∀ᶠ y in nhdsWithin x C,
      ‖rho y‖ <= ((1 / 4 : Real) * γ) * ‖y - x‖ ^ 2 := by
    filter_upwards [hrho.bound hcoef_pos] with y hy
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcoef_pos.le (sq_nonneg ‖y - x‖))] using hy
  filter_upwards [hu, hrho_bound] with y huy hρ δ hmargin
  have hnegρ_le : -rho y <= ((1 / 4 : Real) * γ) * ‖y - x‖ ^ 2 := by
    have hρ_abs : -rho y <= ‖rho y‖ := by
      simpa [Real.norm_eq_abs] using neg_le_abs (rho y)
    exact hρ_abs.trans hρ
  have hidentity :
      ((1 / 2 : Real) * γ) * ‖y - x‖ ^ 2 <=
        quadraticModel x 0 0 (γ • (1 : Hessian n)) y :=
    quadraticModel_scalar_identity_lower_bound x y hγ.le
  have hsplit :
      quadraticModel x (u x + δ) J.gradient (J.hessian - γ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y + δ -
          quadraticModel x 0 0 (γ • (1 : Hessian n)) y := by
    have hsub :
        quadraticModel x (u x) J.gradient (J.hessian - γ • (1 : Hessian n)) y =
          quadraticModel x (u x) J.gradient J.hessian y -
            quadraticModel x 0 0 (γ • (1 : Hessian n)) y := by
      simpa using
        (quadraticModel_sub x (u x) 0 J.gradient 0
          J.hessian (γ • (1 : Hessian n)) y)
    calc
      quadraticModel x (u x + δ) J.gradient (J.hessian - γ • (1 : Hessian n)) y =
          quadraticModel x (u x) J.gradient (J.hessian - γ • (1 : Hessian n)) y +
            δ := by
            simp [quadraticModel]
            ring
      _ = quadraticModel x (u x) J.gradient J.hessian y + δ -
          quadraticModel x 0 0 (γ • (1 : Hessian n)) y := by
            rw [hsub]
            ring
  calc
    quadraticModel x (u x + δ) J.gradient
        (J.hessian - γ • (1 : Hessian n)) y =
        quadraticModel x (u x) J.gradient J.hessian y + δ -
          quadraticModel x 0 0 (γ • (1 : Hessian n)) y := hsplit
    _ <= quadraticModel x (u x) J.gradient J.hessian y + δ -
        ((1 / 2 : Real) * γ) * ‖y - x‖ ^ 2 := by linarith
    _ < quadraticModel x (u x) J.gradient J.hessian y + rho y := by linarith
    _ <= u y := huy

/--
If all positive identity-Hessian enlargements of a fixed-gradient jet are
superjets, then the limiting jet is a superjet. This is the asymptotic half of
CIL Remark 2.6(i)'s fixed-gradient closedness statement.
-/
theorem superjet_of_forall_add_pos_smul_one {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {p : Point n} {X : Hessian n}
    (h : ∀ δ : Real, 0 < δ ->
      ({ gradient := p, hessian := X + δ • (1 : Hessian n) } : Jet n) ∈ Superjet C u x) :
    ({ gradient := p, hessian := X } : Jet n) ∈ Superjet C u x := by
  refine superjet_of_superjetExcess_secondOrderNonposWithin ?_
  intro ε hε
  let denom : Real := (n : Real) + 1
  have hdenom_pos : 0 < denom := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  let δ : Real := ε / denom
  have hδ : 0 < δ := div_pos hε hdenom_pos
  let J0 : Jet n := { gradient := p, hessian := X }
  let Jδ : Jet n := { gradient := p, hessian := X + δ • (1 : Hessian n) }
  have hJδ : Jδ ∈ Superjet C u x := h δ hδ
  have hbase := superjetExcess_secondOrderNonposWithin hJδ (ε / 2) (by linarith)
  have hcoef : (1 / 2 : Real) * δ * (n : Real) <= ε / 2 := by
    have hn_nonneg : 0 <= (n : Real) := Nat.cast_nonneg n
    have hfrac : (n : Real) / denom <= 1 := by
      rw [div_le_one hdenom_pos]
      dsimp [denom]
      linarith
    calc
      (1 / 2 : Real) * δ * (n : Real) = (ε / 2) * ((n : Real) / denom) := by
        dsimp [δ]
        field_simp [hdenom_pos.ne']
      _ <= (ε / 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hfrac (by linarith)
      _ = ε / 2 := by ring
  filter_upwards [hbase] with y hy
  have hpert : quadraticModel x 0 (Jδ - J0).gradient (Jδ - J0).hessian y <=
      (ε / 2) * ‖y - x‖ ^ 2 := by
    have hquad : quadraticModel x 0 0 (δ • (1 : Hessian n)) y <=
        ((1 / 2 : Real) * δ * (n : Real)) * ‖y - x‖ ^ 2 :=
      quadraticModel_scalar_identity_bound x y hδ.le
    have hcoef_mul : ((1 / 2 : Real) * δ * (n : Real)) * ‖y - x‖ ^ 2 <=
        (ε / 2) * ‖y - x‖ ^ 2 := by
      gcongr
    calc
      quadraticModel x 0 (Jδ - J0).gradient (Jδ - J0).hessian y =
          quadraticModel x 0 0 (δ • (1 : Hessian n)) y := by
        simp [Jδ, J0]
      _ <= ((1 / 2 : Real) * δ * (n : Real)) * ‖y - x‖ ^ 2 := hquad
      _ <= (ε / 2) * ‖y - x‖ ^ 2 := hcoef_mul
  have hformula := superjetExcess_eq_add_quadraticModel_sub u x J0 Jδ y
  change SuperjetExcess u x J0 y <= ε * ‖y - x‖ ^ 2
  rw [hformula]
  nlinarith [sq_nonneg ‖y - x‖]

/--
If all positive identity-Hessian shrinkings of a fixed-gradient jet are subjets,
then the limiting jet is a subjet.
-/
theorem subjet_of_forall_sub_pos_smul_one {C : Set (Point n)}
    {u : Point n -> Real} {x : Point n} {p : Point n} {X : Hessian n}
    (h : ∀ δ : Real, 0 < δ ->
      ({ gradient := p, hessian := X - δ • (1 : Hessian n) } : Jet n) ∈ Subjet C u x) :
    ({ gradient := p, hessian := X } : Jet n) ∈ Subjet C u x := by
  refine subjet_of_subjetExcess_secondOrderNonposWithin ?_
  intro ε hε
  let denom : Real := (n : Real) + 1
  have hdenom_pos : 0 < denom := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  let δ : Real := ε / denom
  have hδ : 0 < δ := div_pos hε hdenom_pos
  let J0 : Jet n := { gradient := p, hessian := X }
  let Jδ : Jet n := { gradient := p, hessian := X - δ • (1 : Hessian n) }
  have hJδ : Jδ ∈ Subjet C u x := h δ hδ
  have hbase := subjetExcess_secondOrderNonposWithin hJδ (ε / 2) (by linarith)
  have hcoef : (1 / 2 : Real) * δ * (n : Real) <= ε / 2 := by
    have hn_nonneg : 0 <= (n : Real) := Nat.cast_nonneg n
    have hfrac : (n : Real) / denom <= 1 := by
      rw [div_le_one hdenom_pos]
      dsimp [denom]
      linarith
    calc
      (1 / 2 : Real) * δ * (n : Real) = (ε / 2) * ((n : Real) / denom) := by
        dsimp [δ]
        field_simp [hdenom_pos.ne']
      _ <= (ε / 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hfrac (by linarith)
      _ = ε / 2 := by ring
  filter_upwards [hbase] with y hy
  have hpert : quadraticModel x 0 (J0 - Jδ).gradient (J0 - Jδ).hessian y <=
      (ε / 2) * ‖y - x‖ ^ 2 := by
    have hquad : quadraticModel x 0 0 (δ • (1 : Hessian n)) y <=
        ((1 / 2 : Real) * δ * (n : Real)) * ‖y - x‖ ^ 2 :=
      quadraticModel_scalar_identity_bound x y hδ.le
    have hcoef_mul : ((1 / 2 : Real) * δ * (n : Real)) * ‖y - x‖ ^ 2 <=
        (ε / 2) * ‖y - x‖ ^ 2 := by
      gcongr
    calc
      quadraticModel x 0 (J0 - Jδ).gradient (J0 - Jδ).hessian y =
          quadraticModel x 0 0 (δ • (1 : Hessian n)) y := by
        simp [Jδ, J0]
      _ <= ((1 / 2 : Real) * δ * (n : Real)) * ‖y - x‖ ^ 2 := hquad
      _ <= (ε / 2) * ‖y - x‖ ^ 2 := hcoef_mul
  have hformula := subjetExcess_eq_add_quadraticModel_sub u x J0 Jδ y
  change SubjetExcess u x J0 y <= ε * ‖y - x‖ ^ 2
  rw [hformula]
  nlinarith [sq_nonneg ‖y - x‖]

/--
For fixed gradient `p`, the Hessian slice of an ordinary superjet fiber is
closed. This is CIL Remark 2.6(i)'s closedness statement for
`{X | (p, X) ∈ J^{2,+} u(x)}`.
-/
theorem isClosed_superjet_hessian_slice (C : Set (Point n)) (u : Point n -> Real)
    (x : Point n) (p : Point n) :
    IsClosed {X : Hessian n | ({ gradient := p, hessian := X } : Jet n) ∈ Superjet C u x} := by
  rw [← closure_subset_iff_isClosed]
  intro X hX
  refine superjet_of_superjetExcess_secondOrderNonposWithin ?_
  intro ε hε
  let denom : Real := (n : Real) * (n : Real) + 1
  have hdenom_pos : 0 < denom := by
    have hn2 : 0 <= (n : Real) * (n : Real) :=
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
    dsimp [denom]
    linarith
  let η : Real := ε / denom
  have hηpos : 0 < η := div_pos hε hdenom_pos
  have hηnonneg : 0 <= η := hηpos.le
  have hnbhd : {Y : Hessian n | ∀ i j : Fin n, |(Y - X) i j| < η} ∈ nhds X :=
    hessian_eventually_entrywise_abs_sub_lt X hηpos
  rcases (mem_closure_iff_nhds.mp hX _ hnbhd) with ⟨Y, hYclose, hYjet⟩
  have hbase := superjetExcess_secondOrderNonposWithin hYjet (ε / 2) (by linarith)
  have hcoef : (1 / 2 : Real) * η * (n : Real) * (n : Real) <= ε / 2 := by
    have hn2_nonneg : 0 <= (n : Real) * (n : Real) :=
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
    have hfrac : ((n : Real) * (n : Real)) / denom <= 1 := by
      rw [div_le_one hdenom_pos]
      dsimp [denom]
      linarith
    calc
      (1 / 2 : Real) * η * (n : Real) * (n : Real) =
          (ε / 2) * (((n : Real) * (n : Real)) / denom) := by
        dsimp [η]
        field_simp [hdenom_pos.ne']
      _ <= (ε / 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hfrac (by linarith)
      _ = ε / 2 := by ring
  filter_upwards [hbase] with y hy
  let JX : Jet n := { gradient := p, hessian := X }
  let JY : Jet n := { gradient := p, hessian := Y }
  have hA : ∀ i j : Fin n, |(Y - X) i j| <= η := by
    intro i j
    exact (hYclose i j).le
  have hquad_abs : |quadraticModel x 0 0 (Y - X) y| <=
      ((1 / 2 : Real) * η * (n : Real) * (n : Real)) * ‖y - x‖ ^ 2 :=
    abs_quadraticModel_zero_zero_le_of_entrywise_abs_le x y hηnonneg hA
  have hquad : quadraticModel x 0 (JY - JX).gradient (JY - JX).hessian y <=
      (ε / 2) * ‖y - x‖ ^ 2 := by
    have hq1 : quadraticModel x 0 (JY - JX).gradient (JY - JX).hessian y =
        quadraticModel x 0 0 (Y - X) y := by
      simp [JY, JX]
    rw [hq1]
    have hle_abs :
        quadraticModel x 0 0 (Y - X) y <= |quadraticModel x 0 0 (Y - X) y| :=
      le_abs_self _
    exact hle_abs.trans (hquad_abs.trans (by gcongr))
  have hformula := superjetExcess_eq_add_quadraticModel_sub u x JX JY y
  change SuperjetExcess u x JX y <= ε * ‖y - x‖ ^ 2
  rw [hformula]
  nlinarith [sq_nonneg ‖y - x‖]

/--
For fixed gradient `p`, the Hessian slice of an ordinary subjet fiber is closed.
-/
theorem isClosed_subjet_hessian_slice (C : Set (Point n)) (u : Point n -> Real)
    (x : Point n) (p : Point n) :
    IsClosed {X : Hessian n | ({ gradient := p, hessian := X } : Jet n) ∈ Subjet C u x} := by
  rw [← closure_subset_iff_isClosed]
  intro X hX
  refine subjet_of_subjetExcess_secondOrderNonposWithin ?_
  intro ε hε
  let denom : Real := (n : Real) * (n : Real) + 1
  have hdenom_pos : 0 < denom := by
    have hn2 : 0 <= (n : Real) * (n : Real) :=
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
    dsimp [denom]
    linarith
  let η : Real := ε / denom
  have hηpos : 0 < η := div_pos hε hdenom_pos
  have hηnonneg : 0 <= η := hηpos.le
  have hnbhd : {Y : Hessian n | ∀ i j : Fin n, |(Y - X) i j| < η} ∈ nhds X :=
    hessian_eventually_entrywise_abs_sub_lt X hηpos
  rcases (mem_closure_iff_nhds.mp hX _ hnbhd) with ⟨Y, hYclose, hYjet⟩
  have hbase := subjetExcess_secondOrderNonposWithin hYjet (ε / 2) (by linarith)
  have hcoef : (1 / 2 : Real) * η * (n : Real) * (n : Real) <= ε / 2 := by
    have hn2_nonneg : 0 <= (n : Real) * (n : Real) :=
      mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n)
    have hfrac : ((n : Real) * (n : Real)) / denom <= 1 := by
      rw [div_le_one hdenom_pos]
      dsimp [denom]
      linarith
    calc
      (1 / 2 : Real) * η * (n : Real) * (n : Real) =
          (ε / 2) * (((n : Real) * (n : Real)) / denom) := by
        dsimp [η]
        field_simp [hdenom_pos.ne']
      _ <= (ε / 2) * 1 := by
        exact mul_le_mul_of_nonneg_left hfrac (by linarith)
      _ = ε / 2 := by ring
  filter_upwards [hbase] with y hy
  let JX : Jet n := { gradient := p, hessian := X }
  let JY : Jet n := { gradient := p, hessian := Y }
  have hA : ∀ i j : Fin n, |(X - Y) i j| <= η := by
    intro i j
    have hclose := (hYclose i j).le
    simpa [Pi.sub_apply, abs_sub_comm] using hclose
  have hquad_abs : |quadraticModel x 0 0 (X - Y) y| <=
      ((1 / 2 : Real) * η * (n : Real) * (n : Real)) * ‖y - x‖ ^ 2 :=
    abs_quadraticModel_zero_zero_le_of_entrywise_abs_le x y hηnonneg hA
  have hquad : quadraticModel x 0 (JX - JY).gradient (JX - JY).hessian y <=
      (ε / 2) * ‖y - x‖ ^ 2 := by
    have hq1 : quadraticModel x 0 (JX - JY).gradient (JX - JY).hessian y =
        quadraticModel x 0 0 (X - Y) y := by
      simp [JY, JX]
    rw [hq1]
    have hle_abs :
        quadraticModel x 0 0 (X - Y) y <= |quadraticModel x 0 0 (X - Y) y| :=
      le_abs_self _
    exact hle_abs.trans (hquad_abs.trans (by gcongr))
  have hformula := subjetExcess_eq_add_quadraticModel_sub u x JX JY y
  change SubjetExcess u x JX y <= ε * ‖y - x‖ ^ 2
  rw [hformula]
  nlinarith [sq_nonneg ‖y - x‖]

/--
Neg duality for superjets (CIL Remark 2.6): `J` is a superjet of `u` at `x`
if and only if the negated jet `J.neg` is a subjet of `-u` at `x`.
-/
theorem superjet_neg_iff_subjet {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} :
    J ∈ Superjet C u x ↔ J.neg ∈ Subjet C (fun y => -u y) x := by
  constructor
  · rintro ⟨ρ, hρ, hle⟩
    refine ⟨fun y => -ρ y, hρ.neg_left, ?_⟩
    filter_upwards [hle] with y hy
    simp only [Jet.neg_gradient, Jet.neg_hessian, quadraticModel_neg]
    linarith
  · rintro ⟨ρ, hρ, hle⟩
    refine ⟨fun y => -ρ y, hρ.neg_left, ?_⟩
    filter_upwards [hle] with y hy
    simp only [Jet.neg_gradient, Jet.neg_hessian, quadraticModel_neg] at hy
    linarith

/--
Neg duality for subjets (CIL Remark 2.6): `J` is a subjet of `u` at `x`
if and only if the negated jet `J.neg` is a superjet of `-u` at `x`.
-/
theorem subjet_neg_iff_superjet {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} :
    J ∈ Subjet C u x ↔ J.neg ∈ Superjet C (fun y => -u y) x := by
  constructor
  · rintro ⟨ρ, hρ, hle⟩
    refine ⟨fun y => -ρ y, hρ.neg_left, ?_⟩
    filter_upwards [hle] with y hy
    simp only [Jet.neg_gradient, Jet.neg_hessian, quadraticModel_neg]
    linarith
  · rintro ⟨ρ, hρ, hle⟩
    refine ⟨fun y => -ρ y, hρ.neg_left, ?_⟩
    filter_upwards [hle] with y hy
    simp only [Jet.neg_gradient, Jet.neg_hessian, quadraticModel_neg] at hy
    linarith

end ViscositySolns
