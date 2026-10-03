/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Solutions
public import LeanPool.ViscositySolutionTheory.ViscositySolns.TestFunctions.Taylor

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Smooth test functions for viscosity solutions

This file packages the Taylor bridge for `C^2` test functions into the
subsolution and supersolution inequalities.
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The coordinate jet obtained from mathlib's canonical first and second
`fderivWithin` maps for a test function on a set.
-/
def smoothTestJetWithin (C : Set (Point n)) (φ : Point n -> Real) (x : Point n) : Jet n :=
  Jet.ofDerivatives (fderivWithin Real φ C x)
    (fderivWithin Real (fderivWithin Real φ C) C x)

/--
The canonical smooth test jet only depends on the germ of the domain at the
base point.
-/
theorem smoothTestJetWithin_congr_nhdsWithin
    {C D : Set (Point n)} {φ : Point n -> Real} {x : Point n}
    (h : nhdsWithin x C = nhdsWithin x D) :
    smoothTestJetWithin C φ x = smoothTestJetWithin D φ x := by
  have hEq : C =ᶠ[nhds x] D := nhdsWithin_eq_iff_eventuallyEqSet.mp h
  have hDφ : fderivWithin Real φ C x = fderivWithin Real φ D x :=
    fderivWithin_congr_set hEq
  have hD2φ :
      fderivWithin Real (fderivWithin Real φ C) C x =
        fderivWithin Real (fderivWithin Real φ D) D x :=
    fderivWithin_fderivWithin_eq_of_eventuallyEqSet (𝕜 := Real) (f := φ) hEq
  rw [smoothTestJetWithin, smoothTestJetWithin, hDφ, hD2φ]

/--
The canonical smooth test jet varies continuously on the domain whenever the
test function is `C^2` there.
-/
theorem continuousOn_smoothTestJetWithin
    {C : Set (Point n)} {φ : Point n -> Real}
    (huniq : UniqueDiffOn Real C)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C) :
    ContinuousOn (smoothTestJetWithin C φ) C := by
  have hDφ_cont :
      ContinuousOn (fderivWithin Real φ C) C :=
    hφ.continuousOn_fderivWithin huniq (by norm_num)
  have hDφ_cd :
      ContDiffOn Real (1 : ℕ∞ω) (fderivWithin Real φ C) C :=
    hφ.fderivWithin (m := (1 : ℕ∞ω)) huniq (by norm_num)
  have hD2φ_cont :
      ContinuousOn (fderivWithin Real (fderivWithin Real φ C) C) C :=
    hDφ_cd.continuousOn_fderivWithin huniq (by norm_num)
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_induced_rng.mpr ?_
  have hgrad :
      Continuous fun x : C =>
        linearMapGradient (fderivWithin Real φ C x) := by
    exact continuous_pi fun i =>
      hDφ_cont.domRestrict.clm_apply continuous_const
  have hhess :
      Continuous fun x : C =>
        bilinearMapHessian (fderivWithin Real (fderivWithin Real φ C) C x) := by
    exact continuous_pi fun i =>
      continuous_pi fun j =>
        ((hD2φ_cont.domRestrict.clm_apply continuous_const).clm_apply continuous_const)
  exact hgrad.prodMk hhess

/--
A viscosity subsolution satisfies the expected inequality for every `C^2`
test function touching from above, provided its canonical `fderivWithin` data
matches the coordinate jet.
-/
theorem ViscositySubsolution.of_touchesAbove_contDiffOn_two
    {C : Set (Point n)} {F : Operator n} {u φ : Point n -> Real} {x : Point n}
    {J : Jet n}
    (hu : ViscositySubsolution C F u)
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C)
    (hx : x ∈ C) (hx_closure : x ∈ closure (interior C))
    (htouch : TouchesAboveOn C u φ x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C)
    (hDφ : fderivWithin Real φ C x = J.toFirstDerivative)
    (hD2φ : fderivWithin Real (fderivWithin Real φ C) C x = J.toSecondDerivative) :
    F x (u x) J.gradient J.hessian <= 0 :=
  hu.of_touchesAbove_hasSecondOrderExpansionWithin hx htouch
    (hasSecondOrderExpansionWithin_of_contDiffOn_two hC huniq hx hx_closure hφ hDφ hD2φ)

/--
A viscosity subsolution satisfies the expected inequality for every `C^2`
test function touching from above, using the coordinate jet extracted from
mathlib's canonical `fderivWithin` derivatives.
-/
theorem ViscositySubsolution.of_touchesAbove_contDiffOn_two_smoothTestJetWithin
    {C : Set (Point n)} {F : Operator n} {u φ : Point n -> Real} {x : Point n}
    (hu : ViscositySubsolution C F u)
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C)
    (hx : x ∈ C) (hx_closure : x ∈ closure (interior C))
    (htouch : TouchesAboveOn C u φ x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C) :
    F x (u x) (smoothTestJetWithin C φ x).gradient
      (smoothTestJetWithin C φ x).hessian <= 0 :=
  hu.of_touchesAbove_contDiffOn_two (J := smoothTestJetWithin C φ x)
    hC huniq hx hx_closure htouch hφ
    (by simp [smoothTestJetWithin])
    (by simp [smoothTestJetWithin])

/--
A viscosity supersolution satisfies the expected inequality for every `C^2`
test function touching from below, provided its canonical `fderivWithin` data
matches the coordinate jet.
-/
theorem ViscositySupersolution.of_touchesBelow_contDiffOn_two
    {C : Set (Point n)} {F : Operator n} {u φ : Point n -> Real} {x : Point n}
    {J : Jet n}
    (hu : ViscositySupersolution C F u)
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C)
    (hx : x ∈ C) (hx_closure : x ∈ closure (interior C))
    (htouch : TouchesBelowOn C u φ x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C)
    (hDφ : fderivWithin Real φ C x = J.toFirstDerivative)
    (hD2φ : fderivWithin Real (fderivWithin Real φ C) C x = J.toSecondDerivative) :
    0 <= F x (u x) J.gradient J.hessian :=
  hu.of_touchesBelow_hasSecondOrderExpansionWithin hx htouch
    (hasSecondOrderExpansionWithin_of_contDiffOn_two hC huniq hx hx_closure hφ hDφ hD2φ)

/--
A viscosity supersolution satisfies the expected inequality for every `C^2`
test function touching from below, using the coordinate jet extracted from
mathlib's canonical `fderivWithin` derivatives.
-/
theorem ViscositySupersolution.of_touchesBelow_contDiffOn_two_smoothTestJetWithin
    {C : Set (Point n)} {F : Operator n} {u φ : Point n -> Real} {x : Point n}
    (hu : ViscositySupersolution C F u)
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C)
    (hx : x ∈ C) (hx_closure : x ∈ closure (interior C))
    (htouch : TouchesBelowOn C u φ x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C) :
    0 <= F x (u x) (smoothTestJetWithin C φ x).gradient
      (smoothTestJetWithin C φ x).hessian :=
  hu.of_touchesBelow_contDiffOn_two (J := smoothTestJetWithin C φ x)
    hC huniq hx hx_closure htouch hφ
    (by simp [smoothTestJetWithin])
    (by simp [smoothTestJetWithin])

end ViscositySolns
