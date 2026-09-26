/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.Membership
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.H1Function
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Translation

/-! # Difference Quotient H1 -/

@[expose] public section

namespace Homogenization

open scoped Topology

noncomputable section

namespace H1Function

/-!
# H¹ coordinate difference quotients

This file lifts the scalar coordinate difference-quotient notation to the
project's witness-based `H1Function` API.  The quotients are defined only after
restricting to an open set `V` that is contained in the original domain and in
the relevant translated domain.
-/

/-- Forward coordinate difference quotient of an `H¹(U)` function, restricted
to an interior open set `V` on which `x + h e_i` still belongs to `U`. -/
noncomputable def forwardDifferenceQuotientOn {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (h : ℝ) (i : Fin d)
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet ((-h) • basisVec i) U) :
    H1Function V :=
  h⁻¹ •
    ((u.translate ((-h) • basisVec i)).restrict hVopen hVshift -
      u.restrict hVopen hVU)

/-- Backward coordinate difference quotient of an `H¹(U)` function, restricted
to an interior open set `V` on which `x - h e_i` still belongs to `U`. -/
noncomputable def backwardDifferenceQuotientOn {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (h : ℝ) (i : Fin d)
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet (h • basisVec i) U) :
    H1Function V :=
  h⁻¹ •
    (u.restrict hVopen hVU -
      (u.translate (h • basisVec i)).restrict hVopen hVshift)

@[simp] theorem forwardDifferenceQuotientOn_toFun {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (h : ℝ) (i : Fin d)
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet ((-h) • basisVec i) U)
    (x : Vec d) :
    (u.forwardDifferenceQuotientOn h i hVopen hVU hVshift).toFun x =
      euclideanForwardDifferenceQuotient h i u.toFun x := by
  simp [forwardDifferenceQuotientOn, H1Function.restrict, H1Function.translate,
    euclideanForwardDifferenceQuotient, euclideanCoordShift, div_eq_mul_inv,
    sub_eq_add_neg, neg_smul]
  ring_nf

@[simp] theorem backwardDifferenceQuotientOn_toFun {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (h : ℝ) (i : Fin d)
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet (h • basisVec i) U)
    (x : Vec d) :
    (u.backwardDifferenceQuotientOn h i hVopen hVU hVshift).toFun x =
      euclideanBackwardDifferenceQuotient h i u.toFun x := by
  simp [backwardDifferenceQuotientOn, H1Function.restrict, H1Function.translate,
    euclideanBackwardDifferenceQuotient, euclideanCoordShift, div_eq_mul_inv,
    sub_eq_add_neg, neg_smul]
  ring_nf

@[simp] theorem forwardDifferenceQuotientOn_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (h : ℝ) (i : Fin d)
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet ((-h) • basisVec i) U)
    (x : Vec d) :
    (u.forwardDifferenceQuotientOn h i hVopen hVU hVshift).grad x =
      h⁻¹ • (u.grad (euclideanCoordShift h i x) - u.grad x) := by
  ext k
  simp [forwardDifferenceQuotientOn, H1Function.restrict, H1Function.translate,
    euclideanCoordShift, sub_eq_add_neg, neg_smul]
  ring_nf

@[simp] theorem backwardDifferenceQuotientOn_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (h : ℝ) (i : Fin d)
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet (h • basisVec i) U)
    (x : Vec d) :
    (u.backwardDifferenceQuotientOn h i hVopen hVU hVshift).grad x =
      h⁻¹ • (u.grad x - u.grad (euclideanCoordShift (-h) i x)) := by
  ext k
  simp [backwardDifferenceQuotientOn, H1Function.restrict, H1Function.translate,
    euclideanCoordShift, sub_eq_add_neg, neg_smul]
  ring_nf

/-- Choose an `H¹₀(U)` representative of `φ * u` when `φ` is a smooth compactly
supported cutoff inside a bounded open convex domain. This packages the
existing membership theorem as data, so it can be passed directly to
`WeakPoissonEquationOn.h10`. -/
noncomputable def mulContDiffHasCompactSupportToH10 {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    H10Function U :=
  Classical.choose
    (memH10_mul_of_contDiff_hasCompactSupport hU hφ hφ_compact hφ_sub u.memH1)

@[simp] theorem mulContDiffHasCompactSupportToH10_toFun {d : ℕ}
    {U : Set (Vec d)} (u : H1Function U) (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    (u.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub).toH1Function.toFun =
      fun x => φ x * u x :=
  Classical.choose_spec
    (memH10_mul_of_contDiff_hasCompactSupport hU hφ hφ_compact hφ_sub u.memH1)

/-- A smooth cutoff times a forward `H¹` difference quotient, packaged as an
`H¹₀(V)` test. -/
noncomputable def cutoffForwardDifferenceQuotientToH10 {d : ℕ}
    {U V : Set (Vec d)} (u : H1Function U) (h : ℝ) (i : Fin d)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet ((-h) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    H10Function V :=
  (u.forwardDifferenceQuotientOn h i hV.isOpen hVU hVshift).mulContDiffHasCompactSupportToH10
    hV hφ hφ_compact hφ_sub

@[simp] theorem cutoffForwardDifferenceQuotientToH10_toFun {d : ℕ}
    {U V : Set (Vec d)} (u : H1Function U) (h : ℝ) (i : Fin d)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet ((-h) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (u.cutoffForwardDifferenceQuotientToH10 h i hV hVU hVshift
      hφ hφ_compact hφ_sub).toH1Function.toFun =
        fun x => φ x * euclideanForwardDifferenceQuotient h i u.toFun x := by
  simp [cutoffForwardDifferenceQuotientToH10]

/-- A smooth cutoff times a backward `H¹` difference quotient, packaged as an
`H¹₀(V)` test. -/
noncomputable def cutoffBackwardDifferenceQuotientToH10 {d : ℕ}
    {U V : Set (Vec d)} (u : H1Function U) (h : ℝ) (i : Fin d)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet (h • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    H10Function V :=
  (u.backwardDifferenceQuotientOn h i hV.isOpen hVU hVshift).mulContDiffHasCompactSupportToH10
    hV hφ hφ_compact hφ_sub

@[simp] theorem cutoffBackwardDifferenceQuotientToH10_toFun {d : ℕ}
    {U V : Set (Vec d)} (u : H1Function U) (h : ℝ) (i : Fin d)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hVshift : V ⊆ translateSet (h • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (u.cutoffBackwardDifferenceQuotientToH10 h i hV hVU hVshift
      hφ hφ_compact hφ_sub).toH1Function.toFun =
        fun x => φ x * euclideanBackwardDifferenceQuotient h i u.toFun x := by
  simp [cutoffBackwardDifferenceQuotientToH10]

end H1Function

end

end Homogenization
