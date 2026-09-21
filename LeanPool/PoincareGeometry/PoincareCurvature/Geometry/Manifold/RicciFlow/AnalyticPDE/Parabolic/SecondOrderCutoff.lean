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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteLowerOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Lower-order coefficients produced by a scalar cutoff

This file isolates the elementary operator algebra behind a second-order
cutoff commutator.  If `u` is multiplied by a scalar `χ`, the second spatial
jet contains the original jet multiplied by `χ`, two gradient cross terms,
and a Hessian-times-value term.  Consequently every second-order linear
operator loses its principal part in the commutator and leaves a canonical
first-plus-zeroth-order operator.
-/

@[expose] public noncomputable section
namespace RicciFlow
namespace AnalyticPDE

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

@[reducible] local instance secondOrderCutoffFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance secondOrderCutoffFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance secondOrderCutoffSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance secondOrderCutoffSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance secondOrderCutoffPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance secondOrderCutoffPrincipalNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance secondOrderCutoffFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance secondOrderCutoffFirstCoeffNormedSpace :
    NormedSpace ℝ ((X →L[ℝ] W) →L[ℝ] W) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance secondOrderCutoffZeroCoeffNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance secondOrderCutoffZeroCoeffNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W) := ContinuousLinearMap.toNormedSpace

/-- The first-jet contribution `v ↦ dχ(v) u`. -/
def cutoffGradientValueL (dχ : X →L[ℝ] ℝ) :
    W →L[ℝ] X →L[ℝ] W :=
  (ContinuousLinearMap.smulRightL ℝ X W) dχ

@[simp] theorem cutoffGradientValueL_apply
    (dχ : X →L[ℝ] ℝ) (u : W) (v : X) :
    cutoffGradientValueL dχ u v = dχ v • u := by
  rfl

/-- The symmetric first-jet cross term
`(v,w) ↦ dχ(v) Du(w) + dχ(w) Du(v)`. -/
def cutoffGradientCrossL (dχ : X →L[ℝ] ℝ) :
    (X →L[ℝ] W) →L[ℝ] X →L[ℝ] X →L[ℝ] W :=
  let A := (ContinuousLinearMap.smulRightL ℝ X (X →L[ℝ] W)) dχ
  A + (ContinuousLinearMap.flipₗᵢ ℝ X X W).toContinuousLinearEquiv.toContinuousLinearMap.comp A

@[simp] theorem cutoffGradientCrossL_apply
    (dχ : X →L[ℝ] ℝ) (Du : X →L[ℝ] W) (v w : X) :
    cutoffGradientCrossL dχ Du v w =
      dχ v • Du w + dχ w • Du v := by
  rfl

/-- The Hessian-times-value contribution
`(v,w) ↦ D²χ(v,w) u`. -/
def cutoffHessianValueL (ddχ : X →L[ℝ] X →L[ℝ] ℝ) :
    W →L[ℝ] X →L[ℝ] X →L[ℝ] W :=
  (ContinuousLinearMap.flipₗᵢ ℝ X W (X →L[ℝ] W)).toContinuousLinearEquiv.toContinuousLinearMap
      ((ContinuousLinearMap.smulRightL ℝ X W).comp ddχ)

@[simp] theorem cutoffHessianValueL_apply
    (ddχ : X →L[ℝ] X →L[ℝ] ℝ) (u : W) (v w : X) :
    cutoffHessianValueL ddχ u v w = ddχ v w • u := by
  rfl

/-- The canonical first-order coefficient in the commutator of a principal
coefficient `P` with multiplication by `χ`. -/
def secondOrderCutoffFirstCoefficient
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) : (X →L[ℝ] W) →L[ℝ] W :=
  P.comp (cutoffGradientCrossL dχ)

@[simp] theorem secondOrderCutoffFirstCoefficient_apply
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) (Du : X →L[ℝ] W) :
    secondOrderCutoffFirstCoefficient P dχ Du =
      P (cutoffGradientCrossL dχ Du) := by
  rfl

/-- The canonical zeroth-order coefficient in the cutoff commutator.  It
contains the Hessian of the cutoff through the principal coefficient and
its gradient through the original first-order coefficient. -/
def secondOrderCutoffZeroCoefficient
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (B : (X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) (ddχ : X →L[ℝ] X →L[ℝ] ℝ) : W →L[ℝ] W :=
  P.comp (cutoffHessianValueL ddχ) +
    B.comp (cutoffGradientValueL dχ)

@[simp] theorem secondOrderCutoffZeroCoefficient_apply
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (B : (X →L[ℝ] W) →L[ℝ] W)
    (dχ : X →L[ℝ] ℝ) (ddχ : X →L[ℝ] X →L[ℝ] ℝ) (u : W) :
    secondOrderCutoffZeroCoefficient P B dχ ddχ u =
      P (cutoffHessianValueL ddχ u) +
        B (cutoffGradientValueL dχ u) := by
  rfl

/-- Smooth dependence of the first-order cutoff coefficient on the principal
coefficient and the cutoff gradient. -/
theorem contDiffOn_secondOrderCutoffFirstCoefficient
    {n : WithTop ℕ∞} {s : Set X}
    {P : X → (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W}
    {dχ : X → X →L[ℝ] ℝ}
    (hP : ContDiffOn ℝ n P s) (hdχ : ContDiffOn ℝ n dχ s) :
    ContDiffOn ℝ n
      (fun z => secondOrderCutoffFirstCoefficient (P z) (dχ z)) s := by
  let S := ContinuousLinearMap.smulRightL ℝ X (X →L[ℝ] W)
  let R :=
    (ContinuousLinearMap.flipₗᵢ ℝ X X W).toContinuousLinearEquiv.toContinuousLinearMap
  have hA : ContDiffOn ℝ n (fun z => S (dχ z)) s :=
    contDiffOn_const.clm_apply hdχ
  have hRA : ContDiffOn ℝ n (fun z => R.comp (S (dχ z))) s :=
    contDiffOn_const.clm_comp hA
  simpa only [secondOrderCutoffFirstCoefficient, cutoffGradientCrossL,
    S, R] using hP.clm_comp (hA.add hRA)

/-- Smooth dependence of the zeroth-order cutoff coefficient on the
principal and first coefficients and on the first two cutoff derivatives. -/
theorem contDiffOn_secondOrderCutoffZeroCoefficient
    {n : WithTop ℕ∞} {s : Set X}
    {P : X → (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W}
    {B : X → (X →L[ℝ] W) →L[ℝ] W}
    {dχ : X → X →L[ℝ] ℝ} {ddχ : X → X →L[ℝ] X →L[ℝ] ℝ}
    (hP : ContDiffOn ℝ n P s) (hB : ContDiffOn ℝ n B s)
    (hdχ : ContDiffOn ℝ n dχ s) (hddχ : ContDiffOn ℝ n ddχ s) :
    ContDiffOn ℝ n
      (fun z => secondOrderCutoffZeroCoefficient
        (P z) (B z) (dχ z) (ddχ z)) s := by
  let S := ContinuousLinearMap.smulRightL ℝ X W
  let R :=
    (ContinuousLinearMap.flipₗᵢ ℝ X W (X →L[ℝ] W)).toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad : ContDiffOn ℝ n (fun z => S (dχ z)) s :=
    contDiffOn_const.clm_apply hdχ
  have hcomp : ContDiffOn ℝ n (fun z => S.comp (ddχ z)) s :=
    contDiffOn_const.clm_comp hddχ
  have hhess : ContDiffOn ℝ n (fun z => R (S.comp (ddχ z))) s :=
    contDiffOn_const.clm_apply hcomp
  simpa only [secondOrderCutoffZeroCoefficient, cutoffHessianValueL,
    cutoffGradientValueL, S, R] using
      (hP.clm_comp hhess).add (hB.clm_comp hgrad)

/-- Pure operator identity showing cancellation of every second derivative
of the unknown in a cutoff commutator. -/
theorem secondOrder_cutoff_expansion
    (P : (X →L[ℝ] X →L[ℝ] W) →L[ℝ] W)
    (B : (X →L[ℝ] W) →L[ℝ] W) (C : W →L[ℝ] W)
    (χ : ℝ) (dχ : X →L[ℝ] ℝ) (ddχ : X →L[ℝ] X →L[ℝ] ℝ)
    (u : W) (Du : X →L[ℝ] W) (D2u : X →L[ℝ] X →L[ℝ] W) :
    P (χ • D2u + cutoffGradientCrossL dχ Du +
          cutoffHessianValueL ddχ u) +
        B (χ • Du + cutoffGradientValueL dχ u) + C (χ • u) =
      χ • (P D2u + B Du + C u) +
        secondOrderCutoffFirstCoefficient P dχ Du +
        secondOrderCutoffZeroCoefficient P B dχ ddχ u := by
  simp [secondOrderCutoffFirstCoefficient,
    secondOrderCutoffZeroCoefficient, map_add, map_smul]
  abel

/-- The first and second Fréchet jets of a scalar multiple, written in the
same canonical cross-term operators used by the cutoff expansion. -/
theorem secondOrder_cutoff_product_jet
    {χ : X → ℝ} {u : X → W} {s : Set X} {x : X}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hχ : DifferentiableOn ℝ χ s) (hu : DifferentiableOn ℝ u s)
    {ddχ : X →L[ℝ] X →L[ℝ] ℝ} {D2u : X →L[ℝ] X →L[ℝ] W}
    (hdχ : HasFDerivWithinAt
      (fun y => fderivWithin ℝ χ s y) ddχ s x)
    (hDu : HasFDerivWithinAt
      (fun y => fderivWithin ℝ u s y) D2u s x) :
    let dχ := fderivWithin ℝ χ s x
    let Du := fderivWithin ℝ u s x
    fderivWithin ℝ (fun y => χ y • u y) s x =
        χ x • Du + cutoffGradientValueL dχ (u x) ∧
      fderivWithin ℝ
          (fun y => fderivWithin ℝ (fun z => χ z • u z) s y) s x =
        χ x • D2u + cutoffGradientCrossL dχ Du +
          cutoffHessianValueL ddχ (u x) := by
  dsimp only
  let dχ := fderivWithin ℝ χ s x
  let Du := fderivWithin ℝ u s x
  have hχx : HasFDerivWithinAt χ dχ s x :=
    (hχ x hx).hasFDerivWithinAt
  have hux : HasFDerivWithinAt u Du s x :=
    (hu x hx).hasFDerivWithinAt
  have hfirst : HasFDerivWithinAt (fun y => χ y • u y)
      (χ x • Du + cutoffGradientValueL dχ (u x)) s x := by
    change HasFDerivWithinAt (χ • u)
      (χ x • Du + dχ.smulRight (u x)) s x
    exact hχx.smul hux
  constructor
  · exact hfirst.fderivWithin (hs x hx)
  · let S := ContinuousLinearMap.smulRightL ℝ X W
    let F : X → X →L[ℝ] W := fun y =>
      χ y • fderivWithin ℝ u s y +
        cutoffGradientValueL (fderivWithin ℝ χ s y) (u y)
    have hEq : Set.EqOn
        (fun y => fderivWithin ℝ (fun z => χ z • u z) s y) F s := by
      intro y hy
      exact fderivWithin_fun_smul (hs y hy) (hχ y hy) (hu y hy)
    have hterm1 : HasFDerivWithinAt
        (fun y => χ y • fderivWithin ℝ u s y)
        (χ x • D2u + dχ.smulRight Du) s x := hχx.smul hDu
    have hS : HasFDerivAt (fun L => S L) S
        (fderivWithin ℝ χ s x) := S.hasFDerivAt
    have hc := hS.comp_hasFDerivWithinAt
      (f := fun y => fderivWithin ℝ χ s y)
      (g := fun L => S L) (f' := ddχ) (g' := S) x hdχ
    have hterm2raw := hc.clm_apply hux
    have hterm2 : HasFDerivWithinAt
        (fun y => cutoffGradientValueL
          (fderivWithin ℝ χ s y) (u y))
        ((S dχ).comp Du + (S.comp ddχ).flip (u x)) s x := by
      simpa only [S, cutoffGradientValueL, Function.comp_apply] using
        hterm2raw
    have hF : HasFDerivWithinAt F
        ((χ x • D2u + dχ.smulRight Du) +
          ((S dχ).comp Du + (S.comp ddχ).flip (u x))) s x := by
      change HasFDerivWithinAt
        ((fun y => χ y • fderivWithin ℝ u s y) +
          fun y => cutoffGradientValueL
            (fderivWithin ℝ χ s y) (u y)) _ s x
      exact hterm1.add hterm2
    have hactual := hF.congr' hEq hx
    rw [hactual.fderivWithin (hs x hx)]
    ext v w
    simp [S, cutoffGradientCrossL, cutoffHessianValueL]
    abel

/-- Unrestricted-point version of `secondOrder_cutoff_product_jet`.  This is
the convenient form on the interior of a manifold chart, where all within
derivatives agree with ordinary Fréchet derivatives. -/
theorem secondOrder_cutoff_product_jet_at
    {χ : X → ℝ} {u : X → W} {x : X}
    (hχ : ContDiffAt ℝ 2 χ x) (hu : ContDiffAt ℝ 2 u x) :
    let dχ := fderiv ℝ χ x
    let Du := fderiv ℝ u x
    let ddχ := fderiv ℝ (fderiv ℝ χ) x
    let D2u := fderiv ℝ (fderiv ℝ u) x
    fderiv ℝ (fun y => χ y • u y) x =
        χ x • Du + cutoffGradientValueL dχ (u x) ∧
      fderiv ℝ
          (fun y => fderiv ℝ (fun z => χ z • u z) y) x =
        χ x • D2u + cutoffGradientCrossL dχ Du +
          cutoffHessianValueL ddχ (u x) := by
  dsimp only
  let dχ := fderiv ℝ χ x
  let Du := fderiv ℝ u x
  let ddχ := fderiv ℝ (fderiv ℝ χ) x
  let D2u := fderiv ℝ (fderiv ℝ u) x
  have hχdiff : DifferentiableAt ℝ χ x :=
    hχ.differentiableAt (by norm_num)
  have hudiff : DifferentiableAt ℝ u x :=
    hu.differentiableAt (by norm_num)
  have hχx : HasFDerivAt χ dχ x := hχdiff.hasFDerivAt
  have hux : HasFDerivAt u Du x := hudiff.hasFDerivAt
  have hdχ : HasFDerivAt (fderiv ℝ χ) ddχ x :=
    ((hχ.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hDu : HasFDerivAt (fderiv ℝ u) D2u x :=
    ((hu.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hfirst : HasFDerivAt (fun y => χ y • u y)
      (χ x • Du + cutoffGradientValueL dχ (u x)) x := by
    change HasFDerivAt (χ • u)
      (χ x • Du + dχ.smulRight (u x)) x
    exact hχx.smul hux
  constructor
  · exact hfirst.fderiv
  · let S := ContinuousLinearMap.smulRightL ℝ X W
    let F : X → X →L[ℝ] W := fun y =>
      χ y • fderiv ℝ u y +
        cutoffGradientValueL (fderiv ℝ χ y) (u y)
    have hEq : (fun y => fderiv ℝ (fun z => χ z • u z) y) =ᶠ[nhds x] F := by
      filter_upwards [hχ.eventually (by norm_num),
        hu.eventually (by norm_num)] with y hχy huy
      exact fderiv_fun_smul
        (hχy.differentiableAt (by norm_num))
        (huy.differentiableAt (by norm_num))
    have hterm1 : HasFDerivAt
        (fun y => χ y • fderiv ℝ u y)
        (χ x • D2u + dχ.smulRight Du) x := hχx.smul hDu
    have hS : HasFDerivAt (fun L => S L) S (fderiv ℝ χ x) :=
      S.hasFDerivAt
    have hcWithin := hS.comp_hasFDerivWithinAt
      (f := fun y => fderiv ℝ χ y) (g := fun L => S L)
      (f' := ddχ) (g' := S) (s := Set.univ) x
      (hdχ.hasFDerivWithinAt (s := Set.univ))
    have hterm2rawWithin := hcWithin.clm_apply
      (hux.hasFDerivWithinAt (s := Set.univ))
    have hterm2raw : HasFDerivAt
        (fun y => S (fderiv ℝ χ y) (u y))
        ((S (fderiv ℝ χ x)).comp (fderiv ℝ u x) +
          (S.comp ddχ).flip (u x)) x := by
      simpa only [hasFDerivWithinAt_univ, Function.comp_apply] using
        hterm2rawWithin
    have hterm2 : HasFDerivAt
        (fun y => cutoffGradientValueL (fderiv ℝ χ y) (u y))
        ((S dχ).comp Du + (S.comp ddχ).flip (u x)) x := by
      simpa only [S, cutoffGradientValueL, Function.comp_apply] using
        hterm2raw
    have hF : HasFDerivAt F
        ((χ x • D2u + dχ.smulRight Du) +
          ((S dχ).comp Du + (S.comp ddχ).flip (u x))) x := by
      change HasFDerivAt
        ((fun y => χ y • fderiv ℝ u y) +
          fun y => cutoffGradientValueL (fderiv ℝ χ y) (u y)) _ x
      exact hterm1.add hterm2
    have hactual := hF.congr_of_eventuallyEq hEq
    rw [hactual.fderiv]
    ext v w
    simp [S, cutoffGradientCrossL, cutoffHessianValueL]
    abel

end AnalyticPDE
end RicciFlow
