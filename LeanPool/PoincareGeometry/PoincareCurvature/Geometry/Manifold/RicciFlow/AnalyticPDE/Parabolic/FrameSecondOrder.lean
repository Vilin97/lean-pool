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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.LinearSecondOrder
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Second-order operators in a moving finite frame

This file performs the finite-dimensional algebra needed to pass from a
connection-Laplacian formula in a moving local frame to the standard

`A(D²u) + B(Du) + C(u)`

form used by the parabolic Banach-space theory.  The formulas retain all
derivatives of the moving frame and all induced connection coefficients.
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace RicciFlow
namespace AnalyticPDE

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

local notation "W" => (κ → ℝ)
local notation "DW" => (X →L[ℝ] W)
local notation "D2W" => (X →L[ℝ] X →L[ℝ] W)

/-- Read a first derivative in an arbitrary spatial direction. -/
def movingFrameFirstReadout (v : X) : DW →L[ℝ] W :=
  (ContinuousLinearMap.apply ℝ W) v

/-- Read a second derivative in two arbitrary spatial directions. -/
def movingFrameSecondReadout (v w : X) : D2W →L[ℝ] W :=
  ((ContinuousLinearMap.apply ℝ W) w).comp
    ((ContinuousLinearMap.apply ℝ (X →L[ℝ] W)) v)

/-- First covariant coefficient assembled from a value and first derivative
in a moving frame. -/
def movingFrameFirstValue
    (V : ι → X) (gamma₂ : κ → κ → ι → ℝ)
    (u : W) (Du : DW) (out : κ) (j : ι) : ℝ :=
  Du (V j) out + ∑ input : κ, u input * gamma₂ out input j

/-- Pointwise first covariant coefficient when the value, derivative, frame,
and connection coefficient vary over the coordinate domain. -/
def movingFrameFirstFunction
    (V : ι → X → X) (gamma₂ : κ → κ → ι → X → ℝ)
    (u : X → W) (Du : X → DW) (out : κ) (j : ι) : X → ℝ :=
  fun x => movingFrameFirstValue
    (fun i => V i x) (fun a b i => gamma₂ a b i x)
    (u x) (Du x) out j

/-- Fréchet derivative of the first moving-frame coefficient.  This is the
calculus identity which produces the principal Hessian term, the derivative
of the moving frame, and the derivative of the connection coefficient. -/
theorem fderiv_movingFrameFirstFunction_apply
    {V : ι → X → X} {DV : ι → X →L[ℝ] X}
    {gamma₂ : κ → κ → ι → X → ℝ}
    {Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ}
    {u : X → W} {Du : X → DW} {D2u : D2W}
    {x : X}
    (hu : HasFDerivAt u (Du x) x)
    (hDu : HasFDerivAt Du D2u x)
    (hV : ∀ i : ι, HasFDerivAt (V i) (DV i) x)
    (hgamma₂ : ∀ a b : κ, ∀ i : ι,
      HasFDerivAt (gamma₂ a b i) (Dgamma₂ a b i) x)
    (out : κ) (j : ι) (v : X) :
    fderiv ℝ (movingFrameFirstFunction V gamma₂ u Du out j) x v =
      Du x (DV j v) out + D2u v (V j x) out +
        ∑ input : κ,
          (u x input * Dgamma₂ out input j v +
            gamma₂ out input j x * Du x v input) := by
  have hEval := hDu.clm_apply (hV j)
  have hTerm :=
    (hasFDerivAt_const (ContinuousLinearMap.proj out) x).clm_apply hEval
  have hSum := HasFDerivAt.fun_sum (u := Finset.univ) (fun input _ =>
    ((hasFDerivAt_const (ContinuousLinearMap.proj input) x).clm_apply hu).mul
      (hgamma₂ out input j))
  have hTotal := hTerm.add hSum
  change fderiv ℝ
      (((fun y : X =>
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) out)
            (Du y (V j y))) : X → ℝ) +
        (fun y : X => ∑ input : κ,
          ((fun w : X =>
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) input)
                (u w)) *
            gamma₂ out input j) y)) x v = _
  rw [hTotal.fderiv]
  simp [ContinuousLinearMap.comp_apply, Finset.sum_apply]

/-- Within-set version of `fderiv_movingFrameFirstFunction_apply`.  This is
the form used in a manifold chart, whose coordinate representative is only
canonically differentiated on the model-with-corners range. -/
theorem fderivWithin_movingFrameFirstFunction_apply
    {V : ι → X → X} {DV : ι → X →L[ℝ] X}
    {gamma₂ : κ → κ → ι → X → ℝ}
    {Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ}
    {u : X → W} {Du : X → DW} {D2u : D2W}
    {s : Set X} {x : X}
    (hs : UniqueDiffWithinAt ℝ s x)
    (hu : HasFDerivWithinAt u (Du x) s x)
    (hDu : HasFDerivWithinAt Du D2u s x)
    (hV : ∀ i : ι, HasFDerivWithinAt (V i) (DV i) s x)
    (hgamma₂ : ∀ a b : κ, ∀ i : ι,
      HasFDerivWithinAt (gamma₂ a b i) (Dgamma₂ a b i) s x)
    (out : κ) (j : ι) (v : X) :
    fderivWithin ℝ (movingFrameFirstFunction V gamma₂ u Du out j) s x v =
      Du x (DV j v) out + D2u v (V j x) out +
        ∑ input : κ,
          (u x input * Dgamma₂ out input j v +
            gamma₂ out input j x * Du x v input) := by
  have hEval := hDu.clm_apply (hV j)
  have hTerm :=
    (hasFDerivWithinAt_const (ContinuousLinearMap.proj out) x s).clm_apply hEval
  have hSum := HasFDerivWithinAt.fun_sum (u := Finset.univ) (fun input _ =>
    ((hasFDerivWithinAt_const (ContinuousLinearMap.proj input) x s).clm_apply hu).mul
      (hgamma₂ out input j))
  have hTotal := hTerm.add hSum
  change fderivWithin ℝ
      (((fun y : X =>
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) out)
            (Du y (V j y))) : X → ℝ) +
        (fun y : X => ∑ input : κ,
          ((fun w : X =>
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) input)
                (u w)) *
            gamma₂ out input j) y)) s x v = _
  rw [hTotal.fderivWithin hs]
  simp [ContinuousLinearMap.comp_apply, Finset.sum_apply]

/-- Principal scalar row of a moving-frame second-order operator. -/
def movingFramePrincipalScalar
    (gInv : ι → ι → ℝ) (V : ι → X) (out : κ) : D2W →L[ℝ] ℝ :=
  ∑ i : ι, ∑ j : ι,
    gInv i j •
      ((ContinuousLinearMap.proj out).comp
        (movingFrameSecondReadout (X := X) (κ := κ) (V i) (V j)))

/-- First-order scalar row.  Its three terms respectively record the
derivative of the moving input frame, the two-tensor connection, and the
three-tensor connection. -/
def movingFrameFirstScalar
    (gInv : ι → ι → ℝ) (V : ι → X)
    (DV : ι → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (out : κ) : DW →L[ℝ] ℝ :=
  ∑ i : ι, ∑ j : ι,
    gInv i j •
      (((ContinuousLinearMap.proj out).comp
          (movingFrameFirstReadout (X := X) (κ := κ) (DV j (V i)))) +
        (∑ input : κ,
          gamma₂ out input j •
            ((ContinuousLinearMap.proj input).comp
              (movingFrameFirstReadout (X := X) (κ := κ) (V i)))) +
        (∑ input : κ × ι,
          gamma₃ (out, j) input i •
            ((ContinuousLinearMap.proj input.1).comp
              (movingFrameFirstReadout
                (X := X) (κ := κ) (V input.2)))))

/-- Zeroth-order scalar row.  The first term differentiates the induced
two-tensor connection coefficient; the second inserts the zeroth-order part
of the first covariant derivative into the induced three-tensor connection. -/
def movingFrameZeroScalar
    (gInv : ι → ι → ℝ) (V : ι → X)
    (gamma₂ : κ → κ → ι → ℝ)
    (Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (out : κ) : W →L[ℝ] ℝ :=
  ∑ i : ι, ∑ j : ι,
    gInv i j •
      ((∑ input : κ,
          (Dgamma₂ out input j (V i)) • ContinuousLinearMap.proj input) +
        (∑ input : κ × ι, ∑ valueInput : κ,
          (gamma₃ (out, j) input i *
              gamma₂ input.1 valueInput input.2) •
            ContinuousLinearMap.proj valueInput))

/-- Principal coefficient `A` with all output rows assembled. -/
def movingFramePrincipalCoefficient
    (gInv : ι → ι → ℝ) (V : ι → X) : D2W →L[ℝ] W :=
  ContinuousLinearMap.pi fun out => movingFramePrincipalScalar gInv V out

/-- First-order coefficient `B` with all output rows assembled. -/
def movingFrameFirstCoefficient
    (gInv : ι → ι → ℝ) (V : ι → X)
    (DV : ι → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ) : DW →L[ℝ] W :=
  ContinuousLinearMap.pi fun out =>
    movingFrameFirstScalar gInv V DV gamma₂ gamma₃ out

/-- Zeroth-order coefficient `C` with all output rows assembled. -/
def movingFrameZeroCoefficient
    (gInv : ι → ι → ℝ) (V : ι → X)
    (gamma₂ : κ → κ → ι → ℝ)
    (Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ) : W →L[ℝ] W :=
  ContinuousLinearMap.pi fun out =>
    movingFrameZeroScalar gInv V gamma₂ Dgamma₂ gamma₃ out

theorem movingFramePrincipalCoefficient_apply_for_regularity
    (gInv : ι → ι → ℝ) (V : ι → X) (H : D2W) (out : κ) :
    movingFramePrincipalCoefficient gInv V H out =
      ∑ i : ι, ∑ j : ι, gInv i j * H (V i) (V j) out := by
  simp [movingFramePrincipalCoefficient, movingFramePrincipalScalar,
    movingFrameSecondReadout]

theorem movingFrameFirstCoefficient_apply_for_regularity
    (gInv : ι → ι → ℝ) (V : ι → X)
    (DV : ι → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (D : DW) (out : κ) :
    movingFrameFirstCoefficient gInv V DV gamma₂ gamma₃ D out =
      ∑ i : ι, ∑ j : ι, gInv i j *
        (D (DV j (V i)) out +
          ∑ input : κ, gamma₂ out input j * D (V i) input +
          ∑ input : κ × ι,
            gamma₃ (out, j) input i * D (V input.2) input.1) := by
  simp [movingFrameFirstCoefficient, movingFrameFirstScalar,
    movingFrameFirstReadout, mul_add, Finset.mul_sum]

theorem movingFrameZeroCoefficient_apply_for_regularity
    (gInv : ι → ι → ℝ) (V : ι → X)
    (gamma₂ : κ → κ → ι → ℝ)
    (Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (u : W) (out : κ) :
    movingFrameZeroCoefficient gInv V gamma₂ Dgamma₂ gamma₃ u out =
      ∑ i : ι, ∑ j : ι, gInv i j *
        ((∑ input : κ, u input * Dgamma₂ out input j (V i)) +
          ∑ input : κ × ι,
            gamma₃ (out, j) input i *
              (∑ valueInput : κ,
                u valueInput * gamma₂ input.1 valueInput input.2)) := by
  simp [movingFrameZeroCoefficient, movingFrameZeroScalar,
    mul_add, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-! ## Regularity of the assembled coefficients -/

section Regularity

variable [FiniteDimensional ℝ X]

@[reducible] local instance movingFrameRegularityWNormedAddCommGroup :
    NormedAddCommGroup W := Pi.normedAddCommGroup
@[reducible] local instance movingFrameRegularityWNormedSpace :
    NormedSpace ℝ W := Pi.normedSpace
@[reducible] local instance movingFrameRegularityDWNormedAddCommGroup :
    NormedAddCommGroup DW := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance movingFrameRegularityDWNormedSpace :
    NormedSpace ℝ DW := ContinuousLinearMap.toNormedSpace
@[reducible] local instance movingFrameRegularityD2WNormedAddCommGroup :
    NormedAddCommGroup D2W := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance movingFrameRegularityD2WNormedSpace :
    NormedSpace ℝ D2W := ContinuousLinearMap.toNormedSpace

/-- Finite moving-frame assembly preserves `C^n` regularity of the
principal coefficient. -/
theorem contDiffOn_movingFramePrincipalCoefficient
    {n : WithTop ℕ∞} {s : Set X}
    (gInv : ι → ι → X → ℝ) (V : ι → X → X)
    (hg : ∀ i j, ContDiffOn ℝ n (gInv i j) s)
    (hV : ∀ i, ContDiffOn ℝ n (V i) s) :
    ContDiffOn ℝ n (fun x => movingFramePrincipalCoefficient
      (fun i j => gInv i j x) (fun i => V i x) : X → D2W →L[ℝ] W) s := by
  rw [contDiffOn_clm_apply]
  intro H
  rw [contDiffOn_pi]
  intro out
  simp only [movingFramePrincipalCoefficient_apply_for_regularity]
  fun_prop

/-- Finite moving-frame assembly preserves `C^n` regularity of the
first-order coefficient. -/
theorem contDiffOn_movingFrameFirstCoefficient
    {n : WithTop ℕ∞} {s : Set X}
    (gInv : ι → ι → X → ℝ) (V : ι → X → X)
    (DV : ι → X → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → X → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → X → ℝ)
    (hg : ∀ i j, ContDiffOn ℝ n (gInv i j) s)
    (hV : ∀ i, ContDiffOn ℝ n (V i) s)
    (hDV : ∀ i, ContDiffOn ℝ n (DV i) s)
    (hg2 : ∀ a b i, ContDiffOn ℝ n (gamma₂ a b i) s)
    (hg3 : ∀ a b i, ContDiffOn ℝ n (gamma₃ a b i) s) :
    ContDiffOn ℝ n (fun x => movingFrameFirstCoefficient
      (fun i j => gInv i j x) (fun i => V i x) (fun i => DV i x)
      (fun a b i => gamma₂ a b i x) (fun a b i => gamma₃ a b i x) :
        X → DW →L[ℝ] W) s := by
  rw [contDiffOn_clm_apply]
  intro D
  rw [contDiffOn_pi]
  intro out
  simp only [movingFrameFirstCoefficient_apply_for_regularity]
  have hDVV : ∀ i j, ContDiffOn ℝ n (fun x => DV j x (V i x)) s := by
    intro i j
    exact (hDV j).clm_apply (hV i)
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  apply (hg i j).mul
  apply ContDiffOn.add
  · apply ContDiffOn.add
    · have hmap : ContDiffOn ℝ n (fun x => D (DV j x (V i x))) s :=
        contDiffOn_const.clm_apply (hDVV i j)
      exact (contDiffOn_pi.mp hmap) out
    · apply ContDiffOn.sum
      intro input hinput
      apply (hg2 out input j).mul
      have hmap : ContDiffOn ℝ n (fun x => D (V i x)) s :=
        contDiffOn_const.clm_apply (hV i)
      exact (contDiffOn_pi.mp hmap) input
  · apply ContDiffOn.sum
    intro input hinput
    apply (hg3 (out, j) input i).mul
    have hmap : ContDiffOn ℝ n (fun x => D (V input.2 x)) s :=
      contDiffOn_const.clm_apply (hV input.2)
    exact (contDiffOn_pi.mp hmap) input.1

/-- Finite moving-frame assembly preserves `C^n` regularity of the
zeroth-order coefficient. -/
theorem contDiffOn_movingFrameZeroCoefficient
    {n : WithTop ℕ∞} {s : Set X}
    (gInv : ι → ι → X → ℝ) (V : ι → X → X)
    (gamma₂ : κ → κ → ι → X → ℝ)
    (Dgamma₂ : κ → κ → ι → X → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → X → ℝ)
    (hg : ∀ i j, ContDiffOn ℝ n (gInv i j) s)
    (hV : ∀ i, ContDiffOn ℝ n (V i) s)
    (hg2 : ∀ a b i, ContDiffOn ℝ n (gamma₂ a b i) s)
    (hDg2 : ∀ a b i, ContDiffOn ℝ n (Dgamma₂ a b i) s)
    (hg3 : ∀ a b i, ContDiffOn ℝ n (gamma₃ a b i) s) :
    ContDiffOn ℝ n (fun x => movingFrameZeroCoefficient
      (fun i j => gInv i j x) (fun i => V i x)
      (fun a b i => gamma₂ a b i x) (fun a b i => Dgamma₂ a b i x)
      (fun a b i => gamma₃ a b i x) : X → W →L[ℝ] W) s := by
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_pi]
  intro out
  simp only [movingFrameZeroCoefficient_apply_for_regularity]
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  apply (hg i j).mul
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro input hinput
    apply contDiffOn_const.mul
    exact (hDg2 out input j).clm_apply (hV i)
  · apply ContDiffOn.sum
    intro input hinput
    apply (hg3 (out, j) input i).mul
    apply ContDiffOn.sum
    intro valueInput hvalue
    exact contDiffOn_const.mul (hg2 input.1 valueInput input.2)

end Regularity

@[simp]
theorem movingFramePrincipalCoefficient_apply
    (gInv : ι → ι → ℝ) (V : ι → X) (H : D2W) (out : κ) :
    movingFramePrincipalCoefficient gInv V H out =
      ∑ i : ι, ∑ j : ι, gInv i j * H (V i) (V j) out := by
  simp [movingFramePrincipalCoefficient, movingFramePrincipalScalar,
    movingFrameSecondReadout]

@[simp]
theorem movingFrameFirstCoefficient_apply
    (gInv : ι → ι → ℝ) (V : ι → X)
    (DV : ι → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (D : DW) (out : κ) :
    movingFrameFirstCoefficient gInv V DV gamma₂ gamma₃ D out =
      ∑ i : ι, ∑ j : ι, gInv i j *
        (D (DV j (V i)) out +
          ∑ input : κ, gamma₂ out input j * D (V i) input +
          ∑ input : κ × ι,
            gamma₃ (out, j) input i * D (V input.2) input.1) := by
  simp [movingFrameFirstCoefficient, movingFrameFirstScalar,
    movingFrameFirstReadout, mul_add, Finset.mul_sum]

@[simp]
theorem movingFrameZeroCoefficient_apply
    (gInv : ι → ι → ℝ) (V : ι → X)
    (gamma₂ : κ → κ → ι → ℝ)
    (Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (u : W) (out : κ) :
    movingFrameZeroCoefficient gInv V gamma₂ Dgamma₂ gamma₃ u out =
      ∑ i : ι, ∑ j : ι, gInv i j *
        ((∑ input : κ, u input * Dgamma₂ out input j (V i)) +
          ∑ input : κ × ι,
            gamma₃ (out, j) input i *
              (∑ valueInput : κ,
                u valueInput * gamma₂ input.1 valueInput input.2)) := by
  simp [movingFrameZeroCoefficient, movingFrameZeroScalar,
    mul_add, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The standard `A(D²u)+B(Du)+C(u)` expression determined by a moving
frame and its induced connection coefficients. -/
def movingFrameSecondOrderFromJet
    (gInv : ι → ι → ℝ) (V : ι → X)
    (DV : ι → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → ℝ)
    (Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (u : W) (Du : DW) (D2u : D2W) : W :=
  movingFramePrincipalCoefficient gInv V D2u +
    movingFrameFirstCoefficient gInv V DV gamma₂ gamma₃ Du +
      movingFrameZeroCoefficient gInv V gamma₂ Dgamma₂ gamma₃ u

@[simp]
theorem movingFrameSecondOrderFromJet_apply
    (gInv : ι → ι → ℝ) (V : ι → X)
    (DV : ι → X →L[ℝ] X)
    (gamma₂ : κ → κ → ι → ℝ)
    (Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → ℝ)
    (u : W) (Du : DW) (D2u : D2W) (out : κ) :
    movingFrameSecondOrderFromJet gInv V DV gamma₂ Dgamma₂ gamma₃
        u Du D2u out =
      movingFramePrincipalCoefficient gInv V D2u out +
        movingFrameFirstCoefficient gInv V DV gamma₂ gamma₃ Du out +
          movingFrameZeroCoefficient gInv V gamma₂ Dgamma₂ gamma₃ u out :=
  rfl

/-- The second covariant expression obtained by differentiating the genuine
first moving-frame coefficient and then adding the induced three-tensor
connection term. -/
def movingFrameSecondFunction
    (gInv : ι → ι → X → ℝ)
    (V : ι → X → X)
    (gamma₂ : κ → κ → ι → X → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → X → ℝ)
    (u : X → W) (Du : X → DW) : X → W :=
  fun x out =>
    ∑ i : ι, ∑ j : ι, gInv i j x *
      (fderiv ℝ (movingFrameFirstFunction V gamma₂ u Du out j) x (V i x) +
        ∑ input : κ × ι,
          movingFrameFirstFunction V gamma₂ u Du input.1 input.2 x *
            gamma₃ (out, j) input i x)

/-- The same moving-frame second-order expression with every outer derivative
taken within a prescribed coordinate domain. -/
def movingFrameSecondFunctionWithin
    (s : Set X)
    (gInv : ι → ι → X → ℝ)
    (V : ι → X → X)
    (gamma₂ : κ → κ → ι → X → ℝ)
    (gamma₃ : (κ × ι) → (κ × ι) → ι → X → ℝ)
    (u : X → W) (Du : X → DW) : X → W :=
  fun x out =>
    ∑ i : ι, ∑ j : ι, gInv i j x *
      (fderivWithin ℝ (movingFrameFirstFunction V gamma₂ u Du out j)
          s x (V i x) +
        ∑ input : κ × ι,
          movingFrameFirstFunction V gamma₂ u Du input.1 input.2 x *
            gamma₃ (out, j) input i x)

/-- The differentiated moving-frame expression is precisely the standard
second-order operator `A(D²u)+B(Du)+C(u)`. -/
theorem movingFrameSecondFunction_eq_fromJet
    {gInv : ι → ι → X → ℝ}
    {V : ι → X → X} {DV : ι → X →L[ℝ] X}
    {gamma₂ : κ → κ → ι → X → ℝ}
    {Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ}
    {gamma₃ : (κ × ι) → (κ × ι) → ι → X → ℝ}
    {u : X → W} {Du : X → DW} {D2u : D2W}
    {x : X}
    (hu : HasFDerivAt u (Du x) x)
    (hDu : HasFDerivAt Du D2u x)
    (hV : ∀ i : ι, HasFDerivAt (V i) (DV i) x)
    (hgamma₂ : ∀ a b : κ, ∀ i : ι,
      HasFDerivAt (gamma₂ a b i) (Dgamma₂ a b i) x) :
    movingFrameSecondFunction gInv V gamma₂ gamma₃ u Du x =
      movingFrameSecondOrderFromJet
        (fun i j => gInv i j x) (fun i => V i x) DV
        (fun a b i => gamma₂ a b i x) Dgamma₂
        (fun a b i => gamma₃ a b i x) (u x) (Du x) D2u := by
  funext out
  simp only [movingFrameSecondFunction,
    fderiv_movingFrameFirstFunction_apply hu hDu hV hgamma₂,
    movingFrameFirstFunction, movingFrameFirstValue,
    movingFrameSecondOrderFromJet_apply,
    movingFramePrincipalCoefficient_apply,
    movingFrameFirstCoefficient_apply,
    movingFrameZeroCoefficient_apply]
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  abel

/-- Within-set counterpart of `movingFrameSecondFunction_eq_fromJet`. -/
theorem movingFrameSecondFunctionWithin_eq_fromJet
    {s : Set X}
    {gInv : ι → ι → X → ℝ}
    {V : ι → X → X} {DV : ι → X →L[ℝ] X}
    {gamma₂ : κ → κ → ι → X → ℝ}
    {Dgamma₂ : κ → κ → ι → X →L[ℝ] ℝ}
    {gamma₃ : (κ × ι) → (κ × ι) → ι → X → ℝ}
    {u : X → W} {Du : X → DW} {D2u : D2W}
    {x : X}
    (hs : UniqueDiffWithinAt ℝ s x)
    (hu : HasFDerivWithinAt u (Du x) s x)
    (hDu : HasFDerivWithinAt Du D2u s x)
    (hV : ∀ i : ι, HasFDerivWithinAt (V i) (DV i) s x)
    (hgamma₂ : ∀ a b : κ, ∀ i : ι,
      HasFDerivWithinAt (gamma₂ a b i) (Dgamma₂ a b i) s x) :
    movingFrameSecondFunctionWithin s gInv V gamma₂ gamma₃ u Du x =
      movingFrameSecondOrderFromJet
        (fun i j => gInv i j x) (fun i => V i x) DV
        (fun a b i => gamma₂ a b i x) Dgamma₂
        (fun a b i => gamma₃ a b i x) (u x) (Du x) D2u := by
  funext out
  simp only [movingFrameSecondFunctionWithin,
    fderivWithin_movingFrameFirstFunction_apply hs hu hDu hV hgamma₂,
    movingFrameFirstFunction, movingFrameFirstValue,
    movingFrameSecondOrderFromJet_apply,
    movingFramePrincipalCoefficient_apply,
    movingFrameFirstCoefficient_apply,
    movingFrameZeroCoefficient_apply]
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  abel

end AnalyticPDE
end RicciFlow
