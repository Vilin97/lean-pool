/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianChart
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FrameSecondOrder

/-!
# The connection Laplacian as a coordinate second-order operator

This module is the exact geometry-to-analysis bridge for the tensor heat
equation.  In one fixed manifold chart and one genuine tangent-bundle
trivialization, it assembles the coefficients of the actual connection
Laplacian into bounded linear maps

`A : D²u ↦ u`, `B : Du ↦ u`, and `C : u ↦ u`.

The main identity is derived from the intrinsic connection Laplacian.  The
principal coefficient is the inverse Gram matrix of the Riemannian metric;
the lower-order coefficients contain the derivatives of the moving tangent
frame and all induced connection coefficients.  No coordinate PDE is
postulated.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

local instance tensorHeatOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance tensorHeatOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance tensorHeatOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := inferInstance
local instance tensorHeatOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := inferInstance
local instance tensorHeatTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance tensorHeatTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance tensorHeatTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance tensorHeatTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance tensorHeatThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance tensorHeatThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance tensorHeatThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance tensorHeatThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "W" => (ι × ι → ℝ)
local notation "DW" => (E →L[ℝ] W)
local notation "D2W" => (E →L[ℝ] E →L[ℝ] W)

-- Stabilize synthesis for the nested finite-coordinate operator spaces.
@[reducible] local instance tensorCoordinateNormedAddCommGroup :
    NormedAddCommGroup W := Pi.normedAddCommGroup
@[reducible] local instance tensorCoordinateNormedSpace :
    NormedSpace ℝ W := Pi.normedSpace
@[reducible] local instance tensorCoordinateFirstNormedAddCommGroup :
    NormedAddCommGroup DW := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance tensorCoordinateFirstNormedSpace :
    NormedSpace ℝ DW := ContinuousLinearMap.toNormedSpace
@[reducible] local instance tensorCoordinateSecondNormedAddCommGroup :
    NormedAddCommGroup D2W := ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance tensorCoordinateSecondNormedSpace :
    NormedSpace ℝ D2W := ContinuousLinearMap.toNormedSpace
@[reducible] local instance tensorCoordinatePrincipalNormedAddCommGroup :
    NormedAddCommGroup (D2W →L[ℝ] W) :=
  movingFrameRegularityDWNormedAddCommGroup
@[reducible] local instance tensorCoordinatePrincipalNormedSpace :
    NormedSpace ℝ (D2W →L[ℝ] W) := movingFrameRegularityDWNormedSpace
@[reducible] local instance tensorCoordinateFirstCoefficientNormedAddCommGroup :
    NormedAddCommGroup (DW →L[ℝ] W) :=
  movingFrameRegularityDWNormedAddCommGroup
@[reducible] local instance tensorCoordinateFirstCoefficientNormedSpace :
    NormedSpace ℝ (DW →L[ℝ] W) := movingFrameRegularityDWNormedSpace
@[reducible] local instance tensorCoordinateZeroNormedAddCommGroup :
    NormedAddCommGroup (W →L[ℝ] W) :=
  movingFrameRegularityDWNormedAddCommGroup
@[reducible] local instance tensorCoordinateZeroNormedSpace :
    NormedSpace ℝ (W →L[ℝ] W) := movingFrameRegularityDWNormedSpace

/-- All matrix coefficients of a covariant two-tensor in a fixed manifold
chart and the tensor frame induced by a tangent trivialization. -/
def localTensorCoordinates
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x) : E → W :=
  fun z out =>
    localTwoTensorComponentInChart (I := I) chartCenter e b h out z

/-- The canonical within-chart first derivative of all tensor coordinates. -/
def localTensorCoordinateDerivative
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x) : E → DW :=
  fun z => fderivWithin ℝ
    (localTensorCoordinates (I := I) chartCenter e b h) (Set.range I) z

/-- The canonical within-chart second derivative of all tensor coordinates. -/
def localTensorCoordinateSecondDerivative
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x) : E → D2W :=
  fun z => fderivWithin ℝ
    (localTensorCoordinateDerivative (I := I) chartCenter e b h)
    (Set.range I) z

/-- The derivative of a pulled-back local tangent-frame vector. -/
def localFrameDerivativeInChart
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (i : ι) : E → E →L[ℝ] E :=
  fun z => fderivWithin ℝ
    (localFrameInChart (I := I) chartCenter e b i) (Set.range I) z

/-- The derivative of an induced two-tensor frame-connection coefficient. -/
def localTwoTensorConnectionCoefficientDerivativeInChart
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (out input : ι × ι) (j : ι) :
    E → E →L[ℝ] ℝ :=
  fun z => fderivWithin ℝ
    (localTwoTensorConnectionCoefficientInChart (I := I)
      cov chartCenter e b out input j) (Set.range I) z

/-- Principal coefficient field of the actual connection Laplacian. -/
def localTensorHeatPrincipalCoefficient
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) : E → D2W →L[ℝ] W :=
  fun z => movingFramePrincipalCoefficient
    (fun i j => localFrameInverseGramMatrixInChart (I := I)
      chartCenter e b i j z)
    (fun i => localFrameInChart (I := I) chartCenter e b i z)

/-- First-order coefficient field of the actual connection Laplacian. -/
def localTensorHeatFirstCoefficient
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) : E → DW →L[ℝ] W :=
  fun z => movingFrameFirstCoefficient
    (fun i j => localFrameInverseGramMatrixInChart (I := I)
      chartCenter e b i j z)
    (fun i => localFrameInChart (I := I) chartCenter e b i z)
    (fun i => localFrameDerivativeInChart (I := I) chartCenter e b i z)
    (fun out input j => localTwoTensorConnectionCoefficientInChart (I := I)
      cov chartCenter e b out input j z)
    (fun out input i => localThreeTensorConnectionCoefficientInChart (I := I)
      cov chartCenter e b out input i z)

/-- Zeroth-order coefficient field of the actual connection Laplacian. -/
def localTensorHeatZeroCoefficient
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) : E → W →L[ℝ] W :=
  fun z => movingFrameZeroCoefficient
    (fun i j => localFrameInverseGramMatrixInChart (I := I)
      chartCenter e b i j z)
    (fun i => localFrameInChart (I := I) chartCenter e b i z)
    (fun out input j => localTwoTensorConnectionCoefficientInChart (I := I)
      cov chartCenter e b out input j z)
    (fun out input j =>
      localTwoTensorConnectionCoefficientDerivativeInChart (I := I)
        cov chartCenter e b out input j z)
    (fun out input i => localThreeTensorConnectionCoefficientInChart (I := I)
      cov chartCenter e b out input i z)

/-! ## Regularity inherited from geometric chart ingredients -/

/-- The actual principal coefficient is `C^n` wherever the inverse Gram
entries and pulled-back tangent frame are `C^n`. -/
theorem contDiffOn_localTensorHeatPrincipalCoefficient
    {n : WithTop ℕ∞} {s : Set E}
    (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E)
    (hgInv : ∀ i j, ContDiffOn ℝ n
      (localFrameInverseGramMatrixInChart (I := I) chartCenter e b i j) s)
    (hV : ∀ i, ContDiffOn ℝ n
      (localFrameInChart (I := I) chartCenter e b i) s) :
    ContDiffOn ℝ n
      (localTensorHeatPrincipalCoefficient (I := I) chartCenter e b) s := by
  rw [contDiffOn_clm_apply]
  intro H
  rw [contDiffOn_pi]
  intro out
  have h := contDiffOn_movingFramePrincipalCoefficient
      (X := E) (ι := ι) (κ := ι × ι)
      (gInv := fun i j => localFrameInverseGramMatrixInChart (I := I)
        chartCenter e b i j)
      (V := fun i => localFrameInChart (I := I) chartCenter e b i)
      hgInv hV
  have hH := (contDiffOn_clm_apply.mp h) H
  have hout := (contDiffOn_pi.mp hH) out
  simpa [localTensorHeatPrincipalCoefficient,
    movingFramePrincipalCoefficient_apply_for_regularity] using hout

/-- The actual first-order coefficient is `C^n` wherever all of its genuine
moving-frame ingredients are `C^n`. -/
theorem contDiffOn_localTensorHeatFirstCoefficient
    {n : WithTop ℕ∞} {s : Set E}
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E)
    (hgInv : ∀ i j, ContDiffOn ℝ n
      (localFrameInverseGramMatrixInChart (I := I) chartCenter e b i j) s)
    (hV : ∀ i, ContDiffOn ℝ n
      (localFrameInChart (I := I) chartCenter e b i) s)
    (hDV : ∀ i, ContDiffOn ℝ n
      (localFrameDerivativeInChart (I := I) chartCenter e b i) s)
    (hgamma₂ : ∀ out input j, ContDiffOn ℝ n
      (localTwoTensorConnectionCoefficientInChart (I := I)
        cov chartCenter e b out input j) s)
    (hgamma₃ : ∀ out input i, ContDiffOn ℝ n
      (localThreeTensorConnectionCoefficientInChart (I := I)
        cov chartCenter e b out input i) s) :
    ContDiffOn ℝ n
      (localTensorHeatFirstCoefficient (I := I) cov chartCenter e b) s := by
  rw [contDiffOn_clm_apply]
  intro D
  rw [contDiffOn_pi]
  intro out
  have h := contDiffOn_movingFrameFirstCoefficient
      (X := E) (ι := ι) (κ := ι × ι)
      (gInv := fun i j => localFrameInverseGramMatrixInChart (I := I)
        chartCenter e b i j)
      (V := fun i => localFrameInChart (I := I) chartCenter e b i)
      (DV := fun i => localFrameDerivativeInChart (I := I) chartCenter e b i)
      (gamma₂ := fun out input j =>
        localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input j)
      (gamma₃ := fun out input i =>
        localThreeTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input i)
      hgInv hV hDV hgamma₂ hgamma₃
  have hD := (contDiffOn_clm_apply.mp h) D
  have hout := (contDiffOn_pi.mp hD) out
  simpa [localTensorHeatFirstCoefficient,
    movingFrameFirstCoefficient_apply_for_regularity] using hout

/-- The actual zeroth-order coefficient is `C^n` wherever its inverse
metric, frame, induced connection, and differentiated connection
coefficients are `C^n`. -/
theorem contDiffOn_localTensorHeatZeroCoefficient
    {n : WithTop ℕ∞} {s : Set E}
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E)
    (hgInv : ∀ i j, ContDiffOn ℝ n
      (localFrameInverseGramMatrixInChart (I := I) chartCenter e b i j) s)
    (hV : ∀ i, ContDiffOn ℝ n
      (localFrameInChart (I := I) chartCenter e b i) s)
    (hgamma₂ : ∀ out input j, ContDiffOn ℝ n
      (localTwoTensorConnectionCoefficientInChart (I := I)
        cov chartCenter e b out input j) s)
    (hDgamma₂ : ∀ out input j, ContDiffOn ℝ n
      (localTwoTensorConnectionCoefficientDerivativeInChart (I := I)
        cov chartCenter e b out input j) s)
    (hgamma₃ : ∀ out input i, ContDiffOn ℝ n
      (localThreeTensorConnectionCoefficientInChart (I := I)
        cov chartCenter e b out input i) s) :
    ContDiffOn ℝ n
      (localTensorHeatZeroCoefficient (I := I) cov chartCenter e b) s := by
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_pi]
  intro out
  have h := contDiffOn_movingFrameZeroCoefficient
      (X := E) (ι := ι) (κ := ι × ι)
      (gInv := fun i j => localFrameInverseGramMatrixInChart (I := I)
        chartCenter e b i j)
      (V := fun i => localFrameInChart (I := I) chartCenter e b i)
      (gamma₂ := fun out input j =>
        localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input j)
      (Dgamma₂ := fun out input j =>
        localTwoTensorConnectionCoefficientDerivativeInChart (I := I)
          cov chartCenter e b out input j)
      (gamma₃ := fun out input i =>
        localThreeTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input i)
      hgInv hV hgamma₂ hDgamma₂ hgamma₃
  have hu := (contDiffOn_clm_apply.mp h) u
  have hout := (contDiffOn_pi.mp hu) out
  simpa [localTensorHeatZeroCoefficient,
    movingFrameZeroCoefficient_apply_for_regularity] using hout

/-- A scalar first covariant coefficient is exactly the corresponding row of
the moving-frame expression whenever `Du` is a genuine within-chart
derivative of the full coordinate vector. -/
theorem localFirstCovariantComponentInChart_eq_movingFrameFirstFunction
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    {Du : E → DW} {z : E}
    (hzUnique : UniqueDiffWithinAt ℝ (Set.range I) z)
    (hu : HasFDerivWithinAt
      (localTensorCoordinates (I := I) chartCenter e b h) (Du z)
      (Set.range I) z)
    (out : ι × ι) (j : ι) :
    localFirstCovariantComponentInChart (I := I)
        cov chartCenter e b h out j z =
      movingFrameFirstFunction
        (fun i => localFrameInChart (I := I) chartCenter e b i)
        (fun a input i => localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b a input i)
        (localTensorCoordinates (I := I) chartCenter e b h) Du out j z := by
  have hcomponent :=
    (hasFDerivWithinAt_const
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι × ι => ℝ) out)
      z (Set.range I)).clm_apply hu
  have hderiv := hcomponent.fderivWithin hzUnique
  unfold localFirstCovariantComponentInChart
    movingFrameFirstFunction movingFrameFirstValue
  rw [show fderivWithin ℝ
      (localTwoTensorComponentInChart (I := I) chartCenter e b h out)
      (Set.range I) z =
        (ContinuousLinearMap.proj out).comp (Du z) by
    simpa [localTensorCoordinates] using hderiv]
  simp [ContinuousLinearMap.comp_apply, localTensorCoordinates]

/-- Before expanding derivatives, the fixed-chart connection Laplacian is
literally the within-domain moving-frame second-order expression. -/
theorem localConnectionLaplacianComponentInChart_eq_movingFrameSecondFunctionWithin
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    (Du : E → DW) {z : E} (hz : z ∈ Set.range I)
    (huAt : HasFDerivWithinAt
      (localTensorCoordinates (I := I) chartCenter e b h) (Du z)
      (Set.range I) z)
    (huNear : ∀ᶠ w in nhdsWithin z (Set.range I), HasFDerivWithinAt
      (localTensorCoordinates (I := I) chartCenter e b h) (Du w)
      (Set.range I) w) :
    (fun out => localConnectionLaplacianComponentInChart (I := I)
        cov chartCenter e b h out z) =
      movingFrameSecondFunctionWithin (Set.range I)
        (fun i j w => localFrameInverseGramMatrixInChart (I := I)
          chartCenter e b i j w)
        (fun i => localFrameInChart (I := I) chartCenter e b i)
        (fun a input i => localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b a input i)
        (fun a input i => localThreeTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b a input i)
        (localTensorCoordinates (I := I) chartCenter e b h) Du z := by
  funext out
  unfold localConnectionLaplacianComponentInChart
    localSecondCovariantComponentInChart movingFrameSecondFunctionWithin
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have heq (a : ι × ι) (k : ι) :
      localFirstCovariantComponentInChart (I := I)
          cov chartCenter e b h a k =ᶠ[nhdsWithin z (Set.range I)]
        movingFrameFirstFunction
          (fun i => localFrameInChart (I := I) chartCenter e b i)
          (fun out input i =>
            localTwoTensorConnectionCoefficientInChart (I := I)
              cov chartCenter e b out input i)
          (localTensorCoordinates (I := I) chartCenter e b h) Du a k := by
    filter_upwards [self_mem_nhdsWithin, huNear] with w hw hderiv
    exact localFirstCovariantComponentInChart_eq_movingFrameFirstFunction
      (I := I) cov chartCenter e b h
      (I.uniqueDiffOn.uniqueDiffWithinAt hw) hderiv a k
  rw [(heq out j).fderivWithin_eq_of_mem hz]
  congr 1
  apply Finset.sum_congr rfl
  intro input hinput
  rw [localFirstCovariantComponentInChart_eq_movingFrameFirstFunction
    (I := I) cov chartCenter e b h
    (I.uniqueDiffOn.uniqueDiffWithinAt hz) huAt input.1 input.2]

/-- **Coordinate formula for the actual connection Laplacian.**  At every
point where the displayed derivatives are genuine, the fixed-chart
connection Laplacian equals its canonical `A(D²u)+B(Du)+C(u)` expression. -/
theorem localConnectionLaplacianComponentInChart_eq_secondOrder
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (h : ∀ x : M, T₂ x)
    {z : E} (hz : z ∈ Set.range I)
    (huAt : DifferentiableWithinAt ℝ
      (localTensorCoordinates (I := I) chartCenter e b h) (Set.range I) z)
    (huNear : ∀ᶠ w in nhdsWithin z (Set.range I), DifferentiableWithinAt ℝ
      (localTensorCoordinates (I := I) chartCenter e b h) (Set.range I) w)
    (hDu : DifferentiableWithinAt ℝ
      (localTensorCoordinateDerivative (I := I) chartCenter e b h)
      (Set.range I) z)
    (hV : ∀ i : ι, DifferentiableWithinAt ℝ
      (localFrameInChart (I := I) chartCenter e b i) (Set.range I) z)
    (hgamma₂ : ∀ out input : ι × ι, ∀ j : ι,
      DifferentiableWithinAt ℝ
        (localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input j) (Set.range I) z) :
    (fun out => localConnectionLaplacianComponentInChart (I := I)
        cov chartCenter e b h out z) =
      localTensorHeatPrincipalCoefficient (I := I) chartCenter e b z
          (localTensorCoordinateSecondDerivative (I := I) chartCenter e b h z) +
        localTensorHeatFirstCoefficient (I := I) cov chartCenter e b z
          (localTensorCoordinateDerivative (I := I) chartCenter e b h z) +
        localTensorHeatZeroCoefficient (I := I) cov chartCenter e b z
          (localTensorCoordinates (I := I) chartCenter e b h z) := by
  let U := localTensorCoordinates (I := I) chartCenter e b h
  let Du := localTensorCoordinateDerivative (I := I) chartCenter e b h
  let D2u := localTensorCoordinateSecondDerivative (I := I) chartCenter e b h z
  let DV : ι → E →L[ℝ] E := fun i =>
    localFrameDerivativeInChart (I := I) chartCenter e b i z
  let Dgamma₂ : (ι × ι) → (ι × ι) → ι → E →L[ℝ] ℝ :=
    fun out input j =>
      localTwoTensorConnectionCoefficientDerivativeInChart (I := I)
        cov chartCenter e b out input j z
  rw [localConnectionLaplacianComponentInChart_eq_movingFrameSecondFunctionWithin
    (I := I) cov chartCenter e b h Du hz huAt.hasFDerivWithinAt
    (huNear.mono fun w hw => hw.hasFDerivWithinAt)]
  have hframe : ∀ i : ι, HasFDerivWithinAt
      (localFrameInChart (I := I) chartCenter e b i) (DV i)
      (Set.range I) z := fun i => (hV i).hasFDerivWithinAt
  have hconnection : ∀ out input : ι × ι, ∀ j : ι,
      HasFDerivWithinAt
        (localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input j) (Dgamma₂ out input j)
        (Set.range I) z := fun out input j =>
          (hgamma₂ out input j).hasFDerivWithinAt
  have hsecond := movingFrameSecondFunctionWithin_eq_fromJet
    (gInv := fun i j w => localFrameInverseGramMatrixInChart (I := I)
      chartCenter e b i j w)
    (V := fun i => localFrameInChart (I := I) chartCenter e b i)
    (gamma₂ := fun out input i =>
      localTwoTensorConnectionCoefficientInChart (I := I)
        cov chartCenter e b out input i)
    (gamma₃ := fun out input i =>
      localThreeTensorConnectionCoefficientInChart (I := I)
        cov chartCenter e b out input i)
    (u := U) (Du := Du) (D2u := D2u)
    (DV := DV) (Dgamma₂ := Dgamma₂)
    (I.uniqueDiffOn.uniqueDiffWithinAt hz) huAt.hasFDerivWithinAt
    hDu.hasFDerivWithinAt hframe hconnection
  simpa [U, Du, D2u, DV, Dgamma₂,
    localTensorHeatPrincipalCoefficient,
    localTensorHeatFirstCoefficient, localTensorHeatZeroCoefficient,
    movingFrameSecondOrderFromJet, add_assoc,
    localFrameDerivativeInChart,
    localTwoTensorConnectionCoefficientDerivativeInChart] using hsecond

/-- **Intrinsic-to-coordinate identity for the tensor heat operator.**  The
actual connection Laplacian, evaluated on two members of a genuine local
tangent frame, is the corresponding matrix row of the canonical coordinate
operator `A(D²u)+B(Du)+C(u)`. -/
theorem connectionLaplacian_apply_eq_localTensorHeatSecondOrder
    (cov : CovariantDerivative I E TM) (chartCenter : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {h : ∀ x : M, T₂ x}
    (hregFrame : ∀ y ∈ e.baseSet,
      MDiffAt
        (fun z => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) z (h z)) y)
    (hregChart : ∀ y ∈ e.baseSet,
      ∀ out : ι × ι,
        MDiffAt (localTwoTensorComponent (I := I) e b h out) y)
    {y : M} (hyFrame : y ∈ e.baseSet)
    (hyChart : y ∈ (extChartAt I chartCenter).source)
    (hcovFirst : MDiffAt
      (fun z => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
          (E := T₃) z
        (covariantTwoTensorCovariantDerivative cov h z)) y)
    (hlocalFirst : ∀ out : ι × ι, ∀ j : ι,
      MDiffAt (localFirstCovariantComponent (I := I) cov e b h out j) y)
    (huAt : DifferentiableWithinAt ℝ
      (localTensorCoordinates (I := I) chartCenter e b h) (Set.range I)
      ((extChartAt I chartCenter) y))
    (huNear : ∀ᶠ w in
        nhdsWithin ((extChartAt I chartCenter) y) (Set.range I),
      DifferentiableWithinAt ℝ
        (localTensorCoordinates (I := I) chartCenter e b h) (Set.range I) w)
    (hDu : DifferentiableWithinAt ℝ
      (localTensorCoordinateDerivative (I := I) chartCenter e b h)
      (Set.range I) ((extChartAt I chartCenter) y))
    (hV : ∀ i : ι, DifferentiableWithinAt ℝ
      (localFrameInChart (I := I) chartCenter e b i) (Set.range I)
      ((extChartAt I chartCenter) y))
    (hgamma₂ : ∀ out input : ι × ι, ∀ j : ι,
      DifferentiableWithinAt ℝ
        (localTwoTensorConnectionCoefficientInChart (I := I)
          cov chartCenter e b out input j) (Set.range I)
        ((extChartAt I chartCenter) y))
    (p q : ι) :
    connectionLaplacian cov h y
        (e.localFrame b p y) (e.localFrame b q y) =
      (localTensorHeatPrincipalCoefficient (I := I) chartCenter e b
            ((extChartAt I chartCenter) y)
            (localTensorCoordinateSecondDerivative (I := I)
              chartCenter e b h ((extChartAt I chartCenter) y)) +
        localTensorHeatFirstCoefficient (I := I) cov chartCenter e b
            ((extChartAt I chartCenter) y)
            (localTensorCoordinateDerivative (I := I)
              chartCenter e b h ((extChartAt I chartCenter) y)) +
        localTensorHeatZeroCoefficient (I := I) cov chartCenter e b
            ((extChartAt I chartCenter) y)
            (localTensorCoordinates (I := I)
              chartCenter e b h ((extChartAt I chartCenter) y))) (q, p) := by
  rw [connectionLaplacian_apply_eq_inChart
    (I := I) cov chartCenter e b hregFrame hregChart hyFrame hyChart
      hcovFirst hlocalFirst p q]
  have hz : (extChartAt I chartCenter) y ∈ Set.range I :=
    extChartAt_target_subset_range chartCenter
      ((extChartAt I chartCenter).map_source hyChart)
  exact congrFun
    (localConnectionLaplacianComponentInChart_eq_secondOrder
      (I := I) cov chartCenter e b h hz huAt huNear hDu hV hgamma₂) (q, p)

end AnalyticPDE
end RicciFlow
