/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.VariationIntegral

/-!
# Integrated coordinate second variation

This module packages one endpoint-spliced coordinate variation piece and
proves its exact integrated second-variation formula.  Compact-rectangle
domination justifies both differentiations under the integral; the
pointwise coordinate commutator supplies the actual curvature tensor; and
the fundamental theorem of calculus reduces the acceleration term to the
two endpoint pairings.
-/

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology Interval

namespace BonnetMyersEntry.LocalGeodesicData

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

variable [RiemannianBundle (TangentSpace I : M → Type u)]

namespace CoordinateBrokenVariationData

variable (d : CoordinateBrokenVariationData E)

/-- Half squared speed of one packaged coordinate variation piece. -/
def energyDensity (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (e t : ℝ) : ℝ :=
  coordinateEnergyDensity (I := I) (M := M) x₀ basis
    (fun s ↦ d.position s t) (fun s ↦ d.velocity s t) e

/-- First parameter derivative of `energyDensity`. -/
def firstVariationDensity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (e t : ℝ) : ℝ :=
  coordinateFirstVariationDensity (I := I) (M := M) cov x₀ basis
    (fun s ↦ d.position s t) (fun s ↦ d.field s t)
    (fun s ↦ d.velocity s t) (fun s ↦ d.mixed s t) e

/-- Index-form density of the base variational field. -/
def indexDensity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (t : ℝ) : ℝ :=
  let y := (extChartAt I x₀).symm (d.z t)
  let DJ := coordinateCovariantFieldDerivative
    (I := I) (M := M) cov x₀ basis (d.z t) (d.dz t) (d.J t) (d.dJ t)
  inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis DJ y)
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis DJ y) -
    inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis (d.J t) y)
      (curvature (cov := cov) y
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis (d.J t) y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis (d.dz t) y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis (d.dz t) y))

/-- Boundary pairing in the second-variation formula. -/
def boundaryPairing
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (t : ℝ) : ℝ :=
  let y := (extChartAt I x₀).symm (d.z t)
  inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
      (d.secondCovariantField cov x₀ basis t) y)
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
      (d.dz t) y)

/-- Ordinary time derivative displayed for `boundaryPairing`. -/
def boundaryDerivative
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (t : ℝ) : ℝ :=
  let y := (extChartAt I x₀).symm (d.z t)
  let DtC := coordinateCovariantFieldDerivative
    (I := I) (M := M) cov x₀ basis (d.z t) (d.dz t)
      (d.secondCovariantField cov x₀ basis t)
      (d.secondCovariantFieldTimeDerivative cov x₀ basis t)
  inner ℝ
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis DtC y)
    (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis
      (d.dz t) y)

/-- Full second parameter derivative at an arbitrary parameter value.  At
zero it specializes to `secondVariationDensity`. -/
def secondVariationDensityAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (e t : ℝ) : ℝ :=
  let Q := d.position e t
  let W := d.field e t
  let V := d.velocity e t
  let dV := d.mixed e t
  let c := d.secondField e t
  let dc := d.secondMixed e
  let y := (extChartAt I x₀).symm Q
  let B := coordinateCovariantFieldDerivative
    (I := I) (M := M) cov x₀ basis Q V W dV
  let C := c + coordinateParallelOperator
    (I := I) (M := M) (E := E) cov x₀ basis Q W W
  let dC := dc +
    fderiv ℝ (fun q ↦ coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ basis q W W) Q V +
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ basis Q dV W +
    coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ basis Q W dV
  let DtC := coordinateCovariantFieldDerivative
    (I := I) (M := M) cov x₀ basis Q V C dC
  inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis B y)
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis B y) -
    inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis W y)
      (curvature (cov := cov) y
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis W y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis V y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis V y)) +
    inner ℝ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis DtC y)
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) basis V y)

/-- Full pointwise second derivative, before integrating the boundary term. -/
def secondVariationDensity
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (t : ℝ) : ℝ :=
  d.indexDensity cov x₀ basis t + d.boundaryDerivative cov x₀ basis t

/-- Pointwise first derivative of the packaged energy density. -/
theorem energyDensity_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {e t : ℝ}
    (hleft : HasDerivAt d.leftNode (d.leftVelocity e) e)
    (hright : HasDerivAt d.rightNode (d.rightVelocity e) e)
    (htarget : d.position e t ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ basis k =ᶠ[
        nhds ((extChartAt I x₀).symm (d.position e t))]
        (trivializationAt E TM x₀).localFrame basis k) :
    HasDerivAt (fun s ↦ d.energyDensity (I := I) (M := M) x₀ basis s t)
      (d.firstVariationDensity cov x₀ basis e t) e := by
  have hQ := coordinateBrokenVariationPiece_hasDerivAt_parameter
    d.a d.b t d.z d.J d.leftNode d.rightNode d.leftVelocity d.rightVelocity
      hleft hright
  have hV := coordinateBrokenVariationVelocity_hasDerivAt_parameter
    d.a d.b t d.dz d.dJ d.z d.J d.leftNode d.rightNode
      d.leftVelocity d.rightVelocity hleft hright
  exact coordinateEnergyDensity_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ basis hmetric hQ hV htarget hframe

/-- Pointwise second derivative at an arbitrary variation parameter. -/
theorem firstVariationDensity_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    {e t : ℝ}
    (hleftNode : HasDerivAt d.leftNode (d.leftVelocity e) e)
    (hrightNode : HasDerivAt d.rightNode (d.rightVelocity e) e)
    (hleftVelocity : HasDerivAt d.leftVelocity (d.leftAcceleration e) e)
    (hrightVelocity : HasDerivAt d.rightVelocity (d.rightAcceleration e) e)
    (htarget : d.position e t ∈ (extChartAt I x₀).target)
    {O : Set M} (hOopen : IsOpen O)
    (hO : (extChartAt I x₀).symm (d.position e t) ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ basis k y =
        (trivializationAt E TM x₀).localFrame basis k y) :
    HasDerivAt
      (fun s ↦ d.firstVariationDensity cov x₀ basis s t)
      (d.secondVariationDensityAt cov x₀ basis e t) e := by
  have hQ := coordinateBrokenVariationPiece_hasDerivAt_parameter
    d.a d.b t d.z d.J d.leftNode d.rightNode d.leftVelocity d.rightVelocity
      hleftNode hrightNode
  have hW := coordinateBrokenVariationField_hasDerivAt_parameter
    d.a d.b t d.J d.leftVelocity d.rightVelocity
      d.leftAcceleration d.rightAcceleration hleftVelocity hrightVelocity
  have hV := coordinateBrokenVariationVelocity_hasDerivAt_parameter
    d.a d.b t d.dz d.dJ d.z d.J d.leftNode d.rightNode
      d.leftVelocity d.rightVelocity hleftNode hrightNode
  have hdV := coordinateBrokenVariationMixed_hasDerivAt_parameter
    d.a d.b t d.dJ d.J d.leftVelocity d.rightVelocity
      d.leftAcceleration d.rightAcceleration hleftVelocity hrightVelocity
  unfold CoordinateBrokenVariationData.firstVariationDensity
    CoordinateBrokenVariationData.secondVariationDensityAt
    CoordinateBrokenVariationData.position
    CoordinateBrokenVariationData.velocity
    CoordinateBrokenVariationData.field
    CoordinateBrokenVariationData.mixed
    CoordinateBrokenVariationData.secondField
    CoordinateBrokenVariationData.secondMixed
  exact coordinateSecondVariationDensity_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ basis hmetric htorsion
      hQ hW hV hdV htarget hOopen hO hOframe

/-- Pointwise second derivative at the base parameter.  The result is the
index density plus the time derivative of the boundary pairing. -/
theorem firstVariationDensity_hasDerivAt_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    {t : ℝ}
    (hleftNode : HasDerivAt d.leftNode (d.leftVelocity 0) 0)
    (hrightNode : HasDerivAt d.rightNode (d.rightVelocity 0) 0)
    (hleftVelocity : HasDerivAt d.leftVelocity (d.leftAcceleration 0) 0)
    (hrightVelocity : HasDerivAt d.rightVelocity (d.rightAcceleration 0) 0)
    (hleftNode0 : d.leftNode 0 = d.z d.a)
    (hrightNode0 : d.rightNode 0 = d.z d.b)
    (hleftVelocity0 : d.leftVelocity 0 = d.J d.a)
    (hrightVelocity0 : d.rightVelocity 0 = d.J d.b)
    (htarget : d.z t ∈ (extChartAt I x₀).target)
    {O : Set M} (hOopen : IsOpen O)
    (hO : (extChartAt I x₀).symm (d.z t) ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ basis k y =
        (trivializationAt E TM x₀).localFrame basis k y) :
    HasDerivAt
      (fun e ↦ d.firstVariationDensity cov x₀ basis e t)
      (d.secondVariationDensity cov x₀ basis t) 0 := by
  have hQ := coordinateBrokenVariationPiece_hasDerivAt_parameter
    d.a d.b t d.z d.J d.leftNode d.rightNode d.leftVelocity d.rightVelocity
      hleftNode hrightNode
  have hW := coordinateBrokenVariationField_hasDerivAt_parameter
    d.a d.b t d.J d.leftVelocity d.rightVelocity
      d.leftAcceleration d.rightAcceleration hleftVelocity hrightVelocity
  have hV := coordinateBrokenVariationVelocity_hasDerivAt_parameter
    d.a d.b t d.dz d.dJ d.z d.J d.leftNode d.rightNode
      d.leftVelocity d.rightVelocity hleftNode hrightNode
  have hdV := coordinateBrokenVariationMixed_hasDerivAt_parameter
    d.a d.b t d.dJ d.J d.leftVelocity d.rightVelocity
      d.leftAcceleration d.rightAcceleration hleftVelocity hrightVelocity
  have h := coordinateSecondVariationDensity_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ basis hmetric htorsion
      hQ hW hV hdV
      (by simpa [CoordinateBrokenVariationData.position,
        hleftNode0, hrightNode0] using htarget)
      hOopen (by simpa [CoordinateBrokenVariationData.position,
        hleftNode0, hrightNode0] using hO) hOframe
  have hposition0 : coordinateBrokenVariationPiece d.a d.b d.z d.J
      d.leftNode d.rightNode 0 t = d.z t :=
    coordinateBrokenVariationPiece_zero d.a d.b d.z d.J
      d.leftNode d.rightNode hleftNode0 hrightNode0 t
  rw [hposition0] at h
  simpa [CoordinateBrokenVariationData.firstVariationDensity,
    CoordinateBrokenVariationData.secondVariationDensity,
    CoordinateBrokenVariationData.indexDensity,
    CoordinateBrokenVariationData.boundaryDerivative,
    CoordinateBrokenVariationData.secondCovariantField,
    CoordinateBrokenVariationData.secondCovariantFieldTimeDerivative,
    coordinateBrokenVariationSecondCovariantField,
    coordinateBrokenVariationSecondCovariantFieldTimeDerivative,
    CoordinateBrokenVariationData.position,
    CoordinateBrokenVariationData.velocity,
    CoordinateBrokenVariationData.field,
    CoordinateBrokenVariationData.mixed,
    CoordinateBrokenVariationData.secondField,
    CoordinateBrokenVariationData.secondMixed,
    hleftNode0, hrightNode0, hleftVelocity0, hrightVelocity0] using h

/-- The arbitrary-parameter second density specializes at zero to the base
index density plus boundary derivative. -/
theorem secondVariationDensityAt_zero_eq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hleftNode0 : d.leftNode 0 = d.z d.a)
    (hrightNode0 : d.rightNode 0 = d.z d.b)
    (hleftVelocity0 : d.leftVelocity 0 = d.J d.a)
    (hrightVelocity0 : d.rightVelocity 0 = d.J d.b)
    (t : ℝ) :
    d.secondVariationDensityAt cov x₀ basis 0 t =
      d.secondVariationDensity cov x₀ basis t := by
  have hposition0 : coordinateBrokenVariationPiece d.a d.b d.z d.J
      d.leftNode d.rightNode 0 t = d.z t :=
    coordinateBrokenVariationPiece_zero d.a d.b d.z d.J
      d.leftNode d.rightNode hleftNode0 hrightNode0 t
  unfold CoordinateBrokenVariationData.secondVariationDensityAt
    CoordinateBrokenVariationData.secondVariationDensity
    CoordinateBrokenVariationData.indexDensity
    CoordinateBrokenVariationData.boundaryDerivative
    CoordinateBrokenVariationData.secondCovariantField
    CoordinateBrokenVariationData.secondCovariantFieldTimeDerivative
    coordinateBrokenVariationSecondCovariantField
    coordinateBrokenVariationSecondCovariantFieldTimeDerivative
    CoordinateBrokenVariationData.position
    CoordinateBrokenVariationData.velocity
    CoordinateBrokenVariationData.field
    CoordinateBrokenVariationData.mixed
    CoordinateBrokenVariationData.secondField
    CoordinateBrokenVariationData.secondMixed
  rw [hposition0]
  simp [
    hleftNode0, hrightNode0,
    hleftVelocity0, hrightVelocity0]

/-- The packaged boundary term has the displayed ordinary time derivative
along a coordinate geodesic. -/
theorem boundaryPairing_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {t : ℝ}
    (hz : HasDerivAt d.z (d.dz t) t)
    (hdz : HasDerivAt d.dz (d.ddz t) t)
    (hJ : HasDerivAt d.J (d.dJ t) t)
    (hgeodesic : coordinateCovariantFieldDerivative
      (I := I) (M := M) cov x₀ basis
        (d.z t) (d.dz t) (d.dz t) (d.ddz t) = 0)
    (htarget : d.z t ∈ (extChartAt I x₀).target)
    (hframe : ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ basis k =ᶠ[
        nhds ((extChartAt I x₀).symm (d.z t))]
        (trivializationAt E TM x₀).localFrame basis k) :
    HasDerivAt (d.boundaryPairing cov x₀ basis)
      (d.boundaryDerivative cov x₀ basis t) t := by
  unfold CoordinateBrokenVariationData.boundaryPairing
    CoordinateBrokenVariationData.boundaryDerivative
    CoordinateBrokenVariationData.secondCovariantField
    CoordinateBrokenVariationData.secondCovariantFieldTimeDerivative
  exact coordinateBrokenVariationBoundaryPairing_hasDerivAt
    (I := I) (M := M) (E := E) cov x₀ basis hmetric
      d.a d.b t d.ddz d.dz d.dJ d.z d.J
      d.leftAcceleration d.rightAcceleration hz hdz hJ hgeodesic htarget hframe

theorem boundaryPairing_eq_zero_of_secondCovariantField_eq_zero
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {t : ℝ} (hzero : d.secondCovariantField cov x₀ basis t = 0) :
    d.boundaryPairing cov x₀ basis t = 0 := by
  let y := (extChartAt I x₀).symm (d.z t)
  have hcomb : coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) basis (0 : E) y = 0 := by
    have h := coordinateFrameCombination_smul
      (I := I) (M := M) x₀ basis (y := y) 0 (d.dz t)
    simpa using h
  unfold CoordinateBrokenVariationData.boundaryPairing
  dsimp only
  rw [hzero, hcomb, inner_zero_left]

/-- Integrated second variation on one chart piece.  The only surviving
boundary contribution is the difference of the endpoint pairings. -/
theorem iteratedDeriv_two_integral_energyDensity_eq
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    [IsContMDiffRiemannianBundle I 2 E TM]
    (hmetric : cov.IsMetricCompatibleTangent)
    (htorsion : cov.torsion = 0)
    {s : Set ℝ} (hs : IsCompact s) (hs0 : s ∈ nhds (0 : ℝ))
    (hab : d.a ≤ d.b)
    (henergy : ContinuousOn
      (fun p : ℝ × ℝ ↦ d.energyDensity (I := I) (M := M)
        x₀ basis p.1 p.2) (s ×ˢ Icc d.a d.b))
    (hfirst : ContinuousOn
      (fun p : ℝ × ℝ ↦ d.firstVariationDensity cov x₀ basis p.1 p.2)
        (s ×ˢ Icc d.a d.b))
    (hsecond : ContinuousOn
      (fun p : ℝ × ℝ ↦ d.secondVariationDensityAt cov x₀ basis p.1 p.2)
        (s ×ˢ Icc d.a d.b))
    (hleftNode : ∀ e ∈ s,
      HasDerivAt d.leftNode (d.leftVelocity e) e)
    (hrightNode : ∀ e ∈ s,
      HasDerivAt d.rightNode (d.rightVelocity e) e)
    (hleftVelocity : ∀ e ∈ s,
      HasDerivAt d.leftVelocity (d.leftAcceleration e) e)
    (hrightVelocity : ∀ e ∈ s,
      HasDerivAt d.rightVelocity (d.rightAcceleration e) e)
    (htarget : ∀ e ∈ s, ∀ t ∈ Icc d.a d.b,
      d.position e t ∈ (extChartAt I x₀).target)
    {O : Set M} (hOopen : IsOpen O)
    (hO : ∀ e ∈ s, ∀ t ∈ Icc d.a d.b,
      (extChartAt I x₀).symm (d.position e t) ∈ O)
    (hOframe : ∀ y ∈ O, ∀ k : Fin (Module.finrank ℝ E),
      smoothFrame (I := I) (M := M) (E := E) x₀ basis k y =
        (trivializationAt E TM x₀).localFrame basis k y)
    (hleftNode0 : d.leftNode 0 = d.z d.a)
    (hrightNode0 : d.rightNode 0 = d.z d.b)
    (hleftVelocity0 : d.leftVelocity 0 = d.J d.a)
    (hrightVelocity0 : d.rightVelocity 0 = d.J d.b)
    (hboundary : ∀ t ∈ Icc d.a d.b,
      HasDerivAt (d.boundaryPairing cov x₀ basis)
        (d.boundaryDerivative cov x₀ basis t) t)
    (hindexIntegrable : IntervalIntegrable
      (d.indexDensity cov x₀ basis) volume d.a d.b)
    (hboundaryIntegrable : IntervalIntegrable
      (d.boundaryDerivative cov x₀ basis) volume d.a d.b) :
    iteratedDeriv 2
        (fun e ↦ ∫ t in d.a..d.b,
          d.energyDensity (I := I) (M := M) x₀ basis e t) 0 =
      (∫ t in d.a..d.b, d.indexDensity cov x₀ basis t) +
        d.boundaryPairing cov x₀ basis d.b -
        d.boundaryPairing cov x₀ basis d.a := by
  have hframe : ∀ e ∈ s, ∀ t ∈ Icc d.a d.b,
      ∀ k : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ basis k =ᶠ[
          nhds ((extChartAt I x₀).symm (d.position e t))]
          (trivializationAt E TM x₀).localFrame basis k := by
    intro e he t ht k
    filter_upwards [hOopen.mem_nhds (hO e he t ht)] with y hy
    exact hOframe y hy k
  have hdiff₁ : ∀ e ∈ s, ∀ t ∈ Icc d.a d.b,
      HasDerivAt
        (fun y ↦ d.energyDensity (I := I) (M := M) x₀ basis y t)
        (d.firstVariationDensity cov x₀ basis e t) e := by
    intro e he t ht
    exact d.energyDensity_hasDerivAt cov x₀ basis hmetric
      (hleftNode e he) (hrightNode e he) (htarget e he t ht)
      (hframe e he t ht)
  have hdiff₂ : ∀ e ∈ s, ∀ t ∈ Icc d.a d.b,
      HasDerivAt
        (fun y ↦ d.firstVariationDensity cov x₀ basis y t)
        (d.secondVariationDensityAt cov x₀ basis e t) e := by
    intro e he t ht
    exact d.firstVariationDensity_hasDerivAt cov x₀ basis hmetric htorsion
      (hleftNode e he) (hrightNode e he)
      (hleftVelocity e he) (hrightVelocity e he)
      (htarget e he t ht) hOopen (hO e he t ht) hOframe
  have hsecondIntegral :=
    intervalIntegral_iteratedDeriv_two_eq_of_continuousOn
      (F := fun e t ↦ d.energyDensity (I := I) (M := M) x₀ basis e t)
      (F₁ := fun e t ↦ d.firstVariationDensity cov x₀ basis e t)
      (F₂ := fun e t ↦ d.secondVariationDensityAt cov x₀ basis e t)
      hs hs0 hab henergy hfirst hsecond hdiff₁ hdiff₂
  rw [hsecondIntegral]
  have hzero : (fun t ↦ d.secondVariationDensityAt cov x₀ basis 0 t) =
      d.secondVariationDensity cov x₀ basis := by
    funext t
    exact d.secondVariationDensityAt_zero_eq cov x₀ basis
      hleftNode0 hrightNode0 hleftVelocity0 hrightVelocity0 t
  rw [hzero]
  unfold CoordinateBrokenVariationData.secondVariationDensity
  rw [intervalIntegral.integral_add hindexIntegrable hboundaryIntegrable]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hboundary t (by simpa [uIcc_of_le hab] using ht))
    hboundaryIntegrable]
  ring

end CoordinateBrokenVariationData

end BonnetMyersEntry.LocalGeodesicData
