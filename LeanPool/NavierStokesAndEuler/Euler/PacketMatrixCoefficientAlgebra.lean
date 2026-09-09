/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathOrbit

/-! Literal composition, scaling and spatial differentiation of the
actual matrix-coefficient witnesses. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.MatrixCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerBoundedFieldCalculus
  EulerPacketPointJets
open scoped ContDiff BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketMatrixCoefficientAlgebra1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketMatrixCoefficientAlgebra2 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketMatrixCoefficientAlgebra3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketMatrixCoefficientAlgebra4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

variable {T : ℝ} {a b : Domain → Space →L[ℝ] Space}

/-- Comp, bundling `path`, `orbit`, `fun`, `B` and the required compatibility proofs. -/
def comp (A : MatrixCoefficient T a) (B : MatrixCoefficient T b) :
    MatrixCoefficient T (fun z => (a z).comp (b z)) where
  path := pathCompositionMap A.path B.path
  orbit := by
    have he : translateCoefficientPath (pathCompositionMap A.path B.path) =
        fun v => pathCompositionMap (translateCoefficientPath A.path v) (translateCoefficientPath
            B.path v) := by
      funext v
      apply ContinuousMap.ext
      intro t
      apply BoundedContinuousFunction.ext
      intro x
      rfl
    rw [he]
    exact pathComposition_contDiff _ _ A.orbit B.orbit
  raw_eq t x θ := by rw [A.raw_eq,B.raw_eq]; rfl

/-- Add, bundling `path`, `orbit`, `raw_eq`. -/
def add (A : MatrixCoefficient T a) (B : MatrixCoefficient T b) :
    MatrixCoefficient T (a+b) where
  path := A.path+B.path
  orbit := by
    convert A.orbit.add B.orbit using 1
    funext v
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  raw_eq t x θ := by change a (t,(x,θ))+b (t,(x,θ)) = _; rw [A.raw_eq,B.raw_eq]; rfl

/-- Smul, bundling `path`, `orbit`, `raw_eq`. -/
def smul (A : MatrixCoefficient T a) (c : ℝ) : MatrixCoefficient T (c • a) where
  path := c • A.path
  orbit := by
    convert A.orbit.const_smul c using 1
    funext v
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  raw_eq t x θ := by change c • a (t,(x,θ)) = _; rw [A.raw_eq]; rfl

/-- Spatial derivative, bundling `path`, `orbit`, `raw_eq`, `have` and the required
compatibility proofs. -/
def spatialDerivative (A : MatrixCoefficient T a) (v : Space) :
    MatrixCoefficient T (fun z => fderiv ℝ (fun x => a (z.1,(x,z.2.2))) z.2.1 v) where
  path := orbitDerivativePath A.path v
  orbit := orbitDerivativePath_orbit A.path A.orbit v
  raw_eq t x θ := by
    have he : (fun y : Space => a (t,(y,θ))) = (A.path t : Space → Space →L[ℝ] Space) :=
      funext (fun y => A.raw_eq t y θ)
    change fderiv ℝ (fun y : Space => a (t,(y,θ))) x v = orbitDerivativePath A.path v t x
    rw [he,orbitDerivativePath_apply A.path A.orbit]

@[simp] theorem comp_path_apply (A : MatrixCoefficient T a) (B : MatrixCoefficient T b)
    (t : Icc (0 : ℝ) T) (x : Space) : (A.comp B).path t x = (A.path t x).comp (B.path t x) := rfl

@[simp] theorem smul_path_apply (A : MatrixCoefficient T a) (c : ℝ)
    (t : Icc (0 : ℝ) T) (x : Space) : (A.smul c).path t x = c • A.path t x := rfl

theorem spatialDerivative_path_apply (A : MatrixCoefficient T a) (v : Space)
    (t : Icc (0 : ℝ) T) (x : Space) :
    (A.spatialDerivative v).path t x = fderiv ℝ (A.path t : Space → Space →L[ℝ] Space) x v :=
  orbitDerivativePath_apply A.path A.orbit v t x

end EulerPacketCylinderField.MatrixCoefficient
