/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldPrecomp
public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerJetLp
import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeField
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets

/-! A genuine coherent cylinder tower with a weighted bound yields actual
ordinary three-dimensional smooth L² slices and bounded coefficient paths.
The zero-angle restriction costs one fixed radius enlargement, independent
of the derivative order. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerLpTranslation EulerSmoothLimit
  EulerSobolevGevreyOperators EulerCylinderCoordinates EulerCylinderJetLp
  EulerCylinderGraphGevrey EulerGraphPullback EulerCylinderSobolevSpace
open scoped ContDiff BoundedContinuousFunction

variable {P T : ℝ} [Fact (0 < P)] (A : FieldTower P T)

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey2 : NormedSpace ℝ Space := inferInstance
/-- Cache the standard `NormedAddCommGroup LiftTangent` instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey3 : NormedAddCommGroup LiftTangent := inferInstance
/-- Cache the standard `NormedSpace ℝ LiftTangent` instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey4 : NormedSpace ℝ LiftTangent := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instFieldTowerGraphGevrey5 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instFieldTowerGraphGevrey6 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey7 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] Space))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey8 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, LiftTangent →ᵇ (LiftTangent
[×n]→L[ℝ] Space))` instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey9 (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T, LiftTangent
    →ᵇ (LiftTangent
    [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instFieldTowerGraphGevrey10 (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space [×n]→L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instFieldTowerGraphGevrey11 (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to
shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey12 (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ]
    Space)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instFieldTowerGraphGevrey13 (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ]
    Space)) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, Space →ᵇ (Space [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instFieldTowerGraphGevrey14 (n : ℕ) : NormedAddCommGroup C(Icc (0 : ℝ) T, Space →ᵇ
    (Space [×n]→L[ℝ]
    Space)) := inferInstance

/-- Zero graph field, bundling `field`, `smooth`, `integrable`. -/
def zeroGraphField (t : Icc (0 : ℝ) T) : SmoothL2Field Space where
  field := A.physicalPointField 1 0 t
  smooth := A.physicalPointField_smooth 1 0 t
  integrable n := A.physicalTensor_memLp 1 0 n t

/-- Zero graph coefficient, given by `A.toSmoothTimeField.precompLinear (ContinuousLinearMap.inl
ℝ Space ℝ)`. -/
def zeroGraphCoefficient : SmoothTimeField (Icc (0 : ℝ) T) Space Space :=
  A.toSmoothTimeField.precompLinear (ContinuousLinearMap.inl ℝ Space ℝ)

@[simp] theorem zeroGraphField_apply (t : Icc (0 : ℝ) T) (x : Space) :
    (A.zeroGraphField t).field x=A.pointField t (coveringMap P (x,0)) := by
  simp only [zeroGraphField,physicalPointField,EulerCylinderPhysicalTensor.physicalField,
    EulerGraphPressurePotential.cylinderGraph,coveringMap,inner_zero_left,mul_zero]

@[simp] theorem zeroGraphCoefficient_apply (t : Icc (0 : ℝ) T) (x : Space) :
    A.zeroGraphCoefficient.field t x=(A.zeroGraphField t).field x := by
  rw [zeroGraphField_apply]
  rfl

theorem zeroGraphField_jetLp (n : ℕ) (t : Icc (0 : ℝ) T) :
    (A.zeroGraphField t).jetLp n=A.physicalTensorPath 1 0 n t := by
  apply Lp.ext
  exact (SmoothL2Field.jetLp_ae _ n).trans (A.physicalTensorPath_ae 1 0 n t).symm

theorem zeroGraphField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (A.zeroGraphField t).jetLp n) := by
  simp only [zeroGraphField_jetLp]
  exact (A.physicalTensorPath 1 0 n).continuous

variable (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 ≤ C)
  (hb : ∀ n (t : Icc (0 : ℝ) T), weightedNorm P 6 n ρ (A.realization (n + 6) t) ≤ C)

include hρ hC hb in
theorem zeroGraphCoefficient_bound (n : ℕ) :
    ‖A.zeroGraphCoefficient.jet n‖ ≤ (sobolevEmbeddingConstant P 3*C) *
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*ρ⁻¹)^n*(n.factorial : ℝ)^2 := by
  have h := A.toSmoothTimeField.precompLinear_jet_norm_le
    (ContinuousLinearMap.inl ℝ Space ℝ) n
  have hL := pow_le_pow_left₀ (norm_nonneg (ContinuousLinearMap.inl ℝ Space ℝ))
    EulerLiftedSmoothTimeField.spatialInjection_norm n
  have hh := h.trans (mul_le_mul_of_nonneg_left hL (norm_nonneg (A.toSmoothTimeField.jet n)))
  simp only [one_pow,mul_one] at hh
  exact hh.trans (A.toSmoothTimeField_jet_weighted n ρ C hρ hC (hb n))

include hρ hC hb in
theorem zeroGraphField_bound (t : Icc (0 : ℝ) T) :
    (A.zeroGraphField t).HasJetBound
      (Real.sqrt (2/P+2*P)*C*(1+‖coordinateEquiv.symm.toContinuousLinearMap‖*ρ⁻¹))
      (4*(‖coordinateEquiv.symm.toContinuousLinearMap‖*ρ⁻¹)) := by
  let f : LiftTangent → Space := A.toSmoothTimeField.field t
  have he : (A.zeroGraphField t).field = f ∘ graphMap 1 (0 : Space) := by
    funext x
    rw [zeroGraphField_apply]
    change A.pointField t (coveringMap P (x,0)) = A.pointField t (coveringMap P (x,1*inner ℝ (0 :
        Space) x))
    rw [inner_zero_left,mul_zero]
  apply (SmoothL2Field.hasJetBound_iff _ _ _).mpr
  intro n
  have hh := (graph_Lp_bound P f (cover_periodic P (A.pointField t))
    (A.toSmoothTimeField.smooth t) 1 0 C (‖coordinateEquiv.symm.toContinuousLinearMap‖*ρ⁻¹)
    hC (by positivity)
    (fun j => A.coverTensor_memLp j t)
    (fun j => A.coverTensor_weighted j ρ C hρ t (hb j t)) n).2
  rw [he]
  simpa only [graphFactor,norm_zero,mul_zero,add_zero,mul_one] using hh

end EulerAllOrderCorrectionData.FieldTower
