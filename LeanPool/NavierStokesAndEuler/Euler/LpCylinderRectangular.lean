/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPaths
public import LeanPool.NavierStokesAndEuler.Euler.LpOperatorFieldPath
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus

@[expose] public section

/-!
# Rectangular coefficient fields on the actual cylinder

Spatial fields of operators E→F act on R³×AddCircle L², and on its closed
spatial-support subspaces. All coefficient and continuous-path lifting maps
are contractions. The exact mixed-translation identity is proved on L²
classes, so projected forcing and physical-frame application can use the
same external-word calculus as the forward solution.
-/

noncomputable section

namespace EulerLpCylinderRectangular

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (LiftDomain period →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (LiftDomain period →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 period E) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 period E) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 period F) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 period F) := inferInstance
private local instance : NormedAddCommGroup (CylinderL2 period E →L[ℝ] CylinderL2 period F) :=
  inferInstance
private local instance : NormedSpace ℝ (CylinderL2 period E →L[ℝ] CylinderL2 period F) :=
  inferInstance
private local instance : NormedAddCommGroup C(K,Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ C(K,Space →ᵇ E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup C(K,CylinderL2 period E) := inferInstance
private local instance : NormedSpace ℝ C(K,CylinderL2 period E) := inferInstance
private local instance : NormedAddCommGroup C(K,CylinderL2 period F) := inferInstance
private local instance : NormedSpace ℝ C(K,CylinderL2 period F) := inferInstance
private local instance : NormedAddCommGroup C(K,CylinderL2 period E →L[ℝ] CylinderL2 period F) :=
  inferInstance
private local instance : NormedSpace ℝ C(K,CylinderL2 period E →L[ℝ] CylinderL2 period F) :=
  inferInstance
private local instance : NormedAddCommGroup (C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period
  F)) := inferInstance
private local instance : NormedSpace ℝ (C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F)) :=
  inferInstance

/-- Actual multiplication on cylinder L² by an angle-independent field. -/
def fullOperatorMap : (Space →ᵇ E →L[ℝ] F) →L[ℝ]
    (CylinderL2 period E →L[ℝ] CylinderL2 period F) :=
  (EulerLpOperatorField.fullMap (E := E) (F := F) (liftMeasure period)).comp (fieldLift period)

@[simp] theorem fullOperatorMap_apply (A : Space →ᵇ E →L[ℝ] F) :
    fullOperatorMap period A = EulerLpOperatorField.full (liftMeasure period) (fieldLift period A)
      := rfl

theorem fullOperatorMap_norm : ‖fullOperatorMap (E := E) (F := F) period‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul,fullOperatorMap_apply]
  exact (EulerLpOperatorField.full_norm (liftMeasure period) (fieldLift period A)).trans
    ((fieldLift period).le_opNorm A |>.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (fieldLift_norm (W := E →L[ℝ] F)
        period) (norm_nonneg A)))

/-- The same contraction uniformly along a compact time set. -/
def fullPathMap : C(K,Space →ᵇ E →L[ℝ] F) →L[ℝ]
    C(K,CylinderL2 period E →L[ℝ] CylinderL2 period F) :=
  (fullOperatorMap (E := E) (F := F) period).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem fullPathMap_apply (A : C(K,Space →ᵇ E →L[ℝ] F)) (t : K) :
    fullPathMap period A t = fullOperatorMap period (A t) := rfl

theorem fullPathMap_norm : ‖fullPathMap (K := K) (E := E) (F := F) period‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact ((fullOperatorMap (E := E) (F := F) period).le_opNorm (A t)).trans
    ((mul_le_mul_of_nonneg_right (fullOperatorMap_norm (E := E) (F := F) period) (norm_nonneg (A
      t))).trans
      (by simpa only [one_mul] using A.norm_coe_le_norm t))

/-- The actual coefficient-to-multiplication map on continuous cylinder paths. -/
def fullMultiplierMap : C(K,Space →ᵇ E →L[ℝ] F) →L[ℝ]
    (C(K,CylinderL2 period E) →L[ℝ] C(K,CylinderL2 period F)) :=
  (EulerContinuousPathCalculus.coefficientMap (K := K)
    (E := CylinderL2 period E) (F := CylinderL2 period F)).comp (fullPathMap period)

@[simp] theorem fullMultiplierMap_apply (A : C(K,Space →ᵇ E →L[ℝ] F))
    (u : C(K,CylinderL2 period E)) (t : K) :
    fullMultiplierMap period A u t = fullOperatorMap period (A t) (u t) := rfl

theorem fullMultiplierMap_norm : ‖fullMultiplierMap (K := K) (E := E) (F := F) period‖ ≤ 1 := by
  calc
    _ ≤ ‖EulerContinuousPathCalculus.coefficientMap (K := K)
        (E := CylinderL2 period E) (F := CylinderL2 period F)‖ *
        ‖fullPathMap (K := K) (E := E) (F := F) period‖ :=
      ContinuousLinearMap.opNorm_comp_le
        (EulerContinuousPathCalculus.coefficientMap (K := K)
          (E := CylinderL2 period E) (F := CylinderL2 period F))
        (fullPathMap (K := K) (E := E) (F := F) period)
    _ ≤ 1 * 1 := mul_le_mul
      (EulerContinuousPathCalculus.coefficientMap_norm (K := K)
        (E := CylinderL2 period E) (F := CylinderL2 period F))
      (fullPathMap_norm (K := K) (E := E) (F := F) period)
      (norm_nonneg (fullPathMap (K := K) (E := E) (F := F) period)) zero_le_one
    _ = 1 := one_mul 1

/-- Literal mixed translations intertwine the actual rectangular L² multipliers. -/
theorem fullOperator_translation (a : LiftTangent) (A : Space →ᵇ E →L[ℝ] F)
    (u : CylinderL2 period E) :
    fullOperatorMap period (translated A a.1) (translate period a u) =
      translate period a (fullOperatorMap period A u) := by
  apply Lp.ext
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period (translated A
    a.1))
      (translate period a u),
    translate_ae period a u,
    translate_ae period a (fullOperatorMap period A u),
    (measurePreserving_translation period (coveringMap period a)).quasiMeasurePreserving.ae
      (EulerLpOperatorField.full_ae (liftMeasure period) (fieldLift period A) u)]
    with x hl hu hr hA
  change (EulerLpOperatorField.full (liftMeasure period) (fieldLift period (translated A a.1))
    (translate period a u)) x = (translate period a (fullOperatorMap period A u)) x
  rw [hl,hu,hr]
  exact hA.symm

/-- The exact mixed-translation identity holds in the uniform continuous-path space. -/
theorem fullMultiplier_translation (a : LiftTangent) (A : C(K,Space →ᵇ E →L[ℝ] F))
    (u : C(K,CylinderL2 period E)) :
    fullMultiplierMap period (translateCoefficientPath A a.1) (pathTranslate period a u) =
      pathTranslate period a (fullMultiplierMap period A u) := by
  apply ContinuousMap.ext
  intro t
  exact fullOperator_translation period a (A t) (u t)

variable (S : Set Space) (hS : MeasurableSet S)

private local instance : NormedAddCommGroup (Supported period E S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period E S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period F S hS) := inferInstance
private local instance : NormedSpace ℝ (Supported period F S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period E S hS →L[ℝ] Supported period F S hS)
  := inferInstance
private local instance : NormedSpace ℝ (Supported period E S hS →L[ℝ] Supported period F S hS) :=
  inferInstance
private local instance : NormedAddCommGroup C(K,Supported period E S hS) := inferInstance
private local instance : NormedSpace ℝ C(K,Supported period E S hS) := inferInstance
private local instance : NormedAddCommGroup C(K,Supported period F S hS) := inferInstance
private local instance : NormedSpace ℝ C(K,Supported period F S hS) := inferInstance
private local instance : NormedAddCommGroup C(K,Supported period E S hS →L[ℝ] Supported period F S
  hS) := inferInstance
private local instance : NormedSpace ℝ C(K,Supported period E S hS →L[ℝ] Supported period F S hS)
  := inferInstance
private local instance : NormedAddCommGroup (C(K,Supported period E S hS) →L[ℝ] C(K,Supported
  period F S hS)) := inferInstance
private local instance : NormedSpace ℝ (C(K,Supported period E S hS) →L[ℝ] C(K,Supported period F S
  hS)) := inferInstance

/-- Restriction to the closed spatial-support subspaces. -/
def supportedOperatorMap : (Space →ᵇ E →L[ℝ] F) →L[ℝ]
    (Supported period E S hS →L[ℝ] Supported period F S hS) :=
  (EulerLpOperatorField.supportedMap (E := E) (F := F)
    (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)).comp (fieldLift
      period)

@[simp] theorem supportedOperatorMap_coe (A : Space →ᵇ E →L[ℝ] F) (u : Supported period E S hS) :
    (supportedOperatorMap period S hS A u : CylinderL2 period F) =
      fullOperatorMap period A (u : CylinderL2 period E) := rfl

theorem supportedOperatorMap_norm : ‖supportedOperatorMap (E := E) (F := F) period S hS‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  exact (EulerLpOperatorField.supported_norm (liftMeasure period) (spatialSet period S)
    (spatialSet_measurable period S hS) (fieldLift period A) ‖A‖ (norm_nonneg A)
    (fun x _ => A.norm_coe_le_norm x.1))

def supportedPathMap : C(K,Space →ᵇ E →L[ℝ] F) →L[ℝ]
    C(K,Supported period E S hS →L[ℝ] Supported period F S hS) :=
  (supportedOperatorMap (E := E) (F := F) period S hS).compLeftContinuous ℝ K

def supportedMultiplierMap : C(K,Space →ᵇ E →L[ℝ] F) →L[ℝ]
    (C(K,Supported period E S hS) →L[ℝ] C(K,Supported period F S hS)) :=
  (EulerContinuousPathCalculus.coefficientMap (K := K)
    (E := Supported period E S hS) (F := Supported period F S hS)).comp (supportedPathMap period S
      hS)

@[simp] theorem supportedMultiplierMap_apply (A : C(K,Space →ᵇ E →L[ℝ] F))
    (u : C(K,Supported period E S hS)) (t : K) :
    supportedMultiplierMap period S hS A u t = supportedOperatorMap period S hS (A t) (u t) := rfl

/-- Inclusion identifies the supported product with the actual full-cylinder product. -/
theorem include_supportedMultiplier (A : C(K,Space →ᵇ E →L[ℝ] F))
    (u : C(K,Supported period E S hS)) :
    includePath period S hS (supportedMultiplierMap period S hS A u) =
      fullMultiplierMap period A (includePath period S hS u) := rfl

end EulerLpCylinderRectangular
