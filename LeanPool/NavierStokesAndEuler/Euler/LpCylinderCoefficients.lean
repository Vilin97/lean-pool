/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPaths
public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedConstructedEvolution
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Angle-independent coefficients acting on the genuine cylinder L²

Spatial coefficient fields act on R³×AddCircle by pointwise multiplication.
The mixed translation covariance is an equality of actual L² operators.
The homogeneous evolution is constructed from the spatial coefficient's
Banach-algebra fundamental fields. Its H3 bound is used only on spatial
support; no angular regularity or global extension of H3 is assumed.
-/

@[expose] public section


noncomputable section

namespace EulerLpCylinderCoefficients

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpSupportedMultiplier EulerLpSupportedEvolution
  EulerLpSupportedConstructedEvolution EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLinearDuhamel EulerLinearFundamentalExistence EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Cache the standard `NormedRing (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderCoefficients1 : NormedRing (V →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderCoefficients2 : NormedRing (Space →ᵇ V →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedRing (LiftDomain period →ᵇ V →L[ℝ] V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderCoefficients3 : NormedRing (LiftDomain period →ᵇ V →L[ℝ] V) :=
    inferInstance

variable (S : Set Space) (hS : MeasurableSet S)

/-- Cache the standard `NormedAddCommGroup (Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderCoefficients4 : NormedAddCommGroup (Supported period V S hS) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (Supported period V S hS)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderCoefficients5 : InnerProductSpace ℝ (Supported period V S hS) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V S hS →L[ℝ] Supported period V S
hS)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderCoefficients6 : NormedAddCommGroup (Supported period V S hS →L[ℝ]
    Supported period V S hS)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V S hS →L[ℝ] Supported period V S hS)`
instance to shorten typeclass synthesis. -/
local instance instLpCylinderCoefficients7 : NormedSpace ℝ (Supported period V S hS →L[ℝ] Supported
    period V S hS) :=
    inferInstance
/-- Cache the standard `NormedRing (Supported period V S hS →L[ℝ] Supported period V S hS)`
instance to shorten typeclass synthesis. -/
local instance instLpCylinderCoefficients8 : NormedRing (Supported period V S hS →L[ℝ] Supported
    period V S hS) :=
    inferInstance

/-- The actual cylinder operator of a spatial coefficient. -/
def liftedOperator (A : Space →ᵇ V →L[ℝ] V) : Supported period V S hS →L[ℝ] Supported period V S hS
    :=
  operator (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)
      (fieldLift (W := V →L[ℝ] V) period A)

omit [CompleteSpace V] in
/-- Mixed translation intertwines the actual spatial multiplication operators. -/
theorem operator_intertwines (Ω : Set Space) (hΩ : MeasurableSet Ω)
    (a : LiftTangent) (ha : EulerLpSupportedTranslation.shiftedSet a.1 S ⊆ Ω)
    (A : Space →ᵇ V →L[ℝ] V) (u : Supported period V S hS) :
    liftedOperator period Ω hΩ (translated A a.1)
        (EulerLpCylinderTranslation.intoLarger period a S Ω hS hΩ ha u) =
      EulerLpCylinderTranslation.intoLarger period a S Ω hS hΩ ha (liftedOperator period S hS A u)
          := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [full_ae (liftMeasure period)
      (fieldLift (W := V →L[ℝ] V) period (translated A a.1))
      (translate (V := V) period a (u : CylinderL2 period V)),
    translate_ae period a (u : CylinderL2 period V),
    translate_ae period a (full (liftMeasure period) (fieldLift (W := V →L[ℝ] V) period A)
      (u : CylinderL2 period V)),
    (measurePreserving_translation period (coveringMap period a)).quasiMeasurePreserving.ae
      (full_ae (liftMeasure period) (fieldLift (W := V →L[ℝ] V) period A)
        (u : CylinderL2 period V))]
    with x hl hu hr hA
  exact hl.trans ((congrArg (fieldLift (W := V →L[ℝ] V) period (translated A a.1) x) hu).trans
    (hA.symm.trans hr.symm))

variable (T : ℝ)

/-- The entire coefficient time path, acting on the supported cylinder. -/
def liftedOperatorPath (A : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V)) :
    C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS) :=
  operatorPath (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS) T
    (fieldPathLift (K := Icc (0 : ℝ) T) (W := V →L[ℝ] V) period A)

omit [CompleteSpace V] in
/-- Pointwise operator lifting does not enlarge the uniform coefficient norm. -/
theorem liftedOperatorPath_norm (A : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V)) :
    ‖liftedOperatorPath period S hS T A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact (operator_norm_le (liftMeasure period) (spatialSet period S) (spatialSet_measurable period
      S hS)
    (fieldLift (W := V →L[ℝ] V) period (A t)) ‖A t‖ (norm_nonneg _)
    (fun x _ => (A t).norm_coe_le_norm x.1)).trans (A.norm_coe_le_norm t)

/-- The literal linear map underlying coefficient-path lifting. -/
def liftedOperatorPathLinear : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V) →ₗ[ℝ]
    C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS) where
  toFun := liftedOperatorPath period S hS T
  map_add' A D := by
    apply ContinuousMap.ext
    intro t
    exact operator_add (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
        hS)
      (fieldLift (W := V →L[ℝ] V) period (A t)) (fieldLift (W := V →L[ℝ] V) period (D t))
  map_smul' r A := by
    apply ContinuousMap.ext
    intro t
    exact operator_smul (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
        hS)
      r (fieldLift (W := V →L[ℝ] V) period (A t))

/-- Lifting spatial coefficient paths to actual cylinder operators is a linear contraction. -/
def liftedOperatorPathMap : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V) →L[ℝ]
    C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS) :=
  -- The domain norm instance is given through the cached ring instance, as inferred before;
  -- naming it spares a costly unification with the coefficient type still unknown.
  @LinearMap.mkContinuous _ _ C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V) _ _ _
    (@ContinuousMap.instSeminormedAddCommGroup _ _ _ _ (instLpCylinderCoefficients2
      (V := V)).toNonUnitalNormedRing.toNonUnitalSeminormedRing.toSeminormedAddCommGroup)
    _ _ _ _ (liftedOperatorPathLinear (V := V) period S hS T) 1 (fun A => by
    exact (liftedOperatorPath_norm period S hS T A).trans_eq (one_mul ‖A‖).symm)

omit [CompleteSpace V] in
@[simp] theorem liftedOperatorPathMap_apply (A : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V)) :
    liftedOperatorPathMap (V := V) period S hS T A = liftedOperatorPath period S hS T A := rfl

omit [CompleteSpace V] in
/-- No coefficient amplitude is lost in the actual L² lifting. -/
theorem liftedOperatorPathMap_norm : ‖liftedOperatorPathMap (V := V) period S hS T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  exact (liftedOperatorPath_norm period S hS T A).trans_eq (one_mul ‖A‖).symm

omit [CompleteSpace V] in
/-- The actual cylinder coefficient varies smoothly with all four covering parameters. -/
theorem mixedOperator_contDiff (B : SmoothCoefficientPath (Icc (0 : ℝ) T) (V →L[ℝ] V)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => liftedOperatorPath period S hS T
      (translateCoefficientPath B.field a.1)) :=
  (B.translation_contDiff.comp
    (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).continuousLinearMap_comp
      (liftedOperatorPathMap (V := V) period S hS T)

omit [CompleteSpace V] in
/-- Mixed coefficient jets obey the original spatial tensor bound, with constant one. -/
theorem mixedOperator_bound (B : SmoothCoefficientPath (Icc (0 : ℝ) T) (V →L[ℝ] V))
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (B.field t : Space → V →L[ℝ] V) x‖ ≤ C)
    (a : LiftTangent) :
    ‖iteratedFDeriv ℝ n (fun b : LiftTangent => liftedOperatorPath period S hS T
      (translateCoefficientPath B.field b.1)) a‖ ≤ C := by
  let f : Space → C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V) := translateCoefficientPath B.field
  have hf : ContDiff ℝ ∞ f := B.translation_contDiff
  have hright := (congrArg norm ((ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right
    hf a (i := n) (by simp))).trans_le
    ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ)).trans
        (B.norm_iteratedFDeriv_translation_le n C hC hb a.1)))
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (liftedOperatorPathMap (V := V) period S hS T)
    ((hf.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a)) (n := n) (by simp)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (liftedOperatorPathMap_norm period S hS T)
    (norm_nonneg _)).trans ((one_mul _).trans_le hright))

variable (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))

/-- The cylinder evolution is constructed from the genuine spatial fundamental fields. -/
def constructedEvolution : Evolution T hT (liftedOperatorPath (V := V) period S hS T B) :=
  liftEvolution (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
      hS) T hT
    (fieldPathLift (K := Icc (0 : ℝ) T) (W := V →L[ℝ] V) period B)
    (fieldPathLift (K := Icc (0 : ℝ) T) (W := V →L[ℝ] V) period (fundamentalPath T hT B).forward)
    (fieldPathLift (K := Icc (0 : ℝ) T) (W := V →L[ℝ] V) period (fundamentalPath T hT B).backward)
    (fun t x _ => congrArg (fun A : Space →ᵇ V →L[ℝ] V => A x.1)
      ((fundamentalPath T hT B).forward_backward t))
    (fun t x _ => congrArg (fun A : Space →ᵇ V →L[ℝ] V => A x.1)
      ((fundamentalPath T hT B).backward_forward t))
    (fun t ht x => fundamental_pointwise_derivative T hT B t ht x.1)

/-- The cylinder propagator retains the exact relative H3 profile on spatial support. -/
theorem constructedEvolution_propagator_norm
    (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t) (C : ℝ) (hC : 0 ≤ C)
    (hprop : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x ∈ S,
      ‖((fundamentalPath T hT B).forward t x).comp ((fundamentalPath T hT B).backward s x)‖ ≤ C*g
          t/g s)
    (t s : Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖(constructedEvolution period S hS T hT B).propagator t s‖ ≤ C*g t/g s := by
  refine liftEvolution_propagator_norm (liftMeasure period) (spatialSet period S)
    (spatialSet_measurable period S hS) T hT _ _ _ _ _ _ g hg C hC ?_ t s hst
  exact fun t s hst x hx => hprop t s hst x.1 hx

end EulerLpCylinderCoefficients
