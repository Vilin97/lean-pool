/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPaths
public import LeanPool.NavierStokesAndEuler.Euler.LpSupportedConstructedEvolution
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets

@[expose] public section

/-!
# Angle-independent coefficients acting on the genuine cylinder L²

Spatial coefficient fields act on R³×AddCircle by pointwise multiplication.
The mixed translation covariance is an equality of actual L² operators.
The homogeneous evolution is constructed from the spatial coefficient's
Banach-algebra fundamental fields. Its H3 bound is used only on spatial
support; no angular regularity or global extension of H3 is assumed.
-/

noncomputable section

namespace EulerLpCylinderCoefficients

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpSupportedMultiplier EulerLpSupportedEvolution
  EulerLpSupportedConstructedEvolution EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLinearDuhamel EulerLinearFundamentalExistence EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

private local instance : NormedRing (V →L[ℝ] V) := inferInstance
private local instance : NormedRing (Space →ᵇ V →L[ℝ] V) := inferInstance
private local instance : NormedRing (LiftDomain period →ᵇ V →L[ℝ] V) := inferInstance

variable (S : Set Space) (hS : MeasurableSet S)

private local instance : NormedAddCommGroup (Supported period V S hS) := inferInstance
private local instance : InnerProductSpace ℝ (Supported period V S hS) := inferInstance
private local instance : NormedAddCommGroup (Supported period V S hS →L[ℝ] Supported period V S hS)
  := inferInstance
private local instance : NormedSpace ℝ (Supported period V S hS →L[ℝ] Supported period V S hS) :=
  inferInstance
private local instance : NormedRing (Supported period V S hS →L[ℝ] Supported period V S hS) :=
  inferInstance

/-- The actual cylinder operator of a spatial coefficient. -/
def liftedOperator (A : Space →ᵇ V →L[ℝ] V) : Supported period V S hS →L[ℝ] Supported period V S hS
  :=
  operator (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)
    (fieldLift period A)

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
  filter_upwards [full_ae (liftMeasure period) (fieldLift period (translated A a.1))
      (translate period a (u : CylinderL2 period V)),
    translate_ae period a (u : CylinderL2 period V),
    translate_ae period a (full (liftMeasure period) (fieldLift period A) (u : CylinderL2 period
      V)),
    (measurePreserving_translation period (coveringMap period a)).quasiMeasurePreserving.ae
      (full_ae (liftMeasure period) (fieldLift period A) (u : CylinderL2 period V))]
    with x hl hu hr hA
  change (full (liftMeasure period) (fieldLift period (translated A a.1))
    (translate period a (u : CylinderL2 period V))) x =
      (translate period a (full (liftMeasure period) (fieldLift period A) (u : CylinderL2 period
        V))) x
  rw [hl,hu,hr,hA]
  rfl

variable (T : ℝ)

/-- The entire coefficient time path, acting on the supported cylinder. -/
def liftedOperatorPath (A : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)) :
    C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS) :=
  operatorPath (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS) T
    (fieldPathLift period A)

omit [CompleteSpace V] in
/-- Pointwise operator lifting does not enlarge the uniform coefficient norm. -/
theorem liftedOperatorPath_norm (A : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)) :
    ‖liftedOperatorPath period S hS T A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact (operator_norm_le (liftMeasure period) (spatialSet period S) (spatialSet_measurable period
    S hS)
    (fieldLift period (A t)) ‖A t‖ (norm_nonneg _)
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
      (fieldLift period (A t)) (fieldLift period (D t))
  map_smul' r A := by
    apply ContinuousMap.ext
    intro t
    exact operator_smul (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
      hS)
      r (fieldLift period (A t))

/-- Lifting spatial coefficient paths to actual cylinder operators is a linear contraction. -/
def liftedOperatorPathMap : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V) →L[ℝ]
    C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS) :=
  (liftedOperatorPathLinear period S hS T).mkContinuous 1 (fun A => by
    change ‖liftedOperatorPath period S hS T A‖ ≤ 1*‖A‖
    exact (liftedOperatorPath_norm period S hS T A).trans_eq (one_mul ‖A‖).symm)

omit [CompleteSpace V] in
@[simp] theorem liftedOperatorPathMap_apply (A : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V)) :
    liftedOperatorPathMap (V := V) period S hS T A = liftedOperatorPath period S hS T A := rfl

omit [CompleteSpace V] in
/-- No coefficient amplitude is lost in the actual L² lifting. -/
theorem liftedOperatorPathMap_norm : ‖liftedOperatorPathMap (V := V) period S hS T‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  change ‖liftedOperatorPath period S hS T A‖ ≤ 1*‖A‖
  exact (liftedOperatorPath_norm period S hS T A).trans_eq (one_mul ‖A‖).symm

omit [CompleteSpace V] in
/-- The actual cylinder coefficient varies smoothly with all four covering parameters. -/
theorem mixedOperator_contDiff (B : SmoothCoefficientPath (Icc (0 : ℝ) T) (V →L[ℝ] V)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => liftedOperatorPath period S hS T
      (translateCoefficientPath B.field a.1)) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
    (F := C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS))
    (liftedOperatorPathMap period S hS T)).comp
      (B.translation_contDiff.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff)

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
  have hright : ‖iteratedFDeriv ℝ n (f ∘ ContinuousLinearMap.fst ℝ Space ℝ) a‖ ≤ C := by
    rw [(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hf a (by simp)]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    calc
      _ ≤ ‖iteratedFDeriv ℝ n f a.1‖ * ∏ _i : Fin n, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ =>
          ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
      _ ≤ C := by simpa only [Finset.prod_const_one, mul_one] using
        B.norm_iteratedFDeriv_translation_le n C hC hb a.1
  have hleft := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := LiftTangent)
    (F := C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
    (G := C(Icc (0 : ℝ) T,Supported period V S hS →L[ℝ] Supported period V S hS))
    (liftedOperatorPathMap period S hS T)
    ((hf.comp (ContinuousLinearMap.fst ℝ Space ℝ).contDiff).contDiffAt (x := a)) (n := n) (by simp)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (liftedOperatorPathMap_norm period S hS T)
    (norm_nonneg _)).trans (by simpa only [one_mul] using hright))

variable (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))

/-- The cylinder evolution is constructed from the genuine spatial fundamental fields. -/
def constructedEvolution : Evolution T hT (liftedOperatorPath (V := V) period S hS T B) :=
  liftEvolution (V := V) (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
    hS) T hT
    (fieldPathLift period B)
    (fieldPathLift period (fundamentalPath T hT B).forward)
    (fieldPathLift period (fundamentalPath T hT B).backward)
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
  change ‖(operator (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)
      (fieldLift period ((fundamentalPath T hT B).forward t))).comp
    (operator (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S hS)
      (fieldLift period ((fundamentalPath T hT B).backward s)))‖ ≤ _
  rw [← operator_mul]
  exact operator_norm_le (liftMeasure period) (spatialSet period S) (spatialSet_measurable period S
    hS)
    _ (C*g t/g s) (div_nonneg (mul_nonneg hC (hg t).le) (hg s).le)
    (fun x hx => hprop t s hst x.1 hx)

end EulerLpCylinderCoefficients
