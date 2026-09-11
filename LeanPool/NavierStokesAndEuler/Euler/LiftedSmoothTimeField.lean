/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
import LeanPool.NavierStokesAndEuler.Euler.PacketNormalDriftBounds
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Trace
import LeanPool.NavierStokesAndEuler.Euler.ClassicalDivergence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit

/-! The actual lifted velocity retains the small normal component in its
coefficient estimates. No division by the packet amplitude is used. -/

section

/-! The four-dimensional transport velocity associated with a lifted
solenoidal field has zero ordinary trace on the real covering space. -/

@[expose] public section

noncomputable section

namespace EulerLiftedTransportTrace

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives EulerSmoothLimit EulerClassicalDivergence
open scoped ContDiff

/-- Transport linear, given by `(κ • ContinuousLinearMap.id ℝ Vector3).prod (toDual ℝ Vector3
m)`. -/
def transportLinear (κ : ℝ) (m : Vector3) : Vector3 →L[ℝ] LiftTangent :=
  (κ • ContinuousLinearMap.id ℝ Vector3).prod (toDual ℝ Vector3 m)

@[simp] theorem transportLinear_apply (κ : ℝ) (m v : Vector3) :
    transportLinear κ m v = transportDirection κ m v := rfl

theorem transportLinear_single (κ : ℝ) (m : Vector3) (i : Fin 3) :
    transportLinear κ m (EuclideanSpace.single i 1) = coordinateDirection κ m i := by
  apply Prod.ext
  · rfl
  · simp [transportLinear,coordinateDirection,EuclideanSpace.inner_single_right]

theorem trace_transportLinear (κ : ℝ) (m : Vector3) (L : LiftTangent →L[ℝ] Vector3) :
    LinearMap.trace ℝ LiftTangent ((transportLinear κ m).comp L).toLinearMap =
      ∑ i : Fin 3, (L (coordinateDirection κ m i)) i := by
  change LinearMap.trace ℝ LiftTangent ((transportLinear κ m).toLinearMap ∘ₗ L.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  change LinearMap.trace ℝ Vector3 (L.comp (transportLinear κ m)).toLinearMap = _
  rw [← coordinateTrace_eq_linearTrace]
  simp only [coordinateTrace,sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,transportLinear_single]
  rfl

variable (P κ : ℝ) (m : Vector3) (g : LiftDomain P → Vector3)

/-- Cover velocity, given by `transportDirection κ m (g (coveringMap P z))`. -/
def coverVelocity (z : LiftTangent) : LiftTangent :=
  transportDirection κ m (g (coveringMap P z))

theorem coverVelocity_trace
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (z : LiftTangent) :
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (coverVelocity P κ m g) z).toLinearMap =
      ∑ i : Fin 3, (fieldDerivative P (coordinateDirection κ m i) g (coveringMap P z)) i := by
  have he : g ∘ coveringMap P = localFieldLift P g 0 := by
    funext w
    simp [localFieldLift,coveringMap]
  have hdg : Differentiable ℝ (g ∘ coveringMap P) := by
    rw [he]
    exact (hg 0).differentiable (by simp)
  have hd := (transportLinear κ m).hasFDerivAt.comp z (hdg z).hasFDerivAt
  change HasFDerivAt (coverVelocity P κ m g) ((transportLinear κ m).comp (fderiv ℝ (g ∘ coveringMap
      P) z)) z at hd
  rw [hd.fderiv,trace_transportLinear,he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fieldDerivative,fderiv_localFieldLift_cover]

variable [Fact (0 < P)]

theorem coverVelocity_trace_zero (u : LiftL2 P)
    (hu : u ∈ divergenceFreeSpace P κ m)
    (hrep : (u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] g)
    (hg : ∀ q, ContDiff ℝ ∞ (localFieldLift P g q)) (z : LiftTangent) :
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (coverVelocity P κ m g) z).toLinearMap = 0 := by
  rw [coverVelocity_trace P κ m g hg]
  exact divergenceFree_classical_divergence_zero P κ m u hu g hrep hg _

end EulerLiftedTransportTrace

end
end

end

@[expose] public section

noncomputable section

namespace EulerLiftedSmoothTimeField

open InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedTransportTrace EulerPacketCylinderField
      EulerCylinderScalarPrimitive
open scoped ContDiff BoundedContinuousFunction

/-- Angular injection, given by `(ContinuousLinearMap.inr ℝ Space ℝ).comp scalarProject`. -/
def angularInjection : Space →L[ℝ] LiftTangent :=
  (ContinuousLinearMap.inr ℝ Space ℝ).comp scalarProject

theorem angularInjection_norm : ‖angularInjection‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  change ‖((0 : Space), scalarProject v)‖ ≤ 1 * ‖v‖
  simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), one_mul,
    scalarProject_norm] using scalarProject.le_opNorm v

theorem spatialInjection_norm : ‖ContinuousLinearMap.inl ℝ Space ℝ‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem transportLinear_split (κ : ℝ) (m : Space) :
    transportLinear κ m = κ • ContinuousLinearMap.inl ℝ Space ℝ +
      angularInjection.comp (normalComponentMap m) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · simp [transportLinear, angularInjection]
  · simp [transportLinear, angularInjection]

theorem transport_tensor_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : ℝ) (m : Space) {n : ℕ} (A : E [×n]→L[ℝ] Space) :
    ‖(transportLinear κ m).compContinuousMultilinearMap A‖ ≤
      |κ| * ‖A‖ + ‖(normalComponentMap m).compContinuousMultilinearMap A‖ := by
  have he : (transportLinear κ m).compContinuousMultilinearMap A =
      κ • (ContinuousLinearMap.inl ℝ Space ℝ).compContinuousMultilinearMap A +
        angularInjection.compContinuousMultilinearMap
          ((normalComponentMap m).compContinuousMultilinearMap A) := by
    apply ContinuousMultilinearMap.ext
    intro v
    exact congrArg (fun L : Space →L[ℝ] LiftTangent => L (A v)) (transportLinear_split κ m)
  rw [he]
  calc
    _ ≤ ‖κ • (ContinuousLinearMap.inl ℝ Space ℝ).compContinuousMultilinearMap A‖ +
        ‖angularInjection.compContinuousMultilinearMap
          ((normalComponentMap m).compContinuousMultilinearMap A)‖ := norm_add_le _ _
    _ ≤ |κ| * (1 * ‖A‖) +
        1 * ‖(normalComponentMap m).compContinuousMultilinearMap A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (((ContinuousLinearMap.inl ℝ Space ℝ).norm_compContinuousMultilinearMap_le A).trans
            (mul_le_mul_of_nonneg_right spatialInjection_norm (norm_nonneg A))) (abs_nonneg κ)
      · exact (angularInjection.norm_compContinuousMultilinearMap_le _).trans
          (mul_le_mul_of_nonneg_right angularInjection_norm (norm_nonneg _))
    _ = _ := by rw [one_mul, one_mul]

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instLiftedSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instLiftedSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] LiftTangent)` instance to shorten
typeclass synthesis. -/
local instance instLiftedSmoothTimeField3 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] LiftTangent) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] LiftTangent)` instance to shorten typeclass
synthesis. -/
local instance instLiftedSmoothTimeField4 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] LiftTangent) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] Space))` instance to shorten
typeclass synthesis. -/
local instance instLiftedSmoothTimeField5 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] Space))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] Space))` instance to shorten typeclass
synthesis. -/
local instance instLiftedSmoothTimeField6 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] Space)) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] LiftTangent))` instance to shorten
typeclass synthesis. -/
local instance instLiftedSmoothTimeField7 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ]
    LiftTangent)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] LiftTangent))` instance to shorten
typeclass synthesis. -/
local instance instLiftedSmoothTimeField8 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] LiftTangent))
    := inferInstance

/-- Lift, given by `A.map (transportLinear κ m)`. -/
def lift (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) : SmoothTimeField K E LiftTangent :=
  A.map (transportLinear κ m)

@[simp] theorem lift_apply (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) (t : K) (x : E) :
    (lift A κ m).field t x = (κ • A.field t x, inner ℝ m (A.field t x)) := rfl

theorem lift_jet_norm_le (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) (n : ℕ) :
    ‖(lift A κ m).jet n‖ ≤ |κ| * ‖A.jet n‖ + ‖(A.map (normalComponentMap m)).jet n‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  change ‖(transportLinear κ m).compContinuousMultilinearMap (A.jet n t x)‖ ≤ _
  exact (transport_tensor_norm κ m _).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (((A.jet n t).norm_coe_le_norm x).trans ((A.jet n).norm_coe_le_norm t)) (abs_nonneg κ))
      ((((A.map (normalComponentMap m)).jet n t).norm_coe_le_norm x).trans
        (((A.map (normalComponentMap m)).jet n).norm_coe_le_norm t)))

theorem lift_jet_norm_le_full (A : SmoothTimeField K E Space) (κ : ℝ) (m : Space) (n : ℕ) :
    ‖(lift A κ m).jet n‖ ≤ (|κ| + ‖m‖) * ‖A.jet n‖ := by
  apply (lift_jet_norm_le A κ m n).trans
  have hm := ((A.map_jet_norm_le (normalComponentMap m) n).trans
    (mul_le_mul_of_nonneg_right (normalComponentMap_norm_le m) (norm_nonneg (A.jet n))))
  simpa only [add_mul] using add_le_add (le_refl (|κ| * ‖A.jet n‖)) hm

end EulerLiftedSmoothTimeField
