/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftEquation
public import LeanPool.NavierStokesAndEuler.Euler.LiftedSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftFieldDecomposition
import LeanPool.NavierStokesAndEuler.Euler.CylinderMeasureDescent
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldGraphBounds
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerSmoothTimeField
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftRadiusBounds
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionAssemblySourceTower
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTensorBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderBoundedCover
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Compact
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual smooth four-dimensional coefficients of the corrected packet.
The lifted field equals the constructed exact velocity, has the genuine
time derivative, is periodic, and has zero divergence. -/

section

/-! Transposing a tensor with continuous bounded path values gives an
actual continuous path of bounded tensor fields. Finite coordinates prove
continuity; the norm estimate uses the original multilinear map directly
and therefore has constant one. -/

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerContinuousBoundedTensor

variable {K X E V : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instContinuousBoundedTensor2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor3 (n : ℕ) : NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor4 (n : ℕ) : NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

/-- Coordinates, given by `ContinuousLinearMap.pi (fun w => (ContinuousLinearMap.id ℝ (E
[×n]→L[ℝ] V)).flipMultilinear (fun i => Module.finBasis ℝ E (w i)))`. -/
def coordinates (n : ℕ) :
    (E [×n]→L[ℝ] V) →L[ℝ] ((Fin n → Fin (Module.finrank ℝ E)) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear
      (fun i => Module.finBasis ℝ E (w i)))

omit [FiniteDimensional ℝ V] in
private theorem coordinates_injective (n : ℕ) :
    Function.Injective (coordinates (E := E) (V := V) n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => Module.finBasis ℝ E)
  intro w
  exact congrFun h w

/-- Reassembly, given by `((coordinates (E := E) (V := V)
n).toLinearMap.leftInverse).toContinuousLinearMap`. -/
def reassembly (n : ℕ) :
    ((Fin n → Fin (Module.finrank ℝ E)) → V) →L[ℝ] (E [×n]→L[ℝ] V) :=
  ((coordinates (E := E) (V := V) n).toLinearMap.leftInverse).toContinuousLinearMap

private theorem reassembly_coordinates (n : ℕ) (A : E [×n]→L[ℝ] V) :
    reassembly n (coordinates n A) = A :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective n)) A

/-- Tuple bounded as an element of `(ι → (X →ᵇ V)) →L[ℝ] (X →ᵇ (ι → V))`. -/
def tupleBounded {ι : Type*} [Fintype ι] :
    (ι → (X →ᵇ V)) →L[ℝ] (X →ᵇ (ι → V)) := by
  classical
  exact ∑ i : ι,
    ((ContinuousLinearMap.single ℝ (fun _ : ι => V) i).compLeftContinuousBounded X).comp
      (ContinuousLinearMap.proj i)

omit [FiniteDimensional ℝ V] in
private theorem tupleBounded_apply {ι : Type*} [Fintype ι]
    (u : ι → (X →ᵇ V)) (x : X) (i : ι) :
    tupleBounded u x i = u i x := by
  classical
  simp [tupleBounded]

/-- Tensor path, bundling `toFun`, `continuous_toFun`. -/
def tensorPath (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) :
    C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun t := (reassembly (E := E) (V := V) n).compLeftContinuousBounded X
    (tupleBounded (fun w => A (fun i => Module.finBasis ℝ E (w i)) t))
  continuous_toFun :=
    ((reassembly (E := E) (V := V) n).compLeftContinuousBounded X).continuous.comp
      ((tupleBounded (X := X) (V := V)).continuous.comp
        (continuous_pi (fun w => (A (fun i => Module.finBasis ℝ E (w i))).continuous)))

omit [CompactSpace K] in
theorem tensorPath_eq (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) (t : K) (x : X) :
    tensorPath n A t x = (BoundedContinuousFunction.evalCLM ℝ x).compContinuousMultilinearMap
      ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A) := by
  change reassembly n (tupleBounded _ x) = _
  have he : tupleBounded (fun w => A (fun i => Module.finBasis ℝ E (w i)) t) x =
      coordinates n ((BoundedContinuousFunction.evalCLM ℝ x).compContinuousMultilinearMap
        ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A)) := by
    funext w
    rw [tupleBounded_apply]
    rfl
  rw [he, reassembly_coordinates]

omit [CompactSpace K] in
@[simp] theorem tensorPath_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V))
    (t : K) (x : X) (v : Fin n → E) : tensorPath n A t x v = A v t x := by
  rw [tensorPath_eq]
  rfl

/-- Cache the standard `NormedAddCommGroup (C(K, X →ᵇ (E [×n]→L[ℝ] V)))` instance to shorten
typeclass synthesis. -/
local instance instContinuousBoundedTensor5 (n : ℕ) : NormedAddCommGroup (C(K, X →ᵇ (E [×n]→L[ℝ]
    V))) := inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K, X →ᵇ (E [×n]→L[ℝ] V)))` instance to shorten
typeclass synthesis. -/
local instance instContinuousBoundedTensor6 (n : ℕ) : NormedSpace ℝ (C(K, X →ᵇ (E [×n]→L[ℝ] V))) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] C(K, X →ᵇ V))` instance to shorten
typeclass synthesis. -/
local instance instContinuousBoundedTensor7 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] C(K, X →ᵇ V))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] C(K, X →ᵇ V))` instance to shorten typeclass
synthesis. -/
local instance instContinuousBoundedTensor8 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] C(K, X →ᵇ V)) :=
    inferInstance

theorem tensorPath_norm_le (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) :
    ‖tensorPath n A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg A)
  intro v
  rw [tensorPath_apply]
  exact (((A v t).norm_coe_le_norm x).trans ((A v).norm_coe_le_norm t)).trans (A.le_opNorm v)

/-- Tensor path linear, bundling `toFun`, `map_add`, `map_smul`. -/
def tensorPathLinear (n : ℕ) :
    (E [×n]→L[ℝ] C(K, X →ᵇ V)) →ₗ[ℝ] C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun := tensorPath n
  map_add' A B := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, add_apply, ContinuousMap.add_apply,
      BoundedContinuousFunction.add_apply]
  map_smul' c A := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, smul_apply, ContinuousMap.smul_apply,
      BoundedContinuousFunction.smul_apply, RingHom.id_apply]

/-- Tensor path map, bundling `toLinearMap`, `cont`. -/
def tensorPathMap (n : ℕ) :
    (E [×n]→L[ℝ] C(K, X →ᵇ V)) →L[ℝ] C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toLinearMap := tensorPathLinear n
  cont := AddMonoidHomClass.continuous_of_bound
    (tensorPathLinear (K := K) (X := X) (E := E) (V := V) n) 1
    (fun A => by
      change ‖tensorPath n A‖ ≤ 1 * ‖A‖
      simpa only [one_mul] using tensorPath_norm_le n A)

@[simp] theorem tensorPathMap_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V))
    (t : K) (x : X) (v : Fin n → E) : tensorPathMap n A t x v = A v t x :=
  tensorPath_apply n A t x v

theorem tensorPathMap_norm_le (n : ℕ) :
    ‖tensorPathMap (K := K) (X := X) (E := E) (V := V) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖tensorPath n A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using tensorPath_norm_le n A

theorem tensorPath_iteratedFDeriv (f : E → C(K, X →ᵇ V)) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a : E) (t : K) (x : X) :
    tensorPathMap n (iteratedFDeriv ℝ n f a) t x =
      iteratedFDeriv ℝ n (fun b => f b t x) a := by
  change tensorPath n (iteratedFDeriv ℝ n f a) t x = _
  rw [tensorPath_eq]
  have ht := (ContinuousMap.evalCLM ℝ t).iteratedFDeriv_comp_left (x := a) hf.contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)
  rw [← ht]
  exact ((BoundedContinuousFunction.evalCLM ℝ x).iteratedFDeriv_comp_left
    ((ContinuousMap.evalCLM ℝ t).contDiff.comp hf).contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)).symm

end EulerContinuousBoundedTensor

end
end

end

section

/-! The actual finite packet fields supply bounded smooth cover
coefficients. Their fixed-Hq word bounds give uniform tensor-jet bounds,
with a single fixed coordinate radius conversion. -/

section

/-! Actual smooth bounded real-cover coefficients obtained from a smooth
mixed translation orbit in cylinder L². Every spatial tensor jet is a
continuous path in the uniform norm. No integrability on the real cover is
asserted or used. -/

@[expose] public section

noncomputable section

namespace EulerCylinderSmoothTimeField

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerCylinderBoundedCover EulerContinuousBoundedTensor
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {K : Type} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instCylinderSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instCylinderSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

/-- Cover jet, given by `tensorPathMap n (iteratedFDeriv ℝ n (coverOrbit P p hp) 0)`. -/
def coverJet (n : ℕ) : C(K, LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) :=
  tensorPathMap n (iteratedFDeriv ℝ n (coverOrbit P p hp) 0)

theorem coverJet_eq (n : ℕ) (t : K) (x : LiftTangent) :
    coverJet P p hp n t x = iteratedFDeriv ℝ n (coverPath P p hp t : LiftTangent → Space) x := by
  rw [coverJet, tensorPath_iteratedFDeriv _ (coverOrbit_contDiff P p hp)]
  have he : (fun a => coverOrbit P p hp a t x) =
      fun a => coverPath P p hp t (x+a) := funext (fun a => coverOrbit_apply P p hp a t x)
  rw [he, iteratedFDeriv_comp_add_left]
  simp only [add_zero]

theorem coverPath_smooth (t : K) :
    ContDiff ℝ ∞ (coverPath P p hp t : LiftTangent → Space) := by
  have hc := (BoundedContinuousFunction.evalCLM ℝ (0 : LiftTangent)).contDiff.comp
    ((ContinuousMap.evalCLM ℝ t).contDiff.comp (coverOrbit_contDiff P p hp))
  have he : (fun a => coverOrbit P p hp a t 0) =
      (coverPath P p hp t : LiftTangent → Space) := by
    funext a
    simpa only [zero_add] using coverOrbit_apply P p hp a t 0
  exact he ▸ hc

/-- Of path, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def ofPath : SmoothTimeField K LiftTangent Space where
  field := coverPath P p hp
  smooth := coverPath_smooth P p hp
  jet := coverJet P p hp
  jet_eq := coverJet_eq P p hp

@[simp] theorem ofPath_apply (t : K) (x : LiftTangent) :
    (ofPath P p hp).field t x = pointField P p hp t (coveringMap P x) := rfl

theorem ofPath_jet_norm_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (t : K) (x : LiftTangent),
      ‖iteratedFDeriv ℝ n (fun y => pointField P p hp t (coveringMap P y)) x‖ ≤ C) :
    ‖(ofPath P p hp).jet n‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).2
  intro t
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  rw [(ofPath P p hp).jet_eq]
  exact hb t x

end EulerCylinderSmoothTimeField

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerCylinderSmoothTimeField EulerCylinderCoordinates EulerCylinderSobolevSpace
  EulerPacketProfileRecursion EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {P T : ℝ} [Fact (0 < P)] {raw raw_t : VectorField}

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instPacketFieldSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

/-- To smooth time field, given by `ofPath P G.path G.orbit`. -/
def toSmoothTimeField (G : Field P T raw) : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  ofPath P G.path G.orbit

theorem toSmoothTimeField_apply (G : Field P T raw) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    G.toSmoothTimeField.field t x = raw (t,x) := (G.raw_eq t x.1 x.2).symm

theorem toSmoothTimeField_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (hT : 0 ≤ T) (hd : TimeDerivative hT G H) :
    SmoothTimeField.TimeDerivative T hT G.toSmoothTimeField H.toSmoothTimeField := by
  intro t x
  exact pointField_hasDerivWithinAt P T hT G.path H.path G.orbit H.orbit hd t (coveringMap P x)

theorem toSmoothTimeField_map_jet (G : Field P T raw) (L : Space →L[ℝ] Space) (n : ℕ) :
    (G.map L).toSmoothTimeField.jet n = (G.toSmoothTimeField.map L).jet n := by
  apply SmoothTimeField.jet_eq_of_field_eq
  intro t x
  rw [(G.map L).toSmoothTimeField_apply, SmoothTimeField.map_apply, G.toSmoothTimeField_apply]

theorem WordBound.toSmoothTimeField_jet_bound {G : Field P T raw} {q : ℕ} {R A : ℝ}
    (hG : G.WordBound q R A 0) (hq : 3 ≤ q) (hR : 0 ≤ R) (hA : 0 ≤ A) (n : ℕ) :
    ‖G.toSmoothTimeField.jet n‖ ≤ (sobolevEmbeddingConstant P 3*A) *
      (‖coordinateEquiv.symm.toContinuousLinearMap‖*R)^n * (n.factorial : ℝ)^2 := by
  have hS := sobolevEmbeddingConstant_nonneg P 3
  apply ofPath_jet_norm_le P G.path G.orbit n _ (by positivity)
  intro t x
  have he : (fun y => pointField P G.path G.orbit t (coveringMap P y)) =
      fun y => raw (t,y) := funext (fun y => (G.raw_eq t y.1 y.2).symm)
  rw [he]
  apply (hG.raw_tensor_le hq t n x).trans_eq
  simp only [majorant, Nat.add_zero, mul_pow]
  ring

end EulerPacketCylinderField.Field

end
end

end

section

/-! The constructed all-order correction and its true time derivative
are actual smooth bounded cover coefficients. Their quantitative bounds
come from the checked weighted Sobolev estimates. -/

@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerCylinderSobolevSpace
  EulerCylinderCoordinates
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}

/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Vector3)` instance to shorten
typeclass synthesis. -/
local instance instCorrectionSmoothTimeField1 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Vector3) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Vector3)` instance to shorten
typeclass synthesis. -/
local instance instCorrectionSmoothTimeField2 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ]
    Vector3) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3))`
instance to shorten typeclass synthesis. -/
local instance instCorrectionSmoothTimeField3 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3))` instance
to shorten typeclass synthesis. -/
local instance instCorrectionSmoothTimeField4 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Vector3)) := inferInstance

/-- Correction coefficient, given by `(B.fieldTower P).toSmoothTimeField`. -/
def Budget.correctionCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.fieldTower P).toSmoothTimeField

/-- Correction derivative coefficient, given by `(B.timeDerivativeTower P).toSmoothTimeField`. -/
def Budget.correctionDerivativeCoefficient (B : Budget P hT A) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Vector3 :=
  (B.timeDerivativeTower P).toSmoothTimeField

theorem Budget.correctionCoefficient_timeDerivative (B : Budget P hT A) :
    SmoothTimeField.TimeDerivative T hT.le (B.correctionCoefficient P)
      (B.correctionDerivativeCoefficient P) :=
  (B.fieldTower P).toSmoothTimeField_timeDerivative_of_interior (B.timeDerivativeTower P)
    hT.le 6 (by norm_num) (B.fieldTower_hasDerivAt_timeDerivativeTower P 6 le_rfl)

theorem Budget.correctionCoefficient_jet_bound (B : Budget P hT A) (n : ℕ) :
    ‖(B.correctionCoefficient P).jet n‖ ≤
      (sobolevEmbeddingConstant P 3 * B.correctionSize P) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖ * (B.reducedRadius P)⁻¹)^n *
          (n.factorial : ℝ)^2 :=
  (B.fieldTower P).toSmoothTimeField_jet_weighted n (B.reducedRadius P)
    (B.correctionSize P) (B.reducedRadius_pos P) (B.correctionSize_nonneg P)
    (B.fieldTower_reducedNorm P (n+6) n le_rfl)

theorem Budget.correctionDerivativeCoefficient_jet_bound (B : Budget P hT A)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (n : ℕ) (t : Icc (0 : ℝ) T),
      EulerSobolevGevreyOperators.weightedNorm P 6 n (B.reducedRadius P)
        ((B.timeDerivativeTower P).realization (n + 6) t) ≤ C) (n : ℕ) :
    ‖(B.correctionDerivativeCoefficient P).jet n‖ ≤
      (sobolevEmbeddingConstant P 3 * C) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖ * (B.reducedRadius P)⁻¹)^n *
          (n.factorial : ℝ)^2 :=
  (B.timeDerivativeTower P).toSmoothTimeField_jet_weighted n (B.reducedRadius P)
    C (B.reducedRadius_pos P) hC (hb n)

end EulerAllOrderDriftCorrection

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerCylinderSmoothOrbit
  EulerLiftedSmoothTimeField EulerLiftedTransportTrace EulerMetricTransport
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : Data P T}
  (B : Budget P hT A) {raw raw_t : VectorField}

/-- Packet coefficient, given by `G.toSmoothTimeField.add (B.correctionCoefficient P)`. -/
def Budget.packetCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  G.toSmoothTimeField.add (B.correctionCoefficient P)

/-- Packet derivative coefficient, given by `H.toSmoothTimeField.add
(B.correctionDerivativeCoefficient P)`. -/
def Budget.packetDerivativeCoefficient (H : Field P T raw_t) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  H.toSmoothTimeField.add (B.correctionDerivativeCoefficient P)

/-- Lifted packet coefficient, given by `lift (B.packetCoefficient P G) A.κ A.direction`. -/
def Budget.liftedPacketCoefficient (G : Field P T raw) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  lift (B.packetCoefficient P G) A.κ A.direction

/-- Lifted packet derivative coefficient, given by `lift (B.packetDerivativeCoefficient P H) A.κ
A.direction`. -/
def Budget.liftedPacketDerivativeCoefficient (H : Field P T raw_t) :
    SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent :=
  lift (B.packetDerivativeCoefficient P H) A.κ A.direction

theorem Budget.packetCoefficient_eq_corrected (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.packetCoefficient P G).field t x = (B.correctedFieldTower P).pointField t (coveringMap P x)
        := by
  rw [B.correctedFieldTower_eq P, FieldTower.add_pointField, hG]
  change G.toSmoothTimeField.field t x + (B.fieldTower P).pointField t (coveringMap P x) = _
  rw [G.toSmoothTimeField_apply]
  change raw (t,x) + (B.fieldTower P).pointField t (coveringMap P x) =
    G.toFieldTower.pointField t (x.1,(x.2 : AddCircle P)) +
      (B.fieldTower P).pointField t (coveringMap P x)
  rw [G.toFieldTower_pointField_raw]

theorem Budget.liftedPacketCoefficient_eq_corrected (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketCoefficient P G).field t x =
      transportDirection A.κ A.direction ((B.correctedFieldTower P).pointField t (coveringMap P x))
          := by
  change transportDirection A.κ A.direction ((B.packetCoefficient P G).field t x) = _
  rw [B.packetCoefficient_eq_corrected P G hG]

theorem Budget.packetCoefficient_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) :
    SmoothTimeField.TimeDerivative T hT.le (B.packetCoefficient P G)
      (B.packetDerivativeCoefficient P H) :=
  (G.toSmoothTimeField_timeDerivative H hT.le h).add (B.correctionCoefficient_timeDerivative P)

theorem Budget.liftedPacketCoefficient_timeDerivative (G : Field P T raw) (H : Field P T raw_t)
    (h : TimeDerivative hT.le G H) :
    SmoothTimeField.TimeDerivative T hT.le (B.liftedPacketCoefficient P G)
      (B.liftedPacketDerivativeCoefficient P H) :=
  (B.packetCoefficient_timeDerivative P G H h).map (transportLinear A.κ A.direction)

theorem Budget.liftedPacketCoefficient_periodic (G : Field P T raw)
    (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    (B.liftedPacketCoefficient P G).field t (x.1,(c : ℝ)+x.2) =
      (B.liftedPacketCoefficient P G).field t x := by
  have hc : coveringMap P (x.1,(c : ℝ)+x.2) = coveringMap P x :=
    EulerCylinderMeasureDescent.coveringMap_deck P c x
  change transportDirection A.κ A.direction
    (EulerCylinderSmoothOrbit.pointField P G.path G.orbit t (coveringMap P (x.1,(c : ℝ)+x.2)) +
      (B.fieldTower P).pointField t (coveringMap P (x.1,(c : ℝ)+x.2))) = _
  rw [hc]
  rfl

theorem Budget.liftedPacketCoefficient_trace (G : Field P T raw)
    (hG : A.approximation = G.toFieldTower) (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    LinearMap.trace ℝ LiftTangent
      (fderiv ℝ ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent)
          x).toLinearMap = 0 := by
  have he : ((B.liftedPacketCoefficient P G).field t : LiftTangent → LiftTangent) =
      coverVelocity P A.κ A.direction ((B.correctedFieldTower P).pointField t) :=
    funext (B.liftedPacketCoefficient_eq_corrected P G hG t)
  rw [he]
  exact coverVelocity_trace_zero P A.κ A.direction ((B.correctedFieldTower P).pointField t)
    ((B.correctedFieldTower P).field t) (B.correctedFieldTower_divergence P t)
    ((B.correctedFieldTower P).pointField_ae t) ((B.correctedFieldTower P).pointField_smooth t) x

end EulerAllOrderDriftCorrection
