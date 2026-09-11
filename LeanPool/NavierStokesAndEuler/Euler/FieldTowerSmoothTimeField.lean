/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderBoundedCover
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative
import LeanPool.NavierStokesAndEuler.Euler.CylinderCoverTensor
public import LeanPool.NavierStokesAndEuler.Euler.CylinderCoveringDerivative
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPointwiseGevrey
import LeanPool.NavierStokesAndEuler.Euler.InjectivePathDerivativeWithin
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField

/-! An actual coherent Sobolev tower gives a smooth bounded coefficient
on the real cylinder cover, including all spatial jets in the continuous
uniform time norm. The construction uses its genuine derivative words;
no translation-orbit hypothesis is added. -/

section

/-! Continuous bounded coordinate fields reconstruct the actual tensor
field. This is a qualitative finite-dimensional construction; subsequent
norm estimates can use the actual tensor equality without a coordinate
reassembly constant. -/

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerBoundedTensorCoordinates

variable {K X E V ι : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace X] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instBoundedTensorCoordinates1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instBoundedTensorCoordinates2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instBoundedTensorCoordinates3 (n : ℕ) : NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instBoundedTensorCoordinates4 (n : ℕ) : NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

/-- Coordinates, given by `ContinuousLinearMap.pi (fun w => (ContinuousLinearMap.id ℝ (E
[×n]→L[ℝ] V)).flipMultilinear (fun i => b (w i)))`. -/
def coordinates (b : Module.Basis ι ℝ E) (n : ℕ) :
    (E [×n]→L[ℝ] V) →L[ℝ] ((Fin n → ι) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear (fun i => b (w i)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [Fintype ι] in
theorem coordinates_injective (b : Module.Basis ι ℝ E) (n : ℕ) :
    Function.Injective (coordinates (V := V) b n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => b)
  intro w
  exact congrFun h w

/-- Reassembly, given by `((coordinates (V := V) b
n).toLinearMap.leftInverse).toContinuousLinearMap`. -/
def reassembly (b : Module.Basis ι ℝ E) (n : ℕ) :
    ((Fin n → ι) → V) →L[ℝ] (E [×n]→L[ℝ] V) :=
  ((coordinates (V := V) b n).toLinearMap.leftInverse).toContinuousLinearMap

omit [FiniteDimensional ℝ E] in
theorem reassembly_coordinates (b : Module.Basis ι ℝ E) (n : ℕ) (A : E [×n]→L[ℝ] V) :
    reassembly b n (coordinates b n A) = A :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective b n)) A

/-- Tuple bounded as an element of `(j → (X →ᵇ V)) →L[ℝ] (X →ᵇ (j → V))`. -/
def tupleBounded {j : Type*} [Fintype j] :
    (j → (X →ᵇ V)) →L[ℝ] (X →ᵇ (j → V)) := by
  classical
  exact ∑ i : j,
    ((ContinuousLinearMap.single ℝ (fun _ : j => V) i).compLeftContinuousBounded X).comp
      (ContinuousLinearMap.proj i)

omit [FiniteDimensional ℝ V] in
theorem tupleBounded_apply {j : Type*} [Fintype j]
    (u : j → (X →ᵇ V)) (x : X) (i : j) :
    tupleBounded u x i = u i x := by
  classical
  simp [tupleBounded]

/-- Coordinate path, bundling `toFun`, `continuous_toFun`. -/
def coordinatePath (b : Module.Basis ι ℝ E) (n : ℕ)
    (u : (Fin n → ι) → C(K, X →ᵇ V)) : C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun t := (reassembly (V := V) b n).compLeftContinuousBounded X
    (tupleBounded (fun w => u w t))
  continuous_toFun :=
    ((reassembly (V := V) b n).compLeftContinuousBounded X).continuous.comp
      ((tupleBounded (X := X) (V := V)).continuous.comp
        (continuous_pi (fun w => (u w).continuous)))

omit [CompactSpace K] [FiniteDimensional ℝ E] in
theorem coordinatePath_eq (b : Module.Basis ι ℝ E) (n : ℕ)
    (u : (Fin n → ι) → C(K, X →ᵇ V)) (t : K) (x : X)
    (A : E [×n]→L[ℝ] V) (hu : ∀ w, u w t x = A (fun i => b (w i))) :
    coordinatePath b n u t x = A := by
  change reassembly b n (tupleBounded _ x) = A
  have he : tupleBounded (fun w => u w t) x = coordinates b n A := by
    funext w
    rw [tupleBounded_apply]
    exact hu w
  rw [he, reassembly_coordinates]

end EulerBoundedTensorCoordinates

universe u

namespace SmoothTimeField

open EulerBoundedTensorCoordinates

variable {K E V ι : Type u} [TopologicalSpace K] [CompactSpace K] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Of coordinate jets, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def ofCoordinateJets (b : Module.Basis ι ℝ E) (f : C(K, E →ᵇ V))
    (hf : ∀ t, ContDiff ℝ ∞ (f t : E → V))
    (u : (n : ℕ) → (Fin n → ι) → C(K, E →ᵇ V))
    (hu : ∀ n w t x, u n w t x = iteratedFDeriv ℝ n (f t : E → V) x (fun i => b (w i))) :
    SmoothTimeField K E V where
  field := f
  smooth := hf
  jet n := coordinatePath b n (u n)
  jet_eq n t x := coordinatePath_eq b n (u n) t x _ (fun w => hu n w t x)

end SmoothTimeField

end
end

end

@[expose] public section

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory ContinuousLinearMap EulerLiftedGradientSpace EulerSmoothLimit
  EulerMetricTransport EulerCylinderCoordinates EulerCylinderSobolev EulerCylinderSobolevSpace
  EulerCylinderBoundedCover EulerCylinderSmoothOrbit EulerSobolevWordLevel
  EulerSobolevGevreyOperators EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

/-- Cover basis, given by `(EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.map
coordinateLinearEquiv`. -/
def coverBasis : Module.Basis (Fin 4) ℝ LiftTangent :=
  (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.map coordinateLinearEquiv

@[simp] theorem coverBasis_apply (i : Fin 4) : coverBasis i = standardDirection i := by
  simp only [coverBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, standardDirection]
  rfl

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)

/-- Cache the standard `NormedAddCommGroup (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance instFieldTowerSmoothTimeField1 (q : ℕ) : NormedAddCommGroup (SobolevSpace P q) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance instFieldTowerSmoothTimeField2 (q : ℕ) : NormedSpace ℝ (SobolevSpace P q) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instFieldTowerSmoothTimeField3 (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instFieldTowerSmoothTimeField4 (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] Space)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))`
instance to shorten typeclass synthesis. -/
local instance instFieldTowerSmoothTimeField5 (n : ℕ) : NormedAddCommGroup
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space))` instance
to shorten typeclass synthesis. -/
local instance instFieldTowerSmoothTimeField6 (n : ℕ) : NormedSpace ℝ
    (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] Space)) := inferInstance

/-- Bounded cover, given by `coverPathMap P (A.realization 3)`. -/
def boundedCover : C(Icc (0 : ℝ) T, LiftTangent →ᵇ Space) :=
  coverPathMap P (A.realization 3)

@[simp] theorem boundedCover_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    A.boundedCover t x = A.pointField t (coveringMap P x) := rfl

/-- Bounded word, given by `coverPathMap P ((wordAtLevel P 3 n w (le_refl
(n+3))).compLeftContinuous ℝ (Icc (0 : ℝ) T) (A.realization (n+3)))`. -/
def boundedWord (n : ℕ) (w : Fin n → Fin 4) : C(Icc (0 : ℝ) T, LiftTangent →ᵇ Space) :=
  coverPathMap P ((wordAtLevel P 3 n w (le_refl (n+3))).compLeftContinuous ℝ (Icc (0 : ℝ) T)
    (A.realization (n+3)))

theorem boundedWord_apply (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    A.boundedWord n w t x = iteratedFieldDerivative P w (A.pointField t) (coveringMap P x) := by
  change EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)
    (wordAtLevel P 3 n w (le_refl (n+3)) (A.realization (n+3) t)) = _
  simpa only [restrictOperator_self] using
    (A.pointField_wordAtLevel (n+3) 3 n (le_refl 3) (le_refl (n+3)) w t (coveringMap P x)).symm

theorem boundedWord_tensor (n : ℕ) (w : Fin n → Fin 4)
    (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    A.boundedWord n w t x = iteratedFDeriv ℝ n (A.boundedCover t : LiftTangent → Space) x
      (fun i => coverBasis (w i)) := by
  rw [A.boundedWord_apply, coverField_word P w (A.pointField t) (A.pointField_smooth t)]
  simp only [coverBasis_apply]
  rfl

/-- To smooth time field, constructed using `SmoothTimeField.ofCoordinateJets`. -/
def toSmoothTimeField : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent Space :=
  SmoothTimeField.ofCoordinateJets coverBasis A.boundedCover
    (fun t => coverField_contDiff P (A.pointField t) (A.pointField_smooth t))
    A.boundedWord A.boundedWord_tensor

@[simp] theorem toSmoothTimeField_apply (t : Icc (0 : ℝ) T) (x : LiftTangent) :
    A.toSmoothTimeField.field t x = A.pointField t (coveringMap P x) := rfl

theorem toSmoothTimeField_timeDerivative (B : EulerAllOrderCorrectionData.FieldTower P T)
    (hT : 0 ≤ T)
    (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT (A.realization 3))
      (B.realization 3 t) (Icc (0 : ℝ) T) t) :
    SmoothTimeField.TimeDerivative T hT A.toSmoothTimeField B.toSmoothTimeField := by
  intro t x
  exact A.pointField_hasDerivWithinAt B hT t (hd t) (coveringMap P x)

theorem toSmoothTimeField_timeDerivative_of_interior
    (B : EulerAllOrderCorrectionData.FieldTower P T) (hT : 0 ≤ T)
    (q : ℕ) (hq : 3 ≤ q)
    (hd : ∀ (t : ℝ) (ht : t ∈ Ioo 0 T), HasDerivAt (extendPath T hT (A.realization q))
      (B.realization q ⟨t, ht.1.le, ht.2.le⟩) t) :
    SmoothTimeField.TimeDerivative T hT A.toSmoothTimeField B.toSmoothTimeField := by
  intro t x
  let L : SobolevSpace P q →L[ℝ] Space :=
    (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x)).comp (restrictOperator P hq)
  let u : C(Icc (0 : ℝ) T, Space) := L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (A.realization q)
  let v : C(Icc (0 : ℝ) T, Space) := L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (B.realization q)
  have hu (s : Icc (0 : ℝ) T) : u s = A.pointField s (coveringMap P x) :=
    congrArg (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x))
      (A.restrict_realization hq s)
  have hv (s : Icc (0 : ℝ) T) : v s = B.pointField s (coveringMap P x) :=
    congrArg (EulerSobolevPointEvaluation.pointEvaluation P (coveringMap P x))
      (B.restrict_realization hq s)
  have hi : ∀ r ∈ Ioo 0 T, HasDerivAt
      (fun s => (ContinuousLinearMap.id ℝ Space) (extendPath T hT u s))
      ((ContinuousLinearMap.id ℝ Space) (extendPath T hT v r)) r := by
    intro r hr
    have h := L.hasFDerivAt.comp_hasDerivAt r (hd r hr)
    change HasDerivAt (fun s => L (A.realization q (projIcc 0 T hT s)))
      (L (B.realization q ⟨r,hr.1.le,hr.2.le⟩)) r at h
    change HasDerivAt (fun s => L (A.realization q (projIcc 0 T hT s)))
      (L (B.realization q (projIcc 0 T hT r))) r
    simpa only [projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩] using h
  have ht := EulerInjectivePathDerivative.hasDerivWithinAt_of_injective_map
    (ContinuousLinearMap.id ℝ Space) (fun _ _ h => h) T hT u v hi t
  have he : extendPath T hT u =
      fun r => A.pointField (projIcc 0 T hT r) (coveringMap P x) := by
    funext r
    exact hu (projIcc 0 T hT r)
  rw [he, hv] at ht
  change HasDerivWithinAt (fun r => A.pointField (projIcc 0 T hT r) (coveringMap P x))
    (B.pointField t (coveringMap P x)) (Icc (0 : ℝ) T) t
  exact ht

theorem toSmoothTimeField_jet_norm_le (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (t : Icc (0 : ℝ) T) (x : LiftTangent),
      ‖iteratedFDeriv ℝ n (fun y => A.pointField t (coveringMap P y)) x‖ ≤ C) :
    ‖A.toSmoothTimeField.jet n‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).2
  intro t
  apply (BoundedContinuousFunction.norm_le hC).2
  intro x
  rw [A.toSmoothTimeField.jet_eq]
  exact hb t x

theorem toSmoothTimeField_jet_weighted (n : ℕ) (ρ C : ℝ) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hb : ∀ t : Icc (0 : ℝ) T,
      weightedNorm P 6 n ρ (A.realization (n+6) t) ≤ C) :
    ‖A.toSmoothTimeField.jet n‖ ≤
      (sobolevEmbeddingConstant P 3*C) *
        (‖coordinateEquiv.symm.toContinuousLinearMap‖*ρ⁻¹)^n * (n.factorial : ℝ)^2 := by
  have hS := sobolevEmbeddingConstant_nonneg P 3
  apply A.toSmoothTimeField_jet_norm_le n _ (by positivity)
  intro t x
  have hs := A.pointField_wordSum_gevrey (n+6) 6 n n (by norm_num) (le_refl (n+6))
    (le_refl n) ρ C hρ t (hb t) (coveringMap P x)
  have hc := coverField_tensor_norm_le P n (A.pointField t) (A.pointField_smooth t) x
  apply hc.trans
  calc
    _ ≤ ‖coordinateEquiv.symm.toContinuousLinearMap‖^n *
        ((sobolevEmbeddingConstant P 3*C)*(ρ⁻¹)^n*(n.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (norm_nonneg _) n)
    _ = _ := by rw [mul_pow]; ring

end EulerAllOrderCorrectionData.FieldTower
