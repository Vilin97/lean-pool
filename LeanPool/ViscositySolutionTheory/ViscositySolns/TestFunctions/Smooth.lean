/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Definitions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Smooth test-function adapters

This file connects the coordinate gradient/Hessian data used by semijets with
mathlib's continuous-linear derivative definitions and theorems. The Taylor
theorems for smooth test functions are phrased using continuous linear and
multilinear maps, while the viscosity solution definitions use concrete finite
coordinate gradients and Hessian matrices.
-/

@[expose] public noncomputable section

open Matrix

namespace ViscositySolns

variable {n : Nat}

/-- The coordinate basis vector with value `1` at `i` and `0` elsewhere. -/
def coordinateVector (i : Fin n) : Point n :=
  fun j => if i = j then 1 else 0

@[simp]
theorem coordinateVector_apply (i j : Fin n) :
    coordinateVector i j = if i = j then 1 else 0 :=
  rfl

theorem coordinateVector_apply_self (i : Fin n) : coordinateVector i i = 1 := by
  simp [coordinateVector]

theorem point_eq_sum_coordinateVector (v : Point n) :
    (∑ i : Fin n, v i • coordinateVector i) = v := by
  ext j
  simp [coordinateVector]

/-- The continuous linear functional represented by a coordinate gradient. -/
def gradientLinearMap (p : Point n) : Point n →L[Real] Real :=
  ∑ i : Fin n, (ContinuousLinearMap.proj (R := Real) i).smulRight (p i)

@[simp]
theorem gradientLinearMap_apply (p v : Point n) :
    gradientLinearMap p v = dotProduct p v := by
  suffices (∑ i : Fin n, v i * p i) = ∑ i : Fin n, p i * v i by
    simpa [gradientLinearMap, dotProduct, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm (v i) (p i)

/-- The coordinate gradient represented by a continuous linear functional. -/
def linearMapGradient (D : Point n →L[Real] Real) : Point n :=
  fun i => D (coordinateVector i)

@[simp]
theorem linearMapGradient_apply (D : Point n →L[Real] Real) (i : Fin n) :
    linearMapGradient D i = D (coordinateVector i) :=
  rfl

/--
The coordinate-gradient extraction map as a continuous linear map.

In quantified mathematical form, this sends a continuous linear functional
`D : R^n ->L R` to the vector whose `i`-th coordinate is `D e_i`.
-/
def linearMapGradientCLM : (Point n →L[Real] Real) →L[Real] Point n :=
  ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.apply Real Real (coordinateVector i)

@[simp]
theorem linearMapGradientCLM_apply (D : Point n →L[Real] Real) :
    linearMapGradientCLM D = linearMapGradient D := by
  ext i
  simp [linearMapGradientCLM, linearMapGradient]

@[simp]
theorem gradientLinearMap_linearMapGradient (D : Point n →L[Real] Real) :
    gradientLinearMap (linearMapGradient D) = D := by
  ext v
  calc
    gradientLinearMap (linearMapGradient D) v =
        ∑ i : Fin n, v i * D (coordinateVector i) := by
      simp [dotProduct, mul_comm]
    _ = D v := by
      rw [show D v = D.toLinearMap v by rfl]
      conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ (f := D.toLinearMap) v]
      apply Finset.sum_congr rfl
      intro i _
      rfl

@[simp]
theorem linearMapGradient_gradientLinearMap (p : Point n) :
    linearMapGradient (gradientLinearMap p) = p := by
  ext i
  simp [linearMapGradient, coordinateVector, dotProduct]

/-- The continuous bilinear form represented by a coordinate Hessian matrix. -/
def hessianBilinearMap (X : Hessian n) : Point n →L[Real] Point n →L[Real] Real :=
  ∑ i : Fin n, (ContinuousLinearMap.proj (R := Real) i).smulRight (gradientLinearMap (X i))

@[simp]
theorem hessianBilinearMap_apply (X : Hessian n) (v w : Point n) :
    hessianBilinearMap X v w = dotProduct (Matrix.mulVec X w) v := by
  suffices
      (∑ i : Fin n, v i * (∑ j : Fin n, X i j * w j)) =
        ∑ i : Fin n, (∑ j : Fin n, X i j * w j) * v i by
    simpa [hessianBilinearMap, gradientLinearMap_apply, dotProduct, Matrix.mulVec,
      Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coordinate Hessian represented by a continuous bilinear map. -/
def bilinearMapHessian (D2 : Point n →L[Real] Point n →L[Real] Real) : Hessian n :=
  fun i j => D2 (coordinateVector i) (coordinateVector j)

@[simp]
theorem bilinearMapHessian_apply
    (D2 : Point n →L[Real] Point n →L[Real] Real) (i j : Fin n) :
    bilinearMapHessian D2 i j = D2 (coordinateVector i) (coordinateVector j) :=
  rfl

@[simp]
theorem hessianBilinearMap_bilinearMapHessian
    (D2 : Point n →L[Real] Point n →L[Real] Real) :
    hessianBilinearMap (bilinearMapHessian D2) = D2 := by
  ext v w
  have hD2v :
      D2 v = ∑ i : Fin n, v i • D2 (coordinateVector i) := by
    rw [show D2 v = D2.toLinearMap v by rfl]
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ (f := D2.toLinearMap) v]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hD2iw (i : Fin n) :
      D2 (coordinateVector i) w =
        ∑ j : Fin n, w j * D2 (coordinateVector i) (coordinateVector j) := by
    rw [show D2 (coordinateVector i) w =
      (D2 (coordinateVector i)).toLinearMap w by rfl]
    conv_lhs =>
      rw [LinearMap.pi_apply_eq_sum_univ
        (f := (D2 (coordinateVector i)).toLinearMap) w]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  have hD2vw :
      D2 v w =
        ∑ i : Fin n, v i * (∑ j : Fin n,
          w j * D2 (coordinateVector i) (coordinateVector j)) := by
    calc
      D2 v w = (∑ i : Fin n, v i • D2 (coordinateVector i)) w := by
        rw [hD2v]
      _ = ∑ i : Fin n, v i * D2 (coordinateVector i) w := by
        simp [smul_eq_mul]
      _ = ∑ i : Fin n, v i * (∑ j : Fin n,
          w j * D2 (coordinateVector i) (coordinateVector j)) := by
        simp [hD2iw]
  calc
    hessianBilinearMap (bilinearMapHessian D2) v w =
        ∑ i : Fin n, (∑ j : Fin n,
          D2 (coordinateVector i) (coordinateVector j) * w j) * v i := by
      simp [hessianBilinearMap_apply, dotProduct, Matrix.mulVec, bilinearMapHessian]
    _ = ∑ i : Fin n, v i * (∑ j : Fin n,
          w j * D2 (coordinateVector i) (coordinateVector j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = D2 v w := hD2vw.symm

@[simp]
theorem bilinearMapHessian_hessianBilinearMap (X : Hessian n) :
    bilinearMapHessian (hessianBilinearMap X) = X := by
  ext i j
  simp [bilinearMapHessian, coordinateVector, dotProduct, Matrix.mulVec]

namespace Jet

/-- The first Fréchet derivative represented by a jet's coordinate gradient. -/
def toFirstDerivative (J : Jet n) : Point n →L[Real] Real :=
  gradientLinearMap J.gradient

/-- The second Fréchet derivative represented by a jet's coordinate Hessian. -/
def toSecondDerivative (J : Jet n) : Point n →L[Real] Point n →L[Real] Real :=
  hessianBilinearMap J.hessian

/-- The coordinate jet represented by continuous first- and second-derivative maps. -/
def ofDerivatives (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real) : Jet n where
  gradient := linearMapGradient Dφ
  hessian := bilinearMapHessian D2φ

@[simp]
theorem toFirstDerivative_apply (J : Jet n) (v : Point n) :
    J.toFirstDerivative v = dotProduct J.gradient v :=
  gradientLinearMap_apply J.gradient v

@[simp]
theorem toSecondDerivative_apply (J : Jet n) (v w : Point n) :
    J.toSecondDerivative v w = dotProduct (Matrix.mulVec J.hessian w) v :=
  hessianBilinearMap_apply J.hessian v w

@[simp]
theorem toFirstDerivative_ofDerivatives (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real) :
    (ofDerivatives Dφ D2φ).toFirstDerivative = Dφ :=
  gradientLinearMap_linearMapGradient Dφ

@[simp]
theorem toSecondDerivative_ofDerivatives (Dφ : Point n →L[Real] Real)
    (D2φ : Point n →L[Real] Point n →L[Real] Real) :
    (ofDerivatives Dφ D2φ).toSecondDerivative = D2φ :=
  hessianBilinearMap_bilinearMapHessian D2φ

@[simp]
theorem ofDerivatives_toFirst_toSecond (J : Jet n) :
    ofDerivatives J.toFirstDerivative J.toSecondDerivative = J := by
  cases J
  simp [ofDerivatives, toFirstDerivative, toSecondDerivative]

end Jet

/--
The concrete quadratic model is the Taylor polynomial built from the continuous
linear maps associated to a coordinate jet.
-/
theorem quadraticModel_eq_linearMap (x0 : Point n) (r : Real) (J : Jet n) (x : Point n) :
    quadraticModel x0 r J.gradient J.hessian x =
      r + J.toFirstDerivative (x - x0) +
        (1 / 2 : Real) * J.toSecondDerivative (x - x0) (x - x0) := by
  simp [quadraticModel, Jet.toFirstDerivative, Jet.toSecondDerivative]

/--
The recentered jet of a quadratic model is a superjet of that quadratic model.

This is the exact-touching test-function fact used by Perron bump
certification and by smooth-selection arguments.
-/
theorem quadraticModelJetAt_mem_superjet
    {C : Set (Point n)} (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) (x : Point n) :
    quadraticModelJetAt x0 p X x ∈
      Superjet C (fun y => quadraticModel x0 r p X y) x := by
  refine superjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue
    (φ := fun y => quadraticModel x0 r p X y) ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => le_rfl
  · exact hasSecondOrderExpansionWithin_quadraticModel_recenter x0 r p X x

/--
The recentered jet of a quadratic model is also a subjet of that quadratic
model.
-/
theorem quadraticModelJetAt_mem_subjet
    {C : Set (Point n)} (x0 : Point n) (r : Real) (p : Point n)
    (X : Hessian n) (x : Point n) :
    quadraticModelJetAt x0 p X x ∈
      Subjet C (fun y => quadraticModel x0 r p X y) x := by
  refine subjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue
    (φ := fun y => quadraticModel x0 r p X y) ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => le_rfl
  · exact hasSecondOrderExpansionWithin_quadraticModel_recenter x0 r p X x

end ViscositySolns
