/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.AffineComponentCoordinateSplit
import LeanPool.Stafford38.Stafford38.Geometry.LocalizedProjectiveChartTransition

/-!
# The projective cone of an affine component

For a prime affine component with function field `F`, this file evaluates
homogeneous coordinates on the generic cone point

`(T, x₀ T, ..., x_{m-1} T) ∈ F[T]^(m+1)`.

The kernel is a prime homogeneous-coordinate ideal, saturated by the zeroth
coordinate. Zeroth-chart dehomogenization recovers the affine component ideal
exactly.
-/

namespace Stafford38.Geometry.ComponentProjectiveClosure

open Stafford38.Geometry.AffineComponentCoordinateSplit
open Stafford38.Geometry.LocalizedProjectiveChartTransition

noncomputable section

universe u

variable {k : Type u} [Field k] {m : ℕ}

/-- The function field of the prime affine component `P`. -/
abbrev ComponentFractionField
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :=
  FractionRing (MvPolynomial (Fin m) k ⧸ P.asIdeal)

/-- Evaluation on the generic affine cone over a prime component:
`X₀ ↦ T` and `X_(j+1) ↦ x_j T`. -/
def componentProjectiveConeMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    MvPolynomial (Fin (m + 1)) k →+* Polynomial (ComponentFractionField P) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : ComponentFractionField P →+* Polynomial
      (ComponentFractionField P)).comp (algebraMap k (ComponentFractionField P)))
    (Fin.cases Polynomial.X fun j ↦
      Polynomial.C (componentCoordinate P j) * Polynomial.X)

/-- The homogeneous-coordinate ideal of the generic projective cone point. -/
def componentProjectiveClosureIdeal
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    Ideal (MvPolynomial (Fin (m + 1)) k) :=
  RingHom.ker (componentProjectiveConeMap P)

/-- Evaluation at the generic point of the affine component. -/
def componentAffineGenericPointMap
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    MvPolynomial (Fin m) k →+* ComponentFractionField P :=
  (algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal)
      (ComponentFractionField P)).comp
    (Ideal.Quotient.mk P.asIdeal)

@[simp]
theorem componentAffineGenericPointMap_X
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    componentAffineGenericPointMap P (MvPolynomial.X j) =
      componentCoordinate P j := by
  rfl

/-- Generic-point evaluation agrees with multivariate evaluation at the
component coordinates. -/
theorem componentAffineGenericPointMap_eq_eval₂
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (f : MvPolynomial (Fin m) k) :
    componentAffineGenericPointMap P f =
      MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
        (fun j ↦ componentCoordinate P j) f := by
  rw [MvPolynomial.map_mvPolynomial_eq_eval₂
    (componentAffineGenericPointMap P) f]
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    exact IsScalarTower.algebraMap_apply k
      (MvPolynomial (Fin m) k ⧸ P.asIdeal) (ComponentFractionField P) c
  · funext j
    rfl
  · rfl

/-- Every equation of the affine component vanishes at its generic point. -/
theorem componentAffineGenericPointMap_eq_zero_of_mem
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {f : MvPolynomial (Fin m) k} (hf : f ∈ P.asIdeal) :
    componentAffineGenericPointMap P f = 0 := by
  change algebraMap (MvPolynomial (Fin m) k ⧸ P.asIdeal)
      (ComponentFractionField P) (Ideal.Quotient.mk P.asIdeal f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- The generic-point map has exactly the prime component as its kernel. -/
theorem componentAffineGenericPointMap_ker
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    RingHom.ker (componentAffineGenericPointMap P) = P.asIdeal := by
  apply le_antisymm
  · intro f hf
    have hzero : Ideal.Quotient.mk P.asIdeal f = 0 := by
      apply IsFractionRing.injective
        (MvPolynomial (Fin m) k ⧸ P.asIdeal) (ComponentFractionField P)
      simpa only [map_zero, RingHom.mem_ker,
        componentAffineGenericPointMap, RingHom.comp_apply] using hf
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  · intro f hf
    exact componentAffineGenericPointMap_eq_zero_of_mem P hf

@[simp]
theorem componentProjectiveConeMap_X_zero
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    componentProjectiveConeMap P (MvPolynomial.X 0) = Polynomial.X := by
  simp [componentProjectiveConeMap]

@[simp]
theorem componentProjectiveConeMap_X_succ
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) (j : Fin m) :
    componentProjectiveConeMap P (MvPolynomial.X (Fin.succ j)) =
      Polynomial.C (componentCoordinate P j) * Polynomial.X := by
  simp [componentProjectiveConeMap]

/-- The cone kernel is prime because its target is a polynomial ring over the
component function field. -/
theorem componentProjectiveClosureIdeal_isPrime
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    (componentProjectiveClosureIdeal P).IsPrime := by
  exact RingHom.ker_isPrime (componentProjectiveConeMap P)

/-- The cone kernel is saturated by the homogeneous zeroth coordinate.  This
is the scheme-free saturation property needed at the projective boundary. -/
theorem componentProjectiveClosureIdeal_colon_zeroCoordinate
    (P : PrimeSpectrum (MvPolynomial (Fin m) k)) :
    (componentProjectiveClosureIdeal P).colon
        ({MvPolynomial.X 0} :
          Set (MvPolynomial (Fin (m + 1)) k)) =
      componentProjectiveClosureIdeal P := by
  ext H
  rw [Submodule.mem_colon_singleton]
  change componentProjectiveConeMap P (H * MvPolynomial.X 0) = 0 ↔
    componentProjectiveConeMap P H = 0
  rw [map_mul, componentProjectiveConeMap_X_zero]
  constructor
  · intro h
    apply Polynomial.ext
    intro n
    have hn := congrArg
      (fun q : Polynomial (ComponentFractionField P) ↦ q.coeff (n + 1)) h
    simpa using hn
  · intro h
    rw [h, zero_mul]

/-- Scaling every variable of a homogeneous multivariate polynomial by the
same scalar extracts the corresponding power of that scalar. -/
theorem eval₂_mul_common_of_isHomogeneous
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    {σ : Type*} {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) (f : R →+* S) (x : σ → S) (t : S) :
    MvPolynomial.eval₂ f (fun i ↦ x i * t) p =
      MvPolynomial.eval₂ f x p * t ^ d := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp ha)
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  change (∏ i ∈ a.support, x i ^ a i) * t ^ a.degree = _
  rw [hdegree]

/-- Evaluation after zeroth-chart dehomogenization is evaluation at the
projective point `(1,y)`, allowing a larger target coefficient ring. -/
theorem eval₂_projectiveDehomogenize
    {S : Type*} [CommSemiring S] (f : k →+* S) (y : Fin m → S)
    (H : MvPolynomial (Fin (m + 1)) k) :
    MvPolynomial.eval₂ f y
        (Stafford38.Geometry.ProjectiveEquationFormalChart.projectiveDehomogenize H) =
      MvPolynomial.eval₂ f (Fin.cases 1 y) H := by
  rw [show
      Stafford38.Geometry.ProjectiveEquationFormalChart.projectiveDehomogenize H =
        MvPolynomial.bind₁
          (Fin.cases 1 fun i ↦ MvPolynomial.X i) H by rfl]
  change MvPolynomial.eval₂Hom f y
      (MvPolynomial.bind₁ (Fin.cases 1 fun i ↦ MvPolynomial.X i) H) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂_congr
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- Evaluating a homogeneous projective polynomial on the generic cone point
is dehomogenized evaluation times the expected power of `T`. -/
theorem componentProjectiveConeMap_eq_eval₂_mul_X_pow_of_isHomogeneous
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {H : MvPolynomial (Fin (m + 1)) k} {d : ℕ}
    (hH : H.IsHomogeneous d) :
    componentProjectiveConeMap P H =
      Polynomial.C
          (MvPolynomial.eval₂ (algebraMap k (ComponentFractionField P))
            (Fin.cases 1 fun j ↦ componentCoordinate P j) H) *
        Polynomial.X ^ d := by
  change MvPolynomial.eval₂
      ((Polynomial.C : ComponentFractionField P →+* Polynomial
        (ComponentFractionField P)).comp (algebraMap k (ComponentFractionField P)))
      (Fin.cases Polynomial.X fun j ↦
        Polynomial.C (componentCoordinate P j) * Polynomial.X) H = _
  let coords : Fin (m + 1) → ComponentFractionField P :=
    Fin.cases 1 fun j ↦ componentCoordinate P j
  have hvars :
      (fun a ↦ Polynomial.C (coords a) * Polynomial.X) =
        Fin.cases Polynomial.X
          (fun j ↦ Polynomial.C (componentCoordinate P j) * Polynomial.X) := by
    funext a
    refine Fin.cases ?_ (fun j ↦ ?_) a
    · simp [coords]
    · simp [coords]
  rw [← hvars]
  have hscale := eval₂_mul_common_of_isHomogeneous hH
    ((Polynomial.C : ComponentFractionField P →+* Polynomial
      (ComponentFractionField P)).comp (algebraMap k (ComponentFractionField P)))
    (fun a ↦ Polynomial.C (coords a)) Polynomial.X
  rw [hscale]
  congr 1
  exact (MvPolynomial.map_eval₂Hom
    (algebraMap k (ComponentFractionField P)) coords Polynomial.C H).symm

/-- The cone-map image of the standard homogenization is generic affine
evaluation times the expected power of `T`. -/
theorem componentProjectiveConeMap_homogenizeAtZero
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (f : MvPolynomial (Fin m) k) :
    componentProjectiveConeMap P (homogenizeAtZero f) =
      Polynomial.C (componentAffineGenericPointMap P f) *
        Polynomial.X ^ f.totalDegree := by
  rw [componentProjectiveConeMap_eq_eval₂_mul_X_pow_of_isHomogeneous P
    (homogenizeAtZero_isHomogeneous f)]
  congr 1
  rw [componentAffineGenericPointMap_eq_eval₂]
  have heval := eval₂_projectiveDehomogenize
    (algebraMap k (ComponentFractionField P))
    (fun j ↦ componentCoordinate P j) (homogenizeAtZero f)
  rw [projectiveDehomogenize_homogenizeAtZero] at heval
  exact congrArg Polynomial.C heval.symm

/-- Setting the cone parameter to one recovers generic-point evaluation in
the zeroth affine chart. -/
theorem componentProjectiveConeMap_eval_one
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    (H : MvPolynomial (Fin (m + 1)) k) :
    Polynomial.eval 1 (componentProjectiveConeMap P H) =
      componentAffineGenericPointMap P
        (Stafford38.Geometry.ProjectiveEquationFormalChart.projectiveDehomogenize H) := by
  rw [componentAffineGenericPointMap_eq_eval₂]
  rw [eval₂_projectiveDehomogenize]
  change Polynomial.evalRingHom 1
      (MvPolynomial.eval₂
        ((Polynomial.C : ComponentFractionField P →+* Polynomial
          (ComponentFractionField P)).comp
            (algebraMap k (ComponentFractionField P)))
        (Fin.cases Polynomial.X fun j ↦
          Polynomial.C (componentCoordinate P j) * Polynomial.X) H) = _
  rw [MvPolynomial.eval₂_comp_left]
  change MvPolynomial.eval₂Hom _ _ H = MvPolynomial.eval₂Hom _ _ H
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    simp
  · funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  · rfl

/-- Every homogeneous-coordinate equation in the cone kernel dehomogenizes
to an equation of the original affine component. -/
theorem projectiveDehomogenize_mem_of_mem_componentProjectiveClosureIdeal
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {H : MvPolynomial (Fin (m + 1)) k}
    (hH : H ∈ componentProjectiveClosureIdeal P) :
    Stafford38.Geometry.ProjectiveEquationFormalChart.projectiveDehomogenize H ∈
      P.asIdeal := by
  rw [← componentAffineGenericPointMap_ker P, RingHom.mem_ker]
  rw [← componentProjectiveConeMap_eval_one P H]
  have hzero : componentProjectiveConeMap P H = 0 := by
    exact hH
  rw [hzero]
  simp

/-- Every affine equation of the component yields a homogeneous equation of
its projective cone. -/
theorem homogenizeAtZero_mem_componentProjectiveClosureIdeal
    (P : PrimeSpectrum (MvPolynomial (Fin m) k))
    {f : MvPolynomial (Fin m) k} (hf : f ∈ P.asIdeal) :
    homogenizeAtZero f ∈ componentProjectiveClosureIdeal P := by
  rw [componentProjectiveClosureIdeal, RingHom.mem_ker,
    componentProjectiveConeMap_homogenizeAtZero,
    componentAffineGenericPointMap_eq_zero_of_mem P hf, Polynomial.C_0,
    zero_mul]


end

end Stafford38.Geometry.ComponentProjectiveClosure
