/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.BaseRelativePoisson
import LeanPool.Stafford38.Stafford38.Characteristic.ZeroSectionContainment

/-!
# Pointwise conormal containment

This file packages the finite-linear-combination consequence of the
base-relative Hamiltonian translation theorem.  At a fixed base point, every
finite linear combination of differentials of base equations whose lifts lie
in the ideal is a common zero of the ideal in the corresponding fibre.

The proof forms the same linear combination of the base equations and applies
the existing one-direction translation theorem once.  It assumes zero-section
vanishing at the chosen point; it does not prove that hypothesis or any
homogeneity statement.
-/

namespace Stafford38.Geometry.PointwiseConormalContainment

open Stafford38.Characteristic
open Stafford38.Characteristic.BaseRelativePoisson
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Characteristic.ZeroSectionContainment
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- A finite linear combination of base equations. -/
def baseLinearCombination {ι : Type*} [Fintype ι]
    (a : ι → k) (f : ι → MvPolynomial (Fin n) k) :
    MvPolynomial (Fin n) k :=
  ∑ j, MvPolynomial.C (a j) * f j

/-- The phase-space point whose fibre coordinate is the corresponding finite
linear combination of differentials at `y`. -/
def differentialCombinationPoint {ι : Type*} [Fintype ι]
    (y : Fin n → k) (a : ι → k) (f : ι → MvPolynomial (Fin n) k) :
    PhaseVar n → k
  | Sum.inl i => y i
  | Sum.inr i => ∑ j, a j * differentialAt y (f j) i

/-- Differentiation at a point commutes with the displayed finite linear
combination. -/
theorem differentialAt_baseLinearCombination {ι : Type*} [Fintype ι]
    (y : Fin n → k) (a : ι → k) (f : ι → MvPolynomial (Fin n) k)
    (i : Fin n) :
    differentialAt y (baseLinearCombination a f) i =
      ∑ j, a j * differentialAt y (f j) i := by
  classical
  simp [baseLinearCombination, differentialAt]

/-- With scalar parameter one, translation by the differential of the
combined equation is exactly the point represented by the combined
differentials. -/
theorem differentialTranslatePoint_baseLinearCombination_one
    {ι : Type*} [Fintype ι]
    (y : Fin n → k) (a : ι → k) (f : ι → MvPolynomial (Fin n) k) :
    differentialTranslatePoint y (baseLinearCombination a f) 1 =
      differentialCombinationPoint y a f := by
  classical
  funext i
  rcases i with i | i
  · rfl
  · simp [differentialTranslatePoint, differentialCombinationPoint,
      differentialAt_baseLinearCombination]

/--
Pointwise finite-span form of conormal containment.

If the zero-section point over `y` is a common zero of `J`, and every displayed
base equation lifts into `J`, then the fibre point obtained from any finite
linear combination of their differentials is again a common zero of `J`.
-/
theorem differentialCombinationPoint_isCommonZero
    [CharZero k] {ι : Type*} [Fintype ι]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : ι → MvPolynomial (Fin n) k)
    (hf : ∀ j, baseLift (f j) ∈ J)
    (a : ι → k) :
    ∀ g ∈ J, MvPolynomial.eval (differentialCombinationPoint y a f) g = 0 := by
  classical
  have hcombined : baseLift (baseLinearCombination a f) ∈ J := by
    rw [baseLinearCombination, map_sum]
    apply Ideal.sum_mem
    intro j hj
    rw [map_mul]
    exact J.mul_mem_left _ (hf j)
  intro g hg
  rw [← differentialTranslatePoint_baseLinearCombination_one y a f]
  exact
    zeroSection_stable_under_differential_translation_of_isBaseRelativePoisson
      J hJ y hzero (baseLinearCombination a f) hcombined g hg 1

/-- Concrete reduced-support form: a point of the actual reduced order
support supplies its zero-section point by order homogeneity, after which the
base-relative Gabber fragment contains every displayed finite differential
span in the same support fibre. -/
theorem reducedOrderSupport_differentialCombinationPoint_isCommonZero
    [CharZero k] {ι : Type*} [Fintype ι]
    (I : RightIdeal (PresentedWeyl k n))
    (hJ : IsBaseRelativePoisson (reducedOrderSupportIdeal k I))
    (y ξ : Fin n → k)
    (hpoint : ∀ g ∈ reducedOrderSupportIdeal k I,
      MvPolynomial.eval (Sum.elim y ξ) g = 0)
    (f : ι → MvPolynomial (Fin n) k)
    (hf : ∀ j, baseLift (f j) ∈ reducedOrderSupportIdeal k I)
    (a : ι → k) :
    ∀ g ∈ reducedOrderSupportIdeal k I,
      MvPolynomial.eval (differentialCombinationPoint y a f) g = 0 := by
  exact differentialCombinationPoint_isCommonZero
    (reducedOrderSupportIdeal k I) hJ y
    (zeroSection_mem_of_mem_reducedOrderSupport_zeroSet k I y ξ hpoint)
    f hf a


end

end Stafford38.Geometry.PointwiseConormalContainment
