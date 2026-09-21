/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.OrderRees
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# The order-Rees two-jet ring

This file constructs only the ring half of the order-Rees two-jet.  The
specialization map is defined directly as the finite sum of the order-principal
components of the Rees coefficients.  Its multiplication proof retains the
written coefficient order in the noncommutative Weyl algebra.

No Rees-module action, quotient module, trace package, or Gabber theorem is
constructed here.
-/

namespace Stafford38.CharacteristicOrderReesTwoJet

open Stafford38.Characteristic
open Stafford38.WeylAssociatedGraded
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylOrderRees
open Stafford38.WeylPBW

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The scalar embedding into Rees degree zero. -/
def orderReesScalarHom : k →+* OrderReesRing (n := n) k where
  toFun a := ⟨Polynomial.C (algebraMap k (PresentedWeyl k n) a), by
    intro N
    by_cases hN : N = 0
    · subst N
      rw [Polynomial.coeff_C_zero]
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ a (orderPieceOne (n := n) k).property
    · rw [Polynomial.coeff_C, if_neg hN]
      exact Submodule.zero_mem _⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by ext; simp
  map_mul' a b := by ext; simp

/-- The inherited `k`-algebra structure on the order-Rees subring, with
scalars placed in Rees degree zero. -/
noncomputable instance orderReesRingAlgebra :
    Algebra k (OrderReesRing (n := n) k) where
  smul a f := orderReesScalarHom (n := n) k a * f
  algebraMap := orderReesScalarHom (n := n) k
  commutes' a f := by
    apply Subtype.ext
    change Polynomial.C (algebraMap k (PresentedWeyl k n) a) *
        (f : Polynomial (PresentedWeyl k n)) =
      (f : Polynomial (PresentedWeyl k n)) *
        Polynomial.C (algebraMap k (PresentedWeyl k n) a)
    ext N
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C]
    exact Algebra.commutes _ _
  smul_def' _ _ := rfl

/-- The additive finite sum of degreewise order-principal components. -/
def orderPrincipalSum :
    Polynomial (PresentedWeyl k n) →+ SymbolRing k n where
  toFun f := f.sum fun N z =>
    presentedPrincipalComponent k (@orderWeight n) N z
  map_zero' := Polynomial.sum_zero_index _
  map_add' f g := Polynomial.sum_add_index f g _
    (fun N => by simp)
    (fun N x y => by simp)

@[simp] theorem orderPrincipalSum_monomial
    (N : ℕ) (z : PresentedWeyl k n) :
    orderPrincipalSum (n := n) k (Polynomial.monomial N z) =
      presentedPrincipalComponent k (@orderWeight n) N z := by
  exact Polynomial.sum_monomial_index z _ (by simp)

/-- On Rees polynomials, the degreewise principal-component sum preserves
multiplication.  In the double sum, coefficients occur as `x * y`, in the
same order as in the input product. -/
theorem orderPrincipalSum_mul
    (f g : OrderReesRing (n := n) k) :
    orderPrincipalSum (n := n) k
        ((f * g : OrderReesRing (n := n) k) :
          Polynomial (PresentedWeyl k n)) =
      orderPrincipalSum (n := n) k f *
        orderPrincipalSum (n := n) k g := by
  change orderPrincipalSum (n := n) k
      ((f : Polynomial (PresentedWeyl k n)) *
        (g : Polynomial (PresentedWeyl k n))) = _
  rw [Polynomial.mul_eq_sum_sum, map_sum]
  simp only [Polynomial.sum, map_sum, orderPrincipalSum_monomial]
  change
    (∑ i ∈ (f : Polynomial (PresentedWeyl k n)).support,
      ∑ j ∈ (g : Polynomial (PresentedWeyl k n)).support,
        presentedPrincipalComponent k (@orderWeight n) (i + j)
          ((f : Polynomial (PresentedWeyl k n)).coeff i *
            (g : Polynomial (PresentedWeyl k n)).coeff j)) =
      (∑ i ∈ (f : Polynomial (PresentedWeyl k n)).support,
        presentedPrincipalComponent k (@orderWeight n) i
          ((f : Polynomial (PresentedWeyl k n)).coeff i)) *
      (∑ j ∈ (g : Polynomial (PresentedWeyl k n)).support,
        presentedPrincipalComponent k (@orderWeight n) j
          ((g : Polynomial (PresentedWeyl k n)).coeff j))
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact presentedPrincipalComponent_mul_order k (f.property i) (g.property j)

/-- Global specialization of the order-Rees ring to its commutative symbol
ring. -/
def orderReesSpecialization :
    OrderReesRing (n := n) k →+* SymbolRing k n where
  toFun f := orderPrincipalSum (n := n) k f
  map_zero' := by
    change orderPrincipalSum (n := n) k
      (0 : Polynomial (PresentedWeyl k n)) = 0
    exact map_zero (orderPrincipalSum (n := n) k)
  map_add' f g := by
    change orderPrincipalSum (n := n) k
        ((f : Polynomial (PresentedWeyl k n)) + g) = _
    exact map_add (orderPrincipalSum (n := n) k)
      (f : Polynomial (PresentedWeyl k n))
      (g : Polynomial (PresentedWeyl k n))
  map_one' := by
    change orderPrincipalSum (n := n) k
      (1 : Polynomial (PresentedWeyl k n)) = 1
    rw [show (1 : Polynomial (PresentedWeyl k n)) = Polynomial.monomial 0 1 by
      simp]
    rw [orderPrincipalSum_monomial]
    rw [presentedPrincipalComponent, LinearMap.comp_apply]
    change MvPolynomial.weightedHomogeneousComponent (@orderWeight n) 0
      (presentedNormalFormLinearEquiv k n 1) = 1
    rw [Stafford38.WeylPBW.presentedNormalFormLinearEquiv_one]
    exact (MvPolynomial.isWeightedHomogeneous_one k (@orderWeight n)).weightedHomogeneousComponent_same
  map_mul' := orderPrincipalSum_mul k

@[simp] theorem orderReesSpecialization_monomial
    (N : ℕ) (z : orderPiece k n N) :
    orderReesSpecialization (n := n) k (orderReesMonomial k N z) =
      presentedPrincipalComponent k (@orderWeight n) N z := by
  change orderPrincipalSum (n := n) k
    (Polynomial.monomial N (z : PresentedWeyl k n)) = _
  rw [orderPrincipalSum_monomial]

@[simp] theorem orderReesSpecialization_parameter :
    orderReesSpecialization (n := n) k
        (orderReesParameter (n := n) k) = 0 := by
  rw [orderReesParameter, orderReesSpecialization_monomial]
  exact presentedPrincipalComponent_eq_zero_of_mem_of_lt k
    (@orderWeight n) (1 : PresentedWeyl k n)
      (orderPieceOne (n := n) k).property (by omega)

/-- Every symbol has a Rees lift. -/
theorem orderReesSpecialization_surjective :
    Function.Surjective (orderReesSpecialization (n := n) k) := by
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial m a =>
      let N := monomialWeight (@orderWeight n) m
      let z : orderPiece k n N :=
        ⟨a • Stafford38.WeylPBW.presentedPBWBasis k n m, Submodule.smul_mem _ a
          ((presentedPBWBasis_mem_weightPiece_iff k (@orderWeight n) N m).mpr
            (le_refl N))⟩
      refine ⟨orderReesMonomial k N z, ?_⟩
      rw [orderReesSpecialization_monomial]
      change presentedPrincipalComponent k (@orderWeight n) N
          (a • Stafford38.WeylPBW.presentedPBWBasis k n m) =
        MvPolynomial.monomial m a
      rw [map_smul, presentedPrincipalComponent_basis, if_pos rfl]
      rw [MvPolynomial.smul_monomial]
      simp
  | add P Q hP hQ =>
      obtain ⟨p, hp⟩ := hP
      obtain ⟨q, hq⟩ := hQ
      refine ⟨p + q, ?_⟩
      change orderReesSpecialization (n := n) k (p + q) = P + Q
      rw [(orderReesSpecialization (n := n) k).map_add, hp, hq]

@[simp] theorem orderReesSpecialization_scalar (a : k) :
    orderReesSpecialization (n := n) k
        (orderReesScalarHom (n := n) k a) =
      algebraMap k (SymbolRing k n) a := by
  change (Polynomial.C (algebraMap k (PresentedWeyl k n) a)).sum
      (fun N z => presentedPrincipalComponent k (@orderWeight n) N z) = _
  rw [Polynomial.sum_C_index]
  · change MvPolynomial.weightedHomogeneousComponent (@orderWeight n) 0
      (presentedNormalFormLinearEquiv k n
        (algebraMap k (PresentedWeyl k n) a)) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul,
      Stafford38.WeylPBW.presentedNormalFormLinearEquiv_one]
    rw [map_smul]
    rw [(MvPolynomial.isWeightedHomogeneous_one k
      (@orderWeight n)).weightedHomogeneousComponent_same]
    exact MvPolynomial.C_eq_smul_one.symm
  · simp

/-- The order-Rees specialization as a `k`-algebra homomorphism. -/
def orderReesSpecializationAlg :
    OrderReesRing (n := n) k →ₐ[k] SymbolRing k n :=
  AlgHom.mk' (orderReesSpecialization (n := n) k) (fun a f => by
    change orderReesSpecialization (n := n) k
        (orderReesScalarHom (n := n) k a * f) = _
    rw [(orderReesSpecialization (n := n) k).map_mul,
      orderReesSpecialization_scalar, Algebra.smul_def])

/-- The two-sided ideal generated by the square of the Rees parameter. -/
def orderReesTwoJetIdeal : TwoSidedIdeal (OrderReesRing (n := n) k) :=
  TwoSidedIdeal.span
    ({orderReesParameter (n := n) k ^ 2} :
      Set (OrderReesRing (n := n) k))

/-- The order-Rees ring modulo `T²`. -/
abbrev OrderReesTwoJet :=
  (orderReesTwoJetIdeal (n := n) k).ringCon.Quotient

/-- The canonical algebra quotient map to the two-jet. -/
def orderReesTwoJetQuotient :
    OrderReesRing (n := n) k →ₐ[k] OrderReesTwoJet (n := n) k :=
  AlgHom.mk' (orderReesTwoJetIdeal (n := n) k).ringCon.mk' (fun a r => by
    change (orderReesTwoJetIdeal (n := n) k).ringCon.mk'
        (orderReesScalarHom (n := n) k a * r) = _
    rw [map_mul]
    rfl)

/-- The image of the Rees parameter in the two-jet. -/
def orderReesTwoJetParameter : OrderReesTwoJet (n := n) k :=
  orderReesTwoJetQuotient (n := n) k (orderReesParameter (n := n) k)

/-- The two-jet parameter is central. -/
theorem orderReesTwoJetParameter_mem_center :
    orderReesTwoJetParameter (n := n) k ∈
      Set.center (OrderReesTwoJet (n := n) k) := by
  rw [Semigroup.mem_center_iff]
  intro q
  obtain ⟨r, rfl⟩ := Quotient.mk''_surjective q
  change orderReesTwoJetQuotient (n := n) k r *
      orderReesTwoJetQuotient (n := n) k (orderReesParameter (n := n) k) =
    orderReesTwoJetQuotient (n := n) k (orderReesParameter (n := n) k) *
      orderReesTwoJetQuotient (n := n) k r
  rw [← map_mul, ← map_mul, orderReesParameter_mul_comm]

/-- The two-jet parameter is square-zero. -/
theorem orderReesTwoJetParameter_sq :
    orderReesTwoJetParameter (n := n) k ^ 2 = 0 := by
  change orderReesTwoJetQuotient (n := n) k
      (orderReesParameter (n := n) k) ^ 2 = 0
  rw [← map_pow]
  change (orderReesTwoJetIdeal (n := n) k).ringCon.mk'
      (orderReesParameter (n := n) k ^ 2) =
    (orderReesTwoJetIdeal (n := n) k).ringCon.mk' 0
  apply Quotient.sound
  apply ((orderReesTwoJetIdeal (n := n) k).rel_iff _ _).mpr
  have hmem : orderReesParameter (n := n) k ^ 2 ∈
      orderReesTwoJetIdeal (n := n) k :=
    TwoSidedIdeal.subset_span (Set.mem_singleton _)
  simpa using hmem

theorem orderReesTwoJetIdeal_le_specializationKer :
    orderReesTwoJetIdeal (n := n) k ≤
      TwoSidedIdeal.ker (orderReesSpecialization (n := n) k) := by
  intro x hx
  change x ∈ TwoSidedIdeal.span
    ({orderReesParameter (n := n) k ^ 2} :
      Set (OrderReesRing (n := n) k)) at hx
  rw [TwoSidedIdeal.mem_span_iff] at hx
  apply hx
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  subst z
  change orderReesSpecialization (n := n) k
    (orderReesParameter (n := n) k ^ 2) = 0
  rw [map_pow, orderReesSpecialization_parameter,
    zero_pow (by omega)]

/-- Specialization factors through the order-Rees two-jet. -/
def orderReesTwoJetSpecialization :
    OrderReesTwoJet (n := n) k →ₐ[k] SymbolRing k n :=
  let f := orderReesSpecializationAlg (n := n) k
  let hrel : ∀ ⦃x y : OrderReesRing (n := n) k⦄,
      (orderReesTwoJetIdeal (n := n) k).ringCon x y → f x = f y := by
    intro x y hxy
    have hmem : x - y ∈ orderReesTwoJetIdeal (n := n) k :=
      ((orderReesTwoJetIdeal (n := n) k).rel_iff x y).mp hxy
    have hker := orderReesTwoJetIdeal_le_specializationKer (n := n) k hmem
    rw [TwoSidedIdeal.mem_ker] at hker
    have hker' : f (x - y) = 0 := hker
    rw [map_sub] at hker'
    exact sub_eq_zero.mp hker'
  { toFun := Quotient.lift f hrel
    map_zero' := f.map_zero
    map_one' := f.map_one
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      exact f.map_add x y
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      exact f.map_mul x y
    commutes' := f.commutes }

@[simp] theorem orderReesTwoJetSpecialization_quotient
    (r : OrderReesRing (n := n) k) :
    orderReesTwoJetSpecialization (n := n) k
        (orderReesTwoJetQuotient (n := n) k r) =
      orderReesSpecialization (n := n) k r := by
  rfl

@[simp] theorem orderReesTwoJetSpecialization_parameter :
    orderReesTwoJetSpecialization (n := n) k
        (orderReesTwoJetParameter (n := n) k) = 0 := by
  rw [orderReesTwoJetParameter,
    orderReesTwoJetSpecialization_quotient,
    orderReesSpecialization_parameter]

/-- The two-jet specialization remains surjective. -/
theorem orderReesTwoJetSpecialization_surjective :
    Function.Surjective (orderReesTwoJetSpecialization (n := n) k) := by
  intro P
  obtain ⟨r, hr⟩ := orderReesSpecialization_surjective (n := n) k P
  exact ⟨orderReesTwoJetQuotient (n := n) k r, by
    rw [orderReesTwoJetSpecialization_quotient, hr]⟩


end

end Stafford38.CharacteristicOrderReesTwoJet
