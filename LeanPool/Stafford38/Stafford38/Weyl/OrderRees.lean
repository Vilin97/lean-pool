/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedModule
public import Mathlib.Algebra.Polynomial.Coeff


/-!
# The differential-order Rees ring

This file constructs the literal Rees ring of the differential-order
filtration as the subring of the central polynomial ring `A[T]` whose
degree-`N` coefficient lies in `F_N A`.  No commutativity of `A`, Rees
specialization, or Gabber theorem is assumed.
-/

@[expose] public section

namespace Stafford38.WeylOrderRees

open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The differential-order Rees ring inside the central polynomial ring over
the presented Weyl algebra. -/
def orderReesSubring : Subring (Polynomial (PresentedWeyl k n)) where
  carrier := {f | ∀ N, f.coeff N ∈ orderPiece k n N}
  zero_mem' := by simp
  one_mem' := by
    intro N
    by_cases hN : N = 0
    · subst N
      rw [Polynomial.coeff_one, ite_eq_left rfl]
      exact (orderPieceOne (n := n) k).property
    · rw [Polynomial.coeff_one, ite_eq_right hN]
      exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg N
    rw [Polynomial.coeff_add]
    exact Submodule.add_mem _ (hf N) (hg N)
  neg_mem' := by
    intro f hf N
    rw [Polynomial.coeff_neg]
    exact Submodule.neg_mem _ (hf N)
  mul_mem' := by
    intro f g hf hg N
    rw [Polynomial.coeff_mul]
    apply Submodule.sum_mem
    intro ij hij
    have hmul := mul_mem_orderPiece k (hf ij.1) (hg ij.2)
    have hij' : ij.1 + ij.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    simpa [hij'] using hmul

/-- The type of elements of the differential-order Rees ring. -/
abbrev OrderReesRing := orderReesSubring (n := n) k

@[simp]
theorem mem_orderReesSubring_iff
    (f : Polynomial (PresentedWeyl k n)) :
    f ∈ orderReesSubring (n := n) k ↔
      ∀ N, f.coeff N ∈ orderPiece k n N :=
  Iff.rfl

/-- A filtered operator inserted in its declared Rees degree. -/
def orderReesMonomial (N : ℕ) (z : orderPiece k n N) :
    OrderReesRing (n := n) k :=
  ⟨Polynomial.monomial N (z : PresentedWeyl k n), by
    intro M
    rw [Polynomial.coeff_monomial]
    split_ifs with h
    · subst M
      exact z.property
    · exact Submodule.zero_mem _⟩

@[simp]
theorem orderReesMonomial_coe (N : ℕ) (z : orderPiece k n N) :
    ((orderReesMonomial k N z : OrderReesRing (n := n) k) :
      Polynomial (PresentedWeyl k n)) =
        Polynomial.monomial N (z : PresentedWeyl k n) :=
  rfl

theorem orderReesMonomial_coeff_same
    (N : ℕ) (z : orderPiece k n N) :
    ((orderReesMonomial k N z : OrderReesRing (n := n) k) :
      Polynomial (PresentedWeyl k n)).coeff N = (z : PresentedWeyl k n) := by
  simp

/-- The central Rees parameter `T`, represented in degree one by the unit
operator. -/
def orderReesParameter : OrderReesRing (n := n) k :=
  orderReesMonomial k 1
    ⟨1, presentedWeightPiece_mono k orderWeight (Nat.zero_le 1)
      (orderPieceOne (n := n) k).property⟩

@[simp]
theorem orderReesParameter_coe :
    ((orderReesParameter (n := n) k : OrderReesRing (n := n) k) :
      Polynomial (PresentedWeyl k n)) = Polynomial.X := by
  rw [orderReesParameter, orderReesMonomial_coe]
  exact Polynomial.monomial_one_one_eq_X

/-- Multiplication of homogeneous Rees representatives is multiplication in
the Weyl algebra, with degrees added. -/
theorem orderReesMonomial_mul
    {N M : ℕ} (z : orderPiece k n N) (y : orderPiece k n M) :
    orderReesMonomial k N z * orderReesMonomial k M y =
      orderReesMonomial k (N + M)
        ⟨(z : PresentedWeyl k n) * (y : PresentedWeyl k n),
          mul_mem_orderPiece k z.property y.property⟩ := by
  apply Subtype.ext
  simp [orderReesMonomial, Polynomial.monomial_mul_monomial]

/-- Multiplication by the Rees parameter raises the declared degree and keeps
the underlying Weyl operator unchanged. -/
theorem orderReesParameter_mul_monomial
    {N : ℕ} (z : orderPiece k n N) :
    orderReesParameter (n := n) k * orderReesMonomial k N z =
      orderReesMonomial k (N + 1)
        ⟨(z : PresentedWeyl k n),
          presentedWeightPiece_mono k orderWeight (Nat.le_succ N) z.property⟩ := by
  apply Subtype.ext
  simp [orderReesParameter_coe, orderReesMonomial,
    Polynomial.X_mul_monomial]

/-- The polynomial Rees parameter is central, including over the
noncommutative Weyl coefficient ring. -/
theorem orderReesParameter_mul_comm
    (r : OrderReesRing (n := n) k) :
    orderReesParameter (n := n) k * r =
      r * orderReesParameter (n := n) k := by
  apply Subtype.ext
  change Polynomial.X * (r : Polynomial (PresentedWeyl k n)) =
    (r : Polynomial (PresentedWeyl k n)) * Polynomial.X
  exact Polynomial.X_mul

/-- A homogeneous class in positive Rees degree is divisible by the Rees
parameter exactly when its coefficient already lies one filtration step
lower.  This is the degreewise kernel statement behind specialization at
`T = 0`. -/
theorem exists_parameter_mul_eq_monomial_iff_mem_lower
    {N : ℕ} (z : orderPiece k n (N + 1)) :
    (∃ r : OrderReesRing (n := n) k,
        orderReesParameter (n := n) k * r =
          orderReesMonomial k (N + 1) z) ↔
      (z : PresentedWeyl k n) ∈ orderPiece k n N := by
  constructor
  · rintro ⟨r, hr⟩
    have hc := congrArg
      (fun p : Polynomial (PresentedWeyl k n) => p.coeff (N + 1))
      (congrArg Subtype.val hr)
    change (Polynomial.X * (r : Polynomial (PresentedWeyl k n))).coeff
        (N + 1) =
      (Polynomial.monomial (N + 1) (z : PresentedWeyl k n)).coeff
        (N + 1) at hc
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_monomial, ite_eq_left rfl] at hc
    rw [← hc]
    exact r.property N
  · intro hz
    let zLower : orderPiece k n N := ⟨z, hz⟩
    refine ⟨orderReesMonomial k N zLower, ?_⟩
    rw [orderReesParameter_mul_monomial]

/-- In Rees degree zero, a homogeneous representative is a parameter multiple
only when it is zero. -/
theorem exists_parameter_mul_eq_degreeZero_iff
    (z : orderPiece k n 0) :
    (∃ r : OrderReesRing (n := n) k,
        orderReesParameter (n := n) k * r = orderReesMonomial k 0 z) ↔
      (z : PresentedWeyl k n) = 0 := by
  constructor
  · rintro ⟨r, hr⟩
    have hc := congrArg
      (fun p : Polynomial (PresentedWeyl k n) => p.coeff 0)
      (congrArg Subtype.val hr)
    change (Polynomial.X * (r : Polynomial (PresentedWeyl k n))).coeff 0 =
      (Polynomial.monomial 0 (z : PresentedWeyl k n)).coeff 0 at hc
    simpa using hc.symm
  · intro hz
    have hz' : z = 0 := Subtype.ext hz
    subst z
    refine ⟨0, ?_⟩
    apply Subtype.ext
    simp [orderReesMonomial]


end

end Stafford38.WeylOrderRees
