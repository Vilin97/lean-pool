/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.LocalizedPolynomialDerivations
public import LeanPool.Stafford38.Stafford38.DifferentialOperators
public import LeanPool.Stafford38.Stafford38.Weyl.Universal
public import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence


/-!
# The Weyl action on a polynomial localization

This file constructs the Weyl action on the genuine finite-order differential
operators of a localization of a polynomial ring.  No identification of the
resulting differential-operator algebra with another presentation is used.
-/

@[expose] public section

namespace Stafford38.LocalizedWeylAction

open Stafford
open Stafford38.DifferentialOperators
open Stafford38.LocalizedPolynomialDerivations
open Stafford38.WeylUniversal
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable {k : Type u} [Field k] {n : ℕ}
variable (S : Submonoid (MvPolynomial (Fin n) k))
variable (B : Type u) [CommRing B]
variable [Algebra (MvPolynomial (Fin n) k) B] [Algebra k B]
variable [IsScalarTower k (MvPolynomial (Fin n) k) B]
variable [IsLocalization S B]

/-- The polynomial algebra whose localization carries the Weyl action. -/
abbrev A := MvPolynomial (Fin n) k
/-- The differential-operator algebra on a coefficient algebra over `k`. -/
abbrev D (B : Type u) [CommRing B] [Algebra k B] :=
  algebra (k := k) (R := B)

/-- The endomorphism given by multiplication by a localized coordinate. -/
def coordinateEnd (i : Fin n) : End (k := k) (R := B) :=
  multiplication (algebraMap (A (k := k) (n := n)) B (MvPolynomial.X i))

/-- The localized partial derivative, regarded as a linear endomorphism. -/
def momentumEnd (i : Fin n) : End (k := k) (R := B) :=
  (localizedPderiv S B i).toLinearMap

omit [IsScalarTower k (MvPolynomial (Fin n) k) B] in
theorem coordinateEnd_mem_order_zero (i : Fin n) :
    coordinateEnd (B := B) i ∈ order (k := k) (R := B) 0 := by
  rw [mem_order_zero_iff_eq_multiplication]
  ext x
  simp [coordinateEnd, multiplication_apply]

theorem momentumEnd_mem_order_one (i : Fin n) :
    momentumEnd S B i ∈ order (k := k) (R := B) 1 := by
  rw [show 1 = 0 + 1 by rfl, mem_order_succ_iff]
  intro a
  rw [mem_order_zero_iff_eq_multiplication]
  apply LinearMap.ext
  intro x
  change localizedPderiv S B i (a * x) - a * localizedPderiv S B i x = _
  rw [(localizedPderiv S B i).leibniz]
  simp [DifferentialOperators.commutator_apply, multiplication_apply,
    momentumEnd, mul_comm]

/-- The coordinate multiplication and differentiation operators forming the Weyl generators. -/
def differentialGenerator : (Fin n ⊕ Fin n) → D (k := k) B
  | .inl i => ⟨coordinateEnd (B := B) i, 0,
      coordinateEnd_mem_order_zero (B := B) i⟩
  | .inr i => ⟨momentumEnd S B i, 1, momentumEnd_mem_order_one S B i⟩

theorem differentialGenerator_commutator (i j : Fin n ⊕ Fin n) :
    Stafford.commutator (differentialGenerator S B i)
        (differentialGenerator S B j) =
      algebraMap k (D (k := k) B) (Matrix.J (Fin n) k i j) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [Stafford.commutator, differentialGenerator,
          coordinateEnd, Module.End.mul_apply, Matrix.J, mul_comm,
          mul_left_comm]
      | inr j =>
          by_cases h : i = j
          · subst j
            simp [Stafford.commutator, differentialGenerator, coordinateEnd,
              momentumEnd, Module.End.mul_apply, Matrix.J,
              localizedPderiv_apply_algebraMap_X]
          · simp [Stafford.commutator, differentialGenerator, coordinateEnd,
              momentumEnd, Module.End.mul_apply, Matrix.J, h,
              Ne.symm h, localizedPderiv_apply_algebraMap_X]
  | inr i =>
      cases j with
      | inl j =>
          by_cases h : i = j
          · subst j
            simp [Stafford.commutator, differentialGenerator, coordinateEnd,
              momentumEnd, Module.End.mul_apply, Matrix.J,
              localizedPderiv_apply_algebraMap_X]
          · simp [Stafford.commutator, differentialGenerator, coordinateEnd,
              momentumEnd, differentialGenerator, coordinateEnd,
              Matrix.J, h, localizedPderiv_apply_algebraMap_X]
      | inr j =>
          have hc := localizedPderiv_comm S B i j
          have hcf := LinearMap.congr_fun hc f
          simpa [Stafford.commutator, differentialGenerator, momentumEnd,
            Module.End.mul_apply, Matrix.J] using (sub_eq_zero.mpr hcf)

/-- The algebra map realizing the presented Weyl algebra as differential operators on a
localization. -/
def localizedWeylAction :
    PresentedWeyl k n →ₐ[k] D (k := k) B :=
  freeWeylLift (Matrix.J (Fin n) k) (differentialGenerator S B)
    (differentialGenerator_commutator S B)

@[simp]
theorem localizedWeylAction_generator (i : Fin n ⊕ Fin n) :
    localizedWeylAction S B
        (freeWeylGenerator (Matrix.J (Fin n) k) i) =
      differentialGenerator S B i :=
  freeWeylLift_generator _ _ _ i

theorem localizedWeylAction_mem (a : PresentedWeyl k n) :
    (localizedWeylAction S B a : End (k := k) (R := B)) ∈ D (k := k) B :=
  (localizedWeylAction S B a).property

include S
theorem multiplication_algebraMap_mem_range (f : A (k := k) (n := n)) :
    ∃ P : D (k := k) B, (P : End (k := k) (R := B)) =
      multiplication (algebraMap (A (k := k) (n := n)) B f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
      refine ⟨algebraMap k (D (k := k) B) c, ?_⟩
      ext x
      have hc : algebraMap (A (k := k) (n := n)) B (MvPolynomial.C c) =
          algebraMap k B c := by
        calc
          _ = algebraMap (A (k := k) (n := n)) B
              (algebraMap k (A (k := k) (n := n)) c) := by
                rw [MvPolynomial.algebraMap_eq]
          _ = algebraMap k B c := by
            exact (IsScalarTower.algebraMap_apply k
              (A (k := k) (n := n)) B c).symm
      rw [hc]
      simp [multiplication_apply, Algebra.smul_def]
  | add f g hf hg =>
      obtain ⟨P, hP⟩ := hf
      obtain ⟨Q, hQ⟩ := hg
      refine ⟨P + Q, ?_⟩
      ext x
      simp [hP, hQ, multiplication_apply, map_add, add_mul]
  | mul_X f i hf =>
      obtain ⟨P, hP⟩ := hf
      refine ⟨(differentialGenerator S B (.inl i)) * P, ?_⟩
      ext x
      change algebraMap (A (k := k) (n := n)) B (MvPolynomial.X i) *
          (P : End (k := k) (R := B)) x = _
      rw [hP]
      simp [multiplication_apply, map_mul, mul_assoc]
      ring


end
end Stafford38.LocalizedWeylAction
