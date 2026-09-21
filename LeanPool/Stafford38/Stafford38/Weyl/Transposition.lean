/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Module.RingHom
import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence

/-!
# Transposition of the presented Weyl algebra

This file constructs the scalar-preserving Weyl transposition as an algebra
equivalence with the opposite algebra.  Coordinates are fixed and momenta
change sign.  The construction uses only the checked universal property of
the quotient presentation.
-/

namespace Stafford38.WeylTransposition

open MulOpposite
open Stafford
open AlgebraicAnalysis
open Stafford38.WeylUniversal
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u v

variable (k : Type u) [Field k]

/-- The coordinate generator with index `i`. -/
def coordinate (n : Nat) (i : Fin n) : PresentedWeyl k n :=
  freeWeylGenerator (Matrix.J (Fin n) k) (.inl i)

/-- The momentum generator with index `i`. -/
def momentum (n : Nat) (i : Fin n) : PresentedWeyl k n :=
  freeWeylGenerator (Matrix.J (Fin n) k) (.inr i)

/-- Generator images for the Weyl transposition. -/
def transposedGenerator (n : Nat) :
    (Fin n ⊕ Fin n) → (PresentedWeyl k n)ᵐᵒᵖ
  | .inl i => op (coordinate k n i)
  | .inr i => op (-momentum k n i)

private theorem neg_commutator_right_neg {A : Type*} [Ring A] (a b : A) :
    -Stafford.commutator a (-b) = Stafford.commutator a b := by
  simp [Stafford.commutator]
  abel

private theorem neg_commutator_left_neg {A : Type*} [Ring A] (a b : A) :
    -Stafford.commutator (-a) b = Stafford.commutator a b := by
  simp [Stafford.commutator]
  abel

private theorem neg_commutator_both_neg {A : Type*} [Ring A] (a b : A) :
    -Stafford.commutator (-a) (-b) = -Stafford.commutator a b := by
  simp [Stafford.commutator]

theorem underlying_transposedGenerator_commutator (n : Nat) :
    ∀ i j,
      -Stafford.commutator (unop (transposedGenerator k n i))
          (unop (transposedGenerator k n j)) =
        algebraMap k (PresentedWeyl k n) (Matrix.J (Fin n) k i j) := by
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change -Stafford.commutator (coordinate k n i) (coordinate k n j) = _
          rw [show Stafford.commutator (coordinate k n i) (coordinate k n j) =
            algebraMap k (PresentedWeyl k n)
              (Matrix.J (Fin n) k (.inl i) (.inl j)) from
            freeWeylGenerator_commutator
              (k := k) (Matrix.J (Fin n) k) (.inl i) (.inl j)]
          simp [Matrix.J]
      | inr j =>
          change -Stafford.commutator (coordinate k n i) (-momentum k n j) = _
          have h := freeWeylGenerator_commutator
            (k := k) (Matrix.J (Fin n) k) (.inl i) (.inr j)
          rw [neg_commutator_right_neg]
          exact h
  | inr i =>
      cases j with
      | inl j =>
          change -Stafford.commutator (-momentum k n i) (coordinate k n j) = _
          have h := freeWeylGenerator_commutator
            (k := k) (Matrix.J (Fin n) k) (.inr i) (.inl j)
          rw [neg_commutator_left_neg]
          exact h
      | inr j =>
          change -Stafford.commutator (-momentum k n i) (-momentum k n j) = _
          have h := freeWeylGenerator_commutator
            (k := k) (Matrix.J (Fin n) k) (.inr i) (.inr j)
          have hJ : Matrix.J (Fin n) k (.inr i) (.inr j) = 0 := by
            simp [Matrix.J]
          rw [hJ] at h ⊢
          rw [neg_commutator_both_neg]
          change
            -Stafford.commutator
                (freeWeylGenerator (Matrix.J (Fin n) k) (.inr i))
                (freeWeylGenerator (Matrix.J (Fin n) k) (.inr j)) = _
          rw [h, map_zero, neg_zero]

theorem transposedGenerator_commutator (n : Nat) :
    ∀ i j,
      Stafford.commutator (transposedGenerator k n i) (transposedGenerator k n j) =
        algebraMap k (PresentedWeyl k n)ᵐᵒᵖ (Matrix.J (Fin n) k i j) := by
  intro i j
  apply unop_injective
  simpa [Stafford.commutator] using
    underlying_transposedGenerator_commutator k n i j

/-- The scalar-preserving anti-homomorphism `x_i ↦ x_i`, `p_i ↦ -p_i`,
represented as an algebra homomorphism to the opposite algebra. -/
def transpositionHom (n : Nat) :
    PresentedWeyl k n →ₐ[k] (PresentedWeyl k n)ᵐᵒᵖ :=
  freeWeylLift (Matrix.J (Fin n) k) (transposedGenerator k n)
    (transposedGenerator_commutator k n)

@[simp]
theorem transpositionHom_coordinate (n : Nat) (i : Fin n) :
    transpositionHom k n (coordinate k n i) = op (coordinate k n i) := by
  simp [transpositionHom, transposedGenerator, coordinate]

@[simp]
theorem transpositionHom_momentum (n : Nat) (i : Fin n) :
    transpositionHom k n (momentum k n i) = op (-momentum k n i) := by
  simp [transpositionHom, transposedGenerator, momentum]

/-- Applying transposition once on each side of the opposite equivalence is
the identity. -/
theorem opComm_transpositionHom_comp_transpositionHom (n : Nat) :
    (AlgHom.opComm (transpositionHom k n)).comp (transpositionHom k n) =
      AlgHom.id k (PresentedWeyl k n) := by
  apply freeWeyl_algHom_ext
  intro i
  cases i with
  | inl i =>
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [show freeWeylGenerator (Matrix.J (Fin n) k) (.inl i) =
        coordinate k n i from rfl, transpositionHom_coordinate]
      change unop (transpositionHom k n (coordinate k n i)) = coordinate k n i
      rw [transpositionHom_coordinate]
      exact unop_op _
  | inr i =>
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [show freeWeylGenerator (Matrix.J (Fin n) k) (.inr i) =
        momentum k n i from rfl, transpositionHom_momentum]
      change unop (transpositionHom k n (-momentum k n i)) = momentum k n i
      rw [map_neg, transpositionHom_momentum]
      simp

theorem transpositionHom_comp_opComm_transpositionHom (n : Nat) :
    (transpositionHom k n).comp (AlgHom.opComm (transpositionHom k n)) =
      AlgHom.id k (PresentedWeyl k n)ᵐᵒᵖ := by
  apply AlgHom.ext
  intro a
  rcases a with ⟨a⟩
  apply unop_injective
  have h := congrArg (fun f : PresentedWeyl k n →ₐ[k] PresentedWeyl k n => f a)
    (opComm_transpositionHom_comp_transpositionHom k n)
  exact h

/-- Transposition is a scalar-preserving equivalence with the opposite Weyl
algebra. -/
def transpositionEquiv (n : Nat) :
    PresentedWeyl k n ≃ₐ[k] (PresentedWeyl k n)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (transpositionHom k n) (AlgHom.opComm (transpositionHom k n))
    (transpositionHom_comp_opComm_transpositionHom k n)
    (opComm_transpositionHom_comp_transpositionHom k n)

@[simp]
theorem transpositionEquiv_apply (n : Nat) (a : PresentedWeyl k n) :
    transpositionEquiv k n a = transpositionHom k n a := rfl

theorem transpositionEquiv_coordinate (n : Nat) (i : Fin n) :
    transpositionEquiv k n (coordinate k n i) = op (coordinate k n i) := by
  simp [transpositionEquiv]

theorem transpositionEquiv_momentum (n : Nat) (i : Fin n) :
    transpositionEquiv k n (momentum k n i) = op (-momentum k n i) := by
  simp [transpositionEquiv]

theorem transpositionEquiv_injective (n : Nat) :
    Function.Injective (transpositionEquiv k n) :=
  (transpositionEquiv k n).injective

theorem transpositionEquiv_surjective (n : Nat) :
    Function.Surjective (transpositionEquiv k n) :=
  (transpositionEquiv k n).surjective

/-- The usual unbundled anti-automorphism underlying `transpositionEquiv`. -/
def transpose (n : Nat) (a : PresentedWeyl k n) : PresentedWeyl k n :=
  unop (transpositionEquiv k n a)

@[simp]
theorem transpose_coordinate (n : Nat) (i : Fin n) :
    transpose k n (coordinate k n i) = coordinate k n i := by
  simp [transpose]

@[simp]
theorem transpose_momentum (n : Nat) (i : Fin n) :
    transpose k n (momentum k n i) = -momentum k n i := by
  simp [transpose]

@[simp]
theorem transpose_algebraMap (n : Nat) (c : k) :
    transpose k n (algebraMap k (PresentedWeyl k n) c) =
      algebraMap k (PresentedWeyl k n) c := by
  simp [transpose]

theorem transpose_mul (n : Nat) (a b : PresentedWeyl k n) :
    transpose k n (a * b) = transpose k n b * transpose k n a := by
  simp [transpose]

@[simp]
theorem transpose_transpose (n : Nat) (a : PresentedWeyl k n) :
    transpose k n (transpose k n a) = a := by
  have h := congrArg (fun f : PresentedWeyl k n →ₐ[k] PresentedWeyl k n => f a)
    (opComm_transpositionHom_comp_transpositionHom k n)
  exact h

theorem transpose_injective (n : Nat) : Function.Injective (transpose k n) := by
  intro a b h
  simpa only [transpose_transpose] using congrArg (transpose k n) h

/-- A right `PresentedWeyl`-module becomes a left module by restriction of
scalars along transposition. -/
@[instance_reducible]
def transposedLeftModule (n : Nat) (M : Type v) [AddCommMonoid M]
    [Module (PresentedWeyl k n)ᵐᵒᵖ M] : Module (PresentedWeyl k n) M :=
  Module.compHom M (transpositionEquiv k n).toRingEquiv.toRingHom

theorem transposedLeftModule_smul (n : Nat) (M : Type v) [AddCommMonoid M]
    [Module (PresentedWeyl k n)ᵐᵒᵖ M]
    (a : PresentedWeyl k n) (m : M) :
    @SMul.smul (PresentedWeyl k n) M
      (transposedLeftModule k n M).toSMul a m =
      transpositionEquiv k n a • m := rfl

theorem transposedLeftModule_coordinate_smul (n : Nat) (M : Type v)
    [AddCommMonoid M] [Module (PresentedWeyl k n)ᵐᵒᵖ M]
    (i : Fin n) (m : M) :
    @SMul.smul (PresentedWeyl k n) M
      (transposedLeftModule k n M).toSMul (coordinate k n i) m =
      op (coordinate k n i) • m := by
  rw [transposedLeftModule_smul, transpositionEquiv_coordinate]

theorem transposedLeftModule_momentum_smul (n : Nat) (M : Type v)
    [AddCommMonoid M] [Module (PresentedWeyl k n)ᵐᵒᵖ M]
    (i : Fin n) (m : M) :
    @SMul.smul (PresentedWeyl k n) M
      (transposedLeftModule k n M).toSMul (momentum k n i) m =
      op (-momentum k n i) • m := by
  rw [transposedLeftModule_smul, transpositionEquiv_momentum]


end
end Stafford38.WeylTransposition
