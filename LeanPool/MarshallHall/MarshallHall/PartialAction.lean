/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Logic.Equiv.Fintype


/-!
The right action of a group on the quotient by the right-coset relation is
available even when the subgroup is not normal.  We record it explicitly
because this is the finite-state action used by the Hall construction.
-/

@[expose] public section

open Function

noncomputable section

namespace MarshallHall

universe u

variable {G : Type u} [Group G]



/-- The quotient by the subgroup's right-coset relation. -/
abbrev RightCosetQuotient (H : Subgroup G) :=
  Quotient (QuotientGroup.rightRel H)

/-- The quotient by the subgroup's left-coset relation. -/
abbrev LeftCosetQuotient (H : Subgroup G) :=
  Quotient (QuotientGroup.leftRel H)

/-- Left multiplication acting on left cosets of a subgroup. -/
def leftMul (H : Subgroup G) (a : G) : LeftCosetQuotient H → LeftCosetQuotient H :=
  Quotient.lift (fun x : G => Quotient.mk'' (a * x)) (by
    intro x y hxy
    apply Quotient.sound'
    have hxy' : (QuotientGroup.leftRel H) x y := hxy
    rw [QuotientGroup.leftRel_apply] at hxy' ⊢
    simpa [mul_assoc] using hxy')

@[simp]
theorem leftMul_mk (H : Subgroup G) (a x : G) :
    leftMul H a (Quotient.mk'' x) = Quotient.mk'' (a * x) := rfl

/-- Left multiplication as a permutation of the left-coset space. -/
def leftMulEquiv (H : Subgroup G) (a : G) :
    LeftCosetQuotient H ≃ LeftCosetQuotient H where
  toFun := leftMul H a
  invFun := leftMul H a⁻¹
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [leftMul]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [leftMul]

@[simp]
theorem leftMulEquiv_mk (H : Subgroup G) (a x : G) :
    leftMulEquiv H a (Quotient.mk'' x) = Quotient.mk'' (a * x) := rfl

@[simp]
theorem leftMulEquiv_one (H : Subgroup G) (x : LeftCosetQuotient H) :
    leftMulEquiv H 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro x
  simp [leftMulEquiv, leftMul]

theorem leftMulEquiv_mul (H : Subgroup G) (a b : G)
    (x : LeftCosetQuotient H) :
    leftMulEquiv H (a * b) x =
      leftMulEquiv H a (leftMulEquiv H b x) := by
  refine Quotient.inductionOn x ?_
  intro x
  simp [leftMulEquiv, leftMul, mul_assoc]

theorem leftMulEquiv_inv_apply (H : Subgroup G) (a : G)
    (x : LeftCosetQuotient H) :
    leftMulEquiv H a⁻¹ (leftMulEquiv H a x) = x := by
  have h := (leftMulEquiv H a).symm_apply_apply x
  simpa [leftMulEquiv] using h

theorem leftCoset_mk_eq_one_iff (H : Subgroup G) (x : G) :
    (Quotient.mk'' x : LeftCosetQuotient H) = Quotient.mk'' (1 : G) ↔ x ∈ H := by
  constructor
  · intro h
    have hrel := Quotient.exact' h
    rw [QuotientGroup.leftRel_apply] at hrel
    have hxinv : x⁻¹ ∈ H := by simpa using hrel
    simpa using H.inv_mem hxinv
  · intro hx
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    simpa using H.inv_mem hx

section Restricted

variable {Q : Type u} (A : Set Q) (e : Q ≃ Q)

/-- The equivalence between points whose image remains in a subset and their image within that
subset. -/
def restrictedEquiv :
    {x : A // e x.1 ∈ A} ≃
      {y : A // ∃ x : A, e x.1 ∈ A ∧ e x.1 = y.1} where
  toFun x := ⟨⟨e x.1, x.2⟩, ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨⟨e.symm y.1, by
    rcases y.2 with ⟨x, hx, hxy⟩
    rw [← hxy, e.symm_apply_apply]
    exact x.2⟩, by
      rw [e.apply_symm_apply]
      exact y.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simp

@[simp]
theorem restrictedEquiv_apply (x : {x : A // e x.1 ∈ A}) :
    restrictedEquiv A e x =
      ⟨⟨e x.1, x.2⟩, ⟨x.1, x.2, rfl⟩⟩ := rfl

end Restricted

/-- Right multiplication acting on right cosets of a subgroup. -/
def rightMul (H : Subgroup G) (a : G) : RightCosetQuotient H → RightCosetQuotient H :=
  Quotient.lift (fun x : G => Quotient.mk'' (x * a)) (by
    intro x y hxy
    apply Quotient.sound'
    have hxy' : (QuotientGroup.rightRel H) x y := hxy
    rw [QuotientGroup.rightRel_apply] at hxy' ⊢
    simpa [mul_assoc] using hxy')

@[simp]
theorem rightMul_mk (H : Subgroup G) (a x : G) :
    rightMul H a (Quotient.mk'' x) = Quotient.mk'' (x * a) := rfl

/-- Right multiplication as a permutation of the right-coset space. -/
def rightMulEquiv (H : Subgroup G) (a : G) :
    RightCosetQuotient H ≃ RightCosetQuotient H where
  toFun := rightMul H a
  invFun := rightMul H a⁻¹
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [rightMul]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    simp [rightMul]

@[simp]
theorem rightMulEquiv_mk (H : Subgroup G) (a x : G) :
    rightMulEquiv H a (Quotient.mk'' x) = Quotient.mk'' (x * a) := rfl

end MarshallHall
