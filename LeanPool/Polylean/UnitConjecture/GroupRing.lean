/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.UnitConjecture.FreeModule
import Mathlib.Algebra.Field.Basic

namespace LeanPool.Polylean

/-!
# Group Rings

We construct the Group ring `R[G]` given a group `G` and a ring `R`, both having
decidable equality. The ring structures is constructed using the (implicit) universal
property of `R`-modules. As a check on our definitions, `R[G]` is proved to be a Ring.

We first define multiplication on formal sums. We prove many properties that are used both
to show invariance under elementary moves and to prove that `R[G]` is a ring.

-/

variable {R : Type} [Ring R] [DecidableEq R]

variable {G : Type} [Group G] [DecidableEq G]

/-!
## Multiplication on formal sums
-/
/-- multiplication by a monomial -/
def _root_.LeanPool.Polylean.FormalSum.mulMonom
    (b : R) (h : G) : FormalSum R G → FormalSum R G
| [] => []
| (a, g) :: tail => (a * b, g * h) :: (mulMonom b h tail)

/-- multiplication for formal sums -/
def _root_.LeanPool.Polylean.FormalSum.mul
    (fst : FormalSum R G) : FormalSum R G → FormalSum R G
| [] => []
| (b, h) :: ys =>
  (FormalSum.mulMonom b h fst) ++ (mul fst ys)

/-!

## Properties of multiplication on formal sums
-/
namespace GroupRing

open FormalSum
-- multiplication by the zero monomial
omit [DecidableEq R] in
theorem mul_monom_zero (g x₀ : G) (s : FormalSum R G) :
    coords (mulMonom 0 g s) x₀ = 0 := by
  induction s with
  | nil =>
    simp only [mulMonom, coords]
  | cons h t ih =>
    simp only [mulMonom, mul_zero, coords, monom_coords_at_zero, zero_add]
    assumption

-- distributivity of multiplication by a monomial
omit [DecidableEq R] in
theorem mul_monom_dist (b : R) (h x₀ : G)
    (s₁ s₂ : FormalSum R G) :
    coords (mulMonom b h (s₁ ++ s₂)) x₀ =
      coords (mulMonom b h s₁) x₀ + coords (mulMonom b h s₂) x₀ := by
    induction s₁ with
    | nil =>
      simp only [List.nil_append, mulMonom, coords, zero_add]
    | cons head tail ih =>
      simp only [List.cons_append, mulMonom, coords]
      rw [ih]
      simp only [add_assoc]

-- right distributivity
omit [DecidableEq R] in
theorem mul_dist (x₀ : G) (s₁ s₂ s₃ : FormalSum R G) :
    coords (mul s₁ (s₂ ++ s₃)) x₀ =
      coords (mul s₁ s₂) x₀ + coords (mul s₁ s₃) x₀ := by
    induction s₂ with
    | nil =>
      simp only [List.nil_append, mul, coords, zero_add]
    | cons head tail ih =>
      simp only [List.cons_append, mul]
      rw [← append_coords]
      rw [← append_coords]
      rw [ih]
      simp only [add_assoc]


-- associativity with two terms monomials
omit [DecidableEq R] in
theorem mul_monom_monom_assoc (a b : R) (h x₀ : G)
    (s : FormalSum R G) :
    coords (mulMonom b h (mulMonom a x s)) x₀ =
      coords (mulMonom (a * b) (x * h) s) x₀ := by
    induction s with
    | nil =>
      simp only [mulMonom, coords]
    | cons head tail ih =>
      let (a₁, x₁) := head
      simp only [mulMonom, mul_assoc, coords, add_right_inj]
      rw [ih]

-- associativity with one term a monomial
omit [DecidableEq R] in
theorem mul_monom_assoc (b : R) (h x₀ : G)
    (s₁ s₂ : FormalSum R G) :
    coords (mulMonom b h (mul s₁ s₂)) x₀ =
      coords (mul s₁ (mulMonom b h s₂)) x₀ := by
    induction s₂ with
    | nil =>
      simp only [mul, mulMonom, coords]
    | cons head tail ih =>
      let (a, x) := head
      simp only [mul, mulMonom]
      rw [← append_coords]
      rw [mul_monom_dist]
      rw [ih]
      simp only [add_left_inj]
      rw [mul_monom_monom_assoc]

-- left distributivity for multiplication by a monomial
omit [DecidableEq R] in
theorem mul_monom_add (b₁ b₂ : R) (h x₀ : G)
    (s : FormalSum R G) :
    coords (mulMonom (b₁ + b₂) h s) x₀ =
      coords (mulMonom b₁ h s) x₀ + coords (mulMonom b₂ h s) x₀ := by
  induction s with
  | nil =>
    simp only [mulMonom, coords, add_zero]
  | cons head tail ih =>
    let (a, g) := head
    simp only [mulMonom, coords]
    rw [left_distrib]
    rw [monom_coords_hom]
    rw [ih]
    conv =>
      lhs
      rw [add_assoc]
      arg 2
      rw [← add_assoc]
      congr
      rw [add_comm]
    conv =>
      rhs
      rw [add_assoc]
    conv =>
      rhs
      arg 2
      skip
      rw [← add_assoc]

/-- multiplication equivalent when adding term with `0` coefficient -/
theorem mul_zero_cons (s t : FormalSum R G) : mul s ((0, h) :: t) ≈ mul s t := by
    induction s
    case nil =>
      simp only [mul, mulMonom, List.nil_append]
      apply eqlCoords.refl
    case cons head tail _ =>
      simp only [mul, mulMonom, mul_zero, List.cons_append]
      apply funext; intro x₀
      simp only [coords]
      rw [monom_coords_at_zero]
      rw [zero_add]
      rw [← append_coords]
      simp only [add_eq_right]
      let l := mul_monom_zero h x₀ tail
      rw [l]

/-!
## Induced product on the quotient
-/

/-- Quotient in second argument for group ring multiplication
-/
def mulAux : FormalSum R G → R[G] → R[G] := by
  intro s
  apply Quotient.lift (⟦FormalSum.mul s ·⟧)
  apply func_eql_of_move_equiv
  intro t t' rel
  induction rel with
  | zeroCoeff tail g a hyp =>
    rw [hyp]
    dsimp [mul]
    apply Quotient.sound
    apply funext
    intro x₀
    rw [← append_coords]
    let l := mul_monom_zero g x₀ s
    rw [l]
    simp only [zero_add]
  | addCoeffs a b x tail =>
    apply Quotient.sound
    apply funext; intro x₀
    simp only [mul]
    repeat (rw [← append_coords])
    simp only [mul_monom_add, add_assoc]
  | cons a x s₁ s₂ _ step =>
    apply Quotient.sound
    apply funext; intro x₀
    simp only [mul]
    rw [← append_coords]
    rw [← append_coords]
    simp only [add_right_inj]
    let l := congrFun (Quotient.exact step) x₀
    rw [l]
  | swap a₁ a₂ x₁ x₂ tail =>
    apply Quotient.sound
    apply funext; intro x₀
    simp only [mul, ← append_coords]
    rw [← add_assoc]
    rw [← add_assoc]
    simp only [add_left_inj]
    let lc :=
      add_comm
        (coords (mulMonom a₁ x₁ s) x₀)
        (coords (mulMonom a₂ x₂ s) x₀)
    rw [lc]

open ElementaryMove
/-- invariance under moves of multiplication by monomials -/
theorem mul_monom_invariant (b : R) (h x₀ : G) (s₁ s₂ : FormalSum R G)
    (rel : ElementaryMove R G s₁ s₂) :
    coords (mulMonom b h s₁) x₀ = coords (mulMonom b h s₂) x₀ := by
      induction rel with
      | zeroCoeff tail g a hyp =>
        rw [hyp]
        simp only [mulMonom, zero_mul, coords, monom_coords_at_zero, zero_add]
      | addCoeffs a₁ a₂ x tail =>
        simp only [mulMonom, coords, right_distrib, monom_coords_hom, add_assoc]
      | cons a x t₁ t₂ _ step =>
        simp only [mulMonom, coords, step]
      | swap a₁ a₂ x₁ x₂ tail =>
        simp only [mulMonom, coords]
        conv =>
          lhs
          rw [← add_assoc]
          arg 1
          rw [add_comm]
        rw [← add_assoc]


/-- invariance under moves for the first argument for multipilication -/
theorem first_arg_invariant (s₁ s₂ t : FormalSum R G)
    (rel : ElementaryMove R G s₁ s₂) :
    FormalSum.mul s₁ t ≈ FormalSum.mul s₂ t := by
    cases t
    case nil =>
      simp only [mul]
      rfl
    case cons head' tail' =>
      let (b, h) := head'
      induction rel with
      | zeroCoeff tail g a hyp =>
        rw [hyp]
        simp only [mul, mulMonom, zero_mul, List.cons_append]
        apply funext; intro x₀
        rw [← append_coords]
        simp only [coords, monom_coords_at_zero, zero_add]
        rw [← append_coords]
        simp only [add_right_inj]
        let rel' : ElementaryMove R G ((0, g) :: tail) tail := by
          apply ElementaryMove.zeroCoeff
          rfl
        let prev := first_arg_invariant _ _ tail' rel'
        let pl := congrFun prev x₀
        rw [pl]
      | addCoeffs a₁ a₂ x tail =>
        simp only [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        simp only [mulMonom, coords]
        rw [right_distrib]
        simp only [monom_coords_hom]
        let rel' : ElementaryMove R G
          ((a₁, x) :: (a₂, x) :: tail)
            ((a₁ + a₂, x) :: tail) := by
            apply ElementaryMove.addCoeffs
        let prev := first_arg_invariant _ _ tail' rel'
        let pl := congrFun prev x₀
        rw [pl]
        simp only [add_assoc]
      | cons a x s₁ s₂ r _ =>
        simp only [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        simp only [mulMonom, coords]
        let rel' : ElementaryMove R G
          ((a, x) :: s₁)
            ((a, x) :: s₂) := by
            apply ElementaryMove.cons
            assumption
        let prev := first_arg_invariant _ _ tail' rel'
        let pl := congrFun prev x₀
        rw [pl]
        let ps := mul_monom_invariant b h x₀ s₁ s₂ r
        rw [ps]
      | swap a₁ a₂ x₁ x₂ tail =>
        simp only [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        rw [mulMonom]
        rw [mulMonom]
        rw [coords]
        rw [coords]
        rw [mulMonom]
        rw [mulMonom]
        rw [coords]
        rw [coords]
        let rel' : ElementaryMove R G
          ((a₁, x₁) :: (a₂, x₂) :: tail)
            ((a₂, x₂) :: (a₁, x₁) :: tail) := by
            apply ElementaryMove.swap
        let prev := first_arg_invariant _ _ tail' rel'
        let pl := congrFun prev x₀
        rw [pl]
        simp only [add_left_inj]
        rw [← add_assoc]
        rw [← add_assoc]
        simp only [add_left_inj]
        conv =>
          lhs
          rw [add_comm]

/-- The empty right factor is preserved by elementary moves in the first factor. -/
theorem first_arg_invariant_nil (s₁ s₂ : FormalSum R G)
    (rel : ElementaryMove R G s₁ s₂) :
    FormalSum.mul s₁ [] ≈ FormalSum.mul s₂ [] :=
  first_arg_invariant s₁ s₂ [] rel

/-- multiplication for free modules -/
def mul : R[G] → R[G] → R[G] := by
  let f := fun (s : FormalSum R G) =>
    fun (t : R[G]) => mulAux s t
  apply Quotient.lift f
  apply func_eql_of_move_equiv
  intro s₁ s₂ rel
  simp only [f]
  apply funext
  apply Quotient.ind
  intro t
  let lhs : mulAux s₁ (Quotient.mk (formalSumSetoid R G) t) =
    ⟦FormalSum.mul s₁ t⟧ := by
      simp only [mulAux, Quotient.lift_mk]
  let rhs : mulAux s₂ (Quotient.mk (formalSumSetoid R G) t) =
    ⟦FormalSum.mul s₂ t⟧ := by
      simp only [mulAux, Quotient.lift_mk]
  rw [lhs, rhs]
  apply Quotient.sound
  apply first_arg_invariant
  exact rel

/-!
## The Ring Structure
-/

instance groupRingMul : Mul (R[G]) :=
  ⟨mul⟩

instance : One (R[G]) :=
  ⟨⟦[(1, 1)]⟧⟩

instance : AddCommGroup (R[G]) :=
  {
    zero := ⟦ [] ⟧
    add := FreeModule.add

    nsmul := nsmulRec
    zsmul := zsmulRec

    add_assoc := FreeModule.addn_assoc
    add_zero := FreeModule.addn_zero
    zero_add := FreeModule.zero_addn
    add_comm := FreeModule.addn_comm
    neg_add_cancel := by
        intro x
        let l := FreeModule.coeffs_distrib (-1 : R) (1 : R) x
        rw [neg_add_cancel, FreeModule.unit_coeffs, FreeModule.zero_coeffs] at l
        exact l
  }

/-- The group ring is a ring -/
instance : Ring (R[G]) :=
  {
    mul := mul
    neg := fun x => (-1 : R) • x
    zsmul := zsmulRec

    sub_eq_add_neg := by
      intro x y
      rfl

    neg_add_cancel := by
        intro x
        let l := FreeModule.coeffs_distrib (-1 : R) (1 : R) x
        simp only [neg_add_cancel] at l
        have lc : (-1 : R) + 1 = 0 := by
            apply neg_add_cancel
        -- rw [lc] at l
        rw [FreeModule.unit_coeffs] at l
        rw [FreeModule.zero_coeffs] at l
        exact l

    left_distrib := by
      apply @Quotient.ind (motive := fun a =>
        ∀ b c, a * (b + c) = a * b + a * c)
      intro x
      apply @Quotient.ind₂ (motive := fun b c =>
        ⟦ x ⟧ * (b + c) = ⟦ x ⟧ * b + ⟦ x ⟧ * c)
      intro y z
      apply Quotient.sound
      induction y with
      | nil =>
          simp only [List.nil_append]
          simp only [FormalSum.mul, List.nil_append]
          apply eqlCoords.refl
      | cons h t ih =>
          simp only [List.cons_append, FormalSum.mul, List.append_assoc]
          apply funext; intro x₀
          repeat (rw [← append_coords])
          simp only [add_right_inj]
          let lih := congrFun ih x₀
          rw [← append_coords] at lih
          rw [lih]
    right_distrib := by
      apply @Quotient.ind (motive := fun a =>
        ∀ b c, (a + b) * c = a * c + b * c)
      intro x
      apply @Quotient.ind₂ (motive := fun b c =>
        (⟦ x ⟧ + b) * c = ⟦ x ⟧ * c + b * c)
      intro y z
      apply Quotient.sound
      induction z with
      | nil =>
          simp only [FormalSum.mul, List.append_nil]
          apply eqlCoords.refl
      | cons h t ih =>
          let (a, h) := h
          simp only [FormalSum.mul, List.append_assoc]
          funext x₀
          repeat (rw [← append_coords])
          let lih := congrFun ih x₀
          rw [← append_coords] at lih
          rw [lih]
          rw [mul_monom_dist]
          simp only [add_left_comm, add_assoc]
    zero_mul := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      induction x with
      | nil =>
        rfl
      | cons h t ih =>
        rw [FormalSum.mul]
        simp only [mulMonom, List.nil_append]
        apply funext; intro x₀
        let lih := congrFun ih x₀
        rw [coords] at lih
        -- rw [← append_coords]
        rw [lih]
        simp only [coords]

    mul_zero := by
      apply Quotient.ind
      intro x
      rfl

    one := ⟦[(1, 1)]⟧
    natCast := fun n => ⟦ [(n, 1)] ⟧
    natCast_zero :=
      by
      apply Quotient.sound
      apply funext; intro x₀
      simp only [coords, monomCoeff, Nat.cast_zero, add_zero]
      cases 1 == x₀ <;> rfl
    natCast_succ := by
      intro n
      apply Quotient.sound
      apply funext; intro x₀
      rw [← append_coords]
      simp only [Nat.cast_add, Nat.cast_one]
      cases m: 1 == x₀ with
      | true => simp only [coords, monomCoeff, m, add_zero]
      | false => simp only [coords, monomCoeff, m, add_zero]
    mul_assoc := by
      apply @Quotient.ind (motive := fun a =>
        ∀ b c, a * b * c = a * (b * c))
      intro x
      apply @Quotient.ind₂ (motive := fun b c =>
        ⟦ x ⟧ * b * c = ⟦ x ⟧ * (b * c))
      intro y z
      apply Quotient.sound
      apply funext; intro x₀
      induction z with
      | nil =>
          simp only [FormalSum.mul]
      | cons h t ih =>
          let (a, h) := h
          simp only [FormalSum.mul]
          repeat (rw [← append_coords])
          rw [mul_dist]
          rw [ih]
          rw [mul_monom_assoc]
    mul_one := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      apply funext; intro x₀
      repeat (rw[FormalSum.mul])
      simp only [List.append_nil]
      induction x with
      | nil => rfl
      | cons h t ih =>
        let (a, x) := h
        rw [mulMonom, coords, monomCoeff]
        simp only [mul_one]
        rw [coords, monomCoeff]
        simp only [ih]

    one_mul := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      apply funext; intro x₀
      induction x with
      | nil => rfl
      | cons h t ih =>
        let (a, x) := h
        repeat (rw [coords])
        rw [FormalSum.mul]
        rw [← append_coords]
        simp only [mulMonom, one_mul, coords, add_zero, ih]
  }

end GroupRing

/-!
## Inclusions of the group and ring into the group ring
-/
/-- Product `R → G → R[G]`, `r ↦ g ↦ r ⬝ g`; used only in verification results. -/
instance groupRingMul {R G : Type _} [Ring R] [DecidableEq G] [DecidableEq R] :
    HMul R G (FreeModule R G) := ⟨fun r g ↦ ⟦[(r, g)]⟧⟩

/-- Scalar multiplication by a group element is represented by the singleton formal sum. -/
theorem groupRingMul_apply {R G : Type _} [Ring R] [DecidableEq G] [DecidableEq R]
    (r : R) (g : G) : r * g = (⟦[(r, g)]⟧ : FreeModule R G) := rfl

/-- Monoid homomorphism from `G` to `R[G]` given by `g ↦ 1 ⬝ g` -/
def groupInclusionHom (G : Type) [Group G] [DecidableEq G] : G →* R[G] :=
  { toFun := baseInclusion 1,
    map_one' := rfl,
    map_mul' :=
    by
      intro _ _
      apply Quotient.sound
      funext x
      simp only [FormalSum.coords, monomCoeff, add_zero, FormalSum.mul, FormalSum.mulMonom, mul_one,
            List.append_nil]

  }

/-- As a function `groupInclusionHom` is `g ↦ 1 ⬝ g` -/
theorem groupInclusionHom_formula (G : Type) [Group G] [DecidableEq G] :
  (groupInclusionHom (R := R) G).toFun =
    fun g : G ↦ (1 : R) * g := rfl

/-- The monoid homomorphism `G → R[G]`, `g ↦ 1 ⬝ g` is injective if `1 ≠ 0` in `R`. -/
theorem groupInclusionHom_injective' (hR : (1 : R) ≠ (0 : R)) :
    Function.Injective (groupInclusionHom (R := R) G) := by
  intro _ _
  apply baseInclusion_injective (1 : R) hR (X := G)

/-- For a field `F` the monoid homomorphism `G → F[G]`, `g ↦ 1 ⬝ g` is injective. -/
theorem groupInclusionHom_injective {F : Type} [Field F] [DecidableEq F]
    (G : Type) [Group G] [DecidableEq G] :
    Function.Injective (groupInclusionHom (R := F) G) := by
  intro _ _
  apply groupInclusionHom_injective'
  have : (0 : F) ≠ (1 : F) := zero_ne_one
  simp_all only [ne_eq, zero_ne_one, not_false_iff, one_ne_zero]

/-- The ring homomorphism `R → R[G]` given by `a ↦  a ⬝ 1` -/
def ringInclusionHom (G : Type) [Group G] [DecidableEq G] : R →+* R[G] :=
  { toFun := coeffInclusion 1,
    map_one' := rfl,
    map_mul' :=
    by
      intro _ _
      apply Quotient.sound
      funext x
      simp only [FormalSum.coords, monomCoeff, add_zero, FormalSum.mul, FormalSum.mulMonom, mul_one,
            List.append_nil]
    map_zero' := by
      apply Quotient.sound
      funext x
      simp only [FormalSum.coords, monomCoeff, add_zero]
      split <;> rfl,
    map_add' := by
      intro _ _
      apply Quotient.sound
      funext x
      rw [← FormalSum.append_coords]
      simp only [FormalSum.coords, monomCoeff]
      by_cases h : (1 : G) == x
      · simp only [h, add_zero]
      · simp only [h, add_zero]
  }


/-- As a function, `ringInclusionHom` is `r ↦ r ⬝ 1` -/
theorem ringInclusionHom_formula (G : Type) [Group G] [DecidableEq G] :
  (ringInclusionHom (R := R) G).toFun =
    fun r : R ↦ r * (1 : G) := rfl

/-- The ring homomorphism `R → R[G]` given by `a ↦  a ⬝ 1` is injective -/
theorem ringInclusionHom_injective'
  (G : Type) [Group G] [DecidableEq G] : Function.Injective (ringInclusionHom (R := R) G) := by
  intro _ _
  apply coeffInclusion_injective

end LeanPool.Polylean
