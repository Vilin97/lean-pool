/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Places
public import Mathlib.Tactic.LinearCombination

/-!
# Small exterior-coordinate layer

Only the exterior degrees used by the manuscript are represented here.  In
characteristic two an alternating two-form is a symmetric zero-diagonal
matrix, and the signs in the coordinate wedge formulas disappear.  These
explicit bilinear maps avoid constructing or deciding equality in a large
general-purpose exterior algebra.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Coefficients of a linear form in the eight input variables. -/
abbrev LinearForm := Fin 8 → F₂
/-- Two-index coordinate arrays used to represent exterior two-forms. -/
abbrev TwoForm := Fin 8 → Fin 8 → F₂
/-- Three-index coordinate arrays used to represent exterior three-forms. -/
abbrev ThreeForm := Fin 8 → Fin 8 → Fin 8 → F₂
/-- Four-index coordinate arrays used to represent exterior four-forms. -/
abbrev FourForm := Fin 8 → Fin 8 → Fin 8 → Fin 8 → F₂
/-- Five-index coordinate arrays used to represent exterior five-forms. -/
abbrev FiveForm := Fin 8 → Fin 8 → Fin 8 → Fin 8 → Fin 8 → F₂

/-- Dimension-polymorphic versions used for quotient and tail arguments. -/
@[expose] def vectorWedgeN {n : Nat} (u v : Fin n → F₂) : Fin n → Fin n → F₂ :=
  fun i j => u i * v j + u j * v i

/-- Coordinates of a vector wedged with a two-form, in arbitrary finite dimension. -/
@[expose] def vectorWedgeTwoN {n : Nat} (u : Fin n → F₂)
    (q : Fin n → Fin n → F₂) : Fin n → Fin n → Fin n → F₂ :=
  fun i j k => u i * q j k + u j * q i k + u k * q i j

/-- If wedging a nonzero vector with an alternating two-form vanishes, that
two-form has the vector as a decomposable factor. -/
theorem decomposable_of_vectorWedgeTwoN_zero {n : Nat}
    (u : Fin n → F₂) (q : Fin n → Fin n → F₂)
    (hu : u ≠ 0)
    (h : vectorWedgeTwoN u q = 0) :
    ∃ v : Fin n → F₂, q = vectorWedgeN u v := by
  have hex : ∃ k, u k ≠ 0 := by
    by_contra hk
    push Not at hk
    exact hu (funext hk)
  rcases hex with ⟨k, huk⟩
  have huk1 : u k = 1 := (f2_eq_zero_or_one (u k)).resolve_left huk
  let v : Fin n → F₂ := fun j => q k j
  refine ⟨v, ?_⟩
  funext i j
  have hij := congrFun (congrFun (congrFun h k) i) j
  simp only [vectorWedgeTwoN, Pi.zero_apply, huk1, one_mul] at hij
  simp only [v, vectorWedgeN]
  apply sub_eq_zero.mp
  rw [CharTwo.sub_eq_add]
  simpa [add_assoc] using hij

/-- Exterior product of two vectors. -/
@[expose] def vectorWedge (u v : LinearForm) : TwoForm :=
  fun i j => u i * v j + u j * v i

/-- Exterior product of a vector and a two-form. -/
@[expose] def vectorWedgeTwo (u : LinearForm) (q : TwoForm) : ThreeForm :=
  fun i j k => u i * q j k + u j * q i k + u k * q i j

theorem vectorWedgeTwo_repeated_left (x y : LinearForm) :
    vectorWedgeTwo x (vectorWedge x y) = 0 := by
  funext i j k
  simp only [vectorWedgeTwo, vectorWedge, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem vectorWedgeTwo_repeated_right (x y : LinearForm) :
    vectorWedgeTwo y (vectorWedge x y) = 0 := by
  funext i j k
  simp only [vectorWedgeTwo, vectorWedge, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem vectorWedgeTwo_smul_left (a : F₂) (x : LinearForm) (q : TwoForm) :
    vectorWedgeTwo (a • x) q = a • vectorWedgeTwo x q := by
  funext i j k
  simp only [vectorWedgeTwo, Pi.smul_apply, smul_eq_mul]
  ring

/-- A vector annihilating a nonzero decomposable two-form belongs to its
two-dimensional support.  This is the coordinate form of exactness of the
Koszul complex in degree one. -/
theorem mem_support_of_vectorWedgeTwo_zero
    (u x y : LinearForm) (hxy : vectorWedge x y ≠ 0)
    (h : vectorWedgeTwo u (vectorWedge x y) = 0) :
    ∃ a b : F₂, u = a • x + b • y := by
  have hex : ∃ i j, vectorWedge x y i j ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hxy (funext fun i => funext fun j => hnone i j)
  rcases hex with ⟨i, j, hij⟩
  have hij1 : vectorWedge x y i j = 1 :=
    (f2_eq_zero_or_one (vectorWedge x y i j)).resolve_left hij
  let a : F₂ := u i * y j + u j * y i
  let b : F₂ := u i * x j + u j * x i
  refine ⟨a, b, ?_⟩
  funext k
  have hk := congrFun (congrFun (congrFun h i) j) k
  simp only [vectorWedgeTwo, Pi.zero_apply] at hk
  rw [hij1, mul_one] at hk
  simp only [vectorWedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
  dsimp [a, b]
  ring_nf at hk ⊢
  let t : F₂ :=
    u i * x j * y k + u i * x k * y j +
      y k * u j * x i + x k * u j * y i
  have htu : t = u k := by
    have ht : t + u k = 0 := by simpa [t] using hk
    rw [← CharTwo.sub_eq_add] at ht
    exact sub_eq_zero.mp ht
  simpa [t] using htu.symm

/-- Exterior product of two two-forms.  The six terms remember which of the
two input forms receives each pair. -/
@[expose] def wedgeTwo (q c : TwoForm) : FourForm :=
  fun i j k l =>
    q i j * c k l + q i k * c j l + q i l * c j k +
    c i j * q k l + c i k * q j l + c i l * q j k

/-- Exterior product of a cubic and a two-form. -/
@[expose] def wedgeThreeTwo (h : ThreeForm) (q : TwoForm) : FiveForm :=
  fun i j k l m =>
    h i j k * q l m + h i j l * q k m + h i j m * q k l +
    h i k l * q j m + h i k m * q j l + h i l m * q j k +
    h j k l * q i m + h j k m * q i l + h j l m * q i k +
    h k l m * q i j

/-- Exterior product of a vector and a four-form. -/
@[expose] def vectorWedgeFour (u : LinearForm) (w : FourForm) : FiveForm :=
  fun i j k l m =>
    u i * w j k l m + u j * w i k l m + u k * w i j l m +
    u l * w i j k m + u m * w i j k l

/-- Associativity in the only exterior degrees needed by the feedback
annihilator.  Keeping the statement in coordinates makes it independent of a
large general-purpose exterior-algebra construction. -/
theorem wedgeThreeTwo_vectorWedgeTwo (u : LinearForm) (q c : TwoForm) :
    wedgeThreeTwo (vectorWedgeTwo u q) c =
      vectorWedgeFour u (wedgeTwo q c) := by
  funext i j k l m
  simp only [wedgeThreeTwo, vectorWedgeTwo, vectorWedgeFour, wedgeTwo]
  ring

theorem wedgeThreeTwo_vectorWedgeTwo_eq_zero {u : LinearForm} {q c : TwoForm}
    (hqc : wedgeTwo q c = 0) :
    wedgeThreeTwo (vectorWedgeTwo u q) c = 0 := by
  rw [wedgeThreeTwo_vectorWedgeTwo, hqc]
  funext i j k l m
  simp [vectorWedgeFour]

theorem wedgeTwo_add_right (q c d : TwoForm) :
    wedgeTwo q (c + d) = wedgeTwo q c + wedgeTwo q d := by
  funext i j k l
  simp only [wedgeTwo, Pi.add_apply]
  ring

theorem wedgeTwo_add_left (q c d : TwoForm) :
    wedgeTwo (q + c) d = wedgeTwo q d + wedgeTwo c d := by
  funext i j k l
  simp only [wedgeTwo, Pi.add_apply]
  ring

/-- A two-plane wedges trivially with every decomposable two-form having a
repeated factor from that plane. -/
theorem wedge_decomposable_repeated_left (x y z : LinearForm) :
    wedgeTwo (vectorWedge x y) (vectorWedge x z) = 0 := by
  funext i j k l
  simp only [wedgeTwo, vectorWedge, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem wedge_decomposable_repeated_right (x y z : LinearForm) :
    wedgeTwo (vectorWedge x y) (vectorWedge z y) = 0 := by
  funext i j k l
  simp only [wedgeTwo, vectorWedge, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

theorem wedge_place_firstJet_zero (x u y v : LinearForm) :
    wedgeTwo (vectorWedge x y)
      (vectorWedge x v + vectorWedge u y) = 0 := by
  rw [wedgeTwo_add_right, wedge_decomposable_repeated_left,
    wedge_decomposable_repeated_right, add_zero]

@[simp] theorem wedgeTwo_self (q : TwoForm) : wedgeTwo q q = 0 := by
  funext i j k l
  simp only [wedgeTwo, Pi.zero_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- The three rational `A`-side place vectors: zero, one, infinity. -/
@[expose] def placeA : Fin 3 → LinearForm :=
  ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0]]

/-- The three rational `B`-side place vectors: zero, one, infinity. -/
@[expose] def placeB : Fin 3 → LinearForm :=
  ![![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- Exterior product of the two input evaluations at a rational place. -/
@[expose] def rationalPlaceTwo (θ : Fin 3) : TwoForm :=
  vectorWedge (placeA θ) (placeB θ)

/-- Linear combination of the two-forms of the three rational places. -/
@[expose] def rationalTwo (α : Fin 3 → F₂) : TwoForm :=
  ∑ θ : Fin 3, α θ • rationalPlaceTwo θ

/-- Ordinary vector dependence over `F₂`, derived algebraically from the
vanishing of every `2 × 2` minor. -/
theorem dependent_of_vectorWedge_zero {n : Nat} (u v : Fin n → F₂)
    (h : ∀ i j, u i * v j + u j * v i = 0) :
    u = 0 ∨ v = 0 ∨ u = v := by
  by_cases hu : u = 0
  · exact Or.inl hu
  · have hex : ∃ k, u k ≠ 0 := by
      by_contra hk
      push Not at hk
      exact hu (funext hk)
    rcases hex with ⟨k, huk⟩
    have huk1 : u k = 1 := (f2_eq_zero_or_one (u k)).resolve_left huk
    rcases f2_eq_zero_or_one (v k) with hvk | hvk
    · apply Or.inr (Or.inl ?_)
      funext j
      simpa [huk1, hvk] using h k j
    · apply Or.inr (Or.inr ?_)
      funext j
      have hj := h k j
      simp only [huk1, hvk, one_mul, mul_one] at hj
      rw [add_comm, ← CharTwo.sub_eq_add] at hj
      exact sub_eq_zero.mp hj

theorem rational_wedge_coord_01 (α β : Fin 3 → F₂) :
    wedgeTwo (rationalTwo α) (rationalTwo β) 0 1 4 6 =
      α 0 * β 1 + α 1 * β 0 := by
  simp [wedgeTwo, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
    Fin.sum_univ_succ]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

theorem rational_wedge_coord_12 (α β : Fin 3 → F₂) :
    wedgeTwo (rationalTwo α) (rationalTwo β) 1 3 5 7 =
      α 1 * β 2 + α 2 * β 1 := by
  simp [wedgeTwo, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
    Fin.sum_univ_succ]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

theorem rational_wedge_coord_mid (α β : Fin 3 → F₂) :
    wedgeTwo (rationalTwo α) (rationalTwo β) 0 3 4 7 =
      (α 0 * β 1 + α 1 * β 0) +
      (α 0 * β 2 + α 2 * β 0) +
      (α 1 * β 2 + α 2 * β 1) := by
  simp [wedgeTwo, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
    Fin.sum_univ_succ]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

/-- The three pair wedges of rational places are independent.  Equivalently,
two forms in their span have zero exterior product exactly when their
coefficient vectors are dependent. -/
theorem rational_wedge_zero_dependent (α β : Fin 3 → F₂)
    (h : wedgeTwo (rationalTwo α) (rationalTwo β) = 0) :
    α = 0 ∨ β = 0 ∨ α = β := by
  have h01 : α 0 * β 1 + α 1 * β 0 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) 6
    simpa [rational_wedge_coord_01] using
      (rational_wedge_coord_01 α β).symm.trans hc
  have h12 : α 1 * β 2 + α 2 * β 1 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun h 1) 3) 5) 7
    simpa using (rational_wedge_coord_12 α β).symm.trans hc
  have h02 : α 0 * β 2 + α 2 * β 0 = 0 := by
    have hc := congrFun (congrFun (congrFun (congrFun h 0) 3) 4) 7
    have hm := (rational_wedge_coord_mid α β).symm.trans hc
    rw [h01, h12] at hm
    simpa using hm
  apply dependent_of_vectorWedge_zero α β
  intro i j
  fin_cases i <;> fin_cases j
  · exact CharTwo.add_self_eq_zero _
  · exact h01
  · exact h02
  · rw [add_comm]
    exact h01
  · exact CharTwo.add_self_eq_zero _
  · exact h12
  · rw [add_comm]
    exact h02
  · rw [add_comm]
    exact h12
  · exact CharTwo.add_self_eq_zero _

end

end N4
end UnrestrictedBooleanMul
