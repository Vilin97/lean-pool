/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticCoordinates

/-!
# Direct sum of the three rational-place cubic spaces

The manuscript uses

`I₀ ⊕ I₁ ⊕ I∞`, where `Iθ = L ∧ rθ`.

The eighteen packed rows below form a left inverse on the six quotient
coordinates of each summand.  Their correctness is checked only on the
`3 × 8` coordinate vectors and extended to arbitrary linear forms by
linearity.  This compact certificate replaces repeated coordinate chases in
the quartic and annihilator arguments.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The 56 strictly increasing triples of eight coordinate indices. -/
def upperTriple : Fin 56 → Fin 8 × Fin 8 × Fin 8 :=
  ![(0,1,2),(0,1,3),(0,1,4),(0,1,5),(0,1,6),(0,1,7),
    (0,2,3),(0,2,4),(0,2,5),(0,2,6),(0,2,7),
    (0,3,4),(0,3,5),(0,3,6),(0,3,7),
    (0,4,5),(0,4,6),(0,4,7),(0,5,6),(0,5,7),(0,6,7),
    (1,2,3),(1,2,4),(1,2,5),(1,2,6),(1,2,7),
    (1,3,4),(1,3,5),(1,3,6),(1,3,7),
    (1,4,5),(1,4,6),(1,4,7),(1,5,6),(1,5,7),(1,6,7),
    (2,3,4),(2,3,5),(2,3,6),(2,3,7),
    (2,4,5),(2,4,6),(2,4,7),(2,5,6),(2,5,7),(2,6,7),
    (3,4,5),(3,4,6),(3,4,7),(3,5,6),(3,5,7),(3,6,7),
    (4,5,6),(4,5,7),(4,6,7),(5,6,7)]

/-- Packed covectors recovering six quotient coordinates at each rational place. -/
def cubicDirectRecoverTable : Fin 18 → Nat :=
  ![0x0000000000000c,0x00000000000180,0x00000000001800,
    0x00000040008000,0x00000040050000,0x000000400a0000,
    0x00000000000008,0x00000000000100,0x00000000001000,
    0x00000040000000,0x00000040040000,0x00000040080000,
    0x00000000005000,0x00000020001008,0x00008000001100,
    0x01000040080000,0x04000000080000,0x080000000c0000]

/-- Extract one coordinate from a three-form coordinate array. -/
def threeFormCoordinate (i j k : Fin 8) : ThreeForm →ₗ[F₂] F₂ where
  toFun := fun h => h i j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear functional encoded by one row of the cubic recovery table. -/
def cubicDirectRecover (r : Fin 18) : ThreeForm →ₗ[F₂] F₂ :=
  ∑ k : Fin 56,
    (if Nat.testBit (cubicDirectRecoverTable r) k.val then (1 : F₂) else 0) •
      threeFormCoordinate (upperTriple k).1 (upperTriple k).2.1
        (upperTriple k).2.2

/-- Wedge a linear form with the two-form of one rational place. -/
@[expose] def cubicPlaceLinear (theta : Fin 3) : LinearForm →ₗ[F₂] ThreeForm where
  toFun := fun u => vectorWedgeTwo u (rationalPlaceTwo theta)
  map_add' u v := vectorWedgeTwo_add_left u v _
  map_smul' a u := vectorWedgeTwo_smul_left a u _

/-- Sum of the cubic contributions at the three rational places. -/
@[expose] def rationalCubicDirectSum (M : Fin 3 → LinearForm) : ThreeForm :=
  ∑ theta : Fin 3, cubicPlaceLinear theta (M theta)

/-- Six quotient coordinates for each of `P₀`, `P₁`, and `P∞`. -/
def cubicDirectQuotient (M : Fin 3 → LinearForm) : Fin 18 → F₂ :=
  ![M 0 1, M 0 2, M 0 3, M 0 5, M 0 6, M 0 7,
    M 1 1 + M 1 0, M 1 2 + M 1 0, M 1 3 + M 1 0,
    M 1 5 + M 1 4, M 1 6 + M 1 4, M 1 7 + M 1 4,
    M 2 0, M 2 1, M 2 2, M 2 4, M 2 5, M 2 6]

/-- A coordinate vector at one rational place, with zero inputs at the other places. -/
def singleCubicInput (theta : Fin 3) (j : Fin 8) : Fin 3 → LinearForm :=
  fun phi => if phi = theta then coordinateLinear j else 0

theorem cubicDirectRecover_basis_check :
    ∀ (r : Fin 18) (theta : Fin 3) (j : Fin 8),
      cubicDirectRecover r
          (vectorWedgeTwo (coordinateLinear j) (rationalPlaceTwo theta)) =
        cubicDirectQuotient (singleCubicInput theta j) r := by
  decide +kernel

theorem cubicDirectRecover_sum (M : Fin 3 → LinearForm) (r : Fin 18) :
    cubicDirectRecover r (rationalCubicDirectSum M) =
      cubicDirectQuotient M r := by
  rw [rationalCubicDirectSum, map_sum]
  have hcoord (theta : Fin 3) :
      cubicDirectRecover r (cubicPlaceLinear theta (M theta)) =
        ∑ j : Fin 8, M theta j •
          cubicDirectRecover r
            (vectorWedgeTwo (coordinateLinear j) (rationalPlaceTwo theta)) := by
    conv_lhs => rw [linear_eq_sum_coordinate (M theta)]
    simp only [map_sum, map_smul, cubicPlaceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [hcoord, cubicDirectRecover_basis_check]
  fin_cases r <;>
    simp [cubicDirectQuotient, singleCubicInput, coordinateLinear, Fin.sum_univ_succ] <;> ring

theorem neg_eq_self_f2 (x : F₂) : -x = x := by
  rw [← neg_one_mul]
  norm_num [N3Certificate.two_eq_zero_f2]

/-- The three rational-place cubic spaces are a direct sum modulo their
two-dimensional support kernels. -/
theorem rationalCubicDirectSum_kernel
    (M : Fin 3 → LinearForm) (h : rationalCubicDirectSum M = 0) :
    ∀ theta : Fin 3, ∃ a b : F₂,
      M theta = a • placeA theta + b • placeB theta := by
  have hq (r : Fin 18) : cubicDirectQuotient M r = 0 := by
    rw [← cubicDirectRecover_sum M r, h, map_zero]
  intro theta
  fin_cases theta
  · refine ⟨M 0 0, M 0 4, ?_⟩
    funext i
    fin_cases i
    · simp [placeA, placeB]
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 0
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 1
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 2
    · simp [placeA, placeB]
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 3
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 4
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 5
  · refine ⟨M 1 0, M 1 4, ?_⟩
    funext i
    fin_cases i
    · simp [placeA, placeB]
    · simp only [Fin.mk_one, Fin.isValue, placeA, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty, placeB,
      Pi.add_apply, add_zero]
      have hr := hq 6
      simp only [cubicDirectQuotient, Fin.isValue, Matrix.cons_val] at hr
      exact (add_eq_zero_iff_eq_neg.mp hr).trans (neg_eq_self_f2 _)
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, placeA, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero,
      Matrix.smul_empty, placeB, Pi.add_apply, Matrix.cons_val, add_zero]
      have hr := hq 7
      simp only [cubicDirectQuotient, Fin.isValue, Matrix.cons_val] at hr
      exact (add_eq_zero_iff_eq_neg.mp hr).trans (neg_eq_self_f2 _)
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, placeA, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero,
      Matrix.smul_empty, placeB, Pi.add_apply, Matrix.cons_val, add_zero]
      have hr := hq 8
      simp only [cubicDirectQuotient, Fin.isValue, Matrix.cons_val] at hr
      exact (add_eq_zero_iff_eq_neg.mp hr).trans (neg_eq_self_f2 _)
    · simp [placeA, placeB]
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, placeA, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero,
      Matrix.smul_empty, placeB, Pi.add_apply, Matrix.cons_val, zero_add]
      have hr := hq 9
      simp only [cubicDirectQuotient, Fin.isValue, Matrix.cons_val] at hr
      exact (add_eq_zero_iff_eq_neg.mp hr).trans (neg_eq_self_f2 _)
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, placeA, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero,
      Matrix.smul_empty, placeB, Pi.add_apply, Matrix.cons_val, zero_add]
      have hr := hq 10
      simp only [cubicDirectQuotient, Fin.isValue, Matrix.cons_val] at hr
      exact (add_eq_zero_iff_eq_neg.mp hr).trans (neg_eq_self_f2 _)
    · simp only [Fin.mk_one, Fin.isValue, Fin.reduceFinMk, placeA, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero,
      Matrix.smul_empty, placeB, Pi.add_apply, Matrix.cons_val, zero_add]
      have hr := hq 11
      simp only [cubicDirectQuotient, Fin.isValue, Matrix.cons_val] at hr
      exact (add_eq_zero_iff_eq_neg.mp hr).trans (neg_eq_self_f2 _)
  · refine ⟨M 2 3, M 2 7, ?_⟩
    funext i
    fin_cases i
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 12
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 13
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 14
    · simp [placeA, placeB]
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 15
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 16
    · simpa [placeA, placeB, cubicDirectQuotient] using hq 17
    · simp [placeA, placeB]

end

end N4
end UnrestrictedBooleanMul
