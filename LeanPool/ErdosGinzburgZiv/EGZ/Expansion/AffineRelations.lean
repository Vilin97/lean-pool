/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.RationalApproximation
public import LeanPool.ErdosGinzburgZiv.EGZ.Balanced.IntegerApproximation
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SlabArithmetic

/-!
# Integer affine relations

Clearing denominators in a rational generalized inverse produces a finite
family of integer relations. Their evaluations measure the discrepancy
from a function that factors through the original constraint matrix.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace EGZ.Expansion

variable {I J : Type*} [Fintype I] [Fintype J]

/-- An integer multiple of a generalized inverse. -/
theorem exists_integer_generalized_inverse (A : Matrix I J ℤ) :
    ∃ (N : ℕ) (M : Matrix J I ℤ), 0 < N ∧ A * M * A = (N : ℤ) • A := by
  classical
  let AQ : Matrix I J ℚ := A.map (Int.castRingHom ℚ)
  obtain ⟨B, hB⟩ := BalancedCombination.exists_matrix_generalized_inverse AQ
  obtain ⟨N, hN, m, hm⟩ := BalancedCombination.exists_common_denominator
    (fun ij : J × I ↦ B ij.1 ij.2)
  let M : Matrix J I ℤ := fun j i ↦ m (j, i)
  have hMQ : M.map (Int.castRingHom ℚ) = (N : ℚ) • B := by
    ext j i
    have h := hm (j, i)
    change (m (j, i) : ℚ) = (N : ℚ) * B j i
    exact_mod_cast h
  have hQ : AQ * M.map (Int.castRingHom ℚ) * AQ = (N : ℚ) • AQ := by
    rw [hMQ, Matrix.mul_smul, Matrix.smul_mul, hB]
  refine ⟨N, M, hN, ?_⟩
  ext i j
  have h := congrArg (fun B : Matrix I J ℚ ↦ B i j) hQ
  dsimp [AQ, Matrix.mul_apply, Matrix.map, Matrix.smul_apply] at h
  exact_mod_cast h

theorem exists_integer_relations [DecidableEq J] (A : Matrix I J ℤ) :
    ∃ (N : ℕ) (B : Matrix J I ℤ) (Q : Matrix J J ℤ),
      0 < N ∧ Q = (N : ℤ) • (1 : Matrix J J ℤ) - B * A ∧ A * Q = 0 := by
  classical
  obtain ⟨N, B, hN, hB⟩ := exists_integer_generalized_inverse A
  refine ⟨N, B, (N : ℤ) • (1 : Matrix J J ℤ) - B * A, hN, rfl, ?_⟩
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hB, sub_self]

/-- The rows recording total mass and every affine coordinate. -/
def affineConstraintMatrix {r : ℕ} (S : Finset (IntCoord r)) :
    Matrix (Option (Fin r)) S ℤ := fun i q ↦ i.elim 1 (fun j ↦ q.val j)

theorem exists_affine_relations {r : ℕ} (S : Finset (IntCoord r)) :
    ∃ (N : ℕ) (B : Matrix S (Option (Fin r)) ℤ) (Q : Matrix S S ℤ),
      0 < N ∧ Q = (N : ℤ) • (1 : Matrix S S ℤ) - B * affineConstraintMatrix S ∧
      affineConstraintMatrix S * Q = 0 :=
  exists_integer_relations (affineConstraintMatrix S)

theorem relation_column_sum {r : ℕ} {S : Finset (IntCoord r)}
    {Q : Matrix S S ℤ} (hQ : affineConstraintMatrix S * Q = 0) (q : S) :
    ∑ z, Q z q = 0 := by
  have h := congrArg (fun M : Matrix (Option (Fin r)) S ℤ ↦ M none q) hQ
  simpa [Matrix.mul_apply, affineConstraintMatrix] using h

theorem relation_column_weighted_sum {r : ℕ} {S : Finset (IntCoord r)}
    {Q : Matrix S S ℤ} (hQ : affineConstraintMatrix S * Q = 0) (q : S) :
    ∑ z, Q z q • z.val = 0 := by
  ext i
  have h := congrArg (fun M : Matrix (Option (Fin r)) S ℤ ↦ M (some i) q) hQ
  simpa [Matrix.mul_apply, affineConstraintMatrix, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul, mul_comm] using h

/-- A signed affine relation is represented by its positive and negative
parts, which have the same nonnegative total size. -/
theorem relation_column_pos_neg_sum {r : ℕ} {S : Finset (IntCoord r)}
    {Q : Matrix S S ℤ} (hQ : affineConstraintMatrix S * Q = 0) (q : S) :
    ∑ z, (Q z q).toNat = ∑ z, (-Q z q).toNat := by
  have h : (∑ z, ((Q z q).toNat : ℤ)) - ∑ z, ((-Q z q).toNat : ℤ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp only [Int.toNat_sub_toNat_neg]
    exact relation_column_sum hQ q
  exact_mod_cast sub_eq_zero.mp h

theorem relation_column_pos_neg_weighted_sum {r : ℕ} {S : Finset (IntCoord r)}
    {Q : Matrix S S ℤ} (hQ : affineConstraintMatrix S * Q = 0) (q : S) :
    ∑ z, (Q z q).toNat • z.val = ∑ z, (-Q z q).toNat • z.val := by
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simp only [← natCast_zsmul, ← sub_smul, Int.toNat_sub_toNat_neg]
  exact relation_column_weighted_sum hQ q

theorem relation_column_evaluation_pos_neg {R : Type*} [AddCommGroup R]
    {Q : Matrix J J ℤ} (q : J) (v : J → R) :
    (∑ z, (Q z q).toNat • v z) - (∑ z, (-Q z q).toNat • v z) =
      ∑ z, Q z q • v z := by
  rw [← Finset.sum_sub_distrib]
  simp only [← natCast_zsmul, ← sub_smul, Int.toNat_sub_toNat_neg]

theorem relation_evaluation {R : Type*} [CommRing R] [DecidableEq J]
    {A : Matrix I J ℤ} {N : ℕ} {B : Matrix J I ℤ} {Q : Matrix J J ℤ}
    (hQ : Q = (N : ℤ) • (1 : Matrix J J ℤ) - B * A) (v : J → R) :
    (Q.map (Int.castRingHom R)).transpose *ᵥ v =
      (N : R) • v - (A.map (Int.castRingHom R)).transpose *ᵥ
        ((B.map (Int.castRingHom R)).transpose *ᵥ v) := by
  classical
  have hmap : Q.map (Int.castRingHom R) =
      (N : R) • (1 : Matrix J J R) -
        B.map (Int.castRingHom R) * A.map (Int.castRingHom R) := by
    ext i j
    have hij := congrArg (fun M : Matrix J J ℤ ↦ M i j) hQ
    change Q i j = (N : ℤ) * (if i = j then 1 else 0) - ∑ k, B i k * A k j at hij
    change (Q i j : R) = (N : R) * (if i = j then 1 else 0) -
      ∑ k, (B i k : R) * (A k j : R)
    have hc := congrArg (fun z : ℤ ↦ (z : R)) hij
    split_ifs at * <;> simpa using hc
  rw [hmap, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.transpose_mul,
    Matrix.mulVec_mulVec]

theorem affine_relation_evaluation {r : ℕ} {R : Type*} [CommRing R]
    {S : Finset (IntCoord r)} {N : ℕ} {B : Matrix S (Option (Fin r)) ℤ}
    {Q : Matrix S S ℤ}
    (hQ : Q = (N : ℤ) • (1 : Matrix S S ℤ) - B * affineConstraintMatrix S)
    (v : S → R) (q : S) :
    ∑ z, (Q z q : R) * v z = (N : R) * v q -
      ((∑ z, (B z none : R) * v z) +
        ∑ i : Fin r, (∑ z, (B z (some i) : R) * v z) * (q.val i : R)) := by
  classical
  have h := congrFun (relation_evaluation hQ v) q
  change (∑ z, (Q z q : R) * v z) = (N : R) * v q -
    ∑ i : Option (Fin r), ((i.elim 1 (fun j ↦ q.val j) : ℤ) : R) *
      (∑ z, (B z i : R) * v z) at h
  simpa [Fintype.sum_option, mul_comm] using h

/-- The affine function encoded by its constant and linear coefficients. -/
def affineFromCoefficients {R : Type*} [CommRing R] {r : ℕ}
    (a : Option (Fin r) → R) : (Fin r → R) →ᵃ[R] R :=
  AffineMap.const R (Fin r → R) (a none) +
    ∑ i : Fin r, a (some i) • AffineMap.proj i

theorem affineFromCoefficients_apply {R : Type*} [CommRing R] {r : ℕ}
    (a : Option (Fin r) → R) (x : Fin r → R) :
    affineFromCoefficients a x = a none + ∑ i, a (some i) * x i := by
  change a none + (∑ i : Fin r, a (some i) •
    (AffineMap.proj i : (Fin r → R) →ᵃ[R] R)) x = _
  congr 1
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change a (some i) * x i + (∑ j ∈ s, a (some j) •
      (AffineMap.proj j : (Fin r → R) →ᵃ[R] R)) x = _
    rw [ih]

theorem affine_relation_residual_bounded {p r t N W L : ℕ}
    {S : Finset (IntCoord r)} {B : Matrix S (Option (Fin r)) ℤ}
    {Q : Matrix S S ℤ}
    (hQ : Q = (N : ℤ) • (1 : Matrix S S ℤ) - B * affineConstraintMatrix S)
    (v : S → ZMod p) (ξ : FpCoord p t →ₗ[ZMod p] ZMod p)
    (q : S) (x : FpCoord p (r + t)) (hx : Coord.first r t x = q.val.mod p)
    (hlocal : HasBoundedRepresentative p W (ξ (Coord.last r t x) - v q))
    (hrelation : HasBoundedRepresentative p L (∑ z, (Q z q : ZMod p) * v z)) :
    HasBoundedRepresentative p (N * W + L)
      (((N : ZMod p) • (ξ.comp (Coord.last r t)).toAffineMap -
        (affineFromCoefficients ((B.map (Int.castRingHom (ZMod p))).transpose *ᵥ v)).comp
          (Coord.first r t).toAffineMap) x) := by
  have hcalc := affine_relation_evaluation hQ v q
  have h := (hlocal.int_mul (N : ℤ)).add hrelation
  simp only [Int.natAbs_natCast, Int.cast_natCast] at h
  convert h using 1
  change (N : ZMod p) * ξ (Coord.last r t x) -
    affineFromCoefficients ((B.map (Int.castRingHom (ZMod p))).transpose *ᵥ v)
      (Coord.first r t x) = _
  rw [affineFromCoefficients_apply, hx]
  change (N : ZMod p) * ξ (Coord.last r t x) -
    ((∑ z, (B z none : ZMod p) * v z) +
      ∑ i, (∑ z, (B z (some i) : ZMod p) * v z) * (q.val i : ZMod p)) = _
  rw [hcalc]
  ring

/-- Scaling a nonzero functional in the fibre directions and subtracting
an arbitrary affine function of the labels still distinguishes a fibre. -/
theorem nonconstant_scaled_fibre_residual {p r t N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hNp : N < p)
    (ξ : FpCoord p t →ₗ[ZMod p] ZMod p) (hξ : ξ ≠ 0)
    (a : FpCoord p r →ᵃ[ZMod p] ZMod p) :
    NonconstantOnFibers (Coord.first r t)
      ((N : ZMod p) • (ξ.comp (Coord.last r t)).toAffineMap -
        a.comp (Coord.first r t).toAffineMap) := by
  classical
  have hNz : (N : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hN hNp
  have hex : ∃ z, ξ z ≠ 0 := by
    by_contra! h
    apply hξ
    apply LinearMap.ext
    intro z
    exact h z
  obtain ⟨z, hz⟩ := hex
  let v := Coord.append (AffineMap.const (ZMod p) (FpCoord p t) (0 : FpCoord p r))
    (AffineMap.id (ZMod p) (FpCoord p t)) z
  have hvfirst : Coord.first r t v = 0 := by simp [v]
  have hvlast : Coord.last r t v = z := by simp [v]
  refine ⟨v, 0, by simpa using hvfirst, ?_⟩
  change (N : ZMod p) * ξ (Coord.last r t v) - a (Coord.first r t v) ≠
    (N : ZMod p) * ξ (Coord.last r t 0) - a (Coord.first r t 0)
  rw [hvfirst, hvlast, (Coord.first r t).map_zero, (Coord.last r t).map_zero,
    ξ.map_zero, mul_zero]
  exact sub_left_inj.not.mpr (mul_ne_zero hNz hz)

end EGZ.Expansion
