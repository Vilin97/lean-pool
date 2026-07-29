/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Rational two-torsion bounds

This file bounds the two-torsion of a Weierstrass curve in characteristic
different from two and excludes an elementary abelian subgroup of order eight.
These are elementary structural inputs to the torsion classification in
Mazur's theorem.
-/

namespace LeanPool.MazurTorsionFoundations

open scoped WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve F) [NeZero (2 : F)]

noncomputable section

private local instance instDecidableEqLeanPool : DecidableEq F := Classical.decEq F

private noncomputable def twoTorsionRootMap :
    {P : (E⁄F).Point // (2 : ℕ) • P = 0} →
      Option (E.twoTorsionPolynomial.toPoly.rootSet F)
  | ⟨0, _⟩ => none
  | ⟨WeierstrassCurve.Affine.Point.some x y h, htwo⟩ => some ⟨x, by
      rw [Polynomial.mem_rootSet_of_ne]
      · simp only [Polynomial.aeval_def]
        rw [Algebra.algebraMap_self, Polynomial.eval₂_id]
        have hneg : WeierstrassCurve.Affine.Point.some x y h =
            -WeierstrassCurve.Affine.Point.some x y h := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        have hy : y = (E⁄F).negY x y := by
          simpa only [WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.some.injEq, true_and] using hneg
        have heq := h.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        simp only [WeierstrassCurve.Affine.negY] at hy
        change y = -y - E.a₁ * x - E.a₃ at hy
        change y ^ 2 + E.a₁ * x * y + E.a₃ * y =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ at heq
        have hlin : 2 * y + E.a₁ * x + E.a₃ = 0 := by
          linear_combination hy
        simp only [Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆]
        linear_combination -4 * heq +
          (2 * y + E.a₁ * x + E.a₃) * hlin
      · intro hp
        have hdeg :
            E.twoTorsionPolynomial.toPoly.natDegree = 3 :=
          Cubic.natDegree_of_a_ne_zero' (by
            rw [show (4 : F) = 2 ^ 2 by norm_num]
            exact pow_ne_zero 2 (NeZero.ne (2 : F)))
        rw [hp, Polynomial.natDegree_zero] at hdeg
        omega⟩

private theorem twoTorsionRootMap_injective :
    Function.Injective (twoTorsionRootMap E) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [twoTorsionRootMap] at h
  | some x y hxy =>
      cases Q with
      | zero => simp [twoTorsionRootMap] at h
      | some x' y' hxy' =>
          simp only [twoTorsionRootMap, Option.some.injEq,
            Subtype.mk.injEq] at h
          have hxrep :
              (WeierstrassCurve.Affine.Point.some x y hxy).xRep =
                (WeierstrassCurve.Affine.Point.some x' y' hxy').xRep := by
            simp [h]
          rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
            with heq | heq
          · exact heq
          · have hself :
                WeierstrassCurve.Affine.Point.some x' y' hxy' =
                  -WeierstrassCurve.Affine.Point.some x' y' hxy' := by
              rw [← add_eq_zero_iff_eq_neg]
              simpa [two_nsmul] using hQ
            rw [hself.symm] at heq
            exact heq

/-- Over a field of characteristic different from two, an elliptic curve has
at most four points killed by `2`. -/
theorem ncard_two_torsion_le_four :
    Set.ncard {P : (E⁄F).Point | (2 : ℕ) • P = 0} ≤ 4 := by
  rw [← Nat.card_coe_set_eq]
  calc
    Nat.card {P : (E⁄F).Point // (2 : ℕ) • P = 0}
        ≤ Nat.card (Option
          (E.twoTorsionPolynomial.toPoly.rootSet F)) :=
      Nat.card_le_card_of_injective (twoTorsionRootMap E)
        (twoTorsionRootMap_injective E)
    _ = Nat.card (E.twoTorsionPolynomial.toPoly.rootSet F) + 1 := by
      rw [Finite.card_option]
    _ ≤ 3 + 1 := by
      gcongr
      rw [Nat.card_coe_set_eq]
      exact (E.twoTorsionPolynomial.toPoly.ncard_rootSet_le F).trans_eq
        (Cubic.natDegree_of_a_ne_zero' (by
          rw [show (4 : F) = 2 ^ 2 by norm_num]
          exact pow_ne_zero 2 (NeZero.ne (2 : F))))
    _ = 4 := by norm_num

/-- There is no embedding of an elementary abelian group of order eight into
the rational points of a Weierstrass curve in characteristic different from
two. This is the full-`2`-torsion obstruction used in Mazur's classification. -/
theorem not_injective_zmod_two_cube
    (φ : (ZMod 2 × ZMod 2 × ZMod 2) →+ (E⁄F).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  have htwo : ∀ z : ZMod 2 × ZMod 2 × ZMod 2, (2 : ℕ) • z = 0 := by
    decide
  let f : (ZMod 2 × ZMod 2 × ZMod 2) →
      {P : (E⁄F).Point // (2 : ℕ) • P = 0} :=
    fun z ↦ ⟨φ z, by rw [← map_nsmul, htwo z, map_zero]⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact hφ (Subtype.ext_iff.mp hxy)
  letI : Finite {P : (E⁄F).Point // (2 : ℕ) • P = 0} :=
    Finite.of_injective (twoTorsionRootMap E)
      (twoTorsionRootMap_injective E)
  have hcard :
      Nat.card (ZMod 2 × ZMod 2 × ZMod 2) ≤
        Nat.card {P : (E⁄F).Point // (2 : ℕ) • P = 0} :=
    Nat.card_le_card_of_injective f hf
  have htarget :
      Nat.card {P : (E⁄F).Point // (2 : ℕ) • P = 0} ≤ 4 := by
    change Set.ncard {P : (E⁄F).Point | (2 : ℕ) • P = 0} ≤ 4
    exact ncard_two_torsion_le_four E
  rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod] at hcard
  omega

end

end LeanPool.MazurTorsionFoundations
